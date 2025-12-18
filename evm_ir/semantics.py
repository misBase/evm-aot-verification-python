"""
EVM IR语义建模。

本模块使用Z3为EVM IR操作提供语义建模。
"""

from z3 import BitVec, BitVecRef, BitVecVal, Concat, Extract, If, UGE, ULT, And, Or
from typing import List, Optional, Dict, Any, Tuple
from .models import EVMBlock, EvmOperator
from common.uint256 import Uint256
from state.smt_state import SMTState, EVMStackState, EVMMemoryState

# RETURN指令的常量
MAX_RETURN_DATA_SIZE = 256  # 最大返回数据大小（字节）（256字节 = 2048位）


class EVMOperationSemantics:
    """单个EVM操作的语义建模。"""
    
    def add_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """构建EVM ADD操作的逻辑公式。
        
        EVM ADD语义：
          - 输入：两个256位值a和b（表示为4x64位limb）
          - 输出：(a + b) mod 2^256
          - 实现：委托给Uint256.add_semantics()方法
          
        这遵循与Go实现相同的模式，其中
        opAdd在uint256类型上调用y.Add(&x, y)。
          
        Args:
            a: 第一个256位操作数（大小为256的Z3 BitVec，或Uint256）
            b: 第二个256位操作数（大小为256的Z3 BitVec，或Uint256）
            
        Returns:
            表示(a + b) mod 2^256的逻辑公式，作为256位BitVec
        """
        # 如果输入是BitVec，则转换为Uint256
        # 检查它是否是BitVecRef（Z3的BitVec类型）
        if isinstance(a, BitVecRef) and a.size() == 256:
            a_uint = Uint256.from_bv256(a)
        elif isinstance(a, Uint256):
            a_uint = a
        elif hasattr(a, 'to_bv256'):
            a_uint = Uint256.from_bv256(a.to_bv256())
        else:
            raise ValueError(f"Unsupported type for operand a: {type(a)}")
        
        if isinstance(b, BitVecRef) and b.size() == 256:
            b_uint = Uint256.from_bv256(b)
        elif isinstance(b, Uint256):
            b_uint = b
        elif hasattr(b, 'to_bv256'):
            b_uint = Uint256.from_bv256(b.to_bv256())
        else:
            raise ValueError(f"Unsupported type for operand b: {type(b)}")
        
        # 调用Uint256.add_semantics()方法（类似于Go的y.Add(&x, y)）
        result_uint = a_uint.add_semantics(b_uint)
        
        # 将结果转换回256位BitVec
        return result_uint.to_bv256()
    
    def push_semantics(self, immediate: int, param: int = 1) -> BitVec:
        """构建EVM PUSH操作的逻辑公式。
        
        Args:
            immediate: 要推送的立即值
            param: 字节数（PUSH1-PUSH32为1-32）
            
        Returns:
            表示推送值的逻辑公式，作为256位BitVec
        """
        # PUSH操作将立即值推送到栈上
        # 立即值右填充到256位
        return BitVecVal(immediate, 256)
    
    def operation_semantics(self, op: EvmOperator, inputs: List[BitVec]) -> BitVec:
        """获取操作的语义公式。
        
        Args:
            op: EVM操作
            inputs: 输入值列表（256位BitVecs）
            
        Returns:
            作为256位BitVec的输出值
        """
        kind = op.kind.upper()
        
        if kind == "ADD":
            if len(inputs) < 2:
                raise ValueError("ADD requires 2 inputs")
            return self.add_semantics(inputs[0], inputs[1])
        
        elif kind.startswith("PUSH"):
            if op.immediate is None:
                raise ValueError("PUSH operation requires immediate value")
            return self.push_semantics(op.immediate, op.param or 1)
        
        else:
            raise NotImplementedError(f"Operation {kind} not yet implemented")


class EVMIRSemantics:
    """EVM IR块的语义建模。"""
    
    def __init__(self):
        """初始化EVM IR语义模型。"""
        self.op_semantics = EVMOperationSemantics()

def evm_operator_to_z3(op: EvmOperator, state: SMTState) -> SMTState:
    """将EVM操作符转换为Z3公式，更新状态。
    
    这是Alive2风格的直接公式构建方法。
    每个操作符直接构建Z3表达式，无需执行模拟。
    
    Args:
        op: 要转换的EVM操作符
        state: 当前SMT状态（将被修改）
        
    Returns:
        更新后的SMT状态
    """
    kind = op.kind.upper()
    op_semantics = EVMOperationSemantics()
    
    if kind == "TAG":
        # TAG对语义是无操作（仅标记块入口）
        return state
    
    elif kind == "BLOCKEND":
        # BLOCKEND对语义是无操作（仅标记块结束）
        return state
    
    elif kind == "ADD":
        # ADD：弹出两个值，相加，推送结果
        # 使用Z3 Array：value_b = Select(Stack, SP-1), value_a = Select(Stack, SP-2)
        # result = value_a + value_b
        # Stack' = Store(Stack, SP-2, result), SP' = SP - 1
        
        # 从栈中弹出两个值
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        
        # 计算加法
        result = op_semantics.add_semantics(a, b)
        
        # 推送结果
        new_stack_state = stack_after_pop2.push(result)
        state.evm_stack = new_stack_state
        return state
    
    elif kind.startswith("PUSH"):
        # PUSH：将立即值推送到栈上
        # 使用Z3 Array：SP' = SP + 1, Stack' = Store(Stack, SP, value)
        if op.immediate is None:
            raise ValueError(f"PUSH operation missing immediate at pc={op.pc}")
        
        value = op_semantics.push_semantics(op.immediate, op.param or 1)
        new_stack_state = state.evm_stack.push(value)
        state.evm_stack = new_stack_state
        return state
    
    elif kind == "MLOAD":
        # MLOAD：从内存加载32字节，推送到栈上
        # 使用Z3 Array：offset = Select(Stack, SP-1)
        # value = load_256bit(Memory, offset), Stack' = Store(Stack, SP-1, value)
        
        # 从栈中弹出偏移量
        offset_bv, stack_after_pop = state.evm_stack.pop()
        
        # 使用Z3 Array从内存加载32字节（256位）
        mem_value, new_memory_state = state.evm_memory.load_256bit(offset_bv)
        
        # 将加载的值推送到栈上
        new_stack_state = stack_after_pop.push(mem_value)
        
        # 更新状态
        state.evm_stack = new_stack_state
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "MSTORE":
        # MSTORE：弹出偏移量和值，将32字节存储到内存
        # 使用Z3 Array：value = Select(Stack, SP-1), offset = Select(Stack, SP-2)
        # Memory' = store_256bit(Memory, offset, value), SP' = SP - 2
        
        # 弹出值和偏移量
        value, stack_after_pop1 = state.evm_stack.pop()
        offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        
        # 使用Z3 Array将32字节（256位）存储到内存
        new_memory_state = state.evm_memory.store_256bit(offset_bv, value)
        
        # 更新状态
        state.evm_stack = stack_after_pop2
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "RETURN":
        # RETURN：弹出偏移量和长度，返回memory[offset:offset+length]
        # 从栈中弹出长度和偏移量
        length_bv, stack_after_pop1 = state.evm_stack.pop()
        offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        
        # 将长度截断为64位以便存储
        from z3 import Extract as Z3Extract
        if length_bv.size() == 256:
            return_length_64 = Z3Extract(63, 0, length_bv)
        elif length_bv.size() == 64:
            return_length_64 = length_bv
        else:
            raise ValueError(f"Unexpected length size: {length_bv.size()}")
        
        if offset_bv.size() == 256:
            return_offset_64 = Z3Extract(63, 0, offset_bv)
        elif offset_bv.size() == 64:
            return_offset_64 = offset_bv
        else:
            raise ValueError(f"Unexpected offset size: {offset_bv.size()}")
        
        # 在状态中存储返回偏移量和长度
        # 我们不提取数据 - 我们将在RefinementChecker中直接比较内存
        # 注意：RETURN只读取内存，不修改内存或MSize
        state.return_offset = return_offset_64
        state.return_length = return_length_64
        
        # 更新栈（两个值都已弹出）
        state.evm_stack = stack_after_pop2
        
        return state
    
    elif kind in ["JUMP", "JUMPI", "STOP", "REVERT"]:
        # 控制流操作 - 原样返回状态
        # 这些将在控制流级别处理
        return state
    
    else:
        # 未知操作 - 返回未更改的状态
        # TODO: 实现更多操作
        return state


def execute_block_with_tag(block: EVMBlock, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
    """使用基于TAG的路径分割执行块（级别1：块级合并）。
    
    TAG指令创建3条路径：
    - 路径1：SP < min_depth -> 错误路径（返回错误状态码）
    - 路径2：SP > max_depth -> 错误路径（返回错误状态码）
    - 路径3：min_depth <= SP <= max_depth -> 正常执行路径
    
    这3条路径使用Z3 If表达式合并。
    
    Args:
        block: 要执行的EVM块
        state: 初始SMT状态
        
    Returns:
        (merged_state, result_dict)元组，其中：
        - merged_state: 包含所有3条路径合并结果的状态
        - result_dict: 包含合并返回值的字典（offset, length, memory, has_return）
    """
    from z3 import IntVal
    
    # 获取栈指针作为Int（SP在EVMStackState中是Int类型）
    sp = state.evm_stack.SP
    
    # 将min_depth和max_depth转换为Int以便比较
    min_depth_int = IntVal(block.min_depth)
    max_depth_int = IntVal(block.max_depth)
    
    # 构建路径条件
    # 路径1：SP < min_depth -> 错误
    path1_condition = sp < min_depth_int
    
    # 路径2：SP > max_depth -> 错误
    path2_condition = sp > max_depth_int
    
    # 路径3：min_depth <= SP <= max_depth -> 正常
    path3_condition = And(sp >= min_depth_int, sp <= max_depth_int)
    
    # 执行路径1：SP < min_depth -> 错误路径
    # 错误路径返回错误状态码（无返回数据）
    from z3 import BitVecVal
    path1_state = state.copy()
    path1_state.return_offset = BitVecVal(0, 64)
    path1_state.return_length = BitVecVal(0, 64)
    # 注意：在实际实现中，我们可能会设置特定的错误状态码
    # 目前，我们使用0表示无返回（错误）
    
    # 执行路径2：SP > max_depth -> 错误路径
    path2_state = state.copy()
    path2_state.return_offset = BitVecVal(0, 64)
    path2_state.return_length = BitVecVal(0, 64)
    
    # 执行路径3：min_depth <= SP <= max_depth -> 正常执行
    path3_state = state.copy()
    
    # 执行块中的所有操作（跳过TAG和BLOCKEND）
    for op in block.operations:
        kind = op.kind.upper()
        if kind == "TAG":
            # TAG在块级别处理，这里跳过
            continue
        elif kind == "BLOCKEND":
            # BLOCKEND是标记，跳过
            continue
        else:
            # 执行操作
            path3_state = op.to_z3(path3_state)
    
    # 使用If表达式合并3条路径
    # 结构：If(path1_cond, path1_result, If(path2_cond, path2_result, path3_result))
    merged_state = state.copy()
    
    # 合并return_offset
    merged_state.return_offset = If(
        path1_condition,
        path1_state.return_offset,
        If(
            path2_condition,
            path2_state.return_offset,
            path3_state.return_offset
        )
    )
    
    # 合并return_length
    merged_state.return_length = If(
        path1_condition,
        path1_state.return_length,
        If(
            path2_condition,
            path2_state.return_length,
            path3_state.return_length
        )
    )
    
    # 合并内存（EVM内存Array）
    # 注意：内存合并更复杂，我们需要合并整个Array
    # 目前，我们使用path3的内存（正常路径），因为错误路径不修改内存
    # 在更复杂的实现中，我们可能需要逐元素合并Arrays
    merged_state.evm_memory = path3_state.evm_memory
    
    # 合并栈
    # 类似于内存，我们使用path3的栈进行正常执行
    # 错误路径不会有意义地修改栈
    merged_state.evm_stack = path3_state.evm_stack
    
    # 构建结果字典
    from z3 import BitVecVal
    has_return = merged_state.return_length != BitVecVal(0, 64)
    
    result = {
        'offset': merged_state.return_offset,
        'length': merged_state.return_length,
        'memory': merged_state.evm_memory.Memory,
        'base_addr': None,  # EVM内存使用直接偏移量
        'has_return': has_return
    }
    
    return merged_state, result

