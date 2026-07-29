"""
EVM IR数据模型。

本模块定义用于表示EVM IR块和操作的数据结构。
"""

from typing import List, Optional, Dict, Any, TYPE_CHECKING
from dataclasses import dataclass, field

if TYPE_CHECKING:
    from state.smt_state import SMTState


# Go 侧 Block.MaxDepth 的初值（ir/evm_ir.go:169），缺键时必须对齐它：
# 退化成 0 会让栈深度守卫把任何非空栈判成 overflow，验证静默空跑。
GO_MAX_INT64 = 2 ** 63 - 1


@dataclass
class EvmOperator:
    """表示IR中的EVM操作。"""
    
    kind: str  # 操作类型（例如，"ADD"、"PUSH"、"JUMP"）
    pc: int  # 程序计数器（原始字节码位置）
    immediate: Optional[int] = None  # 立即值（用于PUSH操作）
    param: Optional[int] = None  # 参数（用于PUSH、DUP、SWAP）
    is_static: bool = False  # 跳转是否为静态
    # 多目标跳转的候选目标集合（Go: EvmOperator.ImmediateSet）。
    # 跳转目标来自多个调用点的不同 return address 时由符号跳转解析器填充，
    # x86 侧对应 impl_amd64.go compileEVMJUMP 里逐个 CMPQ 的比较链。
    immediate_set: Optional[List[int]] = None
    block: Optional['EVMBlock'] = None  # 对包含块的引用
    
    @classmethod
    def from_json(cls, data: Dict[str, Any], block: Optional['EVMBlock'] = None) -> 'EvmOperator':
        """从JSON数据创建EvmOperator。
        
        Args:
            data: 包含操作符数据的字典
            block: 对包含块的可选引用
            
        Returns:
            EvmOperator实例
        """
        # 处理立即值：现在Go端总是字符串，但支持int以向后兼容
        immediate = data.get('immediate')
        if immediate is not None:
            # 转换为int（Python 3 int支持任意精度）
            # Go端现在总是使用字符串，但我们支持int以向后兼容
            immediate = int(immediate)

        # immediate_set 与 immediate 同样由 Go 端导出为十进制字符串列表
        immediate_set = data.get('immediate_set')
        if immediate_set is not None:
            immediate_set = [int(v) for v in immediate_set]

        return cls(
            kind=data.get('kind', ''),
            pc=data.get('pc', 0),
            immediate=immediate,
            param=data.get('param'),
            is_static=data.get('is_static', False),
            immediate_set=immediate_set,
            block=block
        )
    
    def to_json(self) -> Dict[str, Any]:
        """Convert to JSON-serializable dictionary.
        
        Returns:
            Dictionary representation
        """
        result = {
            'kind': self.kind,
            'pc': self.pc,
        }
        if self.immediate is not None:
            result['immediate'] = self.immediate
        if self.immediate_set:
            result['immediate_set'] = list(self.immediate_set)
        if self.param is not None:
            result['param'] = self.param
        if self.is_static:
            result['is_static'] = self.is_static
        return result
    
    def to_z3(self, state: 'SMTState') -> 'SMTState':
        """将此操作符转换为Z3公式，更新状态。
        
        这是Alive2风格的直接公式构建方法。
        委托给语义模块进行实际实现。
        
        Args:
            state: 当前SMT状态（将被修改）
            
        Returns:
            更新后的SMT状态
        """
        # 在此处导入以避免循环依赖
        from evm_ir.semantics import evm_operator_to_z3
        return evm_operator_to_z3(self, state)


@dataclass
class EVMBlock:
    """表示IR中的EVM基本块。"""
    
    pc: int  # 块标签号（PC地址）
    stack_depth: int  # 此块使用的栈深度
    min_depth: int  # 所需的最小栈深度
    max_depth: int  # 最大栈深度
    static_gas: int  # 静态gas成本
    is_jump_target: bool  # 此块是否为跳转目标
    is_inner_block: bool  # 这是否为内部块
    is_stop: bool  # 块是否包含STOP指令
    operations: List[EvmOperator] = field(default_factory=list)  # 此块中的操作
    
    @classmethod
    def from_json(cls, data: Dict[str, Any]) -> 'EVMBlock':
        """从JSON数据创建EVMBlock。
        
        Args:
            data: 包含块数据的字典
            
        Returns:
            EVMBlock实例
        """
        block = cls(
            pc=data.get('pc', 0),
            stack_depth=data.get('stack_depth', 0),
            min_depth=data.get('min_depth', 0),
            max_depth=data.get('max_depth', GO_MAX_INT64),
            static_gas=data.get('static_gas', 0),
            is_jump_target=data.get('is_jump_target', False),
            is_inner_block=data.get('is_inner_block', False),
            is_stop=data.get('is_stop', False),
        )
        
        # 解析操作
        operations_data = data.get('operations', [])
        for op_data in operations_data:
            op = EvmOperator.from_json(op_data, block=block)
            block.operations.append(op)
        
        return block
    
    def to_json(self) -> Dict[str, Any]:
        """转换为JSON可序列化字典。
        
        Returns:
            字典表示
        """
        return {
            'pc': self.pc,
            'stack_depth': self.stack_depth,
            'min_depth': self.min_depth,
            'max_depth': self.max_depth,
            'static_gas': self.static_gas,
            'is_jump_target': self.is_jump_target,
            'is_inner_block': self.is_inner_block,
            'is_stop': self.is_stop,
            'operations': [op.to_json() for op in self.operations]
        }
    
    def __repr__(self):
        return (f"EVMBlock(pc={self.pc}, stack_depth={self.stack_depth}, "
                f"ops={len(self.operations)}, is_jump_target={self.is_jump_target})")

