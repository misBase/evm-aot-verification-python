"""
EVM Gas 状态建模。
"""

from typing import Optional
from z3 import BitVec, BitVecVal, BoolRef


class EVMGasState:
    """EVM Gas状态表示。

    跟踪Gas消耗：Gas : BitVec[64]
    支持静态Gas和动态Gas计算。
    """

    def __init__(self, initial_gas: Optional[BitVec] = None):
        """初始化EVM Gas状态。

        Args:
            initial_gas: 可选的初始Gas值
        """
        # Gas : BitVec[64]
        if initial_gas is None:
            self.Gas = BitVec('Gas', 64)
        else:
            self.Gas = initial_gas

    def consume_static(self, amount: int) -> 'EVMGasState':
        """扣减静态 Gas —— **纯减法，不钳零**。

        对齐 x86 makeStaticUseGas：`gas < staticGas` 时 JCS 跳 OOG handler、**根本不执行
        SUBQ**；所以"gas 不足"这一支是控制流分叉，不是把余额压成 0 继续跑。分叉由
        cfg_executor 的 TAG 守卫负责（无条件建模），到得了这里就意味着 gas 已足够，
        钳零分支恒假。

        曾经这里钳零而分叉被开关关掉，于是 gas=2/static=3 时 IR 给 STOPPED、AOT 给
        OUT_OF_GAS——终止分支不一致。别把钳零加回来。

        Args:
            amount: 要扣减的 Gas 数量。

        Returns:
            新的 EVMGasState。
        """
        from z3 import BitVecVal

        return EVMGasState(initial_gas=self.Gas - BitVecVal(amount, 64))

    def consume_dynamic(self, cost: BitVec) -> 'EVMGasState':
        """消耗动态Gas。

        Args:
            cost: 动态Gas成本（符号表达式）

        Returns:
            具有更新Gas的新EVMGasState
        """
        from z3 import If, UGT

        # 检查Gas溢出：如果Gas < cost，设为0（out of gas）
        new_gas = If(UGT(cost, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - cost)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

    def is_out_of_gas(self) -> BoolRef:
        """检查是否耗尽Gas（Gas == 0）。

        Note: future-use。生产 OOG 判断走 cfg_executor 的路径分叉（ULT(gas, cost)
        分叉出 error_code=OUT_OF_GAS 的终止路径），不依赖这里的「钳零后 == 0」。
        当前仅单测覆盖。

        Returns:
            BoolRef：如果Gas == 0则为True
        """
        from z3 import BitVecVal
        return self.Gas == BitVecVal(0, 64)

    def copy(self) -> 'EVMGasState':
        """创建Gas状态的副本。

        Returns:
            具有相同Gas的新EVMGasState实例
        """
        new_state = EVMGasState(initial_gas=self.Gas)
        return new_state


# --- 内存扩展动态 gas（阶段 1，镜像 go-hpc-evm memoryGasCost）---

# 协议常量（params/protocol_params.go）
_MEMORY_GAS = 3        # params.MemoryGas
_QUAD_COEFF_DIV = 512  # params.QuadCoeffDiv


def memory_expansion_fee(mem_size_bytes, last_gas_cost, requested_size_64):
    """纯计算 memoryGasCost 的 expansion 分支，返回 (fee, new_mem_size, new_last_gas)。

    Go memoryGasCost(newMemSize):
        memWords   = (newMemSize + 31) >> 5
        rounded    = memWords << 5
        if rounded > mem.Len():           # 仅扩容时才扣
            square   = memWords * memWords
            linCoef  = memWords * MemoryGas
            quadCoef = square / QuadCoeffDiv
            newTotal = linCoef + quadCoef
            fee      = newTotal - mem.lastGasCost
            mem.lastGasCost = newTotal
        else:
            fee = 0                        # lastGasCost 不变

    与 x86 codegen 对齐的两个关键点：
    - quad 用 **128-bit** UDiv（`UDiv(ZeroExt(64,square), 512_128)` 取低 64 位），
      使 div_bridge 能以 (udiv, 128) 配对 x86 的 `div r64`（dividend=Concat(RDX,RAX)
      是 128-bit），否则 64-bit UDiv 配不上 → Z3 bit-blast。
    - 扣减/字段更新只在 expands 时发生，避免连续内存操作过扣。

    **不改 state、不注入 assumption**：写回哪几项由调用方决定——gas 错误分支的快照
    要求各不相同（cap/溢出分支一项都不写、dynamic-OOG 分支只写 lastGasCost），
    耦合在一起就没法分别构造。详见 evm_ir.semantics._charge_dynamic_gas。

    Args:
        mem_size_bytes: 当前 [R13+0x18] = mem.Len()（rounded byte size）。
        last_gas_cost: 当前 [R13+0x20] = mem.lastGasCost。
        requested_size_64: 本次访问触及的最高字节+1（如 MSTORE=offset+32）。

    Returns:
        (fee, new_mem_size, new_last_gas)，均为 64-bit BitVec。
    """
    from z3 import BitVecVal, ZeroExt, Extract, UDiv, UGT, If, LShR

    thirty_one = BitVecVal(31, 64)
    # memWords = (requested + 31) >> 5
    mem_words = LShR(requested_size_64 + thirty_one, BitVecVal(5, 64))
    # rounded = memWords << 5
    rounded = mem_words << BitVecVal(5, 64)

    # square = memWords * memWords（cap 内 < 2^64，但用 128-bit 表达保证与 x86
    # 的 128-bit dividend 对齐）
    square_128 = ZeroExt(64, mem_words) * ZeroExt(64, mem_words)
    # quad = (square / 512)，128-bit UDiv 取低 64 位（镜像 x86 div r64）
    quad_128 = UDiv(square_128, BitVecVal(_QUAD_COEFF_DIV, 128))
    quad_64 = Extract(63, 0, quad_128)
    # linCoef = memWords * MemoryGas
    lin_64 = mem_words * BitVecVal(_MEMORY_GAS, 64)
    new_total = lin_64 + quad_64

    expands = UGT(rounded, mem_size_bytes)
    fee = If(expands, new_total - last_gas_cost, BitVecVal(0, 64))
    new_mem_size = If(expands, rounded, mem_size_bytes)
    new_last_gas = If(expands, new_total, last_gas_cost)
    return fee, new_mem_size, new_last_gas


def charge_memory_expansion_gas(state, requested_size_64):
    """**test-only**：memory_expansion_fee 的就地封装。

    生产路径走 evm_ir.semantics._charge_dynamic_gas（累加总额后判一次 OOG 并挂错误
    分支）；本函数只剩单测在用。

    side-channel 字段语义：
    - callengine_memory_size_bytes  = [R13+0x18] = mem.Len()（rounded byte size）
    - callengine_memory_gas_used    = [R13+0x20] = mem.lastGasCost

    Args:
        state: SMTState；就地更新 evm_gas 与两个 callengine 字段。
        requested_size_64: 64-bit BitVec，本次访问触及的最高字节+1。

    Returns:
        更新后的 state（与入参同一对象）。
    """
    from z3 import BitVecVal, ULE

    # ⚠️ 这条 assumption 会**静默缩小验证域**（requested ≤ 0x1FFFFFFFE0，保证
    # memWords ≤ 0xFFFFFFFF ⟹ square < 2^64）。生产路径不再用它——_calc_mem_size_64
    # 把同一边界建成了真实的 OUT_OF_GAS 终态分支。别在新代码里调用本函数。
    state.add_assumption(ULE(requested_size_64, BitVecVal(0x1FFFFFFFE0, 64)))

    fee, new_mem_size, new_last_gas = memory_expansion_fee(
        state.callengine_memory_size_bytes,
        state.callengine_memory_gas_used,
        requested_size_64,
    )
    state.callengine_memory_size_bytes = new_mem_size
    state.callengine_memory_gas_used = new_last_gas
    state.evm_gas = state.evm_gas.consume_dynamic(fee)
    return state


# 协议常量
_SHA3_WORD_GAS = 6   # params.Sha3WordGas
_COPY_GAS = 3        # params.CopyGas

# CREATE 系 word gas（memoryGasCreate 的 gasConst）
INIT_CODE_WORD_GAS = 2                                   # params.InitCodeWordGas
CREATE2_WORD_GAS = INIT_CODE_WORD_GAS + _SHA3_WORD_GAS    # memoryCreate2GasN = 2+6

# LOG 协议常量（params/protocol_params.go）
_LOG_GAS = 375        # params.LogGas（每条 LOG 一次）
_LOG_TOPIC_GAS = 375  # params.LogTopicGas（每个 topic）
_LOG_DATA_GAS = 8     # params.LogDataGas（**每字节**，注意不是每 word）


def log_fee(n_topics, size_64):
    """纯计算 LOG 的常量 + data gas，镜像 go-hpc-evm gasLog / memoryLogGas codegen。

    Go gasLog（gas_table.go:214，x86 memoryLogGas codegen 全程可见）:
        gas  = memoryGasCost(memSize)          # 内存扩展（调用方另算）
        gas += LogGas                          # 375，常量
        gas += n * LogTopicGas                 # n*375，常量
        gas += requestedSize * LogDataGas      # **每字节** 8，size=stack.Back(1)

    与 SHA3/COPY 的 word gas 关键区别：LOG data gas 按**字节**计费（size*8）而非
    按 word，故不能复用 word_fee。本函数只算后三段。

    溢出健全性**依赖调用顺序**：调用点先经 memory_expansion_fee 的 cap 分支
    （requested ≤ 0x1FFFFFFFE0）加上 size ≤ requested，即保证 size*8 < 2^64，
    x86 makeSafeMul 的 overflow 分支恒假被剪。

    Args:
        n_topics: LOG 的 topic 数（int，0..4）。
        size_64: 64-bit BitVec，LOG 数据字节长度（栈 Back(1)）。

    Returns:
        64-bit BitVec fee。
    """
    from z3 import BitVecVal

    flat = BitVecVal(_LOG_GAS + n_topics * _LOG_TOPIC_GAS, 64)
    data_fee = size_64 * BitVecVal(_LOG_DATA_GAS, 64)
    return flat + data_fee


def charge_log_gas(state, n_topics, size_64):
    """**test-only**：log_fee 的就地封装，生产路径已无调用方（走 _charge_dynamic_gas）。

    Args:
        state: SMTState；就地扣减 evm_gas。
        n_topics: LOG 的 topic 数（int，0..4）。
        size_64: 64-bit BitVec，LOG 数据字节长度（栈 Back(1)）。
    """
    state.evm_gas = state.evm_gas.consume_dynamic(log_fee(n_topics, size_64))
    return state


def word_fee(word_len_64, word_gas_const):
    """纯计算「按 word 计费」的动态 gas（SHA3 / COPY / CREATE 系列）。

    镜像 Go memoryGasWithType / memoryGasCreate 的 word gas 段:
        words = toWordSize(word_len) = (word_len + 31) >> 5
        fee   = words * word_gas_const
    （在 memoryGasCost 之上叠加；SHA3=Sha3WordGas 6，COPY=CopyGas 3，
    CREATE=InitCodeWordGas 2，CREATE2=InitCodeWordGas+Sha3WordGas 8。）

    与 memoryGasCost 不同，word gas 基于「数据长度的 word 数」（SHA3 的 size /
    COPY 的 length），**不依赖也不更新 lastGasCost / memory size**——它是纯叠加。

    溢出健全性**依赖调用顺序**：调用点先经 memory_expansion_fee 的 cap 分支
    （requested ≤ 0x1FFFFFFFE0）加上 word_len ≤ requested，即保证
    words*word_gas_const（const≤8）< 2^64，x86 makeSafeMul 的 overflow 分支恒假被剪。
    **若将来在没有 cap 分支的地方调用本函数，必须自行保证 word_len ≤ 0x1FFFFFFFE0。**

    Args:
        word_len_64: 64-bit BitVec，按 word 计费的数据字节长度。
        word_gas_const: 每 word 的 gas（int）。

    Returns:
        64-bit BitVec fee。
    """
    from z3 import BitVecVal, LShR

    words = LShR(word_len_64 + BitVecVal(31, 64), BitVecVal(5, 64))
    return words * BitVecVal(word_gas_const, 64)


def charge_word_gas(state, word_len_64, word_gas_const):
    """**test-only**：word_fee 的就地封装，生产路径已无调用方（走 _charge_dynamic_gas）。

    Args:
        state: SMTState；就地扣减 evm_gas。
        word_len_64: 64-bit BitVec，按 word 计费的数据字节长度。
        word_gas_const: 每 word 的 gas（int）。
    """
    state.evm_gas = state.evm_gas.consume_dynamic(word_fee(word_len_64, word_gas_const))
    return state
