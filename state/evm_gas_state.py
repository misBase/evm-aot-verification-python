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
        """消耗静态Gas。

        Args:
            amount: 要消耗的Gas数量

        Returns:
            具有更新Gas的新EVMGasState

        Note（gas 一致性阶段 0 前提）:
            下面的 If(UGT(amount,Gas), 0, Gas-amount) 把 out-of-gas 钳到 0，
            这与 x86 makeStaticUseGas「gas<staticGas 时 JCS 跳 OOG handler、
            不再 SUBQ」的语义**仅在 gas 恒足前提下等价**（两侧都不触发 OOG）。
            阶段 0 靠 program_verifier 注入的 UGE(G, bound) 假设保证恒足。
            **不要**把「恒足」编进本函数（钳零逻辑要留给将来 OOG 一致性复用）。
        """
        from z3 import BitVecVal, If, UGT
        amount_bv = BitVecVal(amount, 64)

        # 检查Gas溢出：如果Gas < amount，设为0（out of gas）
        new_gas = If(UGT(amount_bv, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - amount_bv)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

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

        Note: future-use。生产 OOG 判断现在走 cfg_executor 的 OOG 路径分叉
        （ULT(gas, cost) 分叉出 error_code=OUT_OF_GAS 的终止路径），不依赖本方法的
        「钳零后 == 0」判断。保留供将来更细的 OOG 状态查询；当前仅单测覆盖。

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


def charge_memory_expansion_gas(state, requested_size_64):
    """对一次内存访问扣减内存扩展动态 gas，镜像 Go memoryGasCost 的 expansion branch。

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

    side-channel 字段语义：
    - callengine_memory_size_bytes  = [R13+0x18] = mem.Len()（rounded byte size）
    - callengine_memory_gas_used    = [R13+0x20] = mem.lastGasCost

    Args:
        state: SMTState；就地更新 evm_gas 与两个 callengine 字段。
        requested_size_64: 64-bit BitVec，本次访问触及的最高字节+1（如 MSTORE=offset+32）。

    Returns:
        更新后的 state（与入参同一对象）。

    Note（scope 前提）:
        调用方需在 success-path scope assumption 下保证 requested ≤ 0x1FFFFFFFE0
        ⟹ memWords ≤ 0xFFFFFFFF ⟹ square < 2^64（高 64 位为 0），x86 128-bit
        mul/div 的低 64 位结果才与此定义式安全对齐。
    """
    from z3 import BitVecVal, ZeroExt, Extract, UDiv, UGT, If, LShR, ULE

    # success-path scope assumption（**关键**）:requested ≤ 0x1FFFFFFFE0。
    # x86 memoryGasCost 在 newMemSize > 0x1FFFFFFFE0 时跳 GasUintOverflow/OOG、
    # 不走 mul/div 成功路径；EVM 侧这里继续算 memWords²/512。若不约束，验证器会
    # 拿「EVM 成功域」对「x86 OOG 域」比较 → 比较域不一致 → 假绿/误报。在所有
    # 内存扩展 gas 入口（本函数是唯一 chokepoint）统一加此 scope 约束。
    state.add_assumption(ULE(requested_size_64, BitVecVal(0x1FFFFFFFE0, 64)))

    thirty_one = BitVecVal(31, 64)
    # memWords = (requested + 31) >> 5
    mem_words = LShR(requested_size_64 + thirty_one, BitVecVal(5, 64))
    # rounded = memWords << 5
    rounded = mem_words << BitVecVal(5, 64)

    # square = memWords * memWords（scope 下 < 2^64，但用 128-bit 表达保证与 x86
    # 的 128-bit dividend 对齐）
    square_128 = ZeroExt(64, mem_words) * ZeroExt(64, mem_words)
    # quad = (square / 512)，128-bit UDiv 取低 64 位（镜像 x86 div r64）
    quad_128 = UDiv(square_128, BitVecVal(_QUAD_COEFF_DIV, 128))
    quad_64 = Extract(63, 0, quad_128)
    # linCoef = memWords * MemoryGas
    lin_64 = mem_words * BitVecVal(_MEMORY_GAS, 64)
    new_total = lin_64 + quad_64

    old_mem_size = state.callengine_memory_size_bytes
    old_last_gas = state.callengine_memory_gas_used

    expands = UGT(rounded, old_mem_size)
    fee = If(expands, new_total - old_last_gas, BitVecVal(0, 64))

    state.callengine_memory_size_bytes = If(expands, rounded, old_mem_size)
    state.callengine_memory_gas_used = If(expands, new_total, old_last_gas)
    state.evm_gas = state.evm_gas.consume_dynamic(fee)
    return state


# 协议常量
_SHA3_WORD_GAS = 6   # params.Sha3WordGas
_COPY_GAS = 3        # params.CopyGas

# LOG 协议常量（params/protocol_params.go）
_LOG_GAS = 375        # params.LogGas（每条 LOG 一次）
_LOG_TOPIC_GAS = 375  # params.LogTopicGas（每个 topic）
_LOG_DATA_GAS = 8     # params.LogDataGas（**每字节**，注意不是每 word）


def charge_log_gas(state, n_topics, size_64):
    """LOG 的常量 + data gas，镜像 go-hpc-evm gasLog / memoryLogGas codegen。

    Go gasLog（gas_table.go:215，x86 memoryLogGas codegen 全程可见）:
        gas  = memoryGasCost(memSize)          # 内存扩展（调用方先扣，见 _charge_log_gas）
        gas += LogGas                          # 375，常量
        gas += n * LogTopicGas                 # n*375，常量
        gas += requestedSize * LogDataGas      # **每字节** 8，size=stack.Back(1)

    与 SHA3/COPY 的 word gas 关键区别:LOG data gas 按**字节**计费（size*8），
    不是按 word（toWordSize），故不能复用 charge_word_gas。

    内存扩展部分由调用方（_charge_log_gas）单独调 charge_memory_expansion_gas，
    本函数只负责 LogGas + n*TopicGas + size*DataGas 三段叠加。

    溢出健全性（**依赖调用顺序**）:本函数不单独加 scope assumption。调用点
    _charge_log_gas 先调 charge_memory_expansion_gas，后者对 requested=offset+size
    加 `ULE(requested, 0x1FFFFFFFE0)`，而 size ≤ requested ⟹ size ≤ 0x1FFFFFFFE0
    ⟹ size*LogDataGas(8) < 2^64 不溢出，x86 makeSafeMul overflow 分支恒假被剪。

    Args:
        state: SMTState；就地扣减 evm_gas。
        n_topics: LOG 的 topic 数（int，0..4）。
        size_64: 64-bit BitVec，LOG 数据字节长度（栈 Back(1)）。
    """
    from z3 import BitVecVal

    flat = BitVecVal(_LOG_GAS + n_topics * _LOG_TOPIC_GAS, 64)
    data_fee = size_64 * BitVecVal(_LOG_DATA_GAS, 64)
    state.evm_gas = state.evm_gas.consume_dynamic(flat + data_fee)
    return state


def charge_word_gas(state, word_len_64, word_gas_const):
    """额外扣减「按 word 计费」的动态 gas（SHA3 / COPY 系列）。

    镜像 Go memoryGasWithType 的 copy/word gas 段:
        words = toWordSize(word_len) = (word_len + 31) >> 5
        fee   = words * word_gas_const
    （在 memoryGasCost 之上叠加；SHA3 word_gas_const=6，COPY=3。）

    与 memoryGasCost 不同，word gas 基于「数据长度的 word 数」（SHA3 的 size /
    COPY 的 length），**不依赖也不更新 lastGasCost / memory size**——它是纯叠加。

    溢出健全性（**依赖调用顺序**）:本函数不单独加 scope assumption，因为所有
    调用点（_charge_memory_and_word_gas / _charge_mcopy_gas）都**先**调用
    charge_memory_expansion_gas，后者已加 `ULE(requested, 0x1FFFFFFFE0)`，而
    word_len ≤ requested（offset≥0）⟹ word_len ≤ 0x1FFFFFFFE0 ⟹ words=
    (word_len+31)>>5 ≤ 0xFFFFFFFF ⟹ words*word_gas_const（const≤6）< 2^64，
    不溢出，x86 makeSafeMul 的 overflow 分支恒假被剪。**若将来单独调用本函数，
    必须自行保证 word_len ≤ 0x1FFFFFFFE0。**

    Args:
        state: SMTState；就地扣减 evm_gas。
        word_len_64: 64-bit BitVec，按 word 计费的数据字节长度。
        word_gas_const: 每 word 的 gas（int）。
    """
    from z3 import BitVecVal, LShR

    words = LShR(word_len_64 + BitVecVal(31, 64), BitVecVal(5, 64))
    fee = words * BitVecVal(word_gas_const, 64)
    state.evm_gas = state.evm_gas.consume_dynamic(fee)
    return state
