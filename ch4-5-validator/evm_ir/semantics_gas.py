"""EVM IR 侧的动态 gas 建模。

从 `evm_ir.semantics` 拆出：内存扩展 fee、按 word/byte 计费的叠加段、以及 gas 相关的
错误分支（E2/E3/E4）与快照时刻。参照侧是 go-ethereum 解释器 + AOT 编译器 的 x86 codegen，
函数 docstring 里逐条记着两边的源码行号对照，改动前请先读。

host 侧不可见的 gas（EXP/SLOAD/SSTORE/CALL 系）走 `state.host_gas` 的 UF，不在本模块。
"""

import logging

from z3 import And, BitVecVal, If, Not, UGT, ULT, is_false, simplify

import state.evm_gas_state as gas_state
from evm_ir.status_code import EvmStatusCode
from state.evm_memory_state import EVMMemoryState
from common.u64 import split_u64
from state.smt_state import PendingErrorBranch


# gas 错误分支的快照类：错误瞬间哪些 side-channel 已写入，必须与 x86 的 exit 时刻一致。
#   PRE_FEE  三项都未写。E2/E3 在 dynamicGas **之前**返回（interpreter.go:190/195）；
#            cap 支的 jmpIfB(gas_dynamic:517) 跳到 :582，**跳过** :578 的 lastGasCost 写入。
#   POST_FEE 只有 lastGasCost 已写。makeUseGas 在 memoryGasCost 之后才跑，其 SUBQ 在 JCS
#            之后（gas_dynamic:402-408）故 gas 不扣；memoryGrow 更在 UseGas 之后，
#            故 mem_size 不变（interpreter.go:204-208）。
SNAPSHOT_PRE_FEE = "pre_fee"
SNAPSHOT_POST_FEE = "post_fee"

# toWordSize 的饱和边界（common.go:70）与 memoryGasCost 的 cap（gas_table.go:38，= 32×0xFFFFFFFF）。
_MAX_UINT64_MINUS_31 = (1 << 64) - 32
_MEM_SIZE_CAP = 0x1FFFFFFFE0


def _mem_size_tail_branches(requested_64):
    """requested 之后的两个共用错误分支。

        interpreter.go:194  if memorySize, ovf = SafeMul(toWordSize(memSize), 32); ovf {
                                return nil, ErrGasUintOverflow                    // → 13
                            }
        gas_table.go:38     if newMemSize > 0x1FFFFFFFE0 {
                                return 0, ErrGasUintOverflow   // 经 :205 塌缩 → **12**
                            }

    两个条件都不是照抄字面，推导写在这里免得被"简化"掉：

    - SafeMul 溢出 ⟺ `requested > MaxUint64-31`：边界内 toWordSize 是
      `(size+31)/32 ≤ MaxUint64/32`、乘 32 不溢出；越界则饱和成 `MaxUint64/32+1`、
      乘 32 必溢出。x86 makeSafeMulWithOverFlow(gas_dynamic:298-323) 是"先饱和再靠
      MULQ 的 CF 检测"，等价。
    - Go 的 cap 比的是**已舍入**的 memorySize，这里比未舍入的 requested：
      `cap = 32×0xFFFFFFFF` ⟹ `ceil(requested/32)*32 ≤ cap ⟺ requested ≤ cap`，双向成立
      （舍入本身溢出的情形已被前一条排除）。

    Returns:
        [(cond, status_code, snapshot_kind), ...]，按解释器顺序。
    """
    return [
        (UGT(requested_64, BitVecVal(_MAX_UINT64_MINUS_31, 64)),
         EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
        (UGT(requested_64, BitVecVal(_MEM_SIZE_CAP, 64)),
         EvmStatusCode.OUT_OF_GAS, SNAPSHOT_PRE_FEE),
    ]


def calc_mem_size_64(offset_bv, length_bv):
    """镜像 Go calcMemSize64（common.go:30）：返回 (requested_64, 有序错误分支)。

    短路顺序一条都不能挪；x86 makeCalcMemSize64(gas_dynamic:325-343) 逐条同构
    （compileLocIsUint64(l) → TESTQ l1/JEQ → compileLocIsUint64(o) → ADDQ/CMPQ/JCS）：

        if !l.IsUint64() { return 0, true }              // ① length 非 uint64 → 13
        if length64 == 0 { return 0, false }             // ② 短路，**不检查 offset**
        offset64, ovf := off.Uint64WithOverflow()
        if ovf           { return 0, true }              // ③ offset 非 uint64 → 13
        val := offset64 + length64
        return val, val < offset64                       // ④ 进位            → 13

    ② 是语义要点：`RETURN(offset=2^200, length=0)` 在解释器和 AOT 里都是正常路径、
    fee=0。旧实现无条件 assume offset 高 192 位为 0，把这条合法路径排除在验证域外。

    返回的分支按 append 顺序即检查顺序；互斥化由
    cfg_executor._execute_op_with_outcome 负责，这里**不要**自己串否定链。
    """
    length_hi_nonzero, length_64 = split_u64(length_bv)
    offset_hi_nonzero, offset_64 = split_u64(offset_bv)

    length_is_zero = length_64 == BitVecVal(0, 64)
    end = offset_64 + length_64

    branches = [
        (length_hi_nonzero, EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
        # ③④ 都带上 ¬② —— length==0 时 Go 已经 return，不看 offset。
        (And(Not(length_is_zero), offset_hi_nonzero),
         EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
        (And(Not(length_is_zero), ULT(end, offset_64)),
         EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
    ]
    requested_64 = If(length_is_zero, BitVecVal(0, 64), end)
    return requested_64, branches + _mem_size_tail_branches(requested_64)


def calc_mem_size_64_with_uint(offset_bv, const_size):
    """镜像 Go calcMemSize64WithUint（common.go:40），length 为非零常量。

    MLOAD/MSTORE 是 32、MSTORE8 是 1，都 ≠ 0 ⟹ `length64 == 0` 短路不可达，
    offset 检查恒执行——即没有 ①②，只剩 ③④ 与共用尾部。
    x86 对应 makeCalcMemSize64WithUintN(gas_dynamic:389-400)。
    """
    if const_size == 0:
        raise ValueError("const_size 必须非零：为零时 Go 走 length==0 短路，应改用 calc_mem_size_64")
    offset_hi_nonzero, offset_64 = split_u64(offset_bv)
    end = offset_64 + BitVecVal(const_size, 64)

    branches = [
        (offset_hi_nonzero, EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
        (ULT(end, offset_64), EvmStatusCode.GAS_UINT_OVERFLOW, SNAPSHOT_PRE_FEE),
    ]
    return end, branches + _mem_size_tail_branches(end)


def charge_dynamic_gas(state, requested_64, mem_size_branches, extra_fees=()):
    """挂 gas 错误分支并在正常路径上演化 gas/bookkeeping。

    对齐 interpreter.go:187-209 的整段流程：

        memSize, ovf := operation.memorySize(stack)   // 溢出 → mem_size_branches
        memorySize, ovf = SafeMul(toWordSize(memSize), 32)
        dynamicCost, err = operation.dynamicGas(...)  // memFee + extra，**累加成总额**
        if err != nil || !contract.UseGas(dynamicCost) {
            return nil, ErrOutOfGas                   // → E4 分支，gas 不扣
        }
        if memorySize > 0 { mem.Resize(memorySize) }  // 正常路径才扩容

    三个要点：

    1. **总额一次判断**。解释器 `UseGas(dynamicCost)` 与 x86 的单个 makeUseGas
       （gas_dynamic:402-408）都只判一次；分成 memFee/wordFee 各判一次在 gas 不足时
       结论不同。
    2. **gas 状态无条件演化**。gas 是决定控制流的内部状态，不是只在比较时才要的
       observable：连续两条动态 gas 指令、`G-f1 < f2 ≤ G` 时不扣 f1 就漏掉 AOT 在第二条
       处的 OOG；lastGasCost 不更新则第二次扩展按 `newTotal-0` 计费，阈值本身就错。
    3. **正常路径是纯减法**。E4 已把不足分叉出去，此路径上钳零分支恒假；纯减法既忠于
       `contract.Gas -= cost`，又避免 gas 退化成深 If-chain。

    E4 用 `UGT(total, gas)`（`total == gas` **不**触发）：解释器 `UseGas` 是
    `if gas < cost`；x86 makeUseGas 同义——assembler 的
    `CompileRegisterToRegister(CMPQ, from, to)` 语义是 `from - to`，由
    makeSafeMulWithOverFlow:304、memoryGasCost:516、:548 三处注释交叉印证。

    opcode 正常执行路径上的内存扩展在这里统一更新 MSize；原始内存读写只修改 Memory。

    Args:
        state: SMTState；就地追加 pending_errors 并演化 gas / MSize / lastGasCost。
        requested_64: 本次访问的 requested memory size（64-bit）。
        mem_size_branches: `calc_mem_size_64*` 返回的有序分支列表。
        extra_fees: 叠加在内存扩展之上的 word/log fee（64-bit BitVec 序列）。
    """
    # mem.Len() 属于 EVM 可见内存状态；lastGasCost 是内存扩展的内部记账，
    # 后续扩展会读取它以计算增量费用。
    fee, new_mem_size, new_last_gas = gas_state.memory_expansion_fee(
        state.evm_memory.MSize,
        state.callengine_memory_gas_used,
        requested_64,
    )
    total_fee = fee
    for part in extra_fees:
        total_fee = total_fee + part

    # blast_select_store 折叠栈上的 Store/Select 链——内存 offset 常来自
    # MLOAD(0x40) 的 free-memory-pointer，不折叠的话具体值识别不出来，会白留一堆
    # 不可满足的错误路径（同 RETURNDATACOPY 的既有先例）。
    live = [(simplify(cond, blast_select_store=True), status, kind)
            for cond, status, kind in mem_size_branches]
    live = [item for item in live if not is_false(item[0])]
    if any(kind != SNAPSHOT_PRE_FEE for _, _, kind in live):
        raise ValueError(
            "mem_size_branches 只能是 PRE_FEE：它们在 dynamicGas 之前就返回，"
            "gas/lastGasCost/mem_size 一项都没写。若要加 POST_FEE 分支，"
            "必须像 E4 那样单独构造快照，不能混进这个列表"
        )

    # E4 无条件建模：makeUseGas 的 CMPQ/JCS 是可见机器码，不能有开关。要让它不产生
    # 路径，靠足够大的具体 gas 预算把条件 simplify 成 False，而不是跳过建模。
    e4_cond = simplify(UGT(total_fee, state.evm_gas.Gas), blast_select_store=True)
    if is_false(e4_cond):
        e4_cond = None

    # 每条分支独占快照对象：共用会被 executor 的 shared_error_snapshot 检查拦下
    # （前一条已进 final_states，改的是同一个引用）。
    snapshots = [state.snapshot_for_error_branch() for _ in live]
    e4_snapshot = state.snapshot_for_error_branch() if e4_cond is not None else None
    if e4_snapshot is not None:
        # POST_FEE：memoryGasCost 已写完 lastGasCost 才轮到 makeUseGas。
        e4_snapshot.callengine_memory_gas_used = new_last_gas

    for (cond, status, _kind), snapshot in zip(live, snapshots):
        state.pending_errors.append(
            PendingErrorBranch(condition=cond, status_code=status,
                               terminal_state=snapshot)
        )
    if e4_cond is not None:
        state.pending_errors.append(
            PendingErrorBranch(condition=e4_cond,
                               status_code=EvmStatusCode.OUT_OF_GAS,
                               terminal_state=e4_snapshot)
        )

    # new_mem_size 已按字取整。必须在错误分支快照之后更新，
    # 使错误终态保留扩展前的 mem.Len()。
    state.evm_memory = EVMMemoryState(
        memory_array=state.evm_memory.Memory,
        msize=new_mem_size,
    )
    state.callengine_memory_gas_used = new_last_gas
    state.evm_gas = gas_state.EVMGasState(initial_gas=state.evm_gas.Gas - total_fee)
    return state


def charge_memory_gas_for_access(state, offset_bv, access_size):
    """MLOAD / MSTORE / MSTORE8 的内存扩展 gas。

    Go: memorySize=calcMemSize64WithUint(Back(0), 32|1) + dynamicGas=pureMemoryGascost
    （jump_table.go:594-614、gas_table.go:265）；x86: makeStoreCheck(storeSize)。
    access_size 是 int 常量（32 或 1）。
    """
    requested, branches = calc_mem_size_64_with_uint(offset_bv, access_size)
    return charge_dynamic_gas(state, requested, branches)


def charge_memory_gas_for_return(state, offset_bv, length_bv):
    """RETURN / REVERT 的内存扩展 gas。

    Go: memoryReturn/memoryRevert=calcMemSize64(Back(0), Back(1)) + pureMemoryGascost；
    x86: makeCalcReturnIns(0, 1)。
    """
    requested, branches = calc_mem_size_64(offset_bv, length_bv)
    return charge_dynamic_gas(state, requested, branches)


def charge_memory_and_word_gas(state, offset_bv, length_bv, word_gas_const):
    """SHA3 / COPY 系列：内存扩展 gas + 按 word 计费的叠加段。

    Go: calcMemSize64(offset, length) + gasSha3 / memoryCopierGas(pos)，都是
    `memoryGasCost(memSize) + toWordSize(length)*const`（gas_table.go:66-87、244-260），
    SHA3=Sha3WordGas 6、COPY 系=CopyGas 3；x86: memoryGasWithType(gas_dynamic:463)。
    两段 fee 交给 charge_dynamic_gas 累加成总额后判一次。
    """
    requested, branches = calc_mem_size_64(offset_bv, length_bv)
    _, length_64 = split_u64(length_bv)
    return charge_dynamic_gas(
        state, requested, branches, [gas_state.word_fee(length_64, word_gas_const)],
    )


def charge_mcopy_gas(state, dst_offset_bv, src_offset_bv, length_bv):
    """MCOPY 动态 gas：内存扩展用 max(dst,src)+length，copy word gas 用 length。

    Go memoryMcopy（memory_table.go）:

        mStart := stack.Back(0)                     // dest
        if stack.Back(1).Gt(mStart) {               // **256-bit** Gt
            mStart = stack.Back(1)                  // source
        }
        return calcMemSize64(mStart, stack.Back(2))

    **max 必须在 256 位上比**：x86 compileSubValuesForCompare(impl_amd64.go:848-866)
    是 SUBQ+SBBQ×3 的全 256 位借位链。先截 64 位只在"高位为零"的 assumption 下等价，
    撤掉后 dst=2^200/src=0 会截成 0 而误选 src。
    """
    mstart_bv = max_uint256(dst_offset_bv, src_offset_bv)
    requested, branches = calc_mem_size_64(mstart_bv, length_bv)
    _, length_64 = split_u64(length_bv)
    return charge_dynamic_gas(
        state, requested, branches, [gas_state.word_fee(length_64, 3)],
    )


def max_uint256(left_bv, right_bv):
    """全宽无符号 max（MCOPY 的 `mStart = max(dest, source)`）。

    宽度不一致时 fail-closed：静默 ZeroExt 会掩盖调用方传错操作数。
    """
    if left_bv.size() != right_bv.size():
        raise ValueError(
            f"max operands must be same width, got {left_bv.size()} vs {right_bv.size()}"
        )
    return If(UGT(left_bv, right_bv), left_bv, right_bv)


def return_gas_for(op) -> int:
    """CALL/CREATE 系列的 returnGas = Blk.StaticGas - op.Immediate。

    与 AOT 编译器 dealWithAddGas/SubGas 同式（impl_amd64.go）。immediate 是块内 CALL
    之前的累计静态 gas（前缀和），故 rg ≥ 0 自然成立。

    缺字段（测试 stub）或 rg<0（IR 异常）时返回 0。这不是无害降级：真实 returnGas≠0
    时返回 0 会让 host 调用点两侧 gas 实参不同、UF 不相消，该 CALL 变成 SAT——保守值
    只会让验证更严（漏报），不会放松。
    """
    block = getattr(op, "block", None)
    static_gas = getattr(block, "static_gas", None) if block is not None else None
    immediate = getattr(op, "immediate", None)
    if not isinstance(static_gas, int) or not isinstance(immediate, int):
        return 0
    rg = static_gas - immediate
    if rg < 0:
        # immediate 正常 ≤ static_gas，rg<0 说明 IR 损坏。返回 0 是 fail-closed
        # （与 x86 加减不对齐 → SAT 而非假绿），warning 用于定位。
        logging.getLogger(__name__).warning(
            "CALL/CREATE returnGas < 0 (static_gas=%d, immediate=%d) at pc=%s; "
            "treating as 0 (fail-closed)",
            static_gas, immediate, getattr(op, "pc", None),
        )
        return 0
    return rg


def charge_log_gas(state, offset_bv, size_bv, n_topics):
    """LOG 动态 gas（x86 memoryLogGas codegen 全程可见，故建真实公式而非 UF）。

    Go: memorySize=memoryLog=calcMemSize64(Back(0), Back(1))，dynamicGas=makeGasLog(n)
    （gas_table.go:214-242）:

        gas  = memoryGasCost(memSize)
        gas += LogGas                          // 375
        gas += n * LogTopicGas                 // n*375
        gas += requestedSize * LogDataGas      // **每字节** 8，不是每 word

    x86 memoryLogGas(gas_dynamic:590) 的 data 段用
    makeSafeMulWithOverFlowWithNoToWordSize——刻意不做 toWordSize。
    """
    requested, branches = calc_mem_size_64(offset_bv, size_bv)
    _, size_64 = split_u64(size_bv)
    return charge_dynamic_gas(
        state, requested, branches, [gas_state.log_fee(n_topics, size_64)],
    )
