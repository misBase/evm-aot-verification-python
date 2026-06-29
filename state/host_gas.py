"""B 类指令 host/builtin gas 的未解释函数（UF）建模 —— 全覆盖 gas 一致性的兜底层。

## 为什么需要它

go-hpc-evm 的 x86 codegen 把一部分指令的 gas 计算完全放在 Go runtime（host
function / builtin）里，x86 机器码里**一行 gas 计算指令都没有**：

- host function（compileGoDefinedHostFunction → ret bridge）:
  SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/EXTCODECOPY/SELFDESTRUCT/
  CALL/CALLCODE/DELEGATECALL/STATICCALL/CREATE/CREATE2
- builtin（compileCallBuiltinFunction → _handle_builtin_*）:
  EXP（gas 在 dealWithExp 内，x86 checkMemoryAndCalcDynamicGasEXPEip158 仅 TODO）

这些指令的 gas 公式（冷热账户、SSTORE 退款、EIP-150 63/64 转发、value stipend、
EXP 指数字节）对验证器是**不可见的黑盒**。验证锚点是「EVM 语义 vs 编译器真实
x86 指令」；x86 里没有这段 gas 指令，就没有对照对象。

## UF 兜底原理（soundness）

把 host gas 建成一个**同名未解释函数** `host_gas_uf(opcode, *stack_args)`，
EVM 侧和 x86 侧在各自的 host/builtin 调用点**各扣同一个 UF**。Z3 中相同名字
+ 相同参数的 UF 求值到同一符号，故 `evm_gas == x86_gas` 时这两个 UF 项相消，
留下两侧**可见**的 gas 部分（如 CREATE 的 dealWithAddGas/SubGas returnGas 链、
内存扩展）去做真实比较。

这与 common/uninterpreted.py 里 CALL/BALANCE **结果值**用同名 UF 相消是同一
技术，只是这里建模的是 gas **副作用**而非结果。

**强度边界（务必清楚）**:UF 兜底证明的是「**两侧扣了同一个 gas**」（结构、
参数一致），**不是**「host gas 公式本身正确」——后者是 assume 不是 prove。要
真证明 host gas 公式须深入 Go runtime 建 SMT 模型（未做）。UF 按 opcode + 栈
参数绑定，故顺带验证「两侧传给 host 的栈参数一致」（抓参数传错的 codegen bug）。

参见 memory: gas_full_coverage_codegen_layers。
"""

from typing import Sequence

from z3 import BitVecRef, BitVecSort, BitVecVal, Function, If, UGT, ZeroExt


# B 类 host function 指令（gas 在 Go host runtime，x86 不可见）。
HOST_GAS_HOST_KINDS = frozenset({
    "SLOAD",
    "SSTORE",
    "BALANCE",
    "EXTCODESIZE",
    "EXTCODEHASH",
    "EXTCODECOPY",
    "SELFDESTRUCT",
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "STATICCALL",
    "CREATE",
    "CREATE2",
})

# B 类 builtin 指令（gas 在 builtin runtime，x86 不可见）。
HOST_GAS_BUILTIN_KINDS = frozenset({
    "EXP",
})

# 所有需要 host-gas UF 兜底的指令。
HOST_GAS_UF_KINDS = HOST_GAS_HOST_KINDS | HOST_GAS_BUILTIN_KINDS


def _normalize_uf_arg(value: BitVecRef) -> BitVecRef:
    """把栈参数规范化成 256-bit（UF 参数统一宽度，保证两侧 UF signature 一致）。

    host gas 公式只依赖参数**值**，不依赖其 BitVec 宽度。统一到 256-bit 让两侧
    （EVM 侧 256-bit 栈值；x86 侧 _pop_uint256 也读完整 256-bit 栈值）产出同一
    UF signature。

    **identity 关键 + 完整性（Fix #1）**:两侧必须对同一栈值用**完整 256 位**作
    identity 才能让 UF 相消，且不丢信息。旧实现取 `Extract(63,0)` 截到低 64 位，
    会让两个仅高 192 位不同的栈值产出**恒等** UF —— 对 EXP 这类 gas 真依赖完整
    256 位 exponent（aotGasExpEIP158 = 50*byteLen(exponent)）的指令，高位传错的
    codegen bug 会同时逃过 gas 检查（UF 假相消）与功能检查（结果被 POP 丢弃时
    不约束高位）→ 假绿。改为承载完整 256 位即可区分。

    本验证模型里两侧栈参都经 _pop_uint256/pop() 得到完整 256-bit 值（x86 侧并未
    建模成读 64-bit 寄存器，而是 load_256bit），故统一到 256 位两侧仍同 signature
    相消。只接受 64 / 256 两种宽度（256 直通；64 ZeroExt 到 256，防御性 —— 当前
    无调用方传 64 位）。其它宽度是上游错误，fail-closed 抛错而非静默截断。
    """
    size = value.size()
    if size == 256:
        return value
    if size == 64:
        # 防御性:无损 ZeroExt 到 256 位（保持两侧 signature 一致）。
        return ZeroExt(192, value)
    raise ValueError(
        f"host-gas UF stack arg must be 64 or 256 bits, got {size}; "
        "其它宽度无法保证与对侧 256 位 identity 对齐"
    )


def host_gas_uf(opcode: str, stack_args: Sequence[BitVecRef]) -> BitVecRef:
    """构造某次 host/builtin 调用的 gas 副作用 UF（64-bit gas cost）。

    Args:
        opcode: 指令名（大写，如 "SLOAD"）。决定 UF 名字 → 不同指令不混用同一 UF。
        stack_args: 该指令影响 gas 的栈输入（已规范化前的原始 BitVec）。
            次序必须与 x86 侧**完全一致**，否则 UF 不相消（fail-closed:检查会
            SAT/unknown，不会假绿）。

    Returns:
        64-bit BitVec，表示这一次调用 host 扣减的 gas。

    Note（soundness）:
        - 同名 + 同参 ⟹ 两侧相消。参数次序/数量错位 ⟹ 不相消 ⟹ 检查失败（安全）。
        - opcode 编进函数名，故 SLOAD 的 UF 与 SSTORE 的 UF 是不同符号，不会
          因都叫 host_gas 而被 Z3 误当同一函数（那会假相消 → 假绿）。
        - **参数承载完整 256 位（Fix #1）**:_normalize_uf_arg 用完整 256 位作
          identity（不再截低 64 位）。两侧对同一栈值都取完整 256 位 → identity
          一致、能相消；且 EXP 这类 gas 依赖完整 exponent 的指令，高位不同的栈值
          会产出不同 UF（不会假相消）。代价仅是 UF arity 用 256-bit sort，无害。
    """
    args = [_normalize_uf_arg(a) for a in stack_args]
    arg_sorts = [BitVecSort(256) for _ in args]
    f = Function(f"host_gas_{opcode.lower()}", *arg_sorts, BitVecSort(64))
    return f(*args)


def charge_host_gas_uf(state, opcode: str, stack_args: Sequence[BitVecRef]):
    """在 EVM 侧对一次 host/builtin 调用扣减 host-gas UF（与 x86 侧同名相消）。

    仅 gas_modeling_enabled 时生效——功能等价验证下不引入 gas UF，避免污染既有
    observable（与 charge_memory_expansion_gas 等的 gate 一致）。

    Args:
        state: SMTState；就地扣减 evm_gas。
        opcode: 指令名（大写）。
        stack_args: 影响 gas 的栈输入（次序须与 x86 侧一致）。

    Returns:
        更新后的 state（与入参同一对象）。
    """
    if not getattr(state, "gas_modeling_enabled", False):
        return state
    cost = host_gas_uf(opcode, stack_args)
    state.evm_gas = state.evm_gas.consume_dynamic(cost)
    return state


def charge_host_gas_uf_with_return_gas(state, opcode: str,
                                       stack_args: Sequence[BitVecRef],
                                       return_gas: int):
    """CALL/CREATE 系列:镜像 x86 dealWithAddGas → host UF → dealWithSubGas 链。

    x86 codegen 在 host 调用**前后**对 [R13+0x70] 做 `+= returnGas` / `-= returnGas`
    （plain ADD/SUB，无 OOG 钳零），returnGas = Blk.StaticGas - op.Immediate（CALL
    之后块内剩余静态 gas）。host UF 扣减夹在中间。EVM 侧若只扣 UF（不模拟 add/sub），
    则在 host 调用点 gas_evm = G 而 gas_x86 = G + returnGas，两侧 clamp 的 gas 实参
    不同 ⟹ UF 不相消 ⟹ returnGas≠0 时假 SAT（虽 fail-closed 但漏报）。

    故这里同样 `+= returnGas`（plain）→ consume_dynamic(UF)（clamp，与 x86 一致）→
    `-= returnGas`（plain），让两侧 clamp 实参一致、UF 相消。returnGas==0 时退化为
    纯 charge_host_gas_uf。仅 gas_modeling_enabled 生效。

    Args:
        state: SMTState；就地扣减 evm_gas。
        opcode: 指令名（大写）。
        stack_args: 影响 gas 的栈输入（与 x86 侧同序）。
        return_gas: Blk.StaticGas - op.Immediate（int，≥0）。
    """
    if not getattr(state, "gas_modeling_enabled", False):
        return state
    from state.evm_gas_state import EVMGasState
    rg = BitVecVal(int(return_gas), 64)
    # dealWithAddGas:plain += returnGas（无钳零，镜像 x86 ADDQ）。
    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas + rg)
    # host UF:clamp 扣减（与 x86 makeUseGas/手动钳零一致）。
    cost = host_gas_uf(opcode, stack_args)
    state.evm_gas = state.evm_gas.consume_dynamic(cost)
    # dealWithSubGas:plain -= returnGas（无钳零，镜像 x86 SUBQ）。
    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas - rg)
    return state


def _consume_clamp_64(gas64: BitVecRef, cost64: BitVecRef) -> BitVecRef:
    """out-of-gas 钳零的 64-bit 扣减:If(cost>gas, 0, gas-cost)。

    **必须**与 EVMGasState.consume_dynamic 逐字一致（见 state/evm_gas_state.py），
    否则 gas 恒足前提下两侧不会同时退化成 gas-cost、UF 不相消 → 假 SAT。
    """
    return If(UGT(cost64, gas64), BitVecVal(0, 64), gas64 - cost64)


def deduct_host_gas_uf_x86(mstate, opcode: str, stack_args: Sequence[BitVecRef],
                           offsets, store_64bit, callengine_domain) -> None:
    """在 x86 侧对一次 host/builtin 调用扣减 host-gas UF（与 EVM 侧同名相消）。

    x86 host gas 在 Go runtime 内、机器码不可见，故这里**手动**从
    callengine_gas_remaining（= [R13+gas_remaining]）扣减同一个 host_gas_uf，
    让两侧 UF 在 evm_gas == x86_gas 时相消。

    **identity 关键**:stack_args 必须是与 EVM 侧**同一组栈值、同次序**（两侧栈
    在该 host 调用点已被功能等价证明相等），且都经 host_gas_uf 内的 _normalize_uf_arg
    规范成完整 256 位。扣减用 _consume_clamp_64（与 EVMGasState.consume_dynamic 一致）。

    仅 gas_modeling_enabled 时生效。

    Args:
        mstate: x86 SMTState；就地更新 callengine_gas_remaining 与 [R13+0x70]。
        opcode: 指令名（大写），须与 EVM 侧 charge_host_gas_uf 用的一致。
        stack_args: 影响 gas 的栈输入（与 EVM 侧同序）。
        offsets: aot_profile.offsets（取 "gas_remaining" 偏移）。
        store_64bit: 回调 store_64bit(addr, value, domain) 写 [R13+off]（保持内存一致）。
        callengine_domain: CALLENGINE 内存域（由 caller 传入，避免本模块依赖 x86 模块）。

    Returns:
        None（就地更新 mstate）。
    """
    if not getattr(mstate, "gas_modeling_enabled", False):
        return
    from x86_64.models import Register

    cost = host_gas_uf(opcode, stack_args)
    gas_before = mstate.callengine_gas_remaining
    gas_after = _consume_clamp_64(gas_before, cost)

    mstate.callengine_gas_remaining = gas_after
    # 同步 [R13+gas_remaining]，保持 side-channel 与 x86_memory 一致（与既有
    # _sync_callengine_u64_field 同范式；用 caller 传入的 store 回调避免循环依赖）。
    r13 = mstate.x86_registers.get_register(Register.R13)
    gas_off = BitVecVal(offsets["gas_remaining"], 64)
    mstate.x86_memory = store_64bit(r13 + gas_off, gas_after, callengine_domain)
