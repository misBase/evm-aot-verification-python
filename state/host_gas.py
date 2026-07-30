"""B 类指令 host/builtin gas 的未解释函数（UF）建模。

go-hpc-evm 把一部分指令的 gas 计算完全放在 Go runtime 里，x86 机器码中没有任何
对应指令：

- host function: SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/EXTCODECOPY/
  SELFDESTRUCT/CALL/CALLCODE/DELEGATECALL/STATICCALL/CREATE/CREATE2
- builtin: EXP（gas 在 dealWithExp 内）

验证锚点是「EVM 语义 vs 编译器真实 x86 指令」，x86 里没有这段 gas 指令就没有对照
对象。做法是把 host gas 建成同名 UF ``host_gas_<opcode>(*stack_args)``，两侧在各自
的 host/builtin 调用点各扣同一个 UF：Z3 中同名同参求值到同一符号，故
``evm_gas == x86_gas`` 时这两项相消，留下两侧**可见**的 gas（内存扩展、returnGas
链）做真实比较。这与 common/uninterpreted.py 用同名 UF 消掉 CALL/BALANCE 结果值是
同一技术，只是这里消的是 gas 副作用。

强度边界：证的是「两侧扣了同一个 gas、传给 host 的栈参数一致」（能抓参数传错的
codegen bug），**不是** host gas 公式本身正确——后者是 assume，要真证明须为 Go
runtime 建 SMT 模型（未做）。

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
    """把栈参数统一成 256-bit，保证两侧 UF signature 一致。

    host gas 只依赖参数值、不依赖 BitVec 宽度，而两侧栈参都经 pop()/_pop_uint256
    得到完整 256-bit 值，故统一到 256 位即可相消。

    必须承载**完整** 256 位：截到低 64 位会让仅高 192 位不同的两个栈值产出恒等
    UF。对 EXP（aotGasExpEIP158 = 50*byteLen(exponent)，gas 真依赖完整 exponent）
    这类指令，高位传错的 codegen bug 会同时逃过 gas 检查（UF 假相消）与功能检查
    （结果被 POP 丢弃时不约束高位）。

    只接受 64/256 位。64 位是防御性分支（当前无调用方走到）；其它宽度无法保证与
    对侧对齐，fail-closed 抛错而非静默截断。
    """
    size = value.size()
    if size == 256:
        return value
    if size == 64:
        return ZeroExt(192, value)
    raise ValueError(
        f"host-gas UF stack arg must be 64 or 256 bits, got {size}; "
        "其它宽度无法保证与对侧 256 位 identity 对齐"
    )


def host_gas_uf(opcode: str, stack_args: Sequence[BitVecRef]) -> BitVecRef:
    """构造一次 host/builtin 调用的 gas 副作用 UF（64-bit gas cost）。

    opcode 编进函数名，故 SLOAD 与 SSTORE 是不同符号，不会被 Z3 当成同一函数而
    假相消。stack_args 的次序必须与 x86 侧完全一致：错位则 UF 不相消，检查会
    SAT/unknown 而不是假绿。

    Args:
        opcode: 指令名（大写，如 "SLOAD"）。
        stack_args: 该指令影响 gas 的栈输入（规范化前的原始 BitVec）。

    Returns:
        64-bit BitVec，表示这一次 host 调用扣减的 gas。
    """
    args = [_normalize_uf_arg(a) for a in stack_args]
    arg_sorts = [BitVecSort(256) for _ in args]
    f = Function(f"host_gas_{opcode.lower()}", *arg_sorts, BitVecSort(64))
    return f(*args)


def charge_host_gas_uf(state, opcode: str, stack_args: Sequence[BitVecRef]):
    """EVM 侧扣减一次 host/builtin 调用的 host-gas UF。

    仅 gas_modeling_enabled 时生效（与 charge_memory_expansion_gas 同一 gate）：
    功能等价验证下不引入 gas UF，避免污染既有 observable。

    Args:
        state: SMTState；就地扣减 evm_gas。
        opcode: 指令名（大写）。
        stack_args: 影响 gas 的栈输入，次序须与 x86 侧一致。

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
    """CALL/CREATE 系列：镜像 x86 dealWithAddGas → host UF → dealWithSubGas 链。

    x86 codegen 在 host 调用前后对 [R13+0x70] 做 plain ADD/SUB returnGas
    （returnGas = Blk.StaticGas - op.Immediate），host gas 扣减夹在中间。EVM 侧若
    只扣 UF，host 调用点两侧 gas 就差一个 returnGas，clamp 的实参不同 ⟹ UF 不
    相消 ⟹ returnGas≠0 时假 SAT（fail-closed 但漏报）。

    故这里三段严格对齐；return_gas==0 时退化为纯 charge_host_gas_uf。仅
    gas_modeling_enabled 生效。

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
    # dealWithAddGas：plain += returnGas（无钳零，镜像 x86 ADDQ）。
    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas + rg)
    # host UF：clamp 扣减（与 x86 makeUseGas 一致）。
    cost = host_gas_uf(opcode, stack_args)
    state.evm_gas = state.evm_gas.consume_dynamic(cost)
    # dealWithSubGas：plain -= returnGas（无钳零，镜像 x86 SUBQ）。
    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas - rg)
    return state


def _consume_clamp_64(gas64: BitVecRef, cost64: BitVecRef) -> BitVecRef:
    """out-of-gas 钳零的 64-bit 扣减：If(cost>gas, 0, gas-cost)。

    必须与 EVMGasState.consume_dynamic 逐字一致，否则 gas 恒足前提下两侧不会同时
    退化成 gas-cost、UF 不相消 → 假 SAT。
    """
    return If(UGT(cost64, gas64), BitVecVal(0, 64), gas64 - cost64)


def deduct_host_gas_uf_x86(mstate, opcode: str, stack_args: Sequence[BitVecRef],
                           offsets, store_64bit, callengine_domain) -> None:
    """x86 侧扣减 host-gas UF（与 EVM 侧 charge_host_gas_uf 同名相消）。

    host gas 在 Go runtime 内、机器码不可见，故手动从 callengine_gas_remaining
    扣同一个 UF。stack_args 必须与 EVM 侧是同一组栈值、同次序（该调用点两侧栈已
    由功能等价证明相等）。仅 gas_modeling_enabled 生效。

    Args:
        mstate: x86 SMTState；就地更新 callengine_gas_remaining 与 [R13+0x70]。
        opcode: 指令名（大写），须与 EVM 侧一致。
        stack_args: 影响 gas 的栈输入（与 EVM 侧同序）。
        offsets: aot_profile.offsets（取 "gas_remaining" 偏移）。
        store_64bit: 写 [R13+off] 的回调，保持 side-channel 与 x86_memory 一致。
        callengine_domain: CALLENGINE 内存域（由 caller 传入，避免依赖 x86 模块）。
    """
    if not getattr(mstate, "gas_modeling_enabled", False):
        return
    from x86_64.models import Register

    cost = host_gas_uf(opcode, stack_args)
    gas_before = mstate.callengine_gas_remaining
    gas_after = _consume_clamp_64(gas_before, cost)

    mstate.callengine_gas_remaining = gas_after
    # 同步 [R13+gas_remaining]（与既有 _sync_callengine_u64_field 同范式）。
    r13 = mstate.x86_registers.get_register(Register.R13)
    gas_off = BitVecVal(offsets["gas_remaining"], 64)
    mstate.x86_memory = store_64bit(r13 + gas_off, gas_after, callengine_domain)
