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

--- 「host gas 耗尽」为什么不建 OOG 分叉：那一处没有代码可验 ---

两侧都用 _consume_clamp_64 钳零续跑、都不分叉，而 host_gas_uf 是无约束自由函数
（`cost > gas` 永远可满足），于是模型里有一批真实执行不存在的「扣爆后带 gas=0 继续跑」
路径。这不是缺口：

- compileCallGoFunction(impl_amd64.go:323-338) 只发射 spill / 写 returnAddress /
  写 status / 写 SP / RET，**返回地址处不检查 host 结果**；要不要重入由 Go 循环决定
  （engine_evm.go:657 `if err != nil { return nil, err }`）。没有 x86 行为可以不一致。
- 那些续跑状态是机器码的**不可达**状态。我们在其上也做了比较 —— 多验不是少验，
  只可能误报，不可能假绿；且两侧带同一钳零值继续走，下游可见 gas 检查照常逐路径比较。
- 该调用点仅有的 codegen（上面 5 条）已在存在的那条路径上验过：UF 只有两侧栈参数一致
  才相消。codegen 不分叉，验一条路径即验完。

与 evm_ir/semantics.py 对**写保护**的既有判断同源（同样是 Go error 终止、不回写 native
status）。范围声明见 ProgramEquivalenceChecker.__init__。

参见 memory: gas_full_coverage_codegen_layers、docs/关键问题记录.md #19。
"""

from typing import Sequence

from z3 import BitVecRef, BitVecSort, BitVecVal, Function, If, UGT, ULE, ZeroExt, simplify


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

# cost 依赖 UF 实参之外状态的指令额外传入调用序号，避免同参调用被强制等价。
# 当前隐藏依赖包括 access-list 状态和 gas ledger。seq 只区分调用事件，
# 不建模隐藏状态及其与 cost 的函数关系；详见设计文档 §7.1。
HOST_GAS_SEQ_KINDS = frozenset({
    "SLOAD",            # host.go:71   SlotInAccessList / AddSlotToAccessList
    "BALANCE",          # host.go:312 → gasCostWithEip2929AccountCheck host.go:880
    "EXTCODESIZE",      # host.go:182
    "EXTCODEHASH",      # host.go:126
    "EXTCODECOPY",      # host.go:216
    # SSTORE 除序号外还吃 slot 的写入前值：host.go:255 的档位取决于 current 值。
    "SSTORE",
    # host.go:809 读写 AddressInAccessList。另有一个 seq 管不了的隐藏依赖：host.go:741
    # 起的 gasCostWithHostCall 把 63/64 转发额度算进 cost，取决于 gas 的具体数值，要靠
    # gas_before 进签名，不在本次范围。
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "STATICCALL",
    # cost 依赖未包含在显式实参中的剩余 gas。
    "CREATE",
    "CREATE2",
})

# host-gas UF 的协议上界（64-bit gas）。值是 **host 动态部分**的最大可能值，不含已由
# static gas 或可见 fee 覆盖的份额。
#
# ⚠️ 上界是 **assume**，且是**手工同步项：上游 gas 实现一改，这里必须跟着手改。**
# 写小了会静默缩域——两侧仍共享同一个 UF、仍相消、仍 UNSAT，Python 侧没有任何测试看得见。
# 没有可执行的 oracle，**也没有任何自动提醒**：代之以逐条记依据（取哪个函数的哪条分支、
# 常量在 params/protocol_params.go 哪一行），照行号读源码复核。换编译器版本时必须主动走
# docs/关键问题记录.md #20 的同步流程；上次复核参照的版本记在 tests/data/README.md。
#
# ⚠️ **依据只能取 AOT 实际执行的 evm/host.go 与 evm/aot/*。** evm/gas_table.go 是**解释器**
# 的 gas 表，AOT 从不调用；两边数值目前一致是巧合，照它复核会验错对象（初版就引错了）。
#
# 分层判据来自 fixture 的 `static_gas`（AOT 实际发射的静态份额）实测：
#   SLOAD/SSTORE/EXP/SELFDESTRUCT 静态 0 ⟹ 全额在 dynamic；其余静态 100（= warm）。
HOST_GAS_UPPER_BOUNDS: dict[str, int] = {
    # host.go:328 Suicide 整个函数体只有一句 return nil, nil，注释原话
    # "Suicide has no gas need cost and it will be return in asm" ⟹ 上界取 0
    # （无符号下 ULE(c, 0) 就等于 c == 0，不必特判成等式）。
    "SELFDESTRUCT": 0,
    # host.go:71 SLoad：dynamicGas 从 0 起，二选一
    # += ColdSloadCostEIP2929(2100, protocol_params.go:101) 或
    # += WarmStorageReadCostEIP2929(100, :102)，之后直接 UseGas。取 cold。
    "SLOAD": 2100,
    # host.go:255 SStore：dynamicGas = cold 时 ColdSloadCostEIP2929(2100)、warm 时 0，
    # 随后 += 四选一，最大是 SstoreSetGasEIP2200(20000, protocol_params.go:96)。
    # host.go:262 的 sentry（剩余 gas <= SstoreSentryGasEIP2200 直接返 error）不产生
    # cost，属已声明的 host-exhaustion out-of-scope。
    "SSTORE": 22100,
    # 账户访问三件套各有自己的 host 函数，都只 += ColdAccountAccessCostEIP2929
    # (2600, protocol_params.go:100) − WarmStorageReadCostEIP2929(100, :102)，warm 时不加
    # （源码原话 "We charge (cold-warm), since 'warm' is already charged as constantGas"）：
    #   Balance host.go:312 → gasCostWithEip2929AccountCheck host.go:880
    #   ExtCodeSize host.go:182 / ExtCodeHash host.go:126
    "BALANCE": 2500,
    "EXTCODESIZE": 2500,
    "EXTCODEHASH": 2500,
    # host.go:216 ExtCodeCopy 只 += 那 2500；内存扩展与 copy word gas 不在 host 里——首行
    # 注释原话 "calculate dynamic gas and grow mem size are doing in asm"，对应
    # impl_amd64.go:3105 的可见 fee。
    "EXTCODECOPY": 2500,
    # aotGasExpEIP158（engine_evm.go:785，AOT 实际调用的那份；注意它是 gas_table.go:347
    # gasExpEIP158 的复制粘贴克隆，改动时两份都要看）：
    # ExpGas(10, protocol_params.go:65) + ExpByteEIP158(50, :166)×byteLen，
    # uint256 的 byteLen ≤ 32 ⟹ 10 + 1600。
    # EXP 全额在 host：checkMemoryAndCalcDynamicGasEXPEip158 从未被调用（源码原话
    # "todo: we calculate this in build function now"），没有可见 fee 分担。
    "EXP": 1610,
}

# 写不出可用于剪枝的小常量上界的 host op —— 由上界表**派生**，不硬编码。
# 这样新增 host opcode 却忘了写上界时会自动落进这个集合，而不是被静默当成有界
# （沿用 program_verifier 把黑名单翻成 allowlist 的同一模式）。
# 它们的 UF **照扣不误**（无约束 UF 仍然健全），只是 OOG 分支剪不掉、路径规模偏大。
#
# 当前成员及其无界的原因（同样按 AOT 实际执行的 host.go 记）：
#   CALL 四件套  host.go:809 先收 cold−warm(2500)，再转 host.go:741 gasCostWithHostCall
#                累加三项：CallNewAccountGas(25000, protocol_params.go:43)、内存扩展
#                (memoryGasCostCopy, host.go:847)、63/64 转发额度。头一项是常数，后两项
#                无界——AOT 侧没有可见 fee 可减，内存二次项整个在 host 内。
#   CREATE/CREATE2  host.go:361/398 的 `gas − gas/64` 以运行时剩余 gas 为界，没有协议常量
#                   可写（同一个 gas 依赖也是它们进 HOST_GAS_SEQ_KINDS 的理由）。
HOST_GAS_UNBOUNDED_KINDS = HOST_GAS_UF_KINDS - frozenset(HOST_GAS_UPPER_BOUNDS)


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


def host_gas_uf(opcode: str, stack_args: Sequence[BitVecRef],
                seq: BitVecRef | None = None) -> BitVecRef:
    """构造一次 host/builtin 调用的 gas 副作用 UF（64-bit gas cost）。

    opcode 编进函数名，故 SLOAD 与 SSTORE 是不同符号，不会被 Z3 当成同一函数而
    假相消。stack_args 的次序必须与 x86 侧完全一致：错位则 UF 不相消，检查会
    SAT/unknown 而不是假绿。

    Args:
        opcode: 指令名（大写，如 "SLOAD"）。
        stack_args: 该指令影响 gas 的栈输入（规范化前的原始 BitVec）。
        seq: HOST_GAS_SEQ_KINDS 里的指令必填——本路径上的调用序号，作为末位参数。
            是 BitVec 而非 int：x86 合流点合并后可能是 `If(cond, 1, 0)`，此时相消靠
            EUF congruence 而不是语法同一。

    Returns:
        64-bit BitVec，表示这一次 host 调用扣减的 gas。

    Raises:
        ValueError: HOST_GAS_SEQ_KINDS 里的指令漏传 seq。
    """
    # fail-closed：漏传 seq 会生成一元 host_gas_sload(key)，Z3 里 arity 不同就是另一个
    # 函数符号——两侧都误用旧接口时照样相消，seq 静默失效而测试全绿。
    if opcode in HOST_GAS_SEQ_KINDS and seq is None:
        raise ValueError(
            f"{opcode} 的 cost 不是实参的纯函数，host_gas_uf 必须带 seq"
            "（见 HOST_GAS_SEQ_KINDS）；漏传会退化成少一元的 UF 并静默失去调用间的区分度"
        )
    args = [_normalize_uf_arg(a) for a in stack_args]
    if seq is not None:
        args.append(_normalize_uf_arg(seq))
    arg_sorts = [BitVecSort(256) for _ in args]
    f = Function(f"host_gas_{opcode.lower()}", *arg_sorts, BitVecSort(64))
    return f(*args)


def next_host_gas_seq(state, opcode: str) -> BitVecRef | None:
    """取该 opcode 在本路径上的当前调用序号并递增；非 stateful 指令返回 None。

    两侧共用这一份递增规则——序号一旦不一致，UF 就不相消。计数器随 state.copy() 走，
    路径分叉后各分支独立计数；合流合并见 cfg_executor._merge_at_confluence。
    """
    if opcode not in HOST_GAS_SEQ_KINDS:
        return None
    counters = state.host_gas_seq
    seq = counters.get(opcode, BitVecVal(0, 256))
    # simplify 不能省：Z3 不折叠常量，否则序号会长成 `0+1+1+...` 的加法链。
    counters[opcode] = simplify(seq + BitVecVal(1, 256))
    return seq


def emit_host_gas_bound(state, opcode: str, cost: BitVecRef) -> None:
    """把该 opcode 的协议上界挂进 ``state.pending_constraints``，等 executor 取走。

    两侧共用这一条规则——只有一侧加的话不会不健全（上界是关于 UF term 的全局事实，
    一侧断言在联合求解里就够），但两侧的 OOG 剪枝会不对称、路径集发散，而**最终结果
    看不出来**。所以只能靠两侧各自的本地测试盯住，见 tests/unit/test_host_gas_bounds.py。

    无上界的 opcode（HOST_GAS_UNBOUNDED_KINDS）什么都不加——它们的 UF 照扣，只是 OOG
    分支剪不掉。宁可慢也不瞎编上界：上界写小了是静默缩域，没有任何测试看得见。
    """
    bound = HOST_GAS_UPPER_BOUNDS.get(opcode)
    if bound is None:
        return
    # 一律用 ULE，bound==0 不特判：无符号下 `ULE(c, 0)` 与 `c == 0` 逻辑等价
    # （0 是无符号最小值），特判没有语义收益。曾经写成等式并注释"比 ULE 更强"，是误述。
    state.pending_constraints.append(ULE(cost, BitVecVal(bound, 64)))


def charge_host_gas_uf(state, opcode: str, stack_args: Sequence[BitVecRef]):
    """EVM 侧扣减一次 host/builtin 调用的 host-gas UF。

    仅 host_gas_uf_enabled 时生效：功能等价验证下不引入 gas UF，避免污染既有
    observable。注意这与 gas **状态语义**（静态/动态 gas 扣减、bookkeeping）不同，
    后者始终建模、不受开关控制。

    Args:
        state: SMTState；就地扣减 evm_gas。
        opcode: 指令名（大写）。
        stack_args: 影响 gas 的栈输入，次序须与 x86 侧一致。

    Returns:
        更新后的 state（与入参同一对象）。
    """
    if not getattr(state, "host_gas_uf_enabled", False):
        return state
    # 序号在开关**之后**才取：OFF 模式下计数器一动不动，功能等价验证零影响。
    cost = host_gas_uf(opcode, stack_args, next_host_gas_seq(state, opcode))
    emit_host_gas_bound(state, opcode, cost)
    state.evm_gas = state.evm_gas.consume_dynamic(cost)
    return state


def add_return_gas(state, return_gas: int):
    """镜像 x86 dealWithAddGas（impl_amd64.go:3967）：`[R13+0x70] += returnGas`。

    这是**可见机器码**（plain ADDQ，不钳零），属于 gas 状态语义而非 host UF，所以
    **无条件执行**、不受 host_gas_uf_enabled 门控。CREATE/CREATE2 的可见动态 fee 检查
    落在 add/sub 这个窗口**之内**（compileEVMCREATE 的顺序是 add → 可见 fee → host →
    sub），门控掉它会让 OOG 阈值差一个 returnGas。
    """
    if not return_gas:
        return state
    from state.evm_gas_state import EVMGasState

    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas + BitVecVal(return_gas, 64))
    return state


def sub_return_gas(state, return_gas: int):
    """镜像 x86 dealWithSubGas（impl_amd64.go:3983）：`[R13+0x70] -= returnGas`。

    与 add_return_gas 成对；同样无条件执行。
    """
    if not return_gas:
        return state
    from state.evm_gas_state import EVMGasState

    state.evm_gas = EVMGasState(initial_gas=state.evm_gas.Gas - BitVecVal(return_gas, 64))
    return state


def charge_host_gas_uf_with_return_gas(state, opcode: str,
                                       stack_args: Sequence[BitVecRef],
                                       return_gas: int):
    """**CALL 系列专用**：dealWithAddGas → host UF → dealWithSubGas。

    x86 codegen 在 host 调用前后对 [R13+0x70] 做 plain ADD/SUB returnGas
    （= Blk.StaticGas - op.Immediate），host gas 扣减夹在中间。EVM 侧若只扣 UF，
    host 调用点两侧 gas 就差一个 returnGas ⟹ clamp 实参不同 ⟹ UF 不相消 ⟹
    returnGas≠0 时假 SAT。

    **CREATE/CREATE2 不能用本函数**：它们在 add/sub 窗口内还有**可见的**动态 fee
    （compileEVMCREATE 的顺序是 add → checkMemoryAndCalcDynamicGasCreate → host → sub，
    impl_amd64.go:3940-3962），必须由调用方显式串成四段，否则可见 fee 的 OOG 阈值会
    少算一个 returnGas。CALL 系没有可见 fee（checkMemoryAndCalcDynamicGasCall 返回 nil），
    所以可以打包。

    Args:
        state: SMTState；就地扣减 evm_gas。
        opcode: 指令名（大写）。
        stack_args: 影响 gas 的栈输入（与 x86 侧同序）。
        return_gas: Blk.StaticGas - op.Immediate（int，≥0）。
    """
    add_return_gas(state, return_gas)
    charge_host_gas_uf(state, opcode, stack_args)
    sub_return_gas(state, return_gas)
    return state


def _consume_clamp_64(gas64: BitVecRef, cost64: BitVecRef) -> BitVecRef:
    """out-of-gas 钳零的 64-bit 扣减：If(cost>gas, 0, gas-cost)。

    必须与 EVMGasState.consume_dynamic 逐字一致：两侧表达式同构才能在比较时相消，
    否则 UF 不相消 → 假 SAT。
    """
    return If(UGT(cost64, gas64), BitVecVal(0, 64), gas64 - cost64)


def deduct_host_gas_uf_x86(mstate, opcode: str, stack_args: Sequence[BitVecRef],
                           offsets, store_64bit, callengine_domain) -> None:
    """x86 侧扣减 host-gas UF（与 EVM 侧 charge_host_gas_uf 同名相消）。

    host gas 在 Go runtime 内、机器码不可见，故手动从 callengine_gas_remaining
    扣同一个 UF。stack_args 必须与 EVM 侧是同一组栈值、同次序（该调用点两侧栈已
    由功能等价证明相等）。仅 host_gas_uf_enabled 生效，且必须与 EVM 侧
    charge_host_gas_uf 同开同关，否则 UF 不相消。

    Args:
        mstate: x86 SMTState；就地更新 callengine_gas_remaining 与 [R13+0x70]。
        opcode: 指令名（大写），须与 EVM 侧一致。
        stack_args: 影响 gas 的栈输入（与 EVM 侧同序）。
        offsets: aot_profile.offsets（取 "gas_remaining" 偏移）。
        store_64bit: 写 [R13+off] 的回调，保持 side-channel 与 x86_memory 一致。
        callengine_domain: CALLENGINE 内存域（由 caller 传入，避免依赖 x86 模块）。
    """
    if not getattr(mstate, "host_gas_uf_enabled", False):
        return
    from x86_64.models import Register

    # 与 EVM 侧 charge_host_gas_uf 同序取号：两侧序号必须一致才相消。
    cost = host_gas_uf(opcode, stack_args, next_host_gas_seq(mstate, opcode))
    emit_host_gas_bound(mstate, opcode, cost)
    gas_before = mstate.callengine_gas_remaining
    gas_after = _consume_clamp_64(gas_before, cost)

    mstate.callengine_gas_remaining = gas_after
    # 同步 [R13+gas_remaining]（与既有 _sync_callengine_u64_field 同范式）。
    r13 = mstate.x86_registers.get_register(Register.R13)
    gas_off = BitVecVal(offsets["gas_remaining"], 64)
    mstate.x86_memory = store_64bit(r13 + gas_off, gas_after, callengine_domain)
