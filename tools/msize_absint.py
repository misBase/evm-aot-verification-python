"""EVM 侧 ``memory_size`` / free-memory-pointer 的前向抽象解释。

见 docs/块级lockstep等价验证方案.md §3.3 与 §2.3：块级 lockstep 把每个块的定理按
三参数 ``(k, msize, fmp)`` 专门化，本模块负责静态地给出后两个参数的候选值——以及
在给不出时**明确地说"给不出"**（⊤），而不是悄悄退回一个"够大的常数"。

抽象域是三个并行分量，都在 ``(pc, ctx)`` 上 join 到不动点：

1. **抽象值栈** ``stack``：top-first 的 tuple，元素是具体 256-bit int 或 :class:`Unknown`
   （带来源标签的非常量）。join 时按栈顶对齐取 min 长度，逐槽相等则保留否则打成
   ``Unknown("JOIN")``。只用来读浅层栈槽（内存 op 的偏移/长度），顶对齐是安全的。
2. **抽象常量内存** ``mem``：``dict[具体地址 -> 具体 256-bit 值]``，缺失即未知。
   它存在的唯一理由是追踪 free-memory-pointer ``mem[0x40]``——Solidity 的每个内存
   访问偏移都从 ``MLOAD(0x40)`` 来，丢掉它整条链立刻塌成 ⊤。
   ``track_constant_memory=False`` 关掉它（MLOAD 一律未知），用作归因对照。
3. **MSize**：具体值集合 ``mset``（超过 :data:`VALUE_SET_CAP` 记 ⊤）+ 区间 ``(lo, hi)``。

演化规则以**本仓库的实现**为准，不是以协议直觉为准
（``evm_ir/semantics_gas.py::charge_dynamic_gas`` → ``state/evm_gas_state.py::memory_expansion_fee``）::

    MSize' = max(MSize, ceil32(requested))      # rounded > mem.Len() 才扩
    length == 0  ⇒  requested = 0               # calcMemSize64: 零长访问不扩容

两条容易写错、且已经踩过的实现依赖：

* **CALL / CALLCODE / DELEGATECALL / STATICCALL 在当前模型里不改 MSize。**
  ``evm_ir/semantics.py::_write_call_return_data`` 明说"当前模型不包含 host 内部的
  CALL 内存扩展，因此两侧均保持 MSize"，且 CALL 族的 gas 走
  ``charge_host_gas_uf_with_return_gas``（纯 UF），根本不经过 ``charge_dynamic_gas``。
  按协议直觉给 CALL 补上 ``max(args_off+args_len, ret_off+ret_len)`` 的扩展，抽象
  解释就会与被验证的语义不一致——那不是"更保守"，而是**结论钉在证明域之外**。
  CREATE/CREATE2 相反：它们走 ``charge_memory_and_word_gas``，**要**扩。
  若哪天把 host 内部扩展纳入建模，这里必须同步改。
* ``requested > MEM_CAP`` 的路径在语义里是 gas 错误分支（cap 支），正常路径不可达，
  故 MSize 保持不变而不是饱和到 cap。

CFG 用**上下文敏感**版本（返回地址影子栈）。裸的 ``build_evm_cfg`` 会把每个 callee
的返回点连回所有 caller，假环让抽象值栈沿环反复 join 成 ⊤——ENS 尚可，CErc20/Safe
直接发散（见方案 §3.2）。

本模块是**纯分析、无证明义务**的前置：选错只影响性能与覆盖率。但它必须 fail-closed
——不动点没收敛、遇到未建模的 opcode、自校验不过，一律抛异常，绝不返回"部分结果"。
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import (
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from evm_ir.models import EVMBlock, EvmOperator
from tools.call_provenance import (
    CallProvenanceError,
    ReturnAwareCfg,
    build_return_aware_cfg,
)
from verification.loop_pairing import _evm_control_op


# ---------------------------------------------------------------------------
# 常量
# ---------------------------------------------------------------------------

UINT256_MASK = (1 << 256) - 1
UINT64_LIMIT = 1 << 64

#: go-hpc-evm ``gas_table.go`` 的 newMemSize cap；超过即 gas 错误分支。
MEM_CAP = 0x1FFFFFFFE0

#: Solidity free-memory-pointer 的固定槽位。
FREE_MEMORY_POINTER_SLOT = 0x40

#: MSize 具体值集合的上限，超出即 ⊤。实测三合约上 2–4 值之后**直接跳到 ⊤**，
#: 5–16 档恒为 0（方案 §3.3 的核心结构性发现），所以这个 cap 从未真正生效——
#: 它只是防止病态输入把集合撑爆。
VALUE_SET_CAP = 16

#: 抽象常量内存的条目上限（超出按地址序截断）。
CONST_MEM_ENTRIES_CAP = 512

#: 返回地址影子栈深度上限。
SHADOW_STACK_CAP = 64

#: 抽象值栈高度上限（只读浅层槽，深处截断无害）。
ABSTRACT_STACK_CAP = 256

#: 每个 ⊤ 状态保留的 ⊤ 源站点数上限。
TOP_SOURCE_CAP = 8

#: 不动点迭代预算；耗尽即 fail-closed。
ITERATION_BUDGET = 3_000_000


class MSizeAnalysisError(RuntimeError):
    """抽象解释无法给出可信结论（未建模 opcode / 不收敛 / 自校验失败）。"""


# ---------------------------------------------------------------------------
# ⊤ 与"带来源标签的未知值"
# ---------------------------------------------------------------------------


class _TopType:
    """⊤ 的单例类型。

    方案 §2.3：⊤ **不是一个"桶"**，它表示该块的参数不可静态确定、只能降级。用
    ``None`` 或空集表示会与"没算过"/"没有值"混淆，进而在下游被当成一个普通取值
    专门化掉——那是静默不健全。因此它是一个独立哨兵，且不可证伪地为真值
    （``bool(TOP) is True``），杜绝 ``if not value`` 这类误用。
    """

    _instance: Optional["_TopType"] = None

    def __new__(cls) -> "_TopType":
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self) -> str:  # pragma: no cover - 调试用
        return "TOP"

    def __bool__(self) -> bool:
        return True


#: 不可静态确定。
TOP = _TopType()

#: 块入口 MSize：具体值集合（非空）或 :data:`TOP`。
MSizeValue = Union[FrozenSet[int], _TopType]

#: 块入口 ``mem[0x40]``：具体值或 :data:`TOP`。
FmpValue = Union[int, _TopType]


class Unknown:
    """非常量的抽象**值**，携带一个有限集合里的来源标签。

    标签只用于 ⊤ 的成因归类（方案 §4.5b 的攻坚清单），不参与任何常量判定：
    ``Unknown`` 之间只按标签相等，join 单调地沿
    ``const > Unknown(t) > Unknown("JOIN")`` 下降，因此不动点仍然终止。
    """

    __slots__ = ("tag",)
    _interned: Dict[str, "Unknown"] = {}

    def __new__(cls, tag: str) -> "Unknown":
        cached = cls._interned.get(tag)
        if cached is None:
            cached = object.__new__(cls)
            object.__setattr__(cached, "tag", tag)
            cls._interned[tag] = cached
        return cached

    def __repr__(self) -> str:  # pragma: no cover - 调试用
        return f"?{self.tag}"

    def __eq__(self, other: object) -> bool:
        return other is self

    def __hash__(self) -> int:
        return hash(("Unknown", self.tag))


UNKNOWN_JOIN = Unknown("JOIN")   # 跨路径 / 跨调用边汇合
UNKNOWN_MIX = Unknown("MIX")     # 多个不同来源的算术混合
UNKNOWN_ANY = Unknown("?")       # 栈底被顶对齐截断等，无来源信息


def is_unknown(value: object) -> bool:
    """value 是否为非常量抽象值。"""
    return isinstance(value, Unknown)


#: ⊤ 成因标签的人话解释（报告用；标签集合即 :class:`Unknown` 的 tag 值域）。
CAUSE_DESCRIPTIONS: Mapping[str, str] = {
    "MLOAD@0x00": "scratch 0x00 内容不可知",
    "MLOAD@0x20": "scratch 0x20 内容不可知",
    "MLOAD@0x40": "free-memory-pointer 不可知（该点 mem[0x40] 已被 join 掉或被清空）",
    "MLOAD@0x60": "0x60 内容不可知",
    "MLOAD@const": "常量地址的内存内容不可知",
    "MLOAD@dyn": "动态地址 MLOAD（偏移本身就不是常量）",
    "CALLDATALOAD": "calldata 输入（ABI 头 / 动态数组长度）",
    "CALLDATASIZE": "calldatasize",
    "SLOAD": "storage / transient storage 读出的值",
    "SHA3": "keccak 结果",
    "CALLRET": "外部调用或 CREATE 的返回值",
    "RETURNDATASIZE": "returndatasize（外部调用返回长度）",
    "EXTCODESIZE": "extcodesize",
    "ENV": "环境量（CALLER/ADDRESS/GAS/…）",
    "JOIN": "跨路径或跨调用边汇合（同一 (pc,ctx) 上两个不同具体值 join 成 ⊤）",
    "MIX": "多来源算术混合",
    "?": "栈底被顶对齐截断 / 未建模",
    "SET_OVERFLOW": "MSize 具体值集合超过上限（循环内累积等）",
}


# ---------------------------------------------------------------------------
# 栈效应表
# ---------------------------------------------------------------------------

_SKIP_OPS = frozenset({"TAG", "BLOCKEND"})
_TERMINAL_OPS = frozenset({"STOP", "RETURN", "REVERT", "SELFDESTRUCT", "INVALID"})
_CONTROL_OPS = _TERMINAL_OPS | frozenset({"JUMP", "JUMPI"})

_BINARY_OPS = (
    "ADD SUB MUL DIV SDIV MOD SMOD EXP SIGNEXTEND LT GT SLT SGT EQ AND OR XOR "
    "BYTE SHL SHR SAR"
).split()
_UNARY_OPS = "ISZERO NOT".split()
_NULLARY_OPS = (
    "ADDRESS ORIGIN CALLER CALLVALUE CALLDATASIZE CODESIZE GASPRICE "
    "RETURNDATASIZE COINBASE TIMESTAMP NUMBER DIFFICULTY PREVRANDAO GASLIMIT "
    "CHAINID SELFBALANCE BASEFEE BLOBBASEFEE PC MSIZE GAS"
).split()
_UNARY_LOAD_OPS = (
    "CALLDATALOAD MLOAD SLOAD TLOAD BALANCE EXTCODESIZE EXTCODEHASH BLOCKHASH "
    "BLOBHASH"
).split()

#: ``kind -> (npop, npush)``；与 ``evm_ir/semantics.py`` 的 pop/push 序列逐条对齐，
#: 正确性由 :func:`validate_stack_effects` 用 Go 导出的 ``EVMBlock.stack_depth``
#: 逐块交叉校验（三合约 1592 块零不符）。
_STACK_EFFECT: Dict[str, Tuple[int, int]] = {}
for _kind in _BINARY_OPS:
    _STACK_EFFECT[_kind] = (2, 1)
for _kind in _UNARY_OPS:
    _STACK_EFFECT[_kind] = (1, 1)
for _kind in _NULLARY_OPS:
    _STACK_EFFECT[_kind] = (0, 1)
for _kind in _UNARY_LOAD_OPS:
    _STACK_EFFECT[_kind] = (1, 1)
_STACK_EFFECT.update(
    {
        "ADDMOD": (3, 1),
        "MULMOD": (3, 1),
        "POP": (1, 0),
        "MSTORE": (2, 0),
        "MSTORE8": (2, 0),
        "SSTORE": (2, 0),
        "TSTORE": (2, 0),
        "SHA3": (2, 1),
        "KECCAK256": (2, 1),
        "CALLDATACOPY": (3, 0),
        "CODECOPY": (3, 0),
        "RETURNDATACOPY": (3, 0),
        "MCOPY": (3, 0),
        "EXTCODECOPY": (4, 0),
        "CREATE": (3, 1),
        "CREATE2": (4, 1),
        "CALL": (7, 1),
        "CALLCODE": (7, 1),
        "DELEGATECALL": (6, 1),
        "STATICCALL": (6, 1),
        "RETURN": (2, 0),
        "REVERT": (2, 0),
        "STOP": (0, 0),
        "INVALID": (0, 0),
        "SELFDESTRUCT": (1, 0),
        "TAG": (0, 0),
        "BLOCKEND": (0, 0),
        "PUSH": (0, 1),
    }
)
del _kind


def op_stack_effect(op: EvmOperator) -> Tuple[int, int]:
    """单条 IR 操作的 ``(npop, npush)``。

    静态 JUMP/JUMPI **不 pop 目标**：Go 侧已把 ``PUSH target; JUMP`` 折成带
    immediate 的 ``JUMP``，目标不在运行时栈上。这条是 ``stack_depth`` 自校验
    能对上的前提之一。
    """
    kind = op.kind.upper()
    if kind == "DUP":
        return (0, 1)
    if kind == "SWAP":
        return (0, 0)
    if kind == "LOG":
        return (2 + (op.immediate or 0), 0)
    if kind == "JUMP":
        return (0, 0) if (op.is_static and op.immediate is not None) else (1, 0)
    if kind == "JUMPI":
        return (1, 0) if (op.is_static and op.immediate is not None) else (2, 0)
    effect = _STACK_EFFECT.get(kind)
    if effect is None:
        raise MSizeAnalysisError(
            f"未建模的 opcode {kind!r}（pc={op.pc}）：抽象解释必须 fail-closed，"
            f"补进 _STACK_EFFECT 并核对 evm_ir/semantics.py 的 pop/push 序列"
        )
    return effect


def live_operations(block: EVMBlock) -> List[EvmOperator]:
    """块的活指令：过滤 TAG/BLOCKEND，截到第一个控制流操作（含）为止。

    与 ``evm_ir/cfg_executor.py`` 的约定一致——其后是死代码。
    """
    out: List[EvmOperator] = []
    for op in block.operations:
        kind = op.kind.upper()
        if kind in _SKIP_OPS:
            continue
        out.append(op)
        if kind in _CONTROL_OPS:
            break
    return out


@dataclass(frozen=True, order=True)
class StackEffectMismatch:
    """自校验失败项：Σ(per-op delta) 与 Go 导出的 ``stack_depth`` 不符。"""

    block_pc: int
    computed_delta: int
    exported_stack_depth: int


def validate_stack_effects(
    blocks: Sequence[EVMBlock],
) -> Tuple[StackEffectMismatch, ...]:
    """逐块核对 ``Σ(per-op delta) == EVMBlock.stack_depth``。

    这是抽象值栈正确性的唯一强证据：Go 编译器独立算出的净栈效应与本模块的
    opcode 表逐块相等。表里错一条（少 pop 一个操作数、静态 JUMP 误 pop）都会在
    某个块上体现为差值。返回空 tuple 即全部相符。
    """
    mismatches: List[StackEffectMismatch] = []
    for block in blocks:
        delta = 0
        for op in live_operations(block):
            npop, npush = op_stack_effect(op)
            delta += npush - npop
        if delta != block.stack_depth:
            mismatches.append(
                StackEffectMismatch(block.pc, delta, block.stack_depth)
            )
    return tuple(mismatches)


# ---------------------------------------------------------------------------
# 具体求值
# ---------------------------------------------------------------------------


def _ceil32(value: int) -> int:
    return ((value + 31) >> 5) << 5


def _merge_unknown_tag(values: Sequence[object]) -> Optional[Unknown]:
    """若操作数里有非常量，返回结果应继承的来源标签，否则 None。"""
    tags = {v.tag for v in values if is_unknown(v)}
    if not tags:
        return None
    if len(tags) == 1:
        return Unknown(next(iter(tags)))
    if "JOIN" in tags:
        return UNKNOWN_JOIN
    return UNKNOWN_MIX


def _eval_op(kind: str, args: Sequence[object]) -> object:
    """具体 256-bit 求值；操作数含非常量则结果继承其来源标签。

    只建模抽象解释真正需要的算术（内存偏移/长度的计算链）。其余一律 ``UNKNOWN_ANY``
    ——少算一条只会多出 ⊤，不会给出错的具体值。
    """
    inherited = _merge_unknown_tag(args)
    if inherited is not None:
        return inherited
    a = args
    try:
        if kind == "ADD":
            return (a[0] + a[1]) & UINT256_MASK
        if kind == "SUB":
            return (a[0] - a[1]) & UINT256_MASK
        if kind == "MUL":
            return (a[0] * a[1]) & UINT256_MASK
        if kind == "DIV":
            return 0 if a[1] == 0 else a[0] // a[1]
        if kind == "MOD":
            return 0 if a[1] == 0 else a[0] % a[1]
        if kind == "AND":
            return a[0] & a[1]
        if kind == "OR":
            return a[0] | a[1]
        if kind == "XOR":
            return a[0] ^ a[1]
        if kind == "NOT":
            return (~a[0]) & UINT256_MASK
        if kind == "ISZERO":
            return 1 if a[0] == 0 else 0
        if kind == "EQ":
            return 1 if a[0] == a[1] else 0
        if kind == "LT":
            return 1 if a[0] < a[1] else 0
        if kind == "GT":
            return 1 if a[0] > a[1] else 0
        if kind == "SHL":
            return (a[1] << a[0]) & UINT256_MASK if a[0] < 256 else 0
        if kind == "SHR":
            return (a[1] >> a[0]) if a[0] < 256 else 0
        if kind == "BYTE":
            index = a[0]
            return 0 if index >= 32 else (a[1] >> (8 * (31 - index))) & 0xFF
    except (IndexError, TypeError, ValueError, OverflowError):
        return UNKNOWN_ANY
    return UNKNOWN_ANY


#: push 出非常量的 opcode -> 来源标签。
_SOURCE_TAG: Mapping[str, str] = {
    "CALLDATALOAD": "CALLDATALOAD",
    "CALLDATASIZE": "CALLDATASIZE",
    "SLOAD": "SLOAD",
    "TLOAD": "SLOAD",
    "SHA3": "SHA3",
    "KECCAK256": "SHA3",
    "CALL": "CALLRET",
    "CALLCODE": "CALLRET",
    "DELEGATECALL": "CALLRET",
    "STATICCALL": "CALLRET",
    "CREATE": "CALLRET",
    "CREATE2": "CALLRET",
    "RETURNDATASIZE": "RETURNDATASIZE",
    "EXTCODESIZE": "EXTCODESIZE",
    "EXTCODEHASH": "ENV",
    "BALANCE": "ENV",
    "BLOCKHASH": "ENV",
}

_ENV_OPS = frozenset(
    "GAS ADDRESS ORIGIN CALLER CALLVALUE GASPRICE NUMBER TIMESTAMP CHAINID "
    "SELFBALANCE COINBASE GASLIMIT DIFFICULTY PREVRANDAO BASEFEE BLOBBASEFEE "
    "CODESIZE MSIZE PC".split()
)


def _push_value(kind: str, args: Sequence[object], mem: Mapping[int, int]) -> object:
    """opcode 压回栈的抽象值。"""
    if kind == "MLOAD":
        offset = args[0]
        if is_unknown(offset):
            return Unknown("MLOAD@dyn")
        if offset in mem:
            return mem[offset]
        if offset in (0x00, 0x20, FREE_MEMORY_POINTER_SLOT, 0x60):
            return Unknown(f"MLOAD@0x{offset:02x}")
        return Unknown("MLOAD@const")
    tag = _SOURCE_TAG.get(kind)
    if tag is not None:
        return Unknown(tag)
    if kind in _ENV_OPS:
        return Unknown("ENV")
    return _eval_op(kind, args)


# ---------------------------------------------------------------------------
# 抽象状态
# ---------------------------------------------------------------------------


@dataclass(frozen=True, order=True)
class TopSource:
    """把 MSize 打成 ⊤ 的具体站点（方案 §4.5b 的攻坚清单条目）。"""

    block_pc: int
    op_pc: int
    op_kind: str
    cause: str

    @property
    def description(self) -> str:
        return CAUSE_DESCRIPTIONS.get(self.cause, self.cause)

    def __str__(self) -> str:  # pragma: no cover - 报告用
        return (
            f"block={self.block_pc} op_pc={self.op_pc} {self.op_kind} "
            f"cause={self.cause}"
        )


class _AbstractState:
    """一个 ``(pc, ctx)`` 上的块入口抽象状态。"""

    __slots__ = ("stack", "mem", "mset", "lo", "hi", "src")

    def __init__(
        self,
        stack: Tuple[object, ...],
        mem: Dict[int, int],
        mset: MSizeValue,
        lo: int,
        hi: int,
        src: FrozenSet[TopSource] = frozenset(),
    ) -> None:
        self.stack = stack          # top-first
        self.mem = mem              # 具体地址 -> 具体值
        self.mset = mset            # frozenset[int] | TOP
        self.lo = lo
        self.hi = hi                # hi >= MEM_CAP 即"无信息上界"
        self.src = src              # mset 为 TOP 时的源站点

    def key(self) -> Tuple[object, ...]:
        """不动点判等用的完整指纹。"""
        return (
            self.stack,
            tuple(sorted(self.mem.items())),
            self.mset,
            self.lo,
            self.hi,
            self.src,
        )


def _join_values(a: object, b: object) -> object:
    """抽象值的 join：不相等即塌成 ``Unknown("JOIN")``。"""
    if a is b or a == b:
        return a
    return UNKNOWN_JOIN


def _join_states(x: _AbstractState, y: _AbstractState) -> _AbstractState:
    """两个抽象状态的 join。

    栈按**栈顶对齐**取 min 长度：不同调用路径上栈底的活跃深度不同，底对齐会把
    完全无关的槽位配到一起。只读浅层槽（内存 op 的操作数）时顶对齐是安全的。

    ⊤ 的源站点只从 ⊤ 的那一侧继承：非 ⊤ 一侧没有源站点可言，混进来会把攻坚
    清单稀释成噪声。
    """
    n = min(len(x.stack), len(y.stack))
    stack = tuple(_join_values(x.stack[i], y.stack[i]) for i in range(n))
    mem = {k: v for k, v in x.mem.items() if k in y.mem and y.mem[k] == v}

    if x.mset is TOP and y.mset is TOP:
        mset: MSizeValue = TOP
        src = x.src | y.src
    elif x.mset is TOP:
        mset, src = TOP, x.src
    elif y.mset is TOP:
        mset, src = TOP, y.src
    else:
        union = x.mset | y.mset
        mset = TOP if len(union) > VALUE_SET_CAP else frozenset(union)
        src = frozenset()
    if len(src) > TOP_SOURCE_CAP:
        src = frozenset(sorted(src)[:TOP_SOURCE_CAP])
    return _AbstractState(stack, mem, mset, min(x.lo, y.lo), max(x.hi, y.hi), src)


# ---------------------------------------------------------------------------
# 传递函数
# ---------------------------------------------------------------------------


class _NoRequest:
    """哨兵：本条指令不触发内存扩展。"""


_NO_REQUEST = _NoRequest()


def _kill_const_mem(mem: Dict[int, int], lo: int, hi: int) -> Dict[int, int]:
    """删掉与字节区间 ``[lo, hi]`` 有交叠的 32 字节槽（槽 a 覆盖 ``[a, a+31]``）。"""
    return {a: v for a, v in mem.items() if a + 31 < lo or a > hi}


def _transfer_block(
    block: EVMBlock,
    state: _AbstractState,
    *,
    track_constant_memory: bool = True,
    track_sources: bool = True,
) -> _AbstractState:
    """跑完一个块的活指令，返回出口抽象状态。"""
    stack: List[object] = list(state.stack)
    mem: Dict[int, int] = dict(state.mem)
    mset, lo, hi, src = state.mset, state.lo, state.hi, state.src

    def pop(count: int) -> List[object]:
        # 栈底被顶对齐 join 截断时补 UNKNOWN_ANY——保守方向正确（多出 ⊤）。
        return [stack.pop(0) if stack else UNKNOWN_ANY for _ in range(count)]

    def offset_plus(offset: object, size: int) -> object:
        """``offset + size``，按 uint64 语义。

        溢出 uint64 在语义里走 ``calcMemSize64`` 的 overflow 错误分支，正常路径
        不可达；抽象上按未知处理（下游只会更保守）。
        """
        if is_unknown(offset):
            return offset
        total = offset + size
        return total if total < UINT64_LIMIT else UNKNOWN_ANY

    def sized_request(offset: object, length: object) -> object:
        """``calcMemSize64``：**length == 0 时 requested = 0，不扩容**。

        这条不能省：零长 CALLDATACOPY/RETURNDATACOPY 在真实代码里很常见，按
        ``offset + 0`` 处理会把一个动态 offset 无谓地传染成 ⊤。
        """
        if is_unknown(length):
            return length
        if length == 0:
            return 0
        return offset_plus(offset, length)

    for op in live_operations(block):
        kind = op.kind.upper()
        npop, npush = op_stack_effect(op)

        if kind == "PUSH":
            stack.insert(0, (op.immediate or 0) & UINT256_MASK)
            continue
        if kind == "DUP":
            n = op.param or 1
            stack.insert(0, stack[n - 1] if len(stack) >= n else UNKNOWN_ANY)
            continue
        if kind == "SWAP":
            n = op.param or 1
            if len(stack) > n:
                stack[0], stack[n] = stack[n], stack[0]
            else:
                # 栈底被截断，无法定位交换目标 ⇒ 整栈保守打成未知。
                stack = [UNKNOWN_ANY] * len(stack)
            continue

        args = pop(npop)

        # ---- 内存扩展（MSize 演化）----------------------------------------
        # 每一条都对应 evm_ir/semantics.py 里一次 charge_dynamic_gas /
        # charge_memory_and_word_gas；**没有对应调用的 opcode 就不能出现在这里**。
        # 尤其：CALL/CALLCODE/DELEGATECALL/STATICCALL 刻意缺席，见模块 docstring。
        request: object = _NO_REQUEST
        if kind in ("MLOAD", "MSTORE"):
            request = offset_plus(args[0], 32)
        elif kind == "MSTORE8":
            request = offset_plus(args[0], 1)
        elif kind in ("SHA3", "KECCAK256"):
            request = sized_request(args[0], args[1])
        elif kind in ("CALLDATACOPY", "CODECOPY", "RETURNDATACOPY"):
            request = sized_request(args[0], args[2])
        elif kind == "MCOPY":
            dst, source, length = args[0], args[1], args[2]
            unknown = _merge_unknown_tag([dst, source])
            base = unknown if unknown is not None else max(dst, source)
            request = sized_request(base, length)
        elif kind == "EXTCODECOPY":
            request = sized_request(args[1], args[3])
        elif kind in ("CREATE", "CREATE2"):
            request = sized_request(args[1], args[2])
        elif kind in ("RETURN", "REVERT"):
            request = sized_request(args[0], args[1])
        elif kind == "LOG":
            request = sized_request(args[0], args[1])

        if request is not _NO_REQUEST:
            if is_unknown(request):
                # 第一个把 MSize 打成 ⊤ 的站点才记源；之后的都是"已经 ⊤"。
                if mset is not TOP and track_sources:
                    src = frozenset(
                        {TopSource(block.pc, op.pc, kind, request.tag)}
                    )
                mset, hi = TOP, MEM_CAP
            elif request <= MEM_CAP:
                rounded = _ceil32(request)
                if mset is not TOP:
                    grown = frozenset(max(m, rounded) for m in mset)
                    mset = TOP if len(grown) > VALUE_SET_CAP else grown
                    if mset is TOP and track_sources:
                        src = frozenset(
                            {TopSource(block.pc, op.pc, kind, "SET_OVERFLOW")}
                        )
                lo, hi = max(lo, rounded), max(hi, rounded)
            # request > MEM_CAP：语义上是 gas 错误分支（cap 支），正常路径不可达，
            # MSize 不变。饱和到 cap 反而会污染下游的具体值。

        # ---- 抽象常量内存（free-memory-pointer 追踪）------------------------
        if track_constant_memory:
            if kind == "MSTORE":
                offset, value = args[0], args[1]
                if is_unknown(offset):
                    mem = {}          # 写到未知地址：整表失效
                else:
                    mem = _kill_const_mem(mem, offset - 31, offset + 31)
                    if not is_unknown(value):
                        mem[offset] = value
            elif kind == "MSTORE8":
                offset = args[0]
                mem = {} if is_unknown(offset) else _kill_const_mem(
                    mem, offset - 31, offset
                )
            elif kind in ("CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "MCOPY"):
                dst, length = args[0], args[2]
                if is_unknown(dst) or is_unknown(length):
                    mem = {}
                elif length:
                    mem = _kill_const_mem(mem, dst - 31, dst + length - 1)
            elif kind == "EXTCODECOPY":
                dst, length = args[1], args[3]
                if is_unknown(dst) or is_unknown(length):
                    mem = {}
                elif length:
                    mem = _kill_const_mem(mem, dst - 31, dst + length - 1)
            elif kind in ("CALL", "CALLCODE"):
                # CALL 不改 MSize，但**会写 returndata 到 [retOffset, +retSize)**
                # （evm_ir/semantics.py::_write_call_return_data），常量内存必须失效。
                ret_offset, ret_size = args[5], args[6]
                if is_unknown(ret_offset) or is_unknown(ret_size):
                    mem = {}
                elif ret_size:
                    mem = _kill_const_mem(
                        mem, ret_offset - 31, ret_offset + ret_size - 1
                    )
            elif kind in ("DELEGATECALL", "STATICCALL"):
                ret_offset, ret_size = args[4], args[5]
                if is_unknown(ret_offset) or is_unknown(ret_size):
                    mem = {}
                elif ret_size:
                    mem = _kill_const_mem(
                        mem, ret_offset - 31, ret_offset + ret_size - 1
                    )
            if len(mem) > CONST_MEM_ENTRIES_CAP:
                kept = sorted(mem)[:CONST_MEM_ENTRIES_CAP]
                mem = {a: mem[a] for a in kept}
        else:
            mem = {}

        if npush:
            stack.insert(0, _push_value(kind, args, mem if track_constant_memory else {}))

        if len(stack) > ABSTRACT_STACK_CAP:
            stack = stack[:ABSTRACT_STACK_CAP]

    return _AbstractState(tuple(stack), mem, mset, lo, hi, src)


class _StackOnlyBlock:
    """给 :func:`_transfer_block` 用的临时块（只跑前缀指令、不记源站点）。"""

    __slots__ = ("operations", "pc")

    def __init__(self, operations: Sequence[EvmOperator]) -> None:
        self.operations = list(operations)
        self.pc = -1


def _returned_address(block: EVMBlock, state: _AbstractState) -> object:
    """返回点块的 ``JUMP`` 弹出的目标地址在块入口状态下的抽象值。

    做法是重跑块内活指令但停在控制流 op 之前，取栈顶。抽象值栈能直接给出返回
    地址时优先用它——比影子栈更精确（影子栈只在抽象值失效时兜底）。
    """
    ops = live_operations(block)
    if not ops or ops[-1].kind.upper() != "JUMP":
        return UNKNOWN_ANY
    prefix = _StackOnlyBlock(ops[:-1])
    out = _transfer_block(
        prefix,
        _AbstractState(state.stack, state.mem, state.mset, state.lo, state.hi, state.src),
        track_sources=False,
    )
    return out.stack[0] if out.stack else UNKNOWN_ANY


# ---------------------------------------------------------------------------
# 上下文敏感 CFG
# ---------------------------------------------------------------------------


def _build_return_aware_cfg(blocks: Sequence[EVMBlock]) -> ReturnAwareCfg:
    """返回地址影子栈所需的 CFG（``by_pc / succs / pads / ret_points / entry``）。

    取自 ``tools/call_provenance.py``（方案 §3.2），与深度类分析同源同口径。其
    结构性拒绝（未解析动态跳转、JUMPI 返回形态等）转成 :class:`MSizeAnalysisError`，
    保持本模块"只抛一种异常"的 fail-closed 约定。
    """
    try:
        return build_return_aware_cfg(blocks)
    except CallProvenanceError as exc:
        raise MSizeAnalysisError(f"无法建立返回地址影子栈的 CFG：{exc}") from exc


def _pads_pushed(block: EVMBlock, pads: Set[int]) -> Tuple[int, ...]:
    """块按程序序压入影子栈的返回 pad。

    方案 §3.2 的踩坑记录：**栈序比集合交集信息量大**。CErc20 块 836 是
    ``PUSH 855; PUSH 850; JUMP 13048``，855 是留给后续调用的 continuation，
    只压"本次调用的 pad"会丢帧，之后返回 thunk 链连弹三帧却只压过一帧，影子栈
    见底 ⇒ 假环复活。所以这里压**全部** pad（不去重、按程序序），只排除跳转目标
    本身。
    """
    ctrl = _evm_control_op(block)
    target = ctrl.immediate if (ctrl is not None and ctrl.is_static) else None
    return tuple(
        op.immediate
        for op in block.operations
        if op.kind.upper() == "PUSH"
        and op.immediate is not None
        and op.immediate in pads
        and op.immediate != target
    )


# ---------------------------------------------------------------------------
# 结果对象
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MSizeStats:
    """抽象解释的规模与分布统计（方案 §3.3 的表就是它）。"""

    contract_blocks: int
    reachable_blocks: int
    states: int
    iterations: int
    #: 入口 MSize 静态唯一的块数 / 占比
    unique_blocks: int
    unique_ratio: float
    #: 值集合分布：2–4 档、5–16 档、⊤ 档
    small_set_blocks: int
    medium_set_blocks: int
    top_blocks: int
    top_ratio: float
    #: 唯一值直方图（值 -> 块数），预期高度集中在 0x60
    unique_value_histogram: Mapping[int, int]
    #: 入口 ``mem[0x40]`` 静态唯一的块数
    fmp_unique_blocks: int
    #: ⊤ 块里"继承自上游"的 / "本块自产"的 / 无归因的
    inherited_top_blocks: int
    self_top_blocks: int
    unattributed_top_blocks: int
    #: ⊤ 源站点 -> 它解释的 ⊤ 块数（§4.5b 攻坚清单）
    top_source_sites: Mapping[TopSource, int]
    #: 返回边的解析方式统计（抽象值栈 / 影子栈 / 未解析）
    return_edge_resolution: Mapping[str, int]
    #: 自校验结果；非空即 :func:`analyze_memory_size` 已抛异常
    stack_effect_mismatches: Tuple[StackEffectMismatch, ...] = ()


@dataclass(frozen=True)
class MSizeAbstraction:
    """三合约级别的分析产出。

    ``msize`` / ``fmp`` 的键是**可达**块的 pc。不可达块不在映射里——它们没有
    "入口值"可言，用 ⊤ 表示会与"到达了但不可确定"混为一谈。
    """

    #: pc -> 入口 MSize 的具体值集合，或 :data:`TOP`
    msize: Mapping[int, MSizeValue]
    #: pc -> 入口 ``mem[0x40]`` 的具体值，或 :data:`TOP`
    fmp: Mapping[int, FmpValue]
    #: pc -> MSize 下界（⊤ 块也有；方案 §4.3：下界有信息，上界恒为 CAP 无信息）
    lower_bounds: Mapping[int, int]
    #: pc -> MSize 上界；``>= MEM_CAP`` 即无信息
    upper_bounds: Mapping[int, int]
    #: ⊤ 块 pc -> 其 ⊤ 的源站点（§4.5b 攻坚清单）
    top_sources: Mapping[int, Tuple[TopSource, ...]]
    stats: MSizeStats

    # -- 查询 --------------------------------------------------------------

    def is_top(self, pc: int) -> bool:
        """块入口 MSize 是否不可静态确定（含不可达：不可达同样不能专门化）。"""
        return self.msize.get(pc, TOP) is TOP

    def msize_values(self, pc: int) -> MSizeValue:
        return self.msize.get(pc, TOP)

    def unique_msize(self, pc: int) -> Optional[int]:
        """入口 MSize 的唯一具体值；非唯一或 ⊤ 返回 None。"""
        values = self.msize.get(pc)
        if values is None or values is TOP or len(values) != 1:
            return None
        return next(iter(values))

    def unique_fmp(self, pc: int) -> Optional[int]:
        """入口 ``mem[0x40]`` 的唯一具体值；⊤ 返回 None。"""
        value = self.fmp.get(pc)
        return None if (value is None or value is TOP) else value

    def specialization(self, pc: int) -> Optional[Tuple[int, int]]:
        """块可用于三参数专门化的 ``(msize, fmp)``；不可专门化返回 None。

        方案 §4.1：两者必须**联合**注入——只注 ``msize``，块内 ``MLOAD(0x40)``
        读到的仍是自由符号，``checkMemoryAndCalcDynamicGas`` 的溢出检查链照样
        泡开（CErc20 5343 只注 msize 仍 TIMEOUT）。因此"可专门化"的判据是两者
        同时具体，而不是任一具体。
        """
        msize = self.unique_msize(pc)
        fmp = self.unique_fmp(pc)
        if msize is None or fmp is None:
            return None
        return (msize, fmp)

    def top_blocks(self) -> Tuple[int, ...]:
        return tuple(sorted(pc for pc in self.msize if self.msize[pc] is TOP))

    def specializable_blocks(self) -> Tuple[int, ...]:
        return tuple(
            sorted(pc for pc in self.msize if self.specialization(pc) is not None)
        )

    def top_source_ranking(self) -> Tuple[Tuple[TopSource, int], ...]:
        """⊤ 源站点按"解释了多少 ⊤ 块"降序——§4.5b 的攻坚顺序。"""
        items = self.stats.top_source_sites.items()
        return tuple(sorted(items, key=lambda kv: (-kv[1], kv[0])))


# ---------------------------------------------------------------------------
# 入口
# ---------------------------------------------------------------------------


def analyze_memory_size(
    evm_blocks: Sequence[EVMBlock],
    *,
    track_constant_memory: bool = True,
    context_sensitive: bool = True,
    validate_stack: bool = True,
    iteration_budget: int = ITERATION_BUDGET,
) -> MSizeAbstraction:
    """对 EVM IR 块做 MSize / fmp 的前向抽象解释。

    Args:
        evm_blocks: ``EVMProgram.blocks``（入口块必须是第一个）。
        track_constant_memory: 是否追踪抽象常量内存。关掉即 free-memory-pointer
            不可知，用于归因对照（关掉后唯一率会明显下降）。
        context_sensitive: 是否用返回地址影子栈。关掉是**保守对照**：返回点连回
            所有 caller（含假环），结论只是下界。生产路径必须开着——裸 CFG 在
            CErc20/Safe 上直接发散。
        validate_stack: 是否先跑 ``stack_depth`` 自校验（默认开，失败即抛）。
        iteration_budget: 不动点迭代预算；耗尽即抛（fail-closed）。

    Raises:
        MSizeAnalysisError: 自校验失败、遇到未建模 opcode、或不动点未收敛。
    """
    blocks = list(evm_blocks)
    if not blocks:
        raise MSizeAnalysisError("空的 EVM IR 块序列")

    mismatches: Tuple[StackEffectMismatch, ...] = ()
    if validate_stack:
        mismatches = validate_stack_effects(blocks)
        if mismatches:
            raise MSizeAnalysisError(
                "抽象值栈自校验失败：Σ(per-op delta) 与 Go 导出的 stack_depth 不符 "
                f"（{len(mismatches)} 块），前几处：{mismatches[:5]}"
            )

    graph = _build_return_aware_cfg(blocks)
    by_pc, succs = graph.by_pc, graph.succs
    push_map = {b.pc: _pads_pushed(b, graph.pads) for b in blocks}

    # (pc, 影子栈) -> 块入口抽象状态
    store: Dict[Tuple[int, Tuple[int, ...]], _AbstractState] = {}
    worklist: List[Tuple[int, Tuple[int, ...]]] = []
    resolution: Counter = Counter()

    entry_key = (graph.entry, ())
    store[entry_key] = _AbstractState((), {}, frozenset({0}), 0, 0)
    worklist.append(entry_key)

    iterations = 0
    while worklist and iterations < iteration_budget:
        key = worklist.pop()
        iterations += 1
        pc, ctx = key
        state = store[key]
        block = by_pc.get(pc)
        if block is None:
            continue

        out = _transfer_block(
            block, state, track_constant_memory=track_constant_memory
        )

        shadow = ctx + push_map[pc]
        if len(shadow) > SHADOW_STACK_CAP:
            shadow = shadow[-SHADOW_STACK_CAP:]

        edges: List[Tuple[int, Tuple[int, ...]]] = []
        if not context_sensitive:
            # 保守对照：返回点连回所有可能 caller，影子栈恒空。
            shadow = ()
            if pc in graph.ret_points:
                resolution["unresolved"] += 1
                edges.extend((t, ()) for t in graph.ret_points[pc])
            else:
                edges.extend((s, ()) for s in succs.get(pc, ()))
        elif pc in graph.ret_points:
            targets = graph.ret_points[pc]
            address = _returned_address(block, state)
            if not is_unknown(address) and address in targets:
                resolution["by_abstract_stack"] += 1
                edges.append((address, shadow[:-1] if shadow else shadow))
            elif shadow and shadow[-1] in targets:
                resolution["by_shadow_stack"] += 1
                edges.append((shadow[-1], shadow[:-1]))
            else:
                # 兜底：连回所有可能返回点。方案 §3.2 记过——保守回退没有优雅降级，
                # 一旦大面积发生影子栈就错位、假环复活；这里的计数必须保持极小。
                resolution["unresolved"] += 1
                rest = shadow[:-1] if shadow else shadow
                edges.extend((t, rest) for t in targets)
        else:
            edges.extend((s, shadow) for s in succs.get(pc, ()))

        for target_pc, target_ctx in edges:
            if target_pc not in by_pc:
                continue
            target_key = (target_pc, target_ctx)
            previous = store.get(target_key)
            merged = out if previous is None else _join_states(previous, out)
            if previous is None or merged.key() != previous.key():
                store[target_key] = merged
                worklist.append(target_key)

    if worklist:
        raise MSizeAnalysisError(
            f"MSize 抽象解释未在 {iteration_budget} 次迭代内收敛"
            f"（剩余 worklist {len(worklist)}）；部分结果不可信，拒绝返回"
        )

    return _summarize(blocks, store, iterations, resolution, mismatches)


def _summarize(
    blocks: Sequence[EVMBlock],
    store: Mapping[Tuple[int, Tuple[int, ...]], _AbstractState],
    iterations: int,
    resolution: Mapping[str, int],
    mismatches: Tuple[StackEffectMismatch, ...],
) -> MSizeAbstraction:
    """把 ``(pc, ctx)`` 粒度的不动点汇总到 pc 粒度。

    块级 lockstep 的定理按 pc 建（同一个块在不同调用上下文下是同一份 codegen），
    所以这里必须把所有 ctx join 掉——一个块只要在某条上下文里 ⊤，它整体就是 ⊤。
    """
    msize: Dict[int, MSizeValue] = {}
    lower: Dict[int, int] = {}
    upper: Dict[int, int] = {}
    sources: Dict[int, FrozenSet[TopSource]] = {}
    fmp_candidates: Dict[int, Set[Optional[int]]] = {}

    for (pc, _ctx), state in store.items():
        state_src = state.src if state.mset is TOP else frozenset()
        if pc in msize:
            current = msize[pc]
            if current is TOP or state.mset is TOP:
                msize[pc] = TOP
            else:
                union = current | state.mset
                msize[pc] = TOP if len(union) > VALUE_SET_CAP else union
            lower[pc] = min(lower[pc], state.lo)
            upper[pc] = max(upper[pc], state.hi)
            sources[pc] = sources[pc] | state_src
        else:
            msize[pc] = state.mset
            lower[pc] = state.lo
            upper[pc] = state.hi
            sources[pc] = state_src
        fmp_candidates.setdefault(pc, set()).add(
            state.mem.get(FREE_MEMORY_POINTER_SLOT)
        )

    fmp: Dict[int, FmpValue] = {}
    for pc, candidates in fmp_candidates.items():
        if len(candidates) == 1:
            only = next(iter(candidates))
            fmp[pc] = TOP if only is None else only
        else:
            fmp[pc] = TOP

    top_pcs = [pc for pc, value in msize.items() if value is TOP]
    top_sources: Dict[int, Tuple[TopSource, ...]] = {
        pc: tuple(sorted(sources[pc])) for pc in top_pcs
    }

    site_counts: Counter = Counter()
    inherited = self_produced = unattributed = 0
    for pc in top_pcs:
        sites = top_sources[pc]
        for site in sites:
            site_counts[site] += 1
        if not sites:
            unattributed += 1
        elif all(site.block_pc != pc for site in sites):
            inherited += 1
        else:
            self_produced += 1

    histogram: Counter = Counter()
    unique = small = medium = 0
    for value in msize.values():
        if value is TOP:
            continue
        if len(value) == 1:
            unique += 1
            histogram[next(iter(value))] += 1
        elif len(value) <= 4:
            small += 1
        else:
            medium += 1

    reachable = len(msize)
    stats = MSizeStats(
        contract_blocks=len(blocks),
        reachable_blocks=reachable,
        states=len(store),
        iterations=iterations,
        unique_blocks=unique,
        unique_ratio=unique / reachable if reachable else 0.0,
        small_set_blocks=small,
        medium_set_blocks=medium,
        top_blocks=len(top_pcs),
        top_ratio=len(top_pcs) / reachable if reachable else 0.0,
        unique_value_histogram=dict(histogram),
        fmp_unique_blocks=sum(1 for v in fmp.values() if v is not TOP),
        inherited_top_blocks=inherited,
        self_top_blocks=self_produced,
        unattributed_top_blocks=unattributed,
        top_source_sites=dict(site_counts),
        return_edge_resolution=dict(resolution),
        stack_effect_mismatches=mismatches,
    )
    return MSizeAbstraction(
        msize=msize,
        fmp=fmp,
        lower_bounds=lower,
        upper_bounds=upper,
        top_sources=top_sources,
        stats=stats,
    )
