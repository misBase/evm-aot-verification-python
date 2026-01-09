"""
CFG 可视化核心模块。

提供通用的控制流图可视化功能，使用 Graphviz DOT 格式。
支持 EVM 和 x86-64 CFG 通过 Protocol 接口。
"""

from __future__ import annotations

from typing import Protocol, List, Dict, Any, Optional, Tuple, Set
from enum import Enum
from dataclasses import dataclass
from z3 import BoolRef


class CFGProtocol(Protocol):
    """CFG 抽象协议，支持 EVM 和 x86-64 CFG。

    任何实现此协议的 CFG 都可以被可视化。
    """

    @property
    def nodes(self) -> Dict[int, Any]:
        """节点字典: address/pc -> node"""
        ...

    @property
    def edges(self) -> List[Any]:
        """边列表"""
        ...

    def get_node(self, addr: int) -> Optional[Any]:
        """获取指定地址的节点"""
        ...


class NodeProtocol(Protocol):
    """节点抽象协议。

    EVM CFGNode 和 x86-64 X86CFGNode 都符合此协议。
    """

    @property
    def address(self) -> int:
        """节点地址（EVM 为 pc，x86-64 为 address）"""
        ...

    @property
    def states(self) -> List[Any]:
        """到达此节点的状态列表"""
        ...

    @property
    def incoming_edges(self) -> List[Any]:
        """入边列表"""
        ...

    @property
    def outgoing_edges(self) -> List[Any]:
        """出边列表"""
        ...

    @property
    def block(self) -> Any:
        """关联的基本块"""
        ...


class EdgeProtocol(Protocol):
    """边抽象协议。

    EVM CFGEdge 和 x86-64 X86CFGEdge 都符合此协议。
    """

    @property
    def node_from(self) -> int:
        """起始节点地址"""
        ...

    @property
    def node_to(self) -> int:
        """目标节点地址"""
        ...

    @property
    def edge_type(self) -> Enum:
        """边类型枚举"""
        ...

    @property
    def condition(self) -> Optional[BoolRef]:
        """条件约束（可选）"""
        ...


@dataclass
class DOTStyle:
    """可视化样式配置。

    可以自定义颜色、形状、字体等样式属性。
    """

    # 节点样式
    NODE_SHAPE: str = "box"
    NODE_STYLE: str = "rounded,filled"
    NODE_FONTNAME: str = "Courier"
    NODE_FONTSIZE: str = "10"

    # 颜色方案
    COLOR_NORMAL: str = "#ffffff"  # 普通节点
    COLOR_ENTRY: str = "#90EE90"  # 入口节点（浅绿）
    COLOR_EXIT: str = "#FFB6C1"  # 出口节点（浅粉红）
    COLOR_LOOP_HEADER: str = "#FFD700"  # 循环节点（金黄）
    COLOR_CONDITIONAL: str = "#87CEEB"  # 条件分支节点（天蓝）

    # 边样式
    EDGE_STYLE_UNCONDITIONAL: str = "solid"
    EDGE_STYLE_CONDITIONAL: str = "dashed"
    EDGE_STYLE_FALLTHROUGH: str = "bold,solid"

    # 边颜色
    EDGE_COLOR_UNCONDITIONAL: str = "#000000"  # 黑色
    EDGE_COLOR_CONDITIONAL_TRUE: str = "#228B22"  # 森林绿
    EDGE_COLOR_CONDITIONAL_FALSE: str = "#DC143C"  # 深红
    EDGE_COLOR_FALLTHROUGH: str = "#4169E1"  # 皇家蓝

    # 约束显示
    MAX_CONSTRAINT_LENGTH: int = 50
    CONSTRAINT_ELLIPSIS: str = "..."

    # 布局
    RANKDIR: str = "TB"  # TB=从上到下, LR=从左到右


class DOTGenerator:
    """Graphviz DOT 格式生成器。

    将 CFG 结构转换为 Graphviz DOT 格式字符串。
    """

    def __init__(self, cfg: CFGProtocol, style: DOTStyle | None = None):
        """初始化生成器。

        Args:
            cfg: 符合 CFGProtocol 的控制流图
            style: 可选的样式配置
        """
        self.cfg = cfg
        self.style = style or DOTStyle()
        self.node_labels: Dict[int, str] = {}
        self.edge_labels: Dict[Tuple[int, int], str] = {}

    def generate(
        self,
        title: str = "Control Flow Graph",
        show_constraints: bool = True,
        show_instructions: bool = True,
        show_states: bool = True,
        compact: bool = False,
    ) -> str:
        """生成完整的 DOT 文件内容。

        Args:
            title: 图标题
            show_constraints: 是否显示约束条件
            show_instructions: 是否显示指令列表
            show_states: 是否显示状态数量
            compact: 紧凑模式（减少显示信息）

        Returns:
            DOT 格式字符串
        """
        lines = []
        lines.extend(self._generate_header(title))
        lines.extend(self._generate_nodes(show_instructions, show_states, compact))
        lines.extend(self._generate_edges(show_constraints, compact))
        lines.extend(self._generate_footer())
        return "\n".join(lines)

    def _generate_header(self, title: str) -> List[str]:
        """生成 DOT 文件头部。"""
        return [
            "digraph CFG {",
            f'    label="{title}";',
            "    labelloc=\"t\";",
            "    fontsize=16;",
            "    fontname=\"Arial\";",
            f"    rankdir={self.style.RANKDIR};",
            "    node [shape=box, style=rounded];",
            "    edge [fontsize=9];",
            "",
        ]

    def _generate_footer(self) -> List[str]:
        """生成 DOT 文件尾部。"""
        return ["}"]

    def _get_node_color(self, node: NodeProtocol) -> str:
        """确定节点颜色。

        根据节点特征（入口、出口、循环头、条件分支）返回对应颜色。
        """
        # 检查是否为循环头
        if hasattr(self.cfg, "detect_loop_headers"):
            loop_headers = self.cfg.detect_loop_headers()
            if node.address in loop_headers:
                return self.style.COLOR_LOOP_HEADER

        # 检查是否为入口节点（无入边）
        if len(node.incoming_edges) == 0:
            return self.style.COLOR_ENTRY

        # 检查是否为出口节点（无出边）
        if len(node.outgoing_edges) == 0:
            return self.style.COLOR_EXIT

        # 检查是否为条件分支节点
        for edge in node.outgoing_edges:
            if hasattr(edge.edge_type, "value"):
                edge_type = edge.edge_type.value.lower()
                if "conditional" in edge_type:
                    return self.style.COLOR_CONDITIONAL

        return self.style.COLOR_NORMAL

    def _format_instructions(self, node: NodeProtocol, compact: bool) -> str:
        """格式化指令列表。

        从节点的基本块中提取指令并格式化为字符串。
        """
        if not hasattr(node, "block") or node.block is None:
            return ""

        block = node.block
        # EVM 使用 operations，x86-64 使用 instructions
        items = getattr(block, "instructions", None) or getattr(block, "operations", [])

        if not items:
            return ""

        if compact:
            # 紧凑模式：只显示数量
            return f"[{len(items)} instrs]"

        # 完整模式：显示所有指令
        lines = []
        max_instructions = 10  # 最多显示 10 条

        for item in items[:max_instructions]:
            if hasattr(item, "mnemonic"):
                # x86-64 指令
                mnemonic = item.mnemonic
                op_str = getattr(item, "op_str", "")
                addr_str = f"0x{item.addr:x}" if hasattr(item, "addr") else ""
                line = f"    {addr_str} {mnemonic} {op_str}".strip()
                lines.append(line)
            elif hasattr(item, "kind"):
                # EVM 操作
                kind = item.kind
                pc_str = f"pc={item.pc}" if hasattr(item, "pc") else ""
                imm_str = ""
                if hasattr(item, "immediate") and item.immediate is not None:
                    imm_str = f"imm={item.immediate}"
                line = f"    {pc_str} {kind} {imm_str}".strip()
                lines.append(line)

        if len(items) > max_instructions:
            lines.append(f"    ... ({len(items) - max_instructions} more)")

        return "\\n".join(lines) if lines else ""

    def _parse_flag_condition(self, cond_str: str) -> str:
        """解析标志位条件为可读格式。

        将 Z3 BoolRef 字符串转换为标志位条件，如 "CF=1", "ZF=0"。

        Args:
            cond_str: Z3 BoolRef 的字符串表示

        Returns:
            可读的标志位条件字符串，如果无法解析则返回原始字符串
        """
        import re

        # 模式匹配：
        # "1 == CF" -> "CF=1"
        # "0 == ZF" -> "ZF=0"
        # "Not(1 == CF)" -> "CF=0"
        # "Not(0 == ZF)" -> "ZF=1"

        # 首先尝试解析 Not(模式)
        not_pattern = r'Not\((\d+)\s*==\s*([A-Z]+)\)'
        not_match = re.search(not_pattern, cond_str)
        if not_match:
            value = int(not_match.group(1))
            flag = not_match.group(2)
            # Not 反转值
            return f"{flag}={1 - value}"

        # 然后尝试解析直接相等模式
        eq_pattern = r'(\d+)\s*==\s*([A-Z]+)'
        eq_match = re.search(eq_pattern, cond_str)
        if eq_match:
            value = eq_match.group(1)
            flag = eq_match.group(2)
            return f"{flag}={value}"

        # 如果都无法匹配，返回原始字符串（可能已经过格式化或包含其他表达式）
        return cond_str

    def _format_constraint(self, condition: BoolRef | None, compact: bool) -> str:
        """格式化约束条件。

        将 Z3 BoolRef 转换为可读的标志位条件。
        """
        if condition is None:
            return ""

        cond_str = str(condition)

        # 尝试解析为标志位条件
        flag_condition = self._parse_flag_condition(cond_str)

        # 如果解析后的字符串与原始不同，说明成功解析
        if flag_condition != cond_str:
            return flag_condition

        # 否则使用原始格式化逻辑
        if compact and len(cond_str) > self.style.MAX_CONSTRAINT_LENGTH:
            return cond_str[: self.style.MAX_CONSTRAINT_LENGTH] + self.style.CONSTRAINT_ELLIPSIS
        return cond_str

    def _get_edge_style_and_color(self, edge: EdgeProtocol) -> Tuple[str, str]:
        """确定边的样式和颜色。

        根据边类型返回对应的样式（solid/dashed/bold）和颜色。
        """
        edge_type = (
            edge.edge_type.value if hasattr(edge.edge_type, "value") else str(edge.edge_type)
        ).lower()

        if "unconditional" in edge_type:
            return self.style.EDGE_STYLE_UNCONDITIONAL, self.style.EDGE_COLOR_UNCONDITIONAL
        elif "conditional_true" in edge_type or "conditional" in edge_type:
            return self.style.EDGE_STYLE_CONDITIONAL, self.style.EDGE_COLOR_CONDITIONAL_TRUE
        elif "conditional_false" in edge_type:
            return self.style.EDGE_STYLE_CONDITIONAL, self.style.EDGE_COLOR_CONDITIONAL_FALSE
        elif "fallthrough" in edge_type:
            return self.style.EDGE_STYLE_FALLTHROUGH, self.style.EDGE_COLOR_FALLTHROUGH
        else:
            return "solid", "#000000"

    def _generate_nodes(
        self, show_instructions: bool, show_states: bool, compact: bool
    ) -> List[str]:
        """生成所有节点定义。"""
        lines = []

        for addr, node in self.cfg.nodes.items():
            # 获取节点属性
            color = self._get_node_color(node)

            # 构建标签
            label_parts = []

            # 地址/PC - 统一使用十六进制显示
            if hasattr(node, "block") and hasattr(node.block, "start_addr"):
                # x86-64
                label_parts.append(f"0x{addr:x}")
            else:
                # EVM
                label_parts.append(f"PC={addr}")

            # 指令
            if show_instructions:
                instr_str = self._format_instructions(node, compact)
                if instr_str:
                    label_parts.append(instr_str)

            # 状态数量
            if show_states and hasattr(node, "states"):
                label_parts.append(f"States: {len(node.states)}")

            label = "\\n".join(label_parts)
            label = label.replace('"', '\\"')  # 转义引号

            # 生成节点定义
            lines.append(f"    node_{addr} [")
            lines.append(f'        label="{label}"')
            lines.append(f'        fillcolor="{color}"')
            lines.append(f'        shape={self.style.NODE_SHAPE}')
            lines.append(f'        style="{self.style.NODE_STYLE}"')
            lines.append(f'        fontname="{self.style.NODE_FONTNAME}"')
            lines.append(f'        fontsize={self.style.NODE_FONTSIZE}')
            lines.append("    ];")
            lines.append("")

        return lines

    def _generate_edges(self, show_constraints: bool, compact: bool) -> List[str]:
        """生成所有边定义。"""
        lines = []

        for edge in self.cfg.edges:
            from_addr = edge.node_from
            to_addr = edge.node_to

            # 获取边样式
            style, color = self._get_edge_style_and_color(edge)

            # 构建标签
            label = self._build_edge_label(edge, show_constraints, compact)
            label = label.replace('"', '\\"')  # 转义引号

            # 生成边定义
            lines.append(f"    node_{from_addr} -> node_{to_addr} [")
            lines.append(f'        label="{label}"')
            lines.append(f'        style="{style}"')
            lines.append(f'        color="{color}"')
            lines.append("    ];")

        return lines

    def _build_edge_label(self, edge: EdgeProtocol, show_constraints: bool, compact: bool) -> str:
        """构建边的标签。

        优先显示指令助记符和条件信息，如 "jb (CF=1)"。

        Args:
            edge: CFG 边
            show_constraints: 是否显示约束条件
            compact: 是否使用紧凑模式

        Returns:
            边标签字符串
        """
        # 检查是否有源指令信息
        source_insn = None
        if hasattr(edge, 'source_instruction'):
            source_insn = edge.source_instruction

        # 如果有源指令，优先显示指令助记符
        if source_insn is not None:
            mnemonic = source_insn.mnemonic if hasattr(source_insn, 'mnemonic') else None
            if mnemonic:
                mnemonic_lower = mnemonic.lower()

                # 对于条件跳转，显示助记符和条件
                if mnemonic_lower in ['jb', 'jae', 'je', 'jne', 'jl', 'jge', 'jle', 'jg']:
                    # 尝试获取条件描述
                    condition_desc = self._get_condition_description(edge, show_constraints, compact)
                    if condition_desc:
                        return f"{mnemonic} ({condition_desc})"
                    return mnemonic

                # 对于无条件跳转，只显示助记符
                elif mnemonic_lower == 'jmp':
                    return mnemonic

        # 尝试解析标志位条件（如果没有源指令）
        if show_constraints and hasattr(edge, 'condition') and edge.condition is not None:
            cond_str = self._format_constraint(edge.condition, compact)
            if cond_str and self._is_simple_flag_condition(cond_str):
                # 如果是简单的标志位条件（如 CF=1），直接显示
                return cond_str

        # 如果没有条件，显示边类型
        edge_type_str = (
            edge.edge_type.value if hasattr(edge.edge_type, "value") else str(edge.edge_type)
        )
        return edge_type_str

    def _get_condition_description(self, edge: EdgeProtocol, show_constraints: bool, compact: bool) -> str:
        """获取条件的描述。

        根据指令类型推断标志位条件，如 "CF=1"。

        Args:
            edge: CFG 边
            show_constraints: 是否显示约束条件
            compact: 是否使用紧凑模式

        Returns:
            条件描述字符串，如果无法解析则返回空字符串
        """
        if not show_constraints:
            return ""

        # 检查是否有源指令
        source_insn = None
        if hasattr(edge, 'source_instruction'):
            source_insn = edge.source_instruction

        if source_insn is None:
            return ""

        mnemonic = source_insn.mnemonic if hasattr(source_insn, 'mnemonic') else None
        if not mnemonic:
            return ""

        # 根据指令类型和边类型推断标志位条件
        mnemonic_lower = mnemonic.lower()
        edge_type = edge.edge_type if hasattr(edge, 'edge_type') else None

        # 只处理条件跳转指令
        if mnemonic_lower not in ['jb', 'jae', 'je', 'jne', 'jl', 'jge', 'jle', 'jg']:
            return ""

        # 获取边类型字符串
        edge_type_str = edge_type.value if hasattr(edge_type, 'value') else str(edge_type)

        # 根据指令和边类型确定标志位条件
        # conditional_true 表示条件为真时跳转，conditional_false 表示条件为假时跳转
        if edge_type_str == 'conditional_true':
            # 跳转分支（条件为真）
            return self._get_flag_for_jump_true(mnemonic_lower)
        elif edge_type_str == 'conditional_false':
            # Fallthrough 分支（条件为假）
            return self._get_flag_for_jump_false(mnemonic_lower)

        return ""

    def _get_flag_for_jump_true(self, mnemonic: str) -> str:
        """获取条件为真时的标志位值。

        Args:
            mnemonic: 指令助记符（小写）

        Returns:
            标志位条件，如 "CF=1"
        """
        # jb: CF=1 (无符号小于)
        # jae: CF=0 (无符号大于等于)
        # je: ZF=1 (等于)
        # jne: ZF=0 (不等于)
        # jl: SF!=OF (有符号小于)
        # jge: SF=OF (有符号大于等于)
        # jle: ZF=1 或 SF!=OF (有符号小于等于)
        # jg: ZF=0 且 SF=OF (有符号大于)
        flag_conditions = {
            'jb': 'CF=1',
            'jae': 'CF=0',
            'je': 'ZF=1',
            'jne': 'ZF=0',
            'jl': 'SF≠OF',
            'jge': 'SF=OF',
            'jle': 'ZF=1 or SF≠OF',
            'jg': 'ZF=0 & SF=OF',
        }
        return flag_conditions.get(mnemonic, '')

    def _get_flag_for_jump_false(self, mnemonic: str) -> str:
        """获取条件为假时的标志位值（fallthrough 分支）。

        Args:
            mnemonic: 指令助记符（小写）

        Returns:
            标志位条件，如 "CF=0"
        """
        # jb fallthrough: CF=0
        # jae fallthrough: CF=1
        # je fallthrough: ZF=0
        # jne fallthrough: ZF=1
        # jl fallthrough: SF=OF
        # jge fallthrough: SF≠OF
        # jle fallthrough: ZF=0 且 SF=OF
        # jg fallthrough: ZF=1 或 SF≠OF
        flag_conditions = {
            'jb': 'CF=0',
            'jae': 'CF=1',
            'je': 'ZF=0',
            'jne': 'ZF=1',
            'jl': 'SF=OF',
            'jge': 'SF≠OF',
            'jle': 'ZF=0 & SF=OF',
            'jg': 'ZF=1 or SF≠OF',
        }
        return flag_conditions.get(mnemonic, '')

    def _is_simple_flag_condition(self, cond_str: str) -> bool:
        """检查是否是简单的标志位条件。

        简单条件如 "CF=1", "ZF=0" 等，不包含复杂的表达式。

        Args:
            cond_str: 条件字符串

        Returns:
            如果是简单的标志位条件则返回 True
        """
        # 如果包含空格或特殊字符（除了 =），说明不是简单条件
        # 简单条件格式: FLAG=VALUE (如 CF=1, ZF=0)
        return '=' in cond_str and ' ' not in cond_str and not cond_str.startswith('(')


class CFGVisualizer:
    """CFG 可视化器主类。

    提供统一的接口来可视化 EVM 和 x86-64 CFG。

    用法示例:
        # EVM CFG
        from evm_ir.cfg import DynamicCFG
        visualizer = CFGVisualizer(evm_cfg, cfg_type="evm")
        dot_content = visualizer.generate_dot()
        visualizer.save_to_file("evm_cfg.dot")

        # x86-64 CFG
        from x86_64.cfg_structures import X86DynamicCFG
        visualizer = CFGVisualizer(x86_cfg, cfg_type="x86")
        visualizer.save_to_file("x86_cfg.dot")
    """

    def __init__(self, cfg: CFGProtocol, cfg_type: str = "auto"):
        """初始化可视化器。

        Args:
            cfg: 符合 CFGProtocol 的控制流图
            cfg_type: CFG 类型 ("evm", "x86", "auto")
        """
        self.cfg = cfg
        self.cfg_type = self._detect_cfg_type(cfg, cfg_type)
        self.generator = DOTGenerator(cfg)

    def _detect_cfg_type(self, cfg: CFGProtocol, cfg_type: str) -> str:
        """自动检测 CFG 类型。

        通过检查节点的块属性来判断是 EVM 还是 x86-64。
        """
        if cfg_type != "auto":
            return cfg_type

        # 检查第一个节点的特征
        for node in cfg.nodes.values():
            if hasattr(node, "block"):
                block = node.block
                if hasattr(block, "instructions"):
                    return "x86"
                elif hasattr(block, "operations"):
                    return "evm"

        return "unknown"

    def generate_dot(
        self,
        title: str | None = None,
        show_constraints: bool = True,
        show_instructions: bool = True,
        show_states: bool = True,
        compact: bool = False,
    ) -> str:
        """生成 DOT 格式内容。

        Args:
            title: 图标题
            show_constraints: 是否显示约束条件
            show_instructions: 是否显示指令列表
            show_states: 是否显示状态数量
            compact: 紧凑模式

        Returns:
            DOT 格式字符串
        """
        if title is None:
            title = f"{self.cfg_type.upper()} Control Flow Graph"

        return self.generator.generate(
            title=title,
            show_constraints=show_constraints,
            show_instructions=show_instructions,
            show_states=show_states,
            compact=compact,
        )

    def save_to_file(self, filepath: str, **kwargs) -> None:
        """保存 DOT 文件。

        Args:
            filepath: 输出文件路径
            **kwargs: 传递给 generate_dot 的参数
        """
        dot_content = self.generate_dot(**kwargs)

        with open(filepath, "w", encoding="utf-8") as f:
            f.write(dot_content)

    def render_png(self, output_path: str, **kwargs) -> None:
        """渲染为 PNG 图片（需要 graphviz 系统包）。

        Args:
            output_path: 输出 PNG 文件路径
            **kwargs: 传递给 generate_dot 的参数

        Raises:
            ImportError: 如果没有安装 graphviz Python 包
            RuntimeError: 如果 graphviz 命令行工具不可用
        """
        try:
            from graphviz import Source
        except ImportError as e:
            raise ImportError(
                "graphviz Python package is required. "
                "Install with: poetry add graphviz"
            ) from e

        dot_content = self.generate_dot(**kwargs)
        src = Source(dot_content)

        # 移除 .png 后缀，因为 render 会自动添加
        base_path = output_path
        if base_path.endswith(".png"):
            base_path = base_path[:-4]

        src.render(base_path, format="png", cleanup=True)

    def render_svg(self, output_path: str, **kwargs) -> None:
        """渲染为 SVG 图片（需要 graphviz 系统包）。

        Args:
            output_path: 输出 SVG 文件路径
            **kwargs: 传递给 generate_dot 的参数

        Raises:
            ImportError: 如果没有安装 graphviz Python 包
        """
        try:
            from graphviz import Source
        except ImportError as e:
            raise ImportError(
                "graphviz Python package is required. "
                "Install with: poetry add graphviz"
            ) from e

        dot_content = self.generate_dot(**kwargs)
        src = Source(dot_content)

        # 移除 .svg 后缀，因为 render 会自动添加
        base_path = output_path
        if base_path.endswith(".svg"):
            base_path = base_path[:-4]

        src.render(base_path, format="svg", cleanup=True)

    def get_statistics(self) -> Dict[str, Any]:
        """获取 CFG 统计信息。

        Returns:
            包含统计信息的字典，包括节点数、边数、边类型分布、状态总数、循环头等
        """
        stats: Dict[str, Any] = {
            "cfg_type": self.cfg_type,
            "num_nodes": len(self.cfg.nodes),
            "num_edges": len(self.cfg.edges),
        }

        # 统计边类型
        edge_types: Dict[str, int] = {}
        for edge in self.cfg.edges:
            edge_type = (
                edge.edge_type.value if hasattr(edge.edge_type, "value") else str(edge.edge_type)
            )
            edge_types[edge_type] = edge_types.get(edge_type, 0) + 1
        stats["edge_types"] = edge_types

        # 统计状态数量
        total_states = 0
        for node in self.cfg.nodes.values():
            if hasattr(node, "states"):
                total_states += len(node.states)
        stats["total_states"] = total_states

        # 检测循环
        if hasattr(self.cfg, "detect_loop_headers"):
            loop_headers = self.cfg.detect_loop_headers()
            stats["loop_headers"] = list(loop_headers)
            stats["num_loops"] = len(loop_headers)

        return stats
