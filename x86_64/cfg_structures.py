"""
x86-64 CFG 数据结构（参考 evm_ir）。

定义控制流图的节点、边和图结构。
"""

from __future__ import annotations

from typing import List, Dict, Tuple, Optional, Set, TYPE_CHECKING
from enum import Enum
from dataclasses import dataclass, field
from z3 import BoolRef

from .models import X86Block, X86Instruction

# 前向引用，避免循环导入
if TYPE_CHECKING:
    from .cfg_state import X86GlobalState


class X86EdgeType(Enum):
    """x86-64 边的类型。

    根据编译器实现（go-hpc-evm/evm/aot/impl_amd64.go）：
    - 无间接跳转（所有跳转目标都是静态确定的）
    - 无 CALL 指令（编译器不生成 CALL）
    - 只有 JMP、Jcc（JE/JNE/JB/JAE/JL/JGE/JLE/JG）和 RET
    """

    UNCONDITIONAL = "unconditional"       # 无条件跳转（JMP）
    CONDITIONAL_TRUE = "conditional_true"  # 条件跳转条件为真（Jcc taken）
    CONDITIONAL_FALSE = "conditional_false"  # 条件跳转条件为假（Jcc not taken）
    FALLTHROUGH = "fallthrough"           # 顺序执行
    # 注：以下类型为预留，当前编译器不生成
    CALL = "call"                         # 函数调用（预留）
    RETURN = "return"                     # 函数返回（RET）


@dataclass
class X86CFGEdge:
    """x86-64 CFG 中的边。

    连接两个节点，包含边类型、条件和源指令。
    """
    node_from: int  # 起始节点的地址
    node_to: int    # 目标节点的地址
    edge_type: X86EdgeType
    condition: Optional[BoolRef] = None  # 条件分支的约束条件
    source_instruction: Optional[X86Instruction] = None  # 产生这条边的源指令

    def __repr__(self):
        cond_str = f" [{self.condition}]" if self.condition else ""
        src_str = f" ({self.source_instruction.mnemonic})" if self.source_instruction else ""
        return f"X86Edge(0x{self.node_from:x} -> 0x{self.node_to:x}, {self.edge_type.value}{cond_str}{src_str})"


@dataclass
class X86CFGNode:
    """x86-64 CFG 中的节点。

    对应一个 X86Block，存储到达此节点的状态列表。
    """
    block: X86Block
    states: List[X86GlobalState] = field(default_factory=list)
    incoming_edges: List[X86CFGEdge] = field(default_factory=list)
    outgoing_edges: List[X86CFGEdge] = field(default_factory=list)

    @property
    def address(self) -> int:
        """获取节点的地址（块起始地址）。"""
        return self.block.start_addr

    def add_incoming_edge(self, edge: X86CFGEdge):
        """添加入边。"""
        self.incoming_edges.append(edge)

    def add_outgoing_edge(self, edge: X86CFGEdge):
        """添加出边。"""
        self.outgoing_edges.append(edge)

    def __repr__(self):
        return f"X86Node(0x{self.address:x}, states={len(self.states)}, in={len(self.incoming_edges)}, out={len(self.outgoing_edges)})"


class X86DynamicCFG:
    """动态构建的 x86-64 控制流图。

    参考 evm_ir 的设计，在符号执行过程中动态构建 CFG。
    """

    def __init__(self, blocks: List[X86Block]):
        """初始化动态 CFG。

        Args:
            blocks: 所有 x86-64 块列表
        """
        self.blocks = blocks
        self.blocks_by_addr: Dict[int, X86Block] = {block.start_addr: block for block in blocks}
        self.nodes: Dict[int, X86CFGNode] = {}  # addr -> X86CFGNode
        self.edges: List[X86CFGEdge] = []

        # 确保所有块都有对应的节点
        for block in blocks:
            self.get_or_create_node(block.start_addr)

    def get_or_create_node(self, addr: int) -> X86CFGNode:
        """获取或创建节点。

        Args:
            addr: 块的起始地址

        Returns:
            对应的 X86CFGNode

        Raises:
            ValueError: 如果地址对应的块不存在
        """
        if addr not in self.nodes:
            block = self.blocks_by_addr.get(addr)
            if block is None:
                raise ValueError(f"Block not found for addr=0x{addr:x}")
            self.nodes[addr] = X86CFGNode(block=block)
        return self.nodes[addr]

    def add_edge(self, from_addr: int, to_addr: int, edge_type: X86EdgeType,
                 condition: Optional[BoolRef] = None,
                 source_instruction: Optional[X86Instruction] = None) -> X86CFGEdge:
        """添加一条边。

        Args:
            from_addr: 起始节点地址
            to_addr: 目标节点地址
            edge_type: 边类型
            condition: 可选的条件约束
            source_instruction: 产生这条边的源指令（可选）

        Returns:
            创建的 X86CFGEdge
        """
        from_node = self.get_or_create_node(from_addr)
        to_node = self.get_or_create_node(to_addr)

        edge = X86CFGEdge(
            node_from=from_addr,
            node_to=to_addr,
            edge_type=edge_type,
            condition=condition,
            source_instruction=source_instruction
        )

        self.edges.append(edge)
        from_node.add_outgoing_edge(edge)
        to_node.add_incoming_edge(edge)

        return edge

    def get_node(self, addr: int) -> Optional[X86CFGNode]:
        """获取指定地址的节点。

        Args:
            addr: 块的起始地址

        Returns:
            X86CFGNode 或 None
        """
        return self.nodes.get(addr)

    def get_successors(self, addr: int) -> List[Tuple[X86CFGNode, Optional[BoolRef]]]:
        """获取节点的后继节点列表。

        Args:
            addr: 当前节点地址

        Returns:
            (successor_node, condition) 元组列表
        """
        node = self.get_node(addr)
        if node is None:
            return []

        successors = []
        for edge in node.outgoing_edges:
            succ_node = self.get_node(edge.node_to)
            if succ_node:
                successors.append((succ_node, edge.condition))
        return successors

    def get_predecessors(self, addr: int) -> List[Tuple[X86CFGNode, Optional[BoolRef]]]:
        """获取节点的前驱节点列表。

        Args:
            addr: 当前节点地址

        Returns:
            (predecessor_node, condition) 元组列表
        """
        node = self.get_node(addr)
        if node is None:
            return []

        predecessors = []
        for edge in node.incoming_edges:
            pred_node = self.get_node(edge.node_from)
            if pred_node:
                predecessors.append((pred_node, edge.condition))
        return predecessors

    def detect_loop_headers(self) -> Set[int]:
        """检测循环头（有多个入边的块）。

        Returns:
            循环头地址集合

        Note:
            这是循环检测的辅助方法，用于未来的循环检测实现。
        """
        loop_headers = set()
        for addr, node in self.nodes.items():
            # 检查是否有多个入边（潜在循环头）
            if len(node.incoming_edges) > 1:
                # 检查是否有回边（来自后面地址的边）
                for edge in node.incoming_edges:
                    if edge.node_from > addr:  # 回边
                        loop_headers.add(addr)
                        break
        return loop_headers

    def __repr__(self):
        return f"X86DynamicCFG(nodes={len(self.nodes)}, edges={len(self.edges)})"

    def visualize(self, output_path: str | None = None, **kwargs) -> str:
        """可视化 CFG。

        生成 Graphviz DOT 格式的控制流图可视化。

        Args:
            output_path: 可选的输出文件路径（.dot 文件）
            **kwargs: 传递给可视化器的参数
                - title: 图标题
                - show_constraints: 是否显示约束条件（默认 True）
                - show_instructions: 是否显示指令列表（默认 True）
                - show_states: 是否显示状态数量（默认 True）
                - compact: 紧凑模式（默认 False）

        Returns:
            DOT 格式字符串

        Example:
            >>> cfg.visualize("x86_cfg.dot")
            >>> dot_content = cfg.visualize(show_constraints=False)
        """
        from visualization.cfg_visualizer import CFGVisualizer

        visualizer = CFGVisualizer(self, cfg_type="x86")
        dot_content = visualizer.generate_dot(**kwargs)

        if output_path:
            visualizer.save_to_file(output_path, **kwargs)

        return dot_content
