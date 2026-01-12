"""
CFG 数据结构（参考 mythril）。

定义控制流图的节点、边和图结构。
"""

from __future__ import annotations

from typing import List, Dict, Tuple, Optional, TYPE_CHECKING
from enum import Enum
from dataclasses import dataclass, field
from z3 import BoolRef

from .models import EVMBlock, EvmOperator

# 前向引用，避免循环导入
if TYPE_CHECKING:
    from .cfg_state import GlobalState


class EdgeType(Enum):
    """边的类型。"""
    UNCONDITIONAL = "unconditional"       # 无条件跳转（JUMP）
    CONDITIONAL_TRUE = "conditional_true"  # 条件跳转条件为真（JUMPI taken）
    CONDITIONAL_FALSE = "conditional_false"  # 条件跳转条件为假（JUMPI not taken）
    CONDITIONAL = "conditional"           # 条件跳转（通用，向后兼容）
    FALLTHROUGH = "fallthrough"           # 顺序执行
    CALL = "call"                         # 函数调用（预留）
    RETURN = "return"                     # 函数返回（预留）


@dataclass
class CFGEdge:
    """CFG 中的边。

    连接两个节点，包含边类型、条件和源操作。
    """
    node_from: int  # 起始节点的 PC
    node_to: int    # 目标节点的 PC
    edge_type: EdgeType
    condition: Optional[BoolRef] = None  # 条件分支的约束条件
    source_operation: Optional['EvmOperator'] = None  # 产生这条边的源操作

    def __repr__(self):
        cond_str = f" [{self.condition}]" if self.condition else ""
        src_str = f" ({self.source_operation.kind})" if self.source_operation else ""
        return f"Edge({self.node_from} -> {self.node_to}, {self.edge_type.value}{cond_str}{src_str})"


@dataclass
class CFGNode:
    """CFG 中的节点。

    对应一个 EVM 块，存储到达此节点的状态列表。
    """
    block: EVMBlock
    states: List[GlobalState] = field(default_factory=list)  # 使用 GlobalState 而非 SMTState
    incoming_edges: List[CFGEdge] = field(default_factory=list)
    outgoing_edges: List[CFGEdge] = field(default_factory=list)

    @property
    def pc(self) -> int:
        """获取节点的 PC（块地址）。"""
        return self.block.pc

    def add_incoming_edge(self, edge: CFGEdge):
        """添加入边。"""
        self.incoming_edges.append(edge)

    def add_outgoing_edge(self, edge: CFGEdge):
        """添加出边。"""
        self.outgoing_edges.append(edge)

    def __repr__(self):
        return f"Node(pc={self.pc}, states={len(self.states)}, in={len(self.incoming_edges)}, out={len(self.outgoing_edges)})"


class DynamicCFG:
    """动态构建的控制流图。

    参考 mythril 的设计，在符号执行过程中动态构建 CFG。
    """

    def __init__(self, blocks: List[EVMBlock]):
        """初始化动态 CFG。

        Args:
            blocks: 所有 EVM 块列表
        """
        self.blocks = blocks
        self.blocks_by_pc: Dict[int, EVMBlock] = {block.pc: block for block in blocks}
        self.nodes: Dict[int, CFGNode] = {}  # pc -> CFGNode
        self.edges: List[CFGEdge] = []

        # 确保所有块都有对应的节点
        for block in blocks:
            self.get_or_create_node(block.pc)

    def get_or_create_node(self, pc: int) -> CFGNode:
        """获取或创建节点。

        Args:
            pc: 块的 PC

        Returns:
            对应的 CFGNode
        """
        if pc not in self.nodes:
            block = self.blocks_by_pc.get(pc)
            if block is None:
                raise ValueError(f"Block not found for pc={pc}")
            self.nodes[pc] = CFGNode(block=block)
        return self.nodes[pc]

    def add_edge(self, from_pc: int, to_pc: int, edge_type: EdgeType,
                 condition: Optional[BoolRef] = None,
                 source_operation: Optional[EvmOperator] = None) -> CFGEdge:
        """添加一条边。

        Args:
            from_pc: 起始节点 PC
            to_pc: 目标节点 PC
            edge_type: 边类型
            condition: 可选的条件约束
            source_operation: 产生这条边的源操作（可选）

        Returns:
            创建的 CFGEdge
        """
        from_node = self.get_or_create_node(from_pc)
        to_node = self.get_or_create_node(to_pc)

        edge = CFGEdge(
            node_from=from_pc,
            node_to=to_pc,
            edge_type=edge_type,
            condition=condition,
            source_operation=source_operation
        )

        self.edges.append(edge)
        from_node.add_outgoing_edge(edge)
        to_node.add_incoming_edge(edge)

        return edge

    def get_node(self, pc: int) -> Optional[CFGNode]:
        """获取指定 PC 的节点。

        Args:
            pc: 块的 PC

        Returns:
            CFGNode 或 None
        """
        return self.nodes.get(pc)

    def get_successors(self, pc: int) -> List[Tuple[CFGNode, Optional[BoolRef]]]:
        """获取节点的后继节点列表。

        Args:
            pc: 当前节点 PC

        Returns:
            (successor_node, condition) 元组列表
        """
        node = self.get_node(pc)
        if node is None:
            return []

        successors = []
        for edge in node.outgoing_edges:
            succ_node = self.get_node(edge.node_to)
            if succ_node:
                successors.append((succ_node, edge.condition))
        return successors

    def __repr__(self):
        return f"DynamicCFG(nodes={len(self.nodes)}, edges={len(self.edges)})"

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
            >>> cfg.visualize("evm_cfg.dot")
            >>> dot_content = cfg.visualize(show_constraints=False)
        """
        from visualization.cfg_visualizer import CFGVisualizer

        visualizer = CFGVisualizer(self, cfg_type="evm")
        dot_content = visualizer.generate_dot(**kwargs)

        if output_path:
            visualizer.save_to_file(output_path, **kwargs)

        return dot_content
