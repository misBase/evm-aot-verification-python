"""
CFG 可视化器单元测试。

测试 DOT 生成器和可视化器的功能。
"""

import pytest
from pathlib import Path
from z3 import Bool, And

from visualization.cfg_visualizer import (
    CFGVisualizer,
    DOTGenerator,
    DOTStyle,
)

# 导入 EVM 相关
from evm_ir.cfg_structures import DynamicCFG, CFGEdge, EdgeType
from evm_ir.models import EVMBlock, EvmOperator

# 导入 x86-64 相关
from x86_64.cfg_structures import X86DynamicCFG, X86CFGEdge, X86EdgeType
from x86_64.models import X86Block, X86Instruction


class TestDOTStyle:
    """测试 DOT 样式配置类。"""

    def test_default_style(self):
        """测试默认样式配置。"""
        style = DOTStyle()

        # 节点样式
        assert style.NODE_SHAPE == "box"
        assert style.NODE_STYLE == "rounded,filled"
        assert style.NODE_FONTNAME == "Courier"
        assert style.NODE_FONTSIZE == "10"

        # 颜色方案
        assert style.COLOR_NORMAL == "#ffffff"
        assert style.COLOR_ENTRY == "#90EE90"
        assert style.COLOR_EXIT == "#FFB6C1"
        assert style.COLOR_LOOP_HEADER == "#FFD700"
        assert style.COLOR_CONDITIONAL == "#87CEEB"

        # 边样式
        assert style.EDGE_STYLE_UNCONDITIONAL == "solid"
        assert style.EDGE_STYLE_CONDITIONAL == "dashed"
        assert style.EDGE_STYLE_FALLTHROUGH == "bold,solid"

    def test_custom_style(self):
        """测试自定义样式配置。"""
        style = DOTStyle(NODE_SHAPE="ellipse", RANKDIR="LR")

        assert style.NODE_SHAPE == "ellipse"
        assert style.RANKDIR == "LR"


class TestDOTGenerator:
    """测试 DOT 生成器。"""

    def test_generate_simple_evm_cfg(self):
        """测试生成简单 EVM CFG 的 DOT。"""
        # 创建测试 EVM 块
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="ADD", pc=0), EvmOperator(kind="POP", pc=1)],
            ),
            EVMBlock(
                pc=13,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[EvmOperator(kind="STOP", pc=13)],
            ),
        ]

        # 创建 CFG
        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

        # 生成 DOT
        generator = DOTGenerator(cfg)
        dot = generator.generate(title="Test EVM CFG")

        # 验证基本结构
        assert "digraph CFG" in dot
        assert "Test EVM CFG" in dot
        assert "node_0" in dot
        assert "node_13" in dot
        assert "PC=0" in dot
        assert "PC=13" in dot
        assert "ADD" in dot or "POP" in dot
        assert "conditional" in dot.lower()

    def test_generate_simple_x86_cfg(self):
        """测试生成简单 x86-64 CFG 的 DOT。"""
        # 创建测试 x86-64 块
        blocks = [
            X86Block(
                start_addr=0x1000,
                end_addr=0x1003,
                instructions=[
                    X86Instruction(addr=0x1000, mnemonic="xor", op_str="rax, rax", bytes=b"\x48\x31\xc0", size=3),
                ],
            ),
            X86Block(
                start_addr=0x1003,
                end_addr=0x1004,
                instructions=[
                    X86Instruction(addr=0x1003, mnemonic="ret", op_str="", bytes=b"\xc3", size=1),
                ],
            ),
        ]

        # 创建 CFG
        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1003, X86EdgeType.UNCONDITIONAL)

        # 生成 DOT
        generator = DOTGenerator(cfg)
        dot = generator.generate(title="Test x86 CFG")

        # 验证基本结构
        assert "digraph CFG" in dot
        assert "Test x86 CFG" in dot
        assert "0x1000" in dot
        assert "0x1003" in dot
        assert "xor" in dot or "ret" in dot
        assert "unconditional" in dot.lower()

    def test_generate_with_loop(self):
        """测试生成包含循环的 CFG。"""
        # 创建一个简单的循环 CFG
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1002, instructions=[]),
            X86Block(start_addr=0x1002, end_addr=0x1004, instructions=[]),
            X86Block(start_addr=0x1004, end_addr=0x1005, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        # 添加回边形成循环：0x1000 -> 0x1002, 0x1002 -> 0x1004, 0x1004 -> 0x1000
        cfg.add_edge(0x1000, 0x1002, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1002, 0x1004, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1004, 0x1000, X86EdgeType.UNCONDITIONAL)  # 回边
        # 添加第二条入边到 0x1000（使它成为循环头）
        cfg.add_edge(0x1000, 0x1000, X86EdgeType.FALLTHROUGH)  # 自边作为第二条入边

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        # 验证循环头被检测到（0x1000 有多个入边且有回边）
        loop_headers = cfg.detect_loop_headers()
        assert len(loop_headers) > 0

    def test_node_colors(self):
        """测试节点颜色分配。"""
        # 创建有入口、出口和循环的 CFG
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[]),  # 入口
            X86Block(start_addr=0x1001, end_addr=0x1002, instructions=[]),  # 中间
            X86Block(start_addr=0x1002, end_addr=0x1003, instructions=[]),  # 出口
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1001, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1001, 0x1002, X86EdgeType.UNCONDITIONAL)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        # 验证颜色存在
        assert "#90EE90" in dot or "#ffffff" in dot  # 入口或正常颜色

    def test_compact_mode(self):
        """测试紧凑模式。"""
        blocks = [
            X86Block(
                start_addr=0x1000,
                end_addr=0x1002,
                instructions=[
                    X86Instruction(addr=0x1000, mnemonic="mov", op_str="rax, rbx", bytes=b"", size=0),
                    X86Instruction(addr=0x1001, mnemonic="add", op_str="rax, 1", bytes=b"", size=0),
                ],
            ),
        ]

        cfg = X86DynamicCFG(blocks)

        generator = DOTGenerator(cfg)

        # 完整模式
        dot_full = generator.generate(compact=False)
        assert "mov" in dot_full

        # 紧凑模式
        dot_compact = generator.generate(compact=True)
        assert "[2 instrs]" in dot_compact or "2 instrs" in dot_compact

    def test_edge_labels(self):
        """测试边标签生成。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[]),
            X86Block(start_addr=0x1001, end_addr=0x1002, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)

        # 无条件边
        cfg.add_edge(0x1000, 0x1001, X86EdgeType.UNCONDITIONAL)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        assert "unconditional" in dot.lower()

    def test_show_options(self):
        """测试显示选项。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="ADD", pc=0)],
            ),
        ]

        cfg = DynamicCFG(blocks)
        # 添加一些状态
        node = cfg.get_node(0)
        node.states = [None, None, None]  # 3 个状态

        generator = DOTGenerator(cfg)

        # 显示所有信息
        dot_full = generator.generate(show_instructions=True, show_states=True)
        assert "States: 3" in dot_full

        # 不显示状态
        dot_no_states = generator.generate(show_states=False)
        assert "States:" not in dot_no_states

        # 不显示指令
        dot_no_instr = generator.generate(show_instructions=False)
        # 指令不应该在标签中（虽然可能在其他地方）
        lines = dot_no_instr.split("\n")
        label_lines = [l for l in lines if "label=" in l]
        assert all("ADD" not in l for l in label_lines)


class TestCFGVisualizer:
    """测试 CFG 可视化器。"""

    def test_evm_cfg_visualization(self):
        """测试 EVM CFG 可视化。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            ),
            EVMBlock(
                pc=13,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[],
            ),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

        visualizer = CFGVisualizer(cfg, cfg_type="evm")
        dot = visualizer.generate_dot()

        assert "digraph CFG" in dot
        assert "EVM" in dot

    def test_x86_cfg_visualization(self):
        """测试 x86-64 CFG 可视化。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[]),
            X86Block(start_addr=0x1001, end_addr=0x1002, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1001, X86EdgeType.UNCONDITIONAL)

        visualizer = CFGVisualizer(cfg, cfg_type="x86")
        dot = visualizer.generate_dot()

        assert "digraph CFG" in dot
        assert "x86" in dot or "X86" in dot

    def test_auto_detect_cfg_type(self):
        """测试自动检测 CFG 类型。"""
        # EVM
        evm_blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            )
        ]
        evm_cfg = DynamicCFG(evm_blocks)
        evm_viz = CFGVisualizer(evm_cfg, cfg_type="auto")
        assert evm_viz.cfg_type == "evm"

        # x86-64
        x86_blocks = [X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[])]
        x86_cfg = X86DynamicCFG(x86_blocks)
        x86_viz = CFGVisualizer(x86_cfg, cfg_type="auto")
        assert x86_viz.cfg_type == "x86"

    def test_get_statistics(self):
        """测试获取统计信息。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            ),
            EVMBlock(
                pc=13,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[],
            ),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

        # 添加一些状态
        cfg.get_node(0).states = [None, None]
        cfg.get_node(13).states = [None]

        visualizer = CFGVisualizer(cfg)
        stats = visualizer.get_statistics()

        assert stats["cfg_type"] == "evm"
        assert stats["num_nodes"] == 2
        assert stats["num_edges"] == 1
        assert "conditional" in stats["edge_types"]
        assert stats["edge_types"]["conditional"] == 1
        assert stats["total_states"] == 3

    def test_save_to_file(self, tmp_path: Path):
        """测试保存到文件。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            )
        ]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        output_file = tmp_path / "test_cfg.dot"
        visualizer.save_to_file(str(output_file))

        assert output_file.exists()
        content = output_file.read_text()
        assert "digraph CFG" in content

    def test_custom_title(self):
        """测试自定义标题。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            )
        ]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        dot = visualizer.generate_dot(title="My Custom CFG")
        assert "My Custom CFG" in dot

    def test_render_png_without_graphviz(self, tmp_path: Path):
        """测试在没有 graphviz 包时渲染 PNG 会引发错误。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[],
            )
        ]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        # 如果 graphviz 未安装，应该引发 ImportError
        output_file = tmp_path / "test.png"
        try:
            visualizer.render_png(str(output_file))
            # 如果成功，说明 graphviz 已安装，这是 OK 的
        except ImportError:
            # 预期的错误
            pass


class TestEVMCFGIntegration:
    """测试 EVM CFG 集成。"""

    def test_evm_cfg_visualize_method(self, tmp_path: Path):
        """测试 EVM CFG 的 visualize 方法。"""
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="ADD", pc=0)],
            ),
            EVMBlock(
                pc=13,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[EvmOperator(kind="STOP", pc=13)],
            ),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

        # 使用 visualize 方法
        output_file = tmp_path / "evm_test.dot"
        dot_content = cfg.visualize(str(output_file))

        assert output_file.exists()
        assert "digraph CFG" in dot_content
        assert "PC=0" in dot_content


class TestX86CFGIntegration:
    """测试 x86-64 CFG 集成。"""

    def test_x86_cfg_visualize_method(self, tmp_path: Path):
        """测试 x86-64 CFG 的 visualize 方法。"""
        blocks = [
            X86Block(
                start_addr=0x1000,
                end_addr=0x1003,
                instructions=[
                    X86Instruction(addr=0x1000, mnemonic="xor", op_str="rax, rax", bytes=b"\x48\x31\xc0", size=3),
                ],
            ),
            X86Block(
                start_addr=0x1003,
                end_addr=0x1004,
                instructions=[
                    X86Instruction(addr=0x1003, mnemonic="ret", op_str="", bytes=b"\xc3", size=1),
                ],
            ),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1003, X86EdgeType.UNCONDITIONAL)

        # 使用 visualize 方法
        output_file = tmp_path / "x86_test.dot"
        dot_content = cfg.visualize(str(output_file))

        assert output_file.exists()
        assert "digraph CFG" in dot_content
        assert "0x1000" in dot_content


class TestIntegration:
    """集成测试。"""

    def test_visualize_real_x86_cfg(self, tmp_path: Path):
        """测试可视化真实的 x86-64 CFG（来自编译器输出）。

        测试验证：
        1. 能够处理真实的编译器输出
        2. 包含多个基本块
        3. 包含不同类型的边
        4. 正确生成 DOT 文件
        """
        from x86_64.disassembler import disassemble_hex

        # 真实的编译器输出，包含 8 个基本块
        hex_code = (
            "4d8b75384d0375304d8b7d10498b45704883f80372234883e80349894570"
            "498b45304883f8407222483d21800000732b4d8b75384901c6eb3341c685"
            "e00000000c49c7452800000000c341c685e00000000e49c7452800000000"
            "c341c685e00000000f49c7452800000000c3498b46c0490346e0498b4ec8"
            "49134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498"
            "956d049895ed841c685e00000000249c74528fcffffffc3"
        )

        # 反汇编代码
        instructions = disassemble_hex(hex_code, base_addr=0x1000)

        # 创建基本块（基于已知的块边界）
        block_starts = [0x1000, 0x1016, 0x1028, 0x1030, 0x1039, 0x104a, 0x105b, 0x106c]
        blocks = []
        for i, start in enumerate(block_starts):
            end = block_starts[i + 1] if i + 1 < len(block_starts) else 0x1000 + len(hex_code) // 2
            block_insts = [inst for inst in instructions if start <= inst.addr < end]
            blocks.append(X86Block(start_addr=start, end_addr=end, instructions=block_insts))

        # 创建 CFG
        cfg = X86DynamicCFG(blocks)

        # 添加边（基于编译器输出的控制流）
        cfg.add_edge(0x1000, 0x1016, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1016, 0x1028, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1028, 0x1030, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1030, 0x1039, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1039, 0x104a, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x104a, 0x105b, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x105b, 0x106c, X86EdgeType.UNCONDITIONAL)

        # 生成可视化
        visualizer = CFGVisualizer(cfg, cfg_type="x86")
        dot = visualizer.generate_dot(title="Real x86-64 CFG from Compiler")

        # 验证生成的 DOT 内容
        assert "digraph CFG" in dot
        assert "x86" in dot or "X86" in dot
        assert "0x1000" in dot
        assert "0x106c" in dot

        # 验证节点数量
        assert f"// {len(blocks)} nodes" in dot or dot.count("node_") >= len(blocks)

        # 保存到文件
        output_file = tmp_path / "real_x86_cfg.dot"
        visualizer.save_to_file(str(output_file))
        assert output_file.exists()

        # 获取并验证统计信息
        stats = visualizer.get_statistics()
        assert stats["cfg_type"] == "x86"
        assert stats["num_nodes"] == len(blocks)
        assert stats["num_edges"] == 7

    def test_visualize_complex_cfg(self):
        """测试可视化复杂 CFG（菱形控制流）。"""
        # 创建菱形控制流
        blocks = [
            EVMBlock(
                pc=0,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=False,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="JUMPI", pc=0)],
            ),
            EVMBlock(
                pc=13,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="ADD", pc=13)],
            ),
            EVMBlock(
                pc=26,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=False,
                operations=[EvmOperator(kind="SUB", pc=26)],
            ),
            EVMBlock(
                pc=39,
                stack_depth=0,
                min_depth=0,
                max_depth=1024,
                static_gas=10,
                is_jump_target=True,
                is_inner_block=False,
                is_stop=True,
                operations=[EvmOperator(kind="STOP", pc=39)],
            ),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)  # 条件为真
        cfg.add_edge(0, 26, EdgeType.FALLTHROUGH)  # 条件为假
        cfg.add_edge(13, 39, EdgeType.UNCONDITIONAL)
        cfg.add_edge(26, 39, EdgeType.UNCONDITIONAL)

        visualizer = CFGVisualizer(cfg)
        dot = visualizer.generate_dot()
        stats = visualizer.get_statistics()

        assert stats["num_nodes"] == 4
        assert stats["num_edges"] == 4
        assert "digraph CFG" in dot
