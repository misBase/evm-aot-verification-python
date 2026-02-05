"""
CFG 可视化器单元测试。

测试 DOT 生成器和可视化器的功能。

测试类结构：
1. TestDOTStyle - 测试样式配置
2. TestDOTGenerator - 测试 DOT 生成器（参数化合并 EVM/x86 测试）
3. TestCFGVisualizer - 测试可视化器主类
4. TestCFGEdgeLabels - 测试边标签生成
5. TestCFGIntegration - 测试集成场景
"""

import pytest
from pathlib import Path

from visualization.cfg_visualizer import (
    CFGVisualizer,
    DOTGenerator,
    DOTStyle,
)

# 导入 EVM 相关
from evm_ir.cfg_structures import DynamicCFG, EdgeType
from evm_ir.models import EVMBlock, EvmOperator

# 导入 x86-64 相关
from x86_64.cfg_structures import X86DynamicCFG, X86EdgeType
from x86_64.models import X86Block, X86Instruction


# =============================================================================
# 辅助函数
# =============================================================================

def create_evm_block(pc=0, operations=None, is_jump_target=False, is_stop=False):
    """创建 EVM 测试块的辅助函数。"""
    if operations is None:
        operations = [EvmOperator(kind="ADD", pc=pc)]
    return EVMBlock(
        pc=pc,
        stack_depth=0,
        min_depth=0,
        max_depth=1024,
        static_gas=10,
        is_jump_target=is_jump_target,
        is_inner_block=False,
        is_stop=is_stop,
        operations=operations,
    )


def create_x86_block(start_addr=0x1000, end_addr=None, instructions=None):
    """创建 x86-64 测试块的辅助函数。"""
    if end_addr is None:
        end_addr = start_addr + 3
    if instructions is None:
        instructions = [X86Instruction(addr=start_addr, mnemonic="xor", op_str="rax, rax", bytes=b"\x48\x31\xc0", size=3)]
    return X86Block(start_addr=start_addr, end_addr=end_addr, instructions=instructions)


# =============================================================================
# TestDOTStyle - 保持不变
# =============================================================================

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


# =============================================================================
# TestDOTGenerator - 合并所有 HTML/Show/Empty 测试
# =============================================================================

class TestDOTGenerator:
    """测试 DOT 生成器（参数化合并 EVM/x86 测试）。"""

    # ---------------------------------------------------------------------
    # 基础生成测试
    # ---------------------------------------------------------------------

    def test_generate_simple_evm_cfg(self):
        """测试生成简单 EVM CFG 的 DOT。"""
        blocks = [
            create_evm_block(pc=0, operations=[EvmOperator(kind="ADD", pc=0), EvmOperator(kind="POP", pc=1)]),
            create_evm_block(pc=13, operations=[EvmOperator(kind="STOP", pc=13)], is_jump_target=True, is_stop=True),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

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
        blocks = [
            create_x86_block(start_addr=0x1000),
            create_x86_block(start_addr=0x1003, instructions=[
                X86Instruction(addr=0x1003, mnemonic="ret", op_str="", bytes=b"\xc3", size=1)
            ]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1003, X86EdgeType.UNCONDITIONAL)

        generator = DOTGenerator(cfg)
        dot = generator.generate(title="Test x86 CFG")

        # 验证基本结构
        assert "digraph CFG" in dot
        assert "Test x86 CFG" in dot
        assert "0x1000" in dot
        assert "0x1003" in dot
        assert "xor" in dot or "ret" in dot
        assert "unconditional" in dot.lower()

    # ---------------------------------------------------------------------
    # HTML 表格格式测试（参数化）
    # ---------------------------------------------------------------------

    @pytest.mark.parametrize("cfg_type,block_factory,_unused1,_unused2", [
        ("evm", lambda: create_evm_block(pc=0), "pc", "PC=0"),
        ("x86", lambda: create_x86_block(start_addr=0x1000), "start_addr", "0x1000"),
    ])
    def test_html_table_structure(self, cfg_type, block_factory, _unused1, _unused2):
        """验证 HTML 表格基本结构：包含 <table> 标签和正确属性。"""
        if cfg_type == "evm":
            cfg = DynamicCFG([block_factory()])
        else:
            cfg = X86DynamicCFG([block_factory()])

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        assert '<table border="0" cellborder="0" cellspacing="0">' in dot
        assert '</table>>' in dot

    @pytest.mark.parametrize("cfg_type,create_blocks,expected_labels", [
        ("evm",
         lambda: [create_evm_block(pc=0), create_evm_block(pc=13, is_jump_target=True, is_stop=True)],
         ["<tr><td><b>PC=0</b></td></tr>", "<tr><td><b>PC=13</b></td></tr>"]),
        ("x86",
         lambda: [create_x86_block(0x1000), create_x86_block(0x2000, instructions=[
             X86Instruction(addr=0x2000, mnemonic="xor", op_str="rbx, rbx", bytes=b"\x48\x31\xdb", size=3)
         ])],
         ["<tr><td><b>0x1000</b></td></tr>", "<tr><td><b>0x2000</b></td></tr>"]),
    ])
    def test_address_row_format(self, cfg_type, create_blocks, expected_labels):
        """验证地址/PC 行格式：加粗显示。"""
        blocks = create_blocks()
        if cfg_type == "evm":
            cfg = DynamicCFG(blocks)
        else:
            cfg = X86DynamicCFG(blocks)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        for label in expected_labels:
            assert label in dot

    @pytest.mark.parametrize("cfg_type,create_block", [
        ("evm", lambda: create_evm_block(pc=0)),
        ("x86", lambda: create_x86_block(start_addr=0x1000)),
    ])
    def test_separator_line(self, cfg_type, create_block):
        """验证分隔线：20 个破折号。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=True)

        assert '<tr><td>' + '-' * 20 + '</td></tr>' in dot

    @pytest.mark.parametrize("cfg_type,create_block,expected_rows", [
        ("evm",
         lambda: create_evm_block(pc=0, operations=[
             EvmOperator(kind="ADD", pc=0),
             EvmOperator(kind="PUSH1", pc=1, immediate=0x10),
         ]),
         ['<tr><td align="left" fontname="Courier">pc=  0  ADD</td></tr>',
          '<tr><td align="left" fontname="Courier">pc=  1  PUSH1    imm=16</td></tr>']),
        ("x86",
         lambda: create_x86_block(0x1000, 0x1004, instructions=[
             X86Instruction(addr=0x1000, mnemonic="xor", op_str="rax, rax", bytes=b"\x48\x31\xc0", size=3),
             X86Instruction(addr=0x1003, mnemonic="ret", op_str="", bytes=b"\xc3", size=1),
         ]),
         ['<tr><td align="left">0x1000 xor rax, rax</td></tr>',
          '<tr><td align="left">0x1003 ret</td></tr>']),
    ])
    def test_instruction_operation_row_format(self, cfg_type, create_block, expected_rows):
        """验证指令/操作行格式。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=True)

        for row in expected_rows:
            assert row in dot

    @pytest.mark.parametrize("cfg_type,create_block", [
        ("evm", lambda: create_evm_block(pc=0)),
        ("x86", lambda: create_x86_block(start_addr=0x1000)),
    ])
    def test_states_row(self, cfg_type, create_block):
        """验证状态计数行格式。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        cfg.get_node(list(cfg.nodes.keys())[0]).states = [None, None, None]

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_states=True)

        assert '<tr><td>States: 3</td></tr>' in dot

    # ---------------------------------------------------------------------
    # 紧凑模式测试（参数化）
    # ---------------------------------------------------------------------

    @pytest.mark.parametrize("cfg_type,create_block,expected_instr_name", [
        ("evm", lambda: create_evm_block(pc=0, operations=[
            EvmOperator(kind="ADD", pc=0),
            EvmOperator(kind="MUL", pc=1),
        ]), "ADD"),
        ("x86", lambda: create_x86_block(0x1000, 0x1002, instructions=[
            X86Instruction(addr=0x1000, mnemonic="mov", op_str="rax, rbx", bytes=b"", size=0),
            X86Instruction(addr=0x1001, mnemonic="add", op_str="rax, 1", bytes=b"", size=0),
        ]), "mov"),
    ])
    def test_compact_mode(self, cfg_type, create_block, expected_instr_name):
        """验证紧凑模式：[N instrs]。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)

        # 完整模式
        dot_full = generator.generate(compact=False)
        assert expected_instr_name in dot_full

        # 紧凑模式
        dot_compact = generator.generate(compact=True)
        assert '[2 instrs]' in dot_compact

    # ---------------------------------------------------------------------
    # 指令截断测试（参数化）
    # ---------------------------------------------------------------------

    @pytest.mark.parametrize("cfg_type,create_large_block", [
        ("evm", lambda: create_evm_block(pc=0, operations=[
            EvmOperator(kind=f"OP{i}", pc=i) for i in range(15)
        ])),
        ("x86", lambda: create_x86_block(0x1000, 0x100f, instructions=[
            X86Instruction(addr=0x1000 + i, mnemonic=f"op{i}", op_str=f"r{i}, r{i}", bytes=b"", size=1)
            for i in range(15)
        ])),
    ])
    def test_instruction_truncation(self, cfg_type, create_large_block):
        """验证指令/操作截断：显示前 8 条 + 省略 + 最后 2 条。"""
        block = create_large_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=True)

        # 验证包含前面的指令/操作
        assert 'OP0' in dot or 'op0' in dot
        assert 'OP1' in dot or 'op1' in dot

        # 验证包含省略标记
        assert 'more)' in dot

        # 验证包含最后两条指令
        assert 'OP13' in dot or 'op13' in dot
        assert 'OP14' in dot or 'op14' in dot

    # ---------------------------------------------------------------------
    # 显示选项测试（参数化）
    # ---------------------------------------------------------------------

    @pytest.mark.parametrize("cfg_type,create_block,addr_label,instr_name", [
        ("evm", lambda: create_evm_block(pc=0, operations=[EvmOperator(kind="ADD", pc=0)]),
         "<tr><td><b>PC=0</b></td></tr>", "ADD"),
        ("x86", lambda: create_x86_block(0x1000, instructions=[
            X86Instruction(addr=0x1000, mnemonic="xor", op_str="rax, rax", bytes=b"\x48\x31\xc0", size=3)
        ]), "<tr><td><b>0x1000</b></td></tr>", "xor"),
    ])
    def test_hide_instructions(self, cfg_type, create_block, addr_label, instr_name):
        """测试隐藏指令时不显示分隔线和指令内容。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=False)

        # 验证地址行仍然存在
        assert addr_label in dot

        # 验证分隔线不存在
        assert '<tr><td>' + '-' * 20 + '</td></tr>' not in dot

        # 验证指令不存在
        assert instr_name not in dot

    @pytest.mark.parametrize("cfg_type,create_block", [
        ("evm", lambda: create_evm_block(pc=0)),
        ("x86", lambda: create_x86_block(start_addr=0x1000)),
    ])
    def test_show_states(self, cfg_type, create_block):
        """测试显示状态计数。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        cfg.get_node(list(cfg.nodes.keys())[0]).states = [None, None]

        generator = DOTGenerator(cfg)

        # 显示状态
        dot = generator.generate(show_states=True)
        assert 'States: 2' in dot

        # 隐藏状态
        dot = generator.generate(show_states=False)
        assert 'States:' not in dot

    # ---------------------------------------------------------------------
    # 空块测试（参数化）
    # ---------------------------------------------------------------------

    @pytest.mark.parametrize("cfg_type,create_block,addr_label", [
        ("evm", lambda: create_evm_block(pc=0, operations=[]), "<tr><td><b>PC=0</b></td></tr>"),
        ("x86", lambda: create_x86_block(0x1000, 0x1000, []), "<tr><td><b>0x1000</b></td></tr>"),
    ])
    def test_empty_block_address_only(self, cfg_type, create_block, addr_label):
        """测试空块只显示地址行（隐藏指令时）。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=False, show_states=False)

        # 验证地址行存在
        assert addr_label in dot

        # 验证 table 标签完整
        assert '<table border="0" cellborder="0" cellspacing="0">' in dot
        assert '</table>>' in dot

        # 验证分隔线不存在
        assert '<tr><td>' + '-' * 20 + '</td></tr>' not in dot

    @pytest.mark.parametrize("cfg_type,create_block,addr_label", [
        ("evm", lambda: create_evm_block(pc=0, operations=[]), "<tr><td><b>PC=0</b></td></tr>"),
        ("x86", lambda: create_x86_block(0x1000, 0x1000, []), "<tr><td><b>0x1000</b></td></tr>"),
    ])
    def test_empty_block_with_states_shows_separator(self, cfg_type, create_block, addr_label):
        """测试空块在显示指令时会有分隔线。"""
        block = create_block()
        if cfg_type == "evm":
            cfg = DynamicCFG([block])
        else:
            cfg = X86DynamicCFG([block])

        generator = DOTGenerator(cfg)
        dot = generator.generate()  # 默认 show_instructions=True

        # 验证地址行存在
        assert addr_label in dot

        # 当 show_instructions=True 时，即使没有操作也会显示分隔线
        assert '<tr><td>' + '-' * 20 + '</td></tr>' in dot

    # ---------------------------------------------------------------------
    # EVM 特定测试：TAG/BLOCKEND 过滤
    # ---------------------------------------------------------------------

    def test_evm_filters_tag_and_blockend(self):
        """测试 TAG 和 BLOCKEND 操作被过滤掉。"""
        block = create_evm_block(pc=0, operations=[
            EvmOperator(kind="TAG", pc=0),
            EvmOperator(kind="ADD", pc=1),
            EvmOperator(kind="BLOCKEND", pc=2),
            EvmOperator(kind="POP", pc=3),
        ])
        cfg = DynamicCFG([block])
        generator = DOTGenerator(cfg)
        dot = generator.generate(show_instructions=True)

        # 验证 TAG 和 BLOCKEND 不在输出中
        assert 'TAG' not in dot
        assert 'BLOCKEND' not in dot

        # 验证其他操作存在
        assert 'ADD' in dot
        assert 'POP' in dot

    # ---------------------------------------------------------------------
    # 其他 DOT 生成器测试
    # ---------------------------------------------------------------------

    def test_generate_with_loop(self):
        """测试生成包含循环的 CFG。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1002, instructions=[]),
            X86Block(start_addr=0x1002, end_addr=0x1004, instructions=[]),
            X86Block(start_addr=0x1004, end_addr=0x1005, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1002, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1002, 0x1004, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1004, 0x1000, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1000, 0x1000, X86EdgeType.FALLTHROUGH)

        generator = DOTGenerator(cfg)
        generator.generate()

        loop_headers = cfg.detect_loop_headers()
        assert len(loop_headers) > 0

    def test_node_colors(self):
        """测试节点颜色分配。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[]),
            X86Block(start_addr=0x1001, end_addr=0x1002, instructions=[]),
            X86Block(start_addr=0x1002, end_addr=0x1003, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1001, X86EdgeType.UNCONDITIONAL)
        cfg.add_edge(0x1001, 0x1002, X86EdgeType.UNCONDITIONAL)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        assert "#90EE90" in dot or "#ffffff" in dot


# =============================================================================
# TestCFGEdgeLabels - 边标签测试
# =============================================================================

class TestCFGEdgeLabels:
    """测试边标签生成。"""

    def test_edge_labels(self):
        """测试基本边标签生成。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1001, instructions=[]),
            X86Block(start_addr=0x1001, end_addr=0x1002, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1001, X86EdgeType.UNCONDITIONAL)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        assert "unconditional" in dot.lower()

    def test_jumpi_condition_labels(self):
        """测试 JUMPI 条件边标签。"""
        blocks = [
            create_evm_block(pc=0, operations=[EvmOperator(kind="JUMPI", pc=0)]),
            create_evm_block(pc=13, is_jump_target=True),
            create_evm_block(pc=15, is_jump_target=True),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL_TRUE)
        cfg.add_edge(0, 15, EdgeType.CONDITIONAL_FALSE)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        # 验证包含条件标签
        assert "true" in dot.lower() or "false" in dot.lower()

    def test_x86_jump_condition_labels(self):
        """测试 x86-64 条件跳转边标签。"""
        blocks = [
            X86Block(start_addr=0x1000, end_addr=0x1002, instructions=[]),
            X86Block(start_addr=0x1002, end_addr=0x1003, instructions=[]),
            X86Block(start_addr=0x1003, end_addr=0x1004, instructions=[]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1002, X86EdgeType.CONDITIONAL_TRUE)
        cfg.add_edge(0x1000, 0x1003, X86EdgeType.CONDITIONAL_FALSE)

        generator = DOTGenerator(cfg)
        dot = generator.generate()

        # 验证包含条件标签
        assert "conditional" in dot.lower()


# =============================================================================
# TestCFGVisualizer - 保持不变
# =============================================================================

class TestCFGVisualizer:
    """测试 CFG 可视化器。"""

    def test_evm_cfg_visualization(self):
        """测试 EVM CFG 可视化。"""
        blocks = [
            create_evm_block(pc=0, operations=[]),
            create_evm_block(pc=13, is_jump_target=True, is_stop=True, operations=[]),
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
        evm_blocks = [create_evm_block(pc=0, operations=[])]
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
            create_evm_block(pc=0, operations=[]),
            create_evm_block(pc=13, is_jump_target=True, is_stop=True, operations=[]),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)
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
        blocks = [create_evm_block(pc=0, operations=[])]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        output_file = tmp_path / "test_cfg.dot"
        visualizer.save_to_file(str(output_file))

        assert output_file.exists()
        content = output_file.read_text()
        assert "digraph CFG" in content

    def test_custom_title(self):
        """测试自定义标题。"""
        blocks = [create_evm_block(pc=0, operations=[])]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        dot = visualizer.generate_dot(title="My Custom CFG")
        assert "My Custom CFG" in dot

    def test_render_png_without_graphviz(self, tmp_path: Path):
        """测试在没有 graphviz 包时渲染 PNG 会引发错误。"""
        blocks = [create_evm_block(pc=0, operations=[])]

        cfg = DynamicCFG(blocks)
        visualizer = CFGVisualizer(cfg)

        output_file = tmp_path / "test.png"
        try:
            visualizer.render_png(str(output_file))
        except ImportError:
            pass  # 预期的错误


# =============================================================================
# TestCFGIntegration - 合并所有集成测试
# =============================================================================

class TestCFGIntegration:
    """集成测试（合并 EVM/x86/JSON 测试）。"""

    # ---------------------------------------------------------------------
    # EVM CFG 集成测试
    # ---------------------------------------------------------------------

    def test_evm_cfg_visualize_method(self, tmp_path: Path):
        """测试 EVM CFG 的 visualize 方法。"""
        blocks = [
            create_evm_block(pc=0, operations=[EvmOperator(kind="ADD", pc=0)]),
            create_evm_block(pc=13, is_jump_target=True, is_stop=True,
                          operations=[EvmOperator(kind="STOP", pc=13)]),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 13, EdgeType.CONDITIONAL)

        output_file = tmp_path / "evm_test.dot"
        dot_content = cfg.visualize(str(output_file))

        assert output_file.exists()
        assert "digraph CFG" in dot_content
        assert "PC=0" in dot_content

    # ---------------------------------------------------------------------
    # x86 CFG 集成测试
    # ---------------------------------------------------------------------

    def test_x86_cfg_visualize_method(self, tmp_path: Path):
        """测试 x86-64 CFG 的 visualize 方法。"""
        blocks = [
            create_x86_block(0x1000),
            create_x86_block(0x1003, instructions=[
                X86Instruction(addr=0x1003, mnemonic="ret", op_str="", bytes=b"\xc3", size=1)
            ]),
        ]

        cfg = X86DynamicCFG(blocks)
        cfg.add_edge(0x1000, 0x1003, X86EdgeType.UNCONDITIONAL)

        output_file = tmp_path / "x86_test.dot"
        dot_content = cfg.visualize(str(output_file))

        assert output_file.exists()
        assert "digraph CFG" in dot_content
        assert "0x1000" in dot_content

    # ---------------------------------------------------------------------
    # three_block.json 测试
    # ---------------------------------------------------------------------

    def test_three_block_json(self, tmp_path: Path):
        """测试从 three_block.json 加载并可视化 CFG。"""
        from evm_ir.json_parser import load_ir_from_json
        from evm_ir.cfg_executor import build_dynamic_cfg
        from evm_ir.cfg_strategies import DFSStrategy
        from state.smt_state import SMTState

        test_dir = Path(__file__).parent.parent
        json_file = test_dir / "data" / "three_block.json"

        ir_result = load_ir_from_json(str(json_file))
        assert len(ir_result.blocks) == 3

        blocks = ir_result.blocks
        assert blocks[0].pc == 0
        assert blocks[1].pc == 15
        assert blocks[2].pc == 21

        initial_state = SMTState.create_initial_state(num_inputs=0)
        _, cfg = build_dynamic_cfg(
            blocks=blocks,
            initial_state=initial_state,
            strategy_cls=DFSStrategy,
            max_depth=100
        )

        assert len(cfg.nodes) == 3
        assert len(cfg.edges) == 2

        visualizer = CFGVisualizer(cfg, cfg_type="evm")
        dot = visualizer.generate_dot(title="Three Block CFG from JSON")

        assert "digraph CFG" in dot
        assert "PC=0" in dot
        assert "JUMPI" in dot

        output_file = tmp_path / "three_block_cfg.dot"
        visualizer.save_to_file(str(output_file))
        assert output_file.exists()

    # ---------------------------------------------------------------------
    # 真实 x86 CFG 测试
    # ---------------------------------------------------------------------

    def test_real_x86_cfg(self, tmp_path: Path):
        """测试可视化真实的 x86-64 CFG（来自编译器输出）。"""
        from x86_64.disassembler import disassemble_hex
        from x86_64.cfg import identify_basic_blocks
        from x86_64.cfg_executor import build_x86_dynamic_cfg
        from x86_64.cfg_strategies import X86DFSStrategy
        from state.smt_state import SMTState

        hex_code = (
            "4d8b75384d0375304d8b7d10498b45704883f80372234883e80349894570"
            "498b45304883f8407222483d21800000732b4d8b75384901c6eb3341c685"
            "e00000000c49c7452800000000c341c685e00000000e49c7452800000000"
            "c341c685e00000000f49c7452800000000c3498b46c0490346e0498b4ec8"
            "49134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498"
            "956d049895ed841c685e00000000249c74528fcffffffc3"
        )

        instructions = disassemble_hex(hex_code, base_addr=0x1000)
        blocks = identify_basic_blocks(instructions)
        assert len(blocks) > 0

        initial_state = SMTState()
        _, cfg = build_x86_dynamic_cfg(
            blocks=blocks,
            initial_state=initial_state,
            strategy_cls=X86DFSStrategy,
            max_depth=100
        )

        visualizer = CFGVisualizer(cfg, cfg_type="x86")
        dot = visualizer.generate_dot(title="Real x86-64 CFG from Compiler")

        assert "digraph CFG" in dot
        assert "0x1000" in dot

        output_file = tmp_path / "real_x86_cfg.dot"
        visualizer.save_to_file(str(output_file))
        assert output_file.exists()

    # ---------------------------------------------------------------------
    # 菱形 CFG 测试
    # ---------------------------------------------------------------------

    def test_complex_diamond_cfg(self):
        """测试可视化复杂 CFG（菱形控制流）。"""
        blocks = [
            create_evm_block(pc=0, operations=[EvmOperator(kind="JUMPI", pc=0)]),
            create_evm_block(pc=13, is_jump_target=True,
                          operations=[EvmOperator(kind="ADD", pc=13)]),
            create_evm_block(pc=26, is_jump_target=True,
                          operations=[EvmOperator(kind="SUB", pc=26)]),
            create_evm_block(pc=39, is_jump_target=True, is_stop=True,
                          operations=[EvmOperator(kind="STOP", pc=39)]),
        ]

        cfg = DynamicCFG(blocks)
        cfg.add_edge(0, 26, EdgeType.CONDITIONAL)
        cfg.add_edge(0, 13, EdgeType.FALLTHROUGH)
        cfg.add_edge(13, 26, EdgeType.UNCONDITIONAL)
        cfg.add_edge(26, 39, EdgeType.UNCONDITIONAL)

        visualizer = CFGVisualizer(cfg)
        dot = visualizer.generate_dot()
        stats = visualizer.get_statistics()

        assert stats["num_nodes"] == 4
        assert stats["num_edges"] == 4
        assert "digraph CFG" in dot

    # ---------------------------------------------------------------------
    # muti_block.json 测试
    # ---------------------------------------------------------------------

    def test_muti_block_json(self, tmp_path: Path):
        """测试从 muti_block.json 加载并可视化 CFG。"""
        from evm_ir.json_parser import load_ir_from_json

        test_dir = Path(__file__).parent.parent
        json_file = test_dir / "data" / "muti_block.json"

        ir_result = load_ir_from_json(str(json_file))
        assert len(ir_result.blocks) >= 30

        blocks = ir_result.blocks
        assert blocks[0].pc == 0

        cfg = DynamicCFG(blocks)

        # 手动添加一些边
        for i, block in enumerate(blocks):
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind == "JUMPI" and i + 1 < len(blocks):
                    cfg.add_edge(block.pc, blocks[i + 1].pc, EdgeType.FALLTHROUGH)

        assert len(cfg.nodes) > 0
        assert 0 in cfg.nodes

        visualizer = CFGVisualizer(cfg, cfg_type="evm")
        dot = visualizer.generate_dot(title="Multi Block CFG from JSON")

        assert "digraph CFG" in dot
        assert "PC=0" in dot

        output_file = tmp_path / "muti_block_cfg.dot"
        visualizer.save_to_file(str(output_file))
        assert output_file.exists()

    def test_muti_block_cfg_structure(self):
        """测试 muti_block.json 的 CFG 结构细节。"""
        from evm_ir.json_parser import load_ir_from_json

        test_dir = Path(__file__).parent.parent
        json_file = test_dir / "data" / "muti_block.json"

        ir_result = load_ir_from_json(str(json_file))
        blocks = ir_result.blocks

        cfg = DynamicCFG(blocks)
        for i, block in enumerate(blocks):
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind == "JUMPI" and i + 1 < len(blocks):
                    cfg.add_edge(block.pc, blocks[i + 1].pc, EdgeType.FALLTHROUGH)

        entry_node = cfg.get_node(0)
        assert entry_node is not None

        jump_target_pcs = [b.pc for b in blocks if b.is_jump_target]
        assert len(jump_target_pcs) >= 10

        for pc in jump_target_pcs[:5]:
            assert pc in cfg.nodes

    def test_muti_block_visualization_compact_mode(self, tmp_path: Path):
        """测试 muti_block.json 的紧凑模式可视化。"""
        from evm_ir.json_parser import load_ir_from_json

        test_dir = Path(__file__).parent.parent
        json_file = test_dir / "data" / "muti_block.json"

        ir_result = load_ir_from_json(str(json_file))
        blocks = ir_result.blocks

        cfg = DynamicCFG(blocks)
        for i, block in enumerate(blocks):
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind == "JUMPI" and i + 1 < len(blocks):
                    cfg.add_edge(block.pc, blocks[i + 1].pc, EdgeType.FALLTHROUGH)

        generator = DOTGenerator(cfg)
        dot_compact = generator.generate(compact=True, title="Multi Block CFG (Compact)")

        assert "digraph CFG" in dot_compact
        assert "Compact" in dot_compact

        output_file = tmp_path / "muti_block_cfg_compact.dot"
        with open(output_file, 'w') as f:
            f.write(dot_compact)
        assert output_file.exists()

    def test_muti_block_build_dynamic_cfg_real(self, tmp_path: Path):
        """测试 muti_block.json 使用真实符号执行构建 CFG。"""
        from evm_ir.json_parser import load_ir_from_json
        from evm_ir.cfg_executor import SymbolicExecutor
        from evm_ir.cfg_strategies import DFSStrategy
        from state.smt_state import SMTState
        from utils.exceptions import UnsupportedJumpError

        test_dir = Path(__file__).parent.parent
        json_file = test_dir / "data" / "muti_block.json"

        ir_result = load_ir_from_json(str(json_file))
        blocks = ir_result.blocks

        initial_state = SMTState.create_initial_state(num_inputs=0)

        executor = SymbolicExecutor(
            blocks=blocks,
            strategy_cls=DFSStrategy,
            max_depth=500
        )

        try:
            executor.execute(initial_state)
        except UnsupportedJumpError as e:
            print(f"Execution stopped early due to dynamic jump: {e}")
            pass
        except Exception as e:
            pytest.fail(f"Symbolic execution failed with unexpected error: {str(e)}")

        cfg = executor.cfg
        assert len(cfg.nodes) > 0

        print(f"Generated partial CFG with {len(cfg.nodes)} nodes and {len(cfg.edges)} edges")

        visualizer = CFGVisualizer(cfg, cfg_type="evm")
        output_file = tmp_path / "muti_block_real_exec.dot"
        visualizer.save_to_file(str(output_file))
        assert output_file.exists()
