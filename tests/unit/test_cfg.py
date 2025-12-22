#!/usr/bin/env python3
"""测试EVM IR控制流图（CFG）构建和路径分析。"""

import os
import pytest
from z3 import BoolVal

from evm_ir.json_parser import load_ir_from_json
from evm_ir.cfg import IRCFG, build_ir_cfg


class TestIRCFGBasic:
    """测试CFG的基本功能。"""
    
    def test_build_cfg_from_two_blocks(self):
        """测试从two_block.json构建CFG。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证块数量
        assert len(cfg.blocks) == 2, "应该有两个块"
        
        # 验证入口块
        entry = cfg.get_entry_block()
        assert entry.pc == 0, "入口块应该是PC=0"
        
        # 验证终止块
        terminals = cfg.get_terminal_blocks()
        assert len(terminals) == 1, "应该有一个终止块"
        assert terminals[0].pc == 13, "终止块应该是PC=13"
        
        # 验证块0的后继：应该有块1（PC=13）作为JUMPI的目标
        block0 = cfg.blocks[0]
        successors = cfg.get_successors(block0)
        assert len(successors) == 2, "块0应该有两个后继（JUMPI：跳转和顺序执行）"
        
        # 验证块0的最后一个操作是JUMPI
        assert block0.operations[-1].kind.upper() == "JUMPI", "块0应该以JUMPI结尾"
        jumpi_op = block0.operations[-1]
        assert jumpi_op.immediate == 13, "JUMPI应该跳转到PC=13"
        assert jumpi_op.is_static == True, "JUMPI应该是静态跳转"
        
        # 验证块1（PC=13）是跳转目标
        block1 = cfg.blocks[1]
        assert block1.pc == 13, "块1的PC应该是13"
        assert block1.is_jump_target == True, "块1应该是跳转目标"
        assert block1.is_stop == True, "块1应该包含STOP"
        
        # 验证块1的后继：应该是空的（终止块）
        successors1 = cfg.get_successors(block1)
        assert len(successors1) == 0, "终止块应该没有后继"
    
    def test_build_cfg_from_three_blocks(self):
        """测试从three_block.json构建CFG。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "three_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证块数量
        assert len(cfg.blocks) == 2, "应该有两个块（注意：JSON中只有2个control_frames）"
        
        # 验证入口块
        entry = cfg.get_entry_block()
        assert entry.pc == 0, "入口块应该是PC=0"
        
        # 验证终止块
        terminals = cfg.get_terminal_blocks()
        assert len(terminals) == 1, "应该有一个终止块"
        assert terminals[0].pc == 21, "终止块应该是PC=21"
        
        # 验证块0的后继
        block0 = cfg.blocks[0]
        successors = cfg.get_successors(block0)
        # 块0有JUMPI到21，还有顺序执行（但顺序执行的下一个块也是21，所以可能只有一个）
        # 实际上，由于块0后面没有其他块，所以只有跳转到21
        assert len(successors) >= 1, "块0应该至少有一个后继"
        
        # 验证块0包含JUMPI和JUMP操作
        jumpi_op = None
        jump_op = None
        for op in block0.operations:
            if op.kind.upper() == "JUMPI":
                jumpi_op = op
            elif op.kind.upper() == "JUMP":
                jump_op = op
        
        assert jumpi_op is not None, "块0应该包含JUMPI操作"
        assert jumpi_op.immediate == 21, "JUMPI应该跳转到PC=21"
        assert jump_op is not None, "块0应该包含JUMP操作"
        assert jump_op.immediate == 21, "JUMP应该跳转到PC=21"
    
    def test_build_cfg_from_multi_blocks(self):
        """测试从muti_block.json构建CFG（复杂控制流）。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "muti_block.json")

        ir_result = load_ir_from_json(ir_file)

        # muti_block.json包含动态跳转，应该抛出异常
        from utils.exceptions import UnsupportedJumpError
        with pytest.raises(UnsupportedJumpError) as exc_info:
            cfg = build_ir_cfg(ir_result.blocks)

        assert "dynamic_jump" in str(exc_info.value), "应该检测到动态跳转"
    
    def test_get_entry_block(self):
        """测试获取入口块。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        entry = cfg.get_entry_block()
        assert entry is not None, "应该返回入口块"
        assert entry == cfg.blocks[0], "入口块应该是第一个块"
    
    def test_get_entry_block_empty(self):
        """测试空块列表时获取入口块应该抛出异常。"""
        cfg = IRCFG([])
        with pytest.raises(ValueError, match="No blocks in CFG"):
            cfg.get_entry_block()
    
    def test_get_terminal_blocks(self):
        """测试获取终止块。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        terminals = cfg.get_terminal_blocks()
        assert len(terminals) > 0, "应该至少有一个终止块"
        
        # 验证所有终止块都以终止操作结尾
        for terminal in terminals:
            assert terminal.operations, "终止块应该有操作"
            last_op = terminal.operations[-1]
            assert last_op.kind.upper() in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"], \
                f"终止块PC={terminal.pc}应该以终止操作结尾"


class TestIRCFGSuccessors:
    """测试CFG的后继关系。"""
    
    def test_successors_two_block(self):
        """测试two_block.json中的后继关系。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        block0 = cfg.blocks[0]
        block1 = cfg.blocks[1]
        
        # 块0的后继应该包含块1（通过JUMPI跳转）
        successors0 = cfg.get_successors(block0)
        assert block1 in successors0, "块1应该是块0的后继（通过JUMPI）"
        
        # 块1是终止块，应该没有后继
        successors1 = cfg.get_successors(block1)
        assert len(successors1) == 0, "终止块应该没有后继"
    
    def test_successors_three_block(self):
        """测试three_block.json中的后继关系。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "three_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        block0 = cfg.blocks[0]
        block1 = cfg.blocks[1]
        
        # 块0的后继应该包含块1（通过JUMPI跳转到PC=21）
        successors0 = cfg.get_successors(block0)
        assert block1 in successors0, "块1应该是块0的后继（通过JUMPI）"
        
        # 块1是终止块，应该没有后继
        successors1 = cfg.get_successors(block1)
        assert len(successors1) == 0, "终止块应该没有后继"
    
    def test_successors_jump_target(self):
        """测试跳转目标的后继关系。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证跳转目标块
        block1 = cfg.blocks[1]
        assert block1.is_jump_target == True, "块1应该是跳转目标"
        assert block1.pc == 13, "块1的PC应该是13"


class TestIRCFGPaths:
    """测试CFG的路径查找。"""
    
    def test_find_all_paths_two_block(self):
        """测试在two_block.json中查找所有路径。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        paths = cfg.find_all_paths()
        assert len(paths) > 0, "应该找到至少一条路径"
        
        # 验证路径结构
        from z3 import BoolRef
        for path, condition in paths:
            assert isinstance(path, list), "路径应该是块列表"
            assert len(path) > 0, "路径应该至少包含一个块"
            assert isinstance(condition, BoolRef), "条件应该是BoolRef类型"
            
            # 验证路径从入口块开始
            assert path[0] == cfg.get_entry_block(), "路径应该从入口块开始"
            
            # 验证路径以终止块结束
            assert path[-1] in cfg.get_terminal_blocks(), "路径应该以终止块结束"
    
    def test_find_all_paths_three_block(self):
        """测试在three_block.json中查找所有路径。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "three_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        paths = cfg.find_all_paths()
        assert len(paths) > 0, "应该找到至少一条路径"
        
        # 验证路径结构
        for path, condition in paths:
            assert isinstance(path, list), "路径应该是块列表"
            assert len(path) > 0, "路径应该至少包含一个块"
            
            # 验证路径从入口块开始
            assert path[0] == cfg.get_entry_block(), "路径应该从入口块开始"
            
            # 验证路径以终止块结束
            assert path[-1] in cfg.get_terminal_blocks(), "路径应该以终止块结束"
    
    def test_find_all_paths_multi_block(self):
        """测试在muti_block.json中查找所有路径。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "muti_block.json")

        ir_result = load_ir_from_json(ir_file)

        # muti_block.json包含动态跳转，应该抛出异常
        from utils.exceptions import UnsupportedJumpError
        with pytest.raises(UnsupportedJumpError) as exc_info:
            cfg = build_ir_cfg(ir_result.blocks)

        assert "dynamic_jump" in str(exc_info.value), "应该检测到动态跳转"


class TestIRCFGJumpOperations:
    """测试CFG对JUMP/JUMPI操作的处理。"""
    
    def test_jumpi_immediate_value(self):
        """测试JUMPI操作的immediate值处理。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        block0 = cfg.blocks[0]
        jumpi_op = block0.operations[-1]
        
        assert jumpi_op.kind.upper() == "JUMPI", "最后一个操作应该是JUMPI"
        assert jumpi_op.immediate == 13, "JUMPI的immediate值应该是13"
        assert jumpi_op.is_static == True, "JUMPI应该是静态跳转"
        
        # 验证跳转目标被正确识别
        successors = cfg.get_successors(block0)
        target_block = cfg.blocks_by_pc.get(13)
        assert target_block in successors, "跳转目标块应该在后继列表中"
    
    def test_jump_immediate_value(self):
        """测试JUMP操作的immediate值处理。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "three_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        block0 = cfg.blocks[0]
        # 查找JUMP操作
        jump_op = None
        for op in block0.operations:
            if op.kind.upper() == "JUMP":
                jump_op = op
                break
        
        assert jump_op is not None, "应该找到JUMP操作"
        assert jump_op.immediate == 21, "JUMP的immediate值应该是21"
        assert jump_op.is_static == True, "JUMP应该是静态跳转"
        
        # 验证跳转目标被正确识别
        target_block = cfg.blocks_by_pc.get(21)
        assert target_block is not None, "应该找到目标块（PC=21）"
    
    def test_static_jump_target_resolution(self):
        """测试静态跳转目标解析。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证blocks_by_pc字典包含所有块
        assert 0 in cfg.blocks_by_pc, "应该包含PC=0的块"
        assert 13 in cfg.blocks_by_pc, "应该包含PC=13的块"
        
        # 验证可以通过PC查找块
        block0 = cfg.blocks_by_pc[0]
        block1 = cfg.blocks_by_pc[13]
        
        assert block0.pc == 0, "通过PC查找应该返回正确的块"
        assert block1.pc == 13, "通过PC查找应该返回正确的块"


class TestIRCFGLoops:
    """测试CFG的循环检测。"""
    
    def test_detect_loops_empty(self):
        """测试在没有循环的CFG中检测循环。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        loops = cfg.detect_loops()
        # two_block.json没有循环，所以应该返回空列表或只包含自循环
        # 由于当前实现返回空列表，我们验证它不会崩溃
        assert isinstance(loops, list), "应该返回列表"
    
    def test_validate_loops(self):
        """测试循环验证。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证不会抛出异常（因为没有不支持的循环）
        try:
            cfg.validate_loops()
        except Exception as e:
            pytest.fail(f"validate_loops不应该抛出异常: {e}")
    
    def test_is_self_loop(self):
        """测试自循环检测。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # two_block.json中没有自循环
        for block in cfg.blocks:
            is_self_loop = cfg._is_self_loop(block)
            assert isinstance(is_self_loop, bool), "应该返回布尔值"
            assert is_self_loop == False, "two_block.json中不应该有自循环"


class TestIRCFGEdgeCases:
    """测试CFG的边界情况。"""
    
    def test_empty_blocks(self):
        """测试空块列表。"""
        cfg = IRCFG([])
        
        with pytest.raises(ValueError):
            cfg.get_entry_block()
        
        terminals = cfg.get_terminal_blocks()
        assert terminals == [], "空CFG应该没有终止块"
    
    def test_single_block(self):
        """测试单个块的CFG。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")

        ir_result = load_ir_from_json(ir_file)
        # 只使用第一个块，它包含JUMPI到不存在的块，应该抛出LogicError
        from utils.exceptions import LogicError
        with pytest.raises(LogicError) as exc_info:
            single_block_cfg = IRCFG([ir_result.blocks[0]])

        assert "target block not found" in str(exc_info.value), "应该因为目标块不存在而抛出逻辑错误"
    
    def test_blocks_by_pc(self):
        """测试blocks_by_pc字典的正确性。"""
        test_dir = os.path.dirname(__file__)
        ir_file = os.path.join(test_dir, "..", "data", "two_block.json")
        
        ir_result = load_ir_from_json(ir_file)
        cfg = build_ir_cfg(ir_result.blocks)
        
        # 验证所有块都在字典中
        for block in cfg.blocks:
            assert block.pc in cfg.blocks_by_pc, f"块PC={block.pc}应该在blocks_by_pc中"
            assert cfg.blocks_by_pc[block.pc] == block, f"blocks_by_pc应该返回正确的块"
        
        # 验证字典大小
        assert len(cfg.blocks_by_pc) == len(cfg.blocks), "blocks_by_pc应该包含所有块"


class TestIRCFGDynamicJump:
    """测试CFG对动态跳转的处理（应抛出错误）。"""

    def test_dynamic_jump_should_error(self):
        """测试动态JUMP应该抛出UnsupportedJumpError异常。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from utils.exceptions import UnsupportedJumpError

        # 创建一个包含动态JUMP的块
        dynamic_jump_op = EvmOperator(
            kind="JUMP",
            pc=0,
            immediate=None,  # 没有immediate值
            is_static=False  # 不是静态跳转
        )
        block0 = EVMBlock(
            pc=0,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=10,
            is_jump_target=False,
            is_inner_block=False,
            is_stop=False,
            operations=[dynamic_jump_op]
        )
        block1 = EVMBlock(
            pc=1,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=1,
            is_jump_target=True,
            is_inner_block=False,
            is_stop=True,
            operations=[EvmOperator(kind="STOP", pc=1)]
        )

        # 构建CFG应该抛出UnsupportedJumpError
        with pytest.raises(UnsupportedJumpError) as exc_info:
            IRCFG([block0, block1])

        assert "dynamic_jump" in str(exc_info.value), "应该抛出dynamic_jump错误"
        assert "pc=0" in str(exc_info.value), "错误消息应该包含PC信息"

    def test_dynamic_jumpi_should_error(self):
        """测试动态JUMPI应该抛出UnsupportedJumpError异常。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from utils.exceptions import UnsupportedJumpError

        dynamic_jumpi_op = EvmOperator(
            kind="JUMPI",
            pc=0,
            immediate=None,
            is_static=False
        )
        block0 = EVMBlock(
            pc=0,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=10,
            is_jump_target=False,
            is_inner_block=False,
            is_stop=False,
            operations=[dynamic_jumpi_op]
        )
        block1 = EVMBlock(
            pc=1,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=1,
            is_jump_target=True,
            is_inner_block=False,
            is_stop=True,
            operations=[EvmOperator(kind="STOP", pc=1)]
        )

        # 构建CFG应该抛出UnsupportedJumpError
        with pytest.raises(UnsupportedJumpError) as exc_info:
            IRCFG([block0, block1])

        assert "dynamic_jumpi" in str(exc_info.value), "应该抛出dynamic_jumpi错误"
        assert "pc=0" in str(exc_info.value), "错误消息应该包含PC信息"

    def test_static_jump_missing_target_should_error(self):
        """测试静态跳转但目标块不存在应该抛出LogicError异常。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from utils.exceptions import LogicError

        # 创建静态JUMP，但目标块不存在
        static_jump_op = EvmOperator(
            kind="JUMP",
            pc=0,
            immediate=999,  # 目标PC不存在
            is_static=True  # 是静态跳转
        )
        block0 = EVMBlock(
            pc=0,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=10,
            is_jump_target=False,
            is_inner_block=False,
            is_stop=False,
            operations=[static_jump_op]
        )

        # 构建CFG应该抛出LogicError（逻辑错误）
        with pytest.raises(LogicError) as exc_info:
            IRCFG([block0])

        assert "target block not found" in str(exc_info.value), "错误消息应该说明目标块未找到"
        assert "pc=999" in str(exc_info.value), "错误消息应该包含目标PC"

    def test_static_jumpi_missing_target_should_error(self):
        """测试静态条件跳转但目标块不存在应该抛出LogicError异常。"""
        from evm_ir.models import EVMBlock, EvmOperator
        from utils.exceptions import LogicError

        # 创建静态JUMPI，但目标块不存在
        static_jumpi_op = EvmOperator(
            kind="JUMPI",
            pc=0,
            immediate=999,  # 目标PC不存在
            is_static=True  # 是静态跳转
        )
        block0 = EVMBlock(
            pc=0,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=10,
            is_jump_target=False,
            is_inner_block=False,
            is_stop=False,
            operations=[static_jumpi_op]
        )
        block1 = EVMBlock(
            pc=1,
            stack_depth=0,
            min_depth=0,
            max_depth=1024,
            static_gas=1,
            is_jump_target=True,
            is_inner_block=False,
            is_stop=True,
            operations=[EvmOperator(kind="STOP", pc=1)]
        )

        # 构建CFG应该抛出LogicError（逻辑错误）
        with pytest.raises(LogicError) as exc_info:
            IRCFG([block0, block1])

        assert "target block not found" in str(exc_info.value), "错误消息应该说明目标块未找到"
        assert "pc=999" in str(exc_info.value), "错误消息应该包含目标PC"

