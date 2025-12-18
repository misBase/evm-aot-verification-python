"""
EVM IR JSON解析器。

本模块处理从JSON格式解析EVM IR（由Go编译器导出）。
"""

import json
from typing import List, Dict, Any
from .models import EVMBlock


class CompilerEVMResult:
    """EVM IR编译结果。"""
    
    def __init__(self, blocks: List[EVMBlock]):
        """使用块列表初始化。
        
        Args:
            blocks: EVM块列表
        """
        self.blocks = blocks
    
    @classmethod
    def from_json(cls, data: Dict[str, Any]) -> 'CompilerEVMResult':
        """从JSON数据创建CompilerEVMResult。
        
        Args:
            data: 包含编译结果的字典
            
        Returns:
            CompilerEVMResult实例
        """
        blocks_data = data.get('control_frames', [])
        blocks = [EVMBlock.from_json(block_data) for block_data in blocks_data]
        return cls(blocks=blocks)
    
    def to_json(self) -> Dict[str, Any]:
        """转换为JSON可序列化字典。
        
        Returns:
            字典表示
        """
        return {
            'control_frames': [block.to_json() for block in self.blocks]
        }


def load_ir_from_json(file_path: str) -> CompilerEVMResult:
    """从JSON文件加载EVM IR。
    
    Args:
        file_path: JSON文件路径
        
    Returns:
        CompilerEVMResult实例
    """
    with open(file_path, 'r') as f:
        data = json.load(f)
    return CompilerEVMResult.from_json(data)


def load_ir_from_json_string(json_str: str) -> CompilerEVMResult:
    """从JSON字符串加载EVM IR。
    
    Args:
        json_str: JSON字符串
        
    Returns:
        CompilerEVMResult实例
    """
    data = json.loads(json_str)
    return CompilerEVMResult.from_json(data)

