"""
EVM IR JSON parser.

This module handles parsing of EVM IR from JSON format (as exported by the Go compiler).
"""

import json
from typing import List, Dict, Any
from .models import EVMBlock


class CompilerEVMResult:
    """Result of EVM IR compilation."""
    
    def __init__(self, blocks: List[EVMBlock]):
        """Initialize with a list of blocks.
        
        Args:
            blocks: List of EVM blocks
        """
        self.blocks = blocks
    
    @classmethod
    def from_json(cls, data: Dict[str, Any]) -> 'CompilerEVMResult':
        """Create CompilerEVMResult from JSON data.
        
        Args:
            data: Dictionary containing compilation result
            
        Returns:
            CompilerEVMResult instance
        """
        blocks_data = data.get('control_frames', [])
        blocks = [EVMBlock.from_json(block_data) for block_data in blocks_data]
        return cls(blocks=blocks)
    
    def to_json(self) -> Dict[str, Any]:
        """Convert to JSON-serializable dictionary.
        
        Returns:
            Dictionary representation
        """
        return {
            'control_frames': [block.to_json() for block in self.blocks]
        }


def load_ir_from_json(file_path: str) -> CompilerEVMResult:
    """Load EVM IR from a JSON file.
    
    Args:
        file_path: Path to JSON file
        
    Returns:
        CompilerEVMResult instance
    """
    with open(file_path, 'r') as f:
        data = json.load(f)
    return CompilerEVMResult.from_json(data)


def load_ir_from_json_string(json_str: str) -> CompilerEVMResult:
    """Load EVM IR from a JSON string.
    
    Args:
        json_str: JSON string
        
    Returns:
        CompilerEVMResult instance
    """
    data = json.loads(json_str)
    return CompilerEVMResult.from_json(data)

