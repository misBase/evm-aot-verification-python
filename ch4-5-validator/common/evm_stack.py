"""
EVM栈：为验证建模EVM栈。
"""

from typing import List
from .uint256 import Uint256


class EVMStack:
    """建模EVM栈。"""
    
    def __init__(self):
        """初始化空栈。"""
        self.items: List[Uint256] = []
    
    def push(self, value: Uint256):
        """将256位值推送到栈上。
        
        Args:
            value: 要推送的Uint256值
        """
        self.items.append(value)
    
    def pop(self) -> Uint256:
        """从栈中弹出256位值。
        
        Returns:
            栈顶的Uint256值
            
        Raises:
            IndexError: 如果栈为空
        """
        if not self.items:
            raise IndexError("Stack underflow")
        return self.items.pop()
    
    def peek(self, index: int = 0) -> Uint256:
        """查看栈上的值而不弹出。
        
        Args:
            index: 从顶部开始的索引（0 = 顶部元素）
            
        Returns:
            指定索引处的Uint256值
            
        Raises:
            IndexError: 如果索引超出范围
        """
        if index >= len(self.items):
            raise IndexError("Stack index out of range")
        return self.items[-(index + 1)]
    
    def __len__(self):
        """返回栈上的项目数。"""
        return len(self.items)
    
    def __repr__(self):
        return f"EVMStack({len(self.items)} items)"

