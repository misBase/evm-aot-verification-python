"""
EVM Storage 状态建模。
"""

from typing import Optional
from z3 import BitVec, Array, BitVecSort, Select, Store


class EVMStorageState:
    """EVM存储状态表示。

    使用Z3 Array对EVM存储建模：Storage : Array[BitVec[256], BitVec[256]]
    键值对存储，256位地址到256位值。
    """

    def __init__(self, storage_array: Optional[Array] = None):
        """初始化EVM存储状态。

        Args:
            storage_array: 可选的现有Storage数组
        """
        # Storage : Array[BitVec[256], BitVec[256]]
        if storage_array is None:
            self.Storage = Array('Storage', BitVecSort(256), BitVecSort(256))
        else:
            self.Storage = storage_array

    def sload(self, key: BitVec) -> BitVec:
        """从存储中加载值。

        Args:
            key: 256位存储键

        Returns:
            256位存储值
        """
        if key.size() != 256:
            raise ValueError(f"Storage key must be 256 bits, got {key.size()}")

        return Select(self.Storage, key)

    def sstore(self, key: BitVec, value: BitVec) -> 'EVMStorageState':
        """存储值到存储中。

        Args:
            key: 256位存储键
            value: 256位要存储的值

        Returns:
            具有更新Storage的新EVMStorageState
        """
        if key.size() != 256:
            raise ValueError(f"Storage key must be 256 bits, got {key.size()}")
        if value.size() != 256:
            raise ValueError(f"Storage value must be 256 bits, got {value.size()}")

        new_storage = Store(self.Storage, key, value)
        new_state = EVMStorageState(storage_array=new_storage)
        return new_state

    def copy(self) -> 'EVMStorageState':
        """创建存储状态的副本。

        Returns:
            具有相同Storage的新EVMStorageState实例
        """
        new_state = EVMStorageState(storage_array=self.Storage)
        return new_state
