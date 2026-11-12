"""
EVM Transient Storage 状态建模。
"""

from typing import Optional
from z3 import BitVec, Array, BitVecSort, Select, Store


class EVMTransientStorageState:
    """EVM transient storage 状态表示。

    使用Z3 Array对EVM transient storage (EIP-1153) 建模：
    TransientStorage : Array[BitVec[256], BitVec[256]]
    键值对存储，256位地址到256位值，仅在单次交易内有效。
    """

    def __init__(self, storage_array: Optional[Array] = None):
        """初始化EVM transient storage状态。

        Args:
            storage_array: 可选的现有TransientStorage数组
        """
        if storage_array is None:
            self.TransientStorage = Array('TransientStorage', BitVecSort(256), BitVecSort(256))
        else:
            self.TransientStorage = storage_array

    def tload(self, key: BitVec) -> BitVec:
        """从transient storage中加载值。

        Args:
            key: 256位存储键

        Returns:
            256位存储值
        """
        if key.size() != 256:
            raise ValueError(f"Transient storage key must be 256 bits, got {key.size()}")

        return Select(self.TransientStorage, key)

    def tstore(self, key: BitVec, value: BitVec) -> 'EVMTransientStorageState':
        """存储值到transient storage中。

        Args:
            key: 256位存储键
            value: 256位要存储的值

        Returns:
            具有更新TransientStorage的新EVMTransientStorageState
        """
        if key.size() != 256:
            raise ValueError(f"Transient storage key must be 256 bits, got {key.size()}")
        if value.size() != 256:
            raise ValueError(f"Transient storage value must be 256 bits, got {value.size()}")

        new_storage = Store(self.TransientStorage, key, value)
        return EVMTransientStorageState(storage_array=new_storage)

    def copy(self) -> 'EVMTransientStorageState':
        """创建transient storage状态的副本。

        Returns:
            具有相同TransientStorage的新EVMTransientStorageState实例
        """
        return EVMTransientStorageState(storage_array=self.TransientStorage)
