"""
Uint256：将256位无符号整数表示为4x64位limb。

本模块提供在验证系统中处理256位值的实用工具。
"""

from z3 import BitVec, BitVecVal, Concat, Extract


class Uint256:
    """将256位无符号整数表示为4x64位limb。
    
    布局：[z3 (位192-255) | z2 (位128-191) | z1 (位64-127) | z0 (位0-63)]
    """
    
    def __init__(self, z0, z1, z2, z3):
        """使用4x64位limb初始化。
        
        Args:
            z0: 最低有效64位
            z1: 位64-127
            z2: 位128-191
            z3: 最高有效64位（位192-255）
        """
        self.z0 = z0  # 最低有效limb
        self.z1 = z1
        self.z2 = z2
        self.z3 = z3  # 最高有效limb
    
    def to_bv256(self):
        """转换为单个256位位向量。
        
        Returns:
            大小为256的Z3 BitVec
        """
        return Concat(self.z3, self.z2, self.z1, self.z0)
    
    @staticmethod
    def from_bv256(bv):
        """从256位位向量创建Uint256。
        
        Args:
            bv: 大小为256的Z3 BitVec
            
        Returns:
            Uint256实例
        """
        z0 = Extract(63, 0, bv)
        z1 = Extract(127, 64, bv)
        z2 = Extract(191, 128, bv)
        z3 = Extract(255, 192, bv)
        return Uint256(z0, z1, z2, z3)
    
    @staticmethod
    def from_int(value):
        """从Python整数创建Uint256。
        
        Args:
            value: Python int（将被截断为256位）
            
        Returns:
            Uint256实例
        """
        bv = BitVecVal(value, 256)
        return Uint256.from_bv256(bv)
    
    @staticmethod
    def symbolic(name):
        """创建符号Uint256变量。
        
        Args:
            name: 符号变量的基础名称（将创建name_z0、name_z1等）
            
        Returns:
            具有符号limb的Uint256
        """
        z0 = BitVec(f"{name}_z0", 64)
        z1 = BitVec(f"{name}_z1", 64)
        z2 = BitVec(f"{name}_z2", 64)
        z3 = BitVec(f"{name}_z3", 64)
        return Uint256(z0, z1, z2, z3)
    
    def add_semantics(self, other: 'Uint256') -> 'Uint256':
        """将两个Uint256值相加，带进位传播（语义建模）。
        
        这使用4x64位limb加法和进位实现EVM ADD语义。
        实现与x86-64 AOT编译器的方法匹配。
        
        Args:
            other: 要相加的另一个Uint256值
            
        Returns:
            表示和(a + b) mod 2^256的新Uint256实例
        """
        from z3 import BitVecVal, Concat, Extract
        
        # 执行4x64位加法，带进位传播
        # 这与x86-64实现匹配
        
        # Limb 0: result_z0 = self.z0 + other.z0
        # Extend to 65 bits to capture carry
        sum0_ext = Concat(BitVecVal(0, 1), self.z0) + Concat(BitVecVal(0, 1), other.z0)
        result_z0 = Extract(63, 0, sum0_ext)
        carry0 = Extract(64, 64, sum0_ext)
        
        # Limb 1: result_z1 = self.z1 + other.z1 + carry0
        sum1_ext = (Concat(BitVecVal(0, 1), self.z1) + 
                    Concat(BitVecVal(0, 1), other.z1) + 
                    Concat(BitVecVal(0, 64), carry0))
        result_z1 = Extract(63, 0, sum1_ext)
        carry1 = Extract(64, 64, sum1_ext)
        
        # Limb 2: result_z2 = self.z2 + other.z2 + carry1
        sum2_ext = (Concat(BitVecVal(0, 1), self.z2) + 
                    Concat(BitVecVal(0, 1), other.z2) + 
                    Concat(BitVecVal(0, 64), carry1))
        result_z2 = Extract(63, 0, sum2_ext)
        carry2 = Extract(64, 64, sum2_ext)
        
        # Limb 3: result_z3 = self.z3 + other.z3 + carry2
        # carry3 is discarded (256-bit overflow)
        sum3_ext = (Concat(BitVecVal(0, 1), self.z3) + 
                    Concat(BitVecVal(0, 1), other.z3) + 
                    Concat(BitVecVal(0, 64), carry2))
        result_z3 = Extract(63, 0, sum3_ext)
        
        return Uint256(result_z0, result_z1, result_z2, result_z3)
    
    def __repr__(self):
        return f"Uint256(z0={self.z0}, z1={self.z1}, z2={self.z2}, z3={self.z3})"

