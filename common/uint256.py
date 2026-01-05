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

    def sub_semantics(self, other: 'Uint256') -> 'Uint256':
        """将两个Uint256值相减，带借位传播（语义建模）。

        这使用4x64位limb减法和借位实现EVM SUB语义。
        计算 (a - b) mod 2^256。

        Args:
            other: 要减去的另一个Uint256值

        Returns:
            表示差(a - b) mod 2^256的新Uint256实例
        """
        from z3 import BitVecVal, Concat, Extract, ZeroExt

        # 执行4x64位减法，带借位传播

        # Limb 0: result_z0 = self.z0 - other.z0
        # Extend to 65 bits to capture borrow
        diff0_ext = Concat(BitVecVal(0, 1), self.z0) - Concat(BitVecVal(0, 1), other.z0)
        result_z0 = Extract(63, 0, diff0_ext)
        borrow0 = Extract(64, 64, diff0_ext)

        # Limb 1: result_z1 = self.z1 - other.z1 - borrow0
        # 将 1-bit borrow 扩展为 65-bit: Concat(0, ZeroExt(63, borrow0))
        diff1_ext = (Concat(BitVecVal(0, 1), self.z1) -
                     Concat(BitVecVal(0, 1), other.z1) -
                     Concat(BitVecVal(0, 1), ZeroExt(63, borrow0)))
        result_z1 = Extract(63, 0, diff1_ext)
        borrow1 = Extract(64, 64, diff1_ext)

        # Limb 2: result_z2 = self.z2 - other.z2 - borrow1
        diff2_ext = (Concat(BitVecVal(0, 1), self.z2) -
                     Concat(BitVecVal(0, 1), other.z2) -
                     Concat(BitVecVal(0, 1), ZeroExt(63, borrow1)))
        result_z2 = Extract(63, 0, diff2_ext)
        borrow2 = Extract(64, 64, diff2_ext)

        # Limb 3: result_z3 = self.z3 - other.z3 - borrow2
        # borrow3 is discarded (underflow wraps around)
        diff3_ext = (Concat(BitVecVal(0, 1), self.z3) -
                     Concat(BitVecVal(0, 1), other.z3) -
                     Concat(BitVecVal(0, 1), ZeroExt(63, borrow2)))
        result_z3 = Extract(63, 0, diff3_ext)

        return Uint256(result_z0, result_z1, result_z2, result_z3)

    def mul_semantics(self, other: 'Uint256') -> 'Uint256':
        """将两个Uint256值相乘（语义建模）。

        计算 (a * b) mod 2^256。
        简化实现：使用256位直接相乘然后截断。

        Args:
            other: 要相乘的另一个Uint256值

        Returns:
            表示积(a * b) mod 2^256的新Uint256实例
        """
        from z3 import BitVecVal

        # 直接使用256位乘法然后截断
        a_256 = self.to_bv256()
        b_256 = other.to_bv256()

        # 256位乘法会溢出，这正是我们想要的（模2^256）
        product_256 = a_256 * b_256

        # 将结果转换回Uint256
        return Uint256.from_bv256(product_256)

    def and_semantics(self, other: 'Uint256') -> 'Uint256':
        """按位与操作（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            a & b 的新Uint256实例
        """
        return Uint256(
            self.z0 & other.z0,
            self.z1 & other.z1,
            self.z2 & other.z2,
            self.z3 & other.z3
        )

    def or_semantics(self, other: 'Uint256') -> 'Uint256':
        """按位或操作（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            a | b 的新Uint256实例
        """
        return Uint256(
            self.z0 | other.z0,
            self.z1 | other.z1,
            self.z2 | other.z2,
            self.z3 | other.z3
        )

    def xor_semantics(self, other: 'Uint256') -> 'Uint256':
        """按位异或操作（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            a ^ b 的新Uint256实例
        """
        return Uint256(
            self.z0 ^ other.z0,
            self.z1 ^ other.z1,
            self.z2 ^ other.z2,
            self.z3 ^ other.z3
        )

    def not_semantics(self) -> 'Uint256':
        """按位非操作（语义建模）。

        Returns:
            ~a 的新Uint256实例
        """
        from z3 import BitVecVal
        return Uint256(
            self.z0 ^ BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            self.z1 ^ BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            self.z2 ^ BitVecVal(0xFFFFFFFFFFFFFFFF, 64),
            self.z3 ^ BitVecVal(0xFFFFFFFFFFFFFFFF, 64)
        )

    def lt_semantics(self, other: 'Uint256'):
        """无符号小于比较（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a < b 则为True
        """
        from z3 import Or, And, ULT

        # 比较从最高位limb开始
        high_lt = ULT(self.z3, other.z3)
        high_eq = self.z3 == other.z3

        mid2_lt = ULT(self.z2, other.z2)
        mid2_eq = self.z2 == other.z2

        mid1_lt = ULT(self.z1, other.z1)
        mid1_eq = self.z1 == other.z1

        low_lt = ULT(self.z0, other.z0)

        result = Or(
            high_lt,
            And(high_eq, mid2_lt),
            And(high_eq, mid2_eq, mid1_lt),
            And(high_eq, mid2_eq, mid1_eq, low_lt)
        )

        return result

    def gt_semantics(self, other: 'Uint256'):
        """无符号大于比较（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a > b 则为True
        """
        return other.lt_semantics(self)

    def eq_semantics(self, other: 'Uint256'):
        """等于比较（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a == b 则为True
        """
        from z3 import And
        return And(
            self.z0 == other.z0,
            self.z1 == other.z1,
            self.z2 == other.z2,
            self.z3 == other.z3
        )

    def iszero_semantics(self):
        """是否为零检查（语义建模）。

        Returns:
            BoolRef：如果 a == 0 则为True
        """
        from z3 import And, BitVecVal
        return And(
            self.z0 == BitVecVal(0, 64),
            self.z1 == BitVecVal(0, 64),
            self.z2 == BitVecVal(0, 64),
            self.z3 == BitVecVal(0, 64)
        )

    def __repr__(self):
        return f"Uint256(z0={self.z0}, z1={self.z1}, z2={self.z2}, z3={self.z3})"

