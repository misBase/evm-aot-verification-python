"""
Uint256：将256位无符号整数表示为4x64位limb。

本模块提供在验证系统中处理256位值的实用工具。
"""

from z3 import BitVec, BitVecVal, Concat, Extract, ZeroExt


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

    @staticmethod
    def mul_codegen_order(p: 'Uint256', q: 'Uint256') -> 'Uint256':
        """(p * q) mod 2^256 built exactly as the AOT compiler compileEVMMul does.

        compileEVMMul multiplies p = the SECOND stack operand by q = the top,
        adding each partial product's `z` term before the running carry (the
        raw add/adc order; see x86_64/summaries/mul_proof.py). The value equals
        holiman Mul (multiplication mod 2^256 commutes); building the same term
        shape lets the block proof compare MUL results syntactically instead
        of re-proving 256-bit commutativity, which bit-blasting cannot do.
        User-approved modelling alignment (2026-09-27).
        """
        zero_64 = BitVecVal(0, 64)
        zero_carry = BitVecVal(0, 1)

        def mul64(x, y):
            product = ZeroExt(64, x) * ZeroExt(64, y)
            return Extract(127, 64, product), Extract(63, 0, product)

        def add64(x, y, carry=zero_carry):
            total = (Concat(BitVecVal(0, 1), x) + Concat(BitVecVal(0, 1), y)
                     + Concat(BitVecVal(0, 64), carry))
            return Extract(63, 0, total), Extract(64, 64, total)

        def hop(z, x, y):
            hi, lo = mul64(x, y)
            lo, carry = add64(lo, z)
            hi, _ = add64(hi, zero_64, carry)
            return hi, lo

        def step_x86_order(z, x, y, carry):
            hi, lo = mul64(x, y)
            lo, bit = add64(lo, z)
            hi, _ = add64(hi, zero_64, bit)
            lo, bit = add64(lo, carry)
            hi, _ = add64(hi, zero_64, bit)
            return hi, lo

        p0, p1, p2, p3 = p.z0, p.z1, p.z2, p.z3
        q0, q1, q2, q3 = q.z0, q.z1, q.z2, q.z3
        carry0, z0 = mul64(p0, q0)
        carry0, res1 = hop(carry0, p1, q0)
        carry0, res2 = hop(carry0, p2, q0)
        _, res3 = hop(carry0, p3, q0)
        carry1, z1 = hop(res1, p0, q1)
        carry1, res2 = step_x86_order(res2, p1, q1, carry1)
        _, res3 = step_x86_order(res3, p2, q1, carry1)
        carry2, z2 = hop(res2, p0, q2)
        _, res3 = step_x86_order(res3, p1, q2, carry2)
        _, z3 = hop(res3, p0, q3)
        return Uint256(z0, z1, z2, z3)

    def mul_semantics(self, other: 'Uint256') -> 'Uint256':
        """将两个Uint256值相乘（语义建模）。

        计算 (a * b) mod 2^256。
        按 holiman/uint256.Int.Mul 的 4x64 limb 算法建模。

        Args:
            other: 要相乘的另一个Uint256值

        Returns:
            表示积(a * b) mod 2^256的新Uint256实例
        """
        zero_64 = BitVecVal(0, 64)
        zero_carry = BitVecVal(0, 1)

        def mul64(x, y):
            product = ZeroExt(64, x) * ZeroExt(64, y)
            return Extract(127, 64, product), Extract(63, 0, product)

        def add64(x, y, carry=zero_carry):
            total = (
                Concat(BitVecVal(0, 1), x) +
                Concat(BitVecVal(0, 1), y) +
                Concat(BitVecVal(0, 64), carry)
            )
            return Extract(63, 0, total), Extract(64, 64, total)

        def umul_hop(z, x, y):
            hi, lo = mul64(x, y)
            lo, carry = add64(lo, z)
            hi, _ = add64(hi, zero_64, carry)
            return hi, lo

        def umul_step(z, x, y, carry):
            hi, lo = mul64(x, y)
            lo, carry_bit = add64(lo, carry)
            hi, _ = add64(hi, zero_64, carry_bit)
            lo, carry_bit = add64(lo, z)
            hi, _ = add64(hi, zero_64, carry_bit)
            return hi, lo

        x0, x1, x2, x3 = self.z0, self.z1, self.z2, self.z3
        y0, y1, y2, y3 = other.z0, other.z1, other.z2, other.z3

        carry0, z0 = mul64(x0, y0)
        carry0, res1 = umul_hop(carry0, x1, y0)
        carry0, res2 = umul_hop(carry0, x2, y0)

        carry1, z1 = umul_hop(res1, x0, y1)
        carry1, res2 = umul_step(res2, x1, y1, carry1)

        carry2, z2 = umul_hop(res2, x0, y2)

        z3 = (
            x3 * y0 +
            x2 * y1 +
            x0 * y3 +
            x1 * y2 +
            carry0 +
            carry1 +
            carry2
        )

        return Uint256(z0, z1, z2, z3)

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

        对齐 github.com/holiman/uint256 v1.3.2 的 Int.Lt：
        从最低 limb 开始做 z - x 的 Sub64 借位链，最终借位非零
        当且仅当 self < other。
        即 z < x <=> z - x < 0，也就是 subtraction overflows。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a < b 则为True
        """
        borrow = BitVecVal(0, 1)
        for z_limb, x_limb in (
            (self.z0, other.z0),
            (self.z1, other.z1),
            (self.z2, other.z2),
            (self.z3, other.z3),
        ):
            diff_ext = (
                Concat(BitVecVal(0, 1), z_limb)
                - Concat(BitVecVal(0, 1), x_limb)
                - Concat(BitVecVal(0, 64), borrow)
            )
            borrow = Extract(64, 64, diff_ext)

        return borrow != BitVecVal(0, 1)

    def gt_semantics(self, other: 'Uint256'):
        """无符号大于比较（语义建模）。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a > b 则为True
        """
        return other.lt_semantics(self)

    def slt_semantics(self, other: 'Uint256'):
        """有符号小于比较（语义建模）。

        对齐 github.com/holiman/uint256 v1.3.2 的 Int.Slt：
        符号不同则负数更小，符号相同则复用 Int.Lt。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a < b（按二补码有符号解释）则为True
        """
        from z3 import And, Not, Or

        self_negative = Extract(63, 63, self.z3) == BitVecVal(1, 1)
        other_negative = Extract(63, 63, other.z3) == BitVecVal(1, 1)
        same_sign = self_negative == other_negative

        return Or(
            And(self_negative, Not(other_negative)),
            And(same_sign, self.lt_semantics(other)),
        )

    def sgt_semantics(self, other: 'Uint256'):
        """有符号大于比较（语义建模）。

        对齐 github.com/holiman/uint256 v1.3.2 的 Int.Sgt：
        符号不同则非负数更大，符号相同则复用 Int.Gt。

        Args:
            other: 另一个Uint256值

        Returns:
            BoolRef：如果 a > b（按二补码有符号解释）则为True
        """
        from z3 import And, Not, Or

        self_negative = Extract(63, 63, self.z3) == BitVecVal(1, 1)
        other_negative = Extract(63, 63, other.z3) == BitVecVal(1, 1)
        same_sign = self_negative == other_negative

        return Or(
            And(Not(self_negative), other_negative),
            And(same_sign, self.gt_semantics(other)),
        )

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
