from z3 import *


def prove_uint256_gt():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)
    y0, y1, y2, y3 = BitVecs('y0 y1 y2 y3', 64)

    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(y3, y2, y1, y0)

    def sub64_borrow(a, b, carry):
        diff = a - b - carry
        borrow = LShR((~a & b) | (~(a ^ b) & diff), BitVecVal(63, 64))
        return diff, borrow

    def go_lt(a0, a1, a2, a3, b0, b1, b2, b3):
        _, c0 = sub64_borrow(a0, b0, BitVecVal(0, 64))
        _, c1 = sub64_borrow(a1, b1, c0)
        _, c2 = sub64_borrow(a2, b2, c1)
        _, c3 = sub64_borrow(a3, b3, c2)
        return c3 != BitVecVal(0, 64)

    lhs = go_lt(y0, y1, y2, y3, x0, x1, x2, x3)
    rhs = UGT(x_bv, y_bv)

    s = SolverFor('QF_BV')
    s.set('timeout', 120000)
    s.add(lhs != rhs)
    result = s.check()
    print('case all inputs: ' + str(result), flush=True)

    if result == sat:
        model = s.model()
        print('  x =', [model.eval(v).as_long() for v in (x0, x1, x2, x3)])
        print('  y =', [model.eval(v).as_long() for v in (y0, y1, y2, y3)])
        print('  lhs =', model.eval(lhs))
        print('  rhs =', model.eval(rhs))

    print('')
    if result == unsat:
        print('Verification Passed: four-u64 Gt matches EVM GT')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_gt()
