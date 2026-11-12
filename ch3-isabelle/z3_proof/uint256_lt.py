from z3 import *


def prove_uint256_lt():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)
    y0, y1, y2, y3 = BitVecs('y0 y1 y2 y3', 64)

    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(y3, y2, y1, y0)

    def sub64_borrow(a, b, carry):
        diff = a - b - carry
        borrow = LShR((~a & b) | (~(a ^ b) & diff), BitVecVal(63, 64))
        return diff, borrow

    def go_lt():
        _, b0 = sub64_borrow(x0, y0, BitVecVal(0, 64))
        _, b1 = sub64_borrow(x1, y1, b0)
        _, b2 = sub64_borrow(x2, y2, b1)
        _, b3 = sub64_borrow(x3, y3, b2)
        return b3 != BitVecVal(0, 64)

    lhs = go_lt()
    rhs = ULT(x_bv, y_bv)

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
        print('Verification Passed: four-u64 Lt matches EVM LT')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_lt()
