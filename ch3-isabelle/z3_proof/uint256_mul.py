from z3 import *

P = 2 ** 256
B = 2 ** 64


def prove_uint256_mul():
    # Four uint64 limbs.
    x0, x1, x2, x3 = Ints('x0 x1 x2 x3')
    y0, y1, y2, y3 = Ints('y0 y1 y2 y3')
    limbs = (x0, x1, x2, x3, y0, y1, y2, y3)
    bounds = And(*[And(0 <= v, v < B) for v in limbs])

    xi = x0 + x1 * B + x2 * B ** 2 + x3 * B ** 3
    yi = y0 + y1 * B + y2 * B ** 2 + y3 * B ** 3

    def umod(a, b):
        return a - (a / b) * b

    # Schoolbook 64-bit limb multiplication for the low 256 bits.
    r0 = umod(x0 * y0, B)
    c0 = (x0 * y0) / B
    r1 = umod(x0 * y1 + x1 * y0 + c0, B)
    c1 = (x0 * y1 + x1 * y0 + c0) / B
    r2 = umod(x0 * y2 + x1 * y1 + x2 * y0 + c1, B)
    c2 = (x0 * y2 + x1 * y1 + x2 * y0 + c1) / B
    r3 = umod(x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + c2, B)

    lhs = r0 + r1 * B + r2 * B ** 2 + r3 * B ** 3
    rhs = umod(xi * yi, P)

    s = Solver()
    s.set('timeout', 300000)
    s.add(bounds, lhs != rhs)
    result = s.check()

    if result == unsat:
        print('Verification Passed: four-u64 Mul matches low 256 bits of multiplication')
    elif result == sat:
        model = s.model()
        print('Counterexample Found:')
        print('  x =', [model.eval(v) for v in (x0, x1, x2, x3)])
        print('  y =', [model.eval(v) for v in (y0, y1, y2, y3)])
        print('  lhs =', model.eval(lhs))
        print('  rhs =', model.eval(rhs))
    else:
        print('Unknown result')


if __name__ == '__main__':
    prove_uint256_mul()
