from z3 import *

P = 2 ** 256
B = 2 ** 64


def prove_uint256_sub():
    x0, x1, x2, x3 = Ints('x0 x1 x2 x3')
    y0, y1, y2, y3 = Ints('y0 y1 y2 y3')
    limbs = (x0, x1, x2, x3, y0, y1, y2, y3)
    bounds = And(*[And(0 <= v, v < B) for v in limbs])

    xi = x0 + x1 * B + x2 * B ** 2 + x3 * B ** 3
    yi = y0 + y1 * B + y2 * B ** 2 + y3 * B ** 3

    def sub64(a, b, borrow):
        diff = a - b - borrow
        return If(diff >= 0, diff, diff + B), If(diff >= 0, 0, 1)

    d0, b0 = sub64(x0, y0, 0)
    d1, b1 = sub64(x1, y1, b0)
    d2, b2 = sub64(x2, y2, b1)
    d3, _ = sub64(x3, y3, b2)

    lhs = d0 + d1 * B + d2 * B ** 2 + d3 * B ** 3
    rhs = If(xi >= yi, xi - yi, xi - yi + P)

    s = Solver()
    s.set('timeout', 300000)
    s.add(bounds, lhs != rhs)
    result = s.check()
    if result == unsat:
        print('Verification Passed: four-u64 Sub matches modular 256-bit subtraction')
    elif result == sat:
        m = s.model()
        print('Counterexample Found:')
        print('  x =', [m.eval(v) for v in (x0, x1, x2, x3)])
        print('  y =', [m.eval(v) for v in (y0, y1, y2, y3)])
    else:
        print('Unknown result')


if __name__ == '__main__':
    prove_uint256_sub()
