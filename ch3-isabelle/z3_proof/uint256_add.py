from z3 import *

P = 2 ** 256
B = 2 ** 64


def prove_uint256_add():
    x0, x1, x2, x3 = Ints('x0 x1 x2 x3')
    y0, y1, y2, y3 = Ints('y0 y1 y2 y3')
    limbs = (x0, x1, x2, x3, y0, y1, y2, y3)
    bounds = And(*[And(0 <= v, v < B) for v in limbs])

    xi = x0 + x1 * B + x2 * B ** 2 + x3 * B ** 3
    yi = y0 + y1 * B + y2 * B ** 2 + y3 * B ** 3

    def umod(a, b):
        return a - (a / b) * b

    r0 = umod(x0 + y0, B)
    c0 = (x0 + y0) / B
    r1 = umod(x1 + y1 + c0, B)
    c1 = (x1 + y1 + c0) / B
    r2 = umod(x2 + y2 + c1, B)
    c2 = (x2 + y2 + c1) / B
    r3 = umod(x3 + y3 + c2, B)

    lhs = r0 + r1 * B + r2 * B ** 2 + r3 * B ** 3
    rhs = umod(xi + yi, P)

    s = Solver()
    s.set('timeout', 300000)
    s.add(bounds, lhs != rhs)
    result = s.check()
    if result == unsat:
        print('Verification Passed: four-u64 Add matches modular 256-bit addition')
    elif result == sat:
        m = s.model()
        print('Counterexample Found:')
        print('  x =', [m.eval(v) for v in (x0, x1, x2, x3)])
        print('  y =', [m.eval(v) for v in (y0, y1, y2, y3)])
    else:
        print('Unknown result')


if __name__ == '__main__':
    prove_uint256_add()
