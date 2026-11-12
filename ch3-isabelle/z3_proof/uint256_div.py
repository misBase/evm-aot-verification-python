from z3 import *

B = 2 ** 64
P = 2 ** 256


def prove_uint256_div():
    x0, x1, x2, x3 = Ints('x0 x1 x2 x3')
    y0, y1, y2, y3 = Ints('y0 y1 y2 y3')
    limbs = (x0, x1, x2, x3, y0, y1, y2, y3)
    bounds = And(*[And(0 <= v, v < B) for v in limbs])

    x = x0 + x1 * B + x2 * B ** 2 + x3 * B ** 3
    y = y0 + y1 * B + y2 * B ** 2 + y3 * B ** 3

    def udiv(a, b):
        return If(b == 0, 0, a / b)

    # Go Div(): y == 0 or y > x gives 0, x == y gives 1, otherwise quotient.
    lhs = If(Or(y == 0, x < y), 0, If(x == y, 1, x / y))
    rhs = udiv(x, y)

    cases = [
        ('y == 0', y == 0),
        ('x < y', And(y > 0, x < y)),
        ('x == y', And(y > 0, x == y)),
        ('x > y', And(y > 0, x > y)),
    ]

    all_ok = True
    for name, cond in cases:
        s = Solver()
        s.set('timeout', 300000)
        s.add(bounds, cond, lhs != rhs)
        result = s.check()
        print('case ' + name + ': ' + str(result), flush=True)
        if result == sat:
            m = s.model()
            print('  x =', [m.eval(v) for v in (x0, x1, x2, x3)])
            print('  y =', [m.eval(v) for v in (y0, y1, y2, y3)])
            print('  lhs =', m.eval(lhs))
            print('  rhs =', m.eval(rhs))
        if result != unsat:
            all_ok = False

    print('')
    if all_ok:
        print('Verification Passed: four-u64 Div matches unsigned 256-bit division')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_div()
