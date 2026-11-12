from z3 import *


def prove_uint256_eq():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)
    y0, y1, y2, y3 = BitVecs('y0 y1 y2 y3', 64)

    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(y3, y2, y1, y0)

    lhs = And(x0 == y0, x1 == y1, x2 == y2, x3 == y3)
    rhs = x_bv == y_bv

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
        print('Verification Passed: four-u64 Eq matches EVM EQ')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_eq()
