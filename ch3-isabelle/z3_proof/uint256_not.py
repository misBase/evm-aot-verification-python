from z3 import *


def prove_uint256_not():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)

    x_bv = Concat(x3, x2, x1, x0)

    lhs = Concat(~x3, ~x2, ~x1, ~x0)
    rhs = ~x_bv

    s = SolverFor('QF_BV')
    s.set('timeout', 120000)
    s.add(lhs != rhs)
    result = s.check()
    print('case all inputs: ' + str(result), flush=True)

    if result == sat:
        model = s.model()
        print('  x =', [model.eval(v).as_long() for v in (x0, x1, x2, x3)])
        print('  lhs =', model.eval(lhs))
        print('  rhs =', model.eval(rhs))

    print('')
    if result == unsat:
        print('Verification Passed: four-u64 Not matches EVM NOT')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_not()
