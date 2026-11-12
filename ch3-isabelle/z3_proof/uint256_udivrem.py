import random
import sys

from z3 import *

from uint256_udivrem_common import (
    Z256,
    Z64,
    algorithm_quot_rem,
    length_case_condition,
)


def prove_uint256_udivrem():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)
    y0, y1, y2, y3 = BitVecs('y0 y1 y2 y3', 64)
    xlimbs = (x0, x1, x2, x3)
    ylimbs = (y0, y1, y2, y3)
    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(y3, y2, y1, y0)

    all_ok = True
    for d_len in range(1, 5):
        for u_len in range(d_len, 5):
            name = 'd_len=%d, u_len=%d' % (d_len, u_len)
            q_alg, r_alg = algorithm_quot_rem(d_len, u_len, xlimbs, ylimbs)
            q_ref = UDiv(x_bv, y_bv)
            r_ref = URem(x_bv, y_bv)
            cond = length_case_condition(d_len, u_len, xlimbs, ylimbs)

            s = Solver()
            s.set('timeout', 120000)
            s.set('max_memory', 8192)
            s.add(cond, Or(q_alg != q_ref, r_alg != r_ref))
            result = s.check()
            print('case ' + name + ': ' + str(result), flush=True)
            if result == sat:
                m = s.model()
                print('  x =', [m.eval(v) for v in xlimbs])
                print('  y =', [m.eval(v) for v in ylimbs])
                print('  q_alg =', m.eval(q_alg))
                print('  q_ref =', m.eval(q_ref))
                print('  r_alg =', m.eval(r_alg))
                print('  r_ref =', m.eval(r_ref))
                all_ok = False
            elif result != unsat:
                all_ok = False

    print('')
    if all_ok:
        print('Verification Passed: Go udivrem limb algorithm matches 256-bit UDiv/URem')
    else:
        print('Verification incomplete')


def differential_prove_uint256_udivrem(cases=200):
    mask64 = (1 << 64) - 1
    rng = random.Random(0)

    for _ in range(cases):
        d_len = rng.randint(1, 4)
        ylimbs = [0] * 4
        for i in range(d_len - 1):
            ylimbs[i] = rng.getrandbits(64)
        ylimbs[d_len - 1] = rng.randint(1, mask64)

        u_len = rng.randint(d_len, 4)
        xlimbs = [0] * 4
        for i in range(u_len - 1):
            xlimbs[i] = rng.getrandbits(64)
        xlimbs[u_len - 1] = rng.randint(1, mask64)

        x_value = sum(xlimbs[i] << (64 * i) for i in range(4))
        y_value = sum(ylimbs[i] << (64 * i) for i in range(4))
        if x_value < y_value:
            continue

        x_bv = [BitVecVal(v, 64) for v in xlimbs]
        y_bv = [BitVecVal(v, 64) for v in ylimbs]
        q_alg, r_alg = algorithm_quot_rem(d_len, u_len, x_bv, y_bv)
        q_value = simplify(q_alg).as_long()
        r_value = simplify(r_alg).as_long()

        if (q_value, r_value) != divmod(x_value, y_value):
            print('Differential mismatch for d_len=%d, u_len=%d' % (d_len, u_len))
            print('  x =', xlimbs)
            print('  y =', ylimbs)
            print('  algorithm =', q_value, r_value)
            print('  reference =', divmod(x_value, y_value))
            return False

    print('Differential check passed on %d valid limb cases' % cases)
    return True


if __name__ == '__main__':
    if '--differential' in sys.argv:
        differential_prove_uint256_udivrem()
    else:
        prove_uint256_udivrem()
