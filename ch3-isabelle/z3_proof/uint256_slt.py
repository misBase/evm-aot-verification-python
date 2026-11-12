from z3 import *

P = 2 ** 256
H = 2 ** 255


def prove_uint256_slt():
    # Four uint64 words: x = x0 + x1*2^64 + x2*2^128 + x3*2^192.
    ix0, ix1, ix2, ix3 = Ints('ix0 ix1 ix2 ix3')
    iy0, iy1, iy2, iy3 = Ints('iy0 iy1 iy2 iy3')
    limbs = (ix0, ix1, ix2, ix3, iy0, iy1, iy2, iy3)
    bounds = And(*[And(0 <= v, v < 2 ** 64) for v in limbs])

    ni = ix0 + ix1 * 2 ** 64 + ix2 * 2 ** 128 + ix3 * 2 ** 192
    di = iy0 + iy1 * 2 ** 64 + iy2 * 2 ** 128 + iy3 * 2 ** 192

    def signed_val(v):
        return If(v < H, v, v - P)

    def go_sign(v, hi):
        # Go Sign: zero is 0; otherwise the top bit of z3 decides the sign.
        return If(v == 0, 0, If(hi < 2 ** 63, 1, -1))

    def go_slt(n, d):
        ns = go_sign(n, ix3)
        ds = go_sign(d, iy3)
        return If(
            And(ns >= 0, ds < 0),
            BoolVal(False),
            If(And(ns < 0, ds >= 0), BoolVal(True), n < d),
        )

    lhs = go_slt(ni, di)
    rhs = signed_val(ni) < signed_val(di)

    cases = [
        ('x == 0', ni == 0),
        ('x > 0, y == 0', And(signed_val(ni) > 0, di == 0)),
        ('x > 0, y > 0', And(signed_val(ni) > 0, signed_val(di) > 0)),
        ('x > 0, y < 0', And(signed_val(ni) > 0, signed_val(di) < 0)),
        ('x < 0, y == 0', And(signed_val(ni) < 0, di == 0)),
        ('x < 0, y > 0', And(signed_val(ni) < 0, signed_val(di) > 0)),
        ('x < 0, y < 0', And(signed_val(ni) < 0, signed_val(di) < 0)),
    ]

    all_ok = True
    for name, cond in cases:
        s = Solver()
        s.set('timeout', 300000)
        s.add(bounds, cond, lhs != rhs)
        result = s.check()
        print('case ' + name + ': ' + str(result), flush=True)
        if result == sat:
            model = s.model()
            print('  x =', [model.eval(v) for v in (ix0, ix1, ix2, ix3)])
            print('  y =', [model.eval(v) for v in (iy0, iy1, iy2, iy3)])
            print('  lhs =', model.eval(lhs))
            print('  rhs =', model.eval(rhs))
        if result != unsat:
            all_ok = False

    print('')
    if all_ok:
        print('Verification Passed: four-u64 SLT matches EVM signed less-than')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_slt()
