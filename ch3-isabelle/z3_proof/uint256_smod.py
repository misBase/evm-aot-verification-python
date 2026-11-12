from z3 import *

P = 2 ** 256
H = 2 ** 255


def prove_uint256_smod():
    # Four uint64 words: x = x0 + x1*2^64 + x2*2^128 + x3*2^192.
    ix0, ix1, ix2, ix3 = Ints('ix0 ix1 ix2 ix3')
    iy0, iy1, iy2, iy3 = Ints('iy0 iy1 iy2 iy3')
    limbs = (ix0, ix1, ix2, ix3, iy0, iy1, iy2, iy3)
    bounds = And(*[And(0 <= v, v < 2 ** 64) for v in limbs])

    ni = ix0 + ix1 * 2 ** 64 + ix2 * 2 ** 128 + ix3 * 2 ** 192
    di = iy0 + iy1 * 2 ** 64 + iy2 * 2 ** 128 + iy3 * 2 ** 192

    def signed_val(v):
        return If(v < H, v, v - P)

    def negw(v):
        return If(v == 0, 0, P - v)

    def umod(a, b):
        return If(b == 0, 0, a - (a / b) * b)

    def go_sign(v, hi):
        # Go Sign: zero is 0; otherwise the top bit of z3 decides the sign.
        return If(v == 0, 0, If(hi < 2 ** 63, 1, -1))

    def go_smod(n, d):
        xs = go_sign(n, ix3)
        ys = go_sign(d, iy3)
        abs_n = If(xs == -1, negw(n), n)
        abs_d = If(ys == -1, negw(d), d)
        r = umod(abs_n, abs_d)
        return If(xs == -1, negw(r), r)

    def trunc_div(a, b):
        return If(
            a >= 0,
            If(b > 0, a / b, -(a / (-b))),
            If(b > 0, -((-a) / b), (-a) / (-b)),
        )

    def trunc_rem(a, b):
        return a - trunc_div(a, b) * b

    def reference_smod(n, d):
        sn = signed_val(n)
        sd = signed_val(d)
        r = If(sd == 0, 0, trunc_rem(sn, sd))
        return If(r < 0, r + P, r)

    lhs = go_smod(ni, di)
    rhs = reference_smod(ni, di)

    cases = [
        ('d == 0', di == 0),
        ('x == 0, d != 0', And(ni == 0, di != 0)),
        ('x > 0, d > 0', And(signed_val(ni) > 0, signed_val(di) > 0)),
        ('x > 0, d < 0', And(signed_val(ni) > 0, signed_val(di) < 0)),
        ('x < 0, d > 0', And(signed_val(ni) < 0, signed_val(di) > 0)),
        ('x < 0, d < 0', And(signed_val(ni) < 0, signed_val(di) < 0)),
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
        print('Verification Passed: four-u64 SMod matches EVM signed modulo')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_smod()
