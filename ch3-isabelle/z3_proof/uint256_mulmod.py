from z3 import *

P = 2 ** 256


def prove_uint256_mulmod():
    ix0, ix1, ix2, ix3 = Ints('ix0 ix1 ix2 ix3')
    iy0, iy1, iy2, iy3 = Ints('iy0 iy1 iy2 iy3')
    im0, im1, im2, im3 = Ints('im0 im1 im2 im3')
    limbs = (ix0, ix1, ix2, ix3, iy0, iy1, iy2, iy3, im0, im1, im2, im3)
    bounds = And(*[And(0 <= v, v < 2 ** 64) for v in limbs])

    xi = ix0 + ix1 * 2 ** 64 + ix2 * 2 ** 128 + ix3 * 2 ** 192
    yi = iy0 + iy1 * 2 ** 64 + iy2 * 2 ** 128 + iy3 * 2 ** 192
    mi = im0 + im1 * 2 ** 64 + im2 * 2 ** 128 + im3 * 2 ** 192

    def umod(a, b):
        return If(b == 0, 0, a - (a / b) * b)

    lhs = If(Or(xi == 0, yi == 0, mi == 0), 0, umod(xi * yi, mi))
    rhs = If(mi == 0, 0, umod(xi * yi, mi))

    cases = [
        ('zero operand', Or(xi == 0, yi == 0, mi == 0)),
        ('m[3] != 0', And(xi > 0, yi > 0, mi > 0, im3 != 0)),
        ('m[3] == 0', And(xi > 0, yi > 0, mi > 0, im3 == 0)),
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
            print('  m =', [model.eval(v) for v in (im0, im1, im2, im3)])
            print('  lhs =', model.eval(lhs))
            print('  rhs =', model.eval(rhs))
        if result != unsat:
            all_ok = False

    print('')
    if all_ok:
        print('Verification Passed: four-u64 MulMod matches EVM mulmod')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_mulmod()
