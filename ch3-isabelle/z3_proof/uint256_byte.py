from z3 import *

P = 2 ** 256


def prove_uint256_byte():
    # Four uint64 words: x = x0 + x1*2^64 + x2*2^128 + x3*2^192.
    ix0, ix1, ix2, ix3 = Ints('ix0 ix1 ix2 ix3')
    iy0, iy1, iy2, iy3 = Ints('iy0 iy1 iy2 iy3')
    limbs = (ix0, ix1, ix2, ix3, iy0, iy1, iy2, iy3)
    bounds = And(*[And(0 <= v, v < 2 ** 64) for v in limbs])

    xi = ix0 + ix1 * 2 ** 64 + ix2 * 2 ** 128 + ix3 * 2 ** 192
    yi = iy0 + iy1 * 2 ** 64 + iy2 * 2 ** 128 + iy3 * 2 ** 192

    # Go Byte() first calls Uint64WithOverflow: index is z0 and overflow
    # means any of the high words is nonzero.
    overflow = yi >= 2 ** 64
    index = iy0

    def word_from_index(idx):
        word_index = idx / 8
        return If(word_index == 0, ix0,
               If(word_index == 1, ix1,
               If(word_index == 2, ix2,
               If(word_index == 3, ix3, 0))))

    def umod(a, b):
        return a - (a / b) * b

    def implementation_byte(idx):
        word_index = idx / 8
        offset = (idx - word_index * 8) * 8
        word = word_from_index(idx)
        return umod(word / (2 ** (56 - offset)), 256)

    def reference_byte(value, idx):
        # EVM BYTE(i, x) is byte i from the most significant end.
        return umod(value / (2 ** (8 * (31 - idx))), 256)

    lhs = If(Or(overflow, index >= 32), 0, implementation_byte(index))
    rhs = If(Or(overflow, yi >= 32), 0, reference_byte(xi, yi))

    cases = [
        ('overflow index', yi >= 2 ** 64),
        ('32 <= index < 2^64', And(yi < 2 ** 64, yi >= 32)),
        ('0 <= index < 8', And(yi < 8, yi >= 0)),
        ('8 <= index < 16', And(yi < 16, yi >= 8)),
        ('16 <= index < 24', And(yi < 24, yi >= 16)),
        ('24 <= index < 32', And(yi < 32, yi >= 24)),
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
        print('Verification Passed: four-u64 Byte matches EVM byte extraction')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_byte()
