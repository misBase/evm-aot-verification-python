from z3 import *

P = 2 ** 256


def prove_uint256_sar():
    x0, x1, x2, x3 = BitVecs('x0 x1 x2 x3', 64)
    y0, y1, y2, y3 = BitVecs('y0 y1 y2 y3', 64)

    x_bv = Concat(x3, x2, x1, x0)
    shift = y0
    high_nonzero = Or(y1 != 0, y2 != 0, y3 != 0)
    normal = And(Not(high_nonzero), ULT(shift, BitVecVal(256, 64)))
    overflow = Or(high_nonzero, UGE(shift, BitVecVal(256, 64)))

    z64 = BitVecVal(0, 64)
    w64 = BitVecVal(64, 64)
    ones64 = BitVecVal((1 << 64) - 1, 64)
    zero256 = BitVecVal(0, 256)
    allones = BitVecVal((1 << 256) - 1, 256)
    sign_set = UGE(x3, BitVecVal(1 << 63, 64))

    def go_rsh(n):
        k64 = n - BitVecVal(64, 64)
        k128 = n - BitVecVal(128, 64)
        k192 = n - BitVecVal(192, 64)
        return If(n == 0, x_bv,
               If(UGE(n, BitVecVal(192, 64)),
                  Concat(z64, z64, z64, LShR(x3, k192)),
               If(UGE(n, BitVecVal(128, 64)),
                  Concat(z64,
                         z64,
                         LShR(x3, k128),
                         LShR(x2, k128) | (x3 << (w64 - k128))),
               If(UGE(n, BitVecVal(64, 64)),
                  Concat(z64,
                         LShR(x3, k64),
                         LShR(x2, k64) | (x3 << (w64 - k64)),
                         LShR(x1, k64) | (x2 << (w64 - k64))),
                  Concat(LShR(x3, n),
                         LShR(x2, n) | (x3 << (w64 - n)),
                         LShR(x1, n) | (x2 << (w64 - n)),
                         LShR(x0, n) | (x1 << (w64 - n)))))))

    def go_srsh(n):
        a = ones64 << (w64 - URem(n, w64))
        k64 = n - BitVecVal(64, 64)
        k128 = n - BitVecVal(128, 64)
        k192 = n - BitVecVal(192, 64)
        signed_body = If(n == 0, x_bv,
                     If(UGE(n, BitVecVal(192, 64)),
                        Concat(ones64, ones64, ones64, LShR(x3, k192) | a),
                     If(UGE(n, BitVecVal(128, 64)),
                        Concat(ones64,
                               ones64,
                               LShR(x3, k128) | a,
                               LShR(x2, k128) | (x3 << (w64 - k128))),
                     If(UGE(n, BitVecVal(64, 64)),
                        Concat(ones64,
                               LShR(x3, k64) | a,
                               LShR(x2, k64) | (x3 << (w64 - k64)),
                               LShR(x1, k64) | (x2 << (w64 - k64))),
                        Concat(LShR(x3, n) | a,
                               LShR(x2, n) | (x3 << (w64 - n)),
                               LShR(x1, n) | (x2 << (w64 - n)),
                               LShR(x0, n) | (x1 << (w64 - n)))))))
        return If(sign_set, signed_body, go_rsh(n))

    lhs_normal = go_srsh(shift)
    rhs_normal = x_bv >> ZeroExt(192, shift)

    lhs_overflow = If(sign_set, allones, zero256)
    rhs_overflow = If(sign_set, allones, zero256)

    cases = [
        ('shift == 0', shift == 0),
        ('1 <= shift < 64', And(UGE(shift, BitVecVal(1, 64)), ULT(shift, BitVecVal(64, 64)))),
        ('shift == 64', shift == BitVecVal(64, 64)),
        ('65 <= shift < 128', And(UGE(shift, BitVecVal(65, 64)), ULT(shift, BitVecVal(128, 64)))),
        ('shift == 128', shift == BitVecVal(128, 64)),
        ('129 <= shift < 192', And(UGE(shift, BitVecVal(129, 64)), ULT(shift, BitVecVal(192, 64)))),
        ('shift == 192', shift == BitVecVal(192, 64)),
        ('193 <= shift < 256', And(UGE(shift, BitVecVal(193, 64)), ULT(shift, BitVecVal(256, 64)))),
    ]

    all_ok = True

    s = SolverFor('QF_BV')
    s.set('timeout', 120000)
    s.add(overflow, lhs_overflow != rhs_overflow)
    result = s.check()
    print('case shift overflow: ' + str(result), flush=True)
    if result != unsat:
        all_ok = False

    for name, cond in cases:
        s = SolverFor('QF_BV')
        s.set('timeout', 120000)
        s.add(normal, cond, lhs_normal != rhs_normal)
        result = s.check()
        print('case ' + name + ': ' + str(result), flush=True)
        if result == sat:
            model = s.model()
            print('  x =', [model.eval(v).as_long() for v in (x0, x1, x2, x3)])
            print('  shift =', model.eval(shift).as_long())
            print('  lhs =', model.eval(lhs_normal))
            print('  rhs =', model.eval(rhs_normal))
        if result != unsat:
            all_ok = False

    print('')
    if all_ok:
        print('Verification Passed: four-u64 SRsh matches EVM SAR')
    else:
        print('Verification incomplete')


if __name__ == '__main__':
    prove_uint256_sar()
