from z3 import *

Z64 = BitVecVal(0, 64)
ONE64 = BitVecVal(1, 64)
MAX64 = BitVecVal((1 << 64) - 1, 64)
W64 = BitVecVal(64, 64)
Z256 = BitVecVal(0, 256)
ONE256 = BitVecVal(1, 256)


def bitlen8(x):
    return If(x == BitVecVal(0, 8), Z64,
           If(UGE(x, BitVecVal(128, 8)), BitVecVal(8, 64),
           If(UGE(x, BitVecVal(64, 8)), BitVecVal(7, 64),
           If(UGE(x, BitVecVal(32, 8)), BitVecVal(6, 64),
           If(UGE(x, BitVecVal(16, 8)), BitVecVal(5, 64),
           If(UGE(x, BitVecVal(8, 8)), BitVecVal(4, 64),
           If(UGE(x, BitVecVal(4, 8)), BitVecVal(3, 64),
           If(UGE(x, BitVecVal(2, 8)), BitVecVal(2, 64),
           BitVecVal(1, 64)))))))))


def bitlen16(x):
    hi = Extract(15, 8, x)
    lo = Extract(7, 0, x)
    return If(hi != BitVecVal(0, 8),
              BitVecVal(8, 64) + bitlen8(hi),
              bitlen8(lo))


def bitlen32(x):
    hi = Extract(31, 16, x)
    lo = Extract(15, 0, x)
    return If(hi != BitVecVal(0, 16),
              BitVecVal(16, 64) + bitlen16(hi),
              bitlen16(lo))


def bitlen64(x):
    hi = Extract(63, 32, x)
    lo = Extract(31, 0, x)
    return If(hi != BitVecVal(0, 32),
              BitVecVal(32, 64) + bitlen32(hi),
              bitlen32(lo))


def leading_zeros64(x):
    return If(x == Z64, W64, W64 - bitlen64(x))


def mul64(x, y):
    p = ZeroExt(64, x) * ZeroExt(64, y)
    return Extract(127, 64, p), Extract(63, 0, p)


def add64_carry(a, b, carry):
    s = ZeroExt(1, a) + ZeroExt(1, b) + ZeroExt(1, carry)
    return Extract(63, 0, s), ZeroExt(63, Extract(64, 64, s))


def sub64_borrow(a, b, borrow):
    d = ZeroExt(1, a) - ZeroExt(1, b) - ZeroExt(1, borrow)
    return Extract(63, 0, d), ZeroExt(63, Extract(64, 64, d))


def reciprocal2by1(d):
    # Go bits.Div64(^d, ^uint64(0), d), modelled as 128-by-64 division.
    numerator = Concat(~d, MAX64)
    return Extract(63, 0, UDiv(numerator, ZeroExt(64, d)))


def udivrem2by1(uh, ul, d, reciprocal):
    qh, ql = mul64(reciprocal, uh)
    ql, carry = add64_carry(ql, ul, Z64)
    qh, _ = add64_carry(qh, uh, carry)
    qh = qh + ONE64

    r = ul - qh * d
    cond1 = UGT(r, ql)
    qh = If(cond1, qh - ONE64, qh)
    r = If(cond1, r + d, r)

    cond2 = UGE(r, d)
    qh = If(cond2, qh + ONE64, qh)
    r = If(cond2, r - d, r)
    return qh, r


def sub_mul_to(u, d, j, multiplier):
    # Fixed-length model of Go subMulTo(u[j:], d, multiplier).
    arr = list(u)
    borrow = Z64
    for i in range(len(d)):
        x_i = arr[j + i]
        y_i = d[i]
        s, c1 = sub64_borrow(x_i, borrow, Z64)
        ph, pl = mul64(y_i, multiplier)
        t, c2 = sub64_borrow(s, pl, Z64)
        arr[j + i] = t
        borrow = ph + c1 + c2
    return arr, borrow


def add_to(u, d, j):
    arr = list(u)
    carry = Z64
    for i in range(len(d)):
        s, carry = add64_carry(arr[j + i], d[i], carry)
        arr[j + i] = s
    return arr, carry


def udivrem_knuth(u_len, d_len, un, dn):
    quot = [Z64] * (u_len - d_len + 1)
    u = list(un)
    dh = dn[d_len - 1]
    dl = dn[d_len - 2]
    reciprocal = reciprocal2by1(dh)

    for j in range(u_len - d_len, -1, -1):
        u2 = u[j + d_len]
        u1 = u[j + d_len - 1]
        u0 = u[j + d_len - 2]

        qhat_else, rhat = udivrem2by1(u2, u1, dh, reciprocal)
        ph, pl = mul64(qhat_else, dl)
        qhat = If(UGE(u2, dh), MAX64,
                  If(Or(UGT(ph, rhat), And(ph == rhat, UGT(pl, u0))),
                     qhat_else - ONE64,
                     qhat_else))

        u_after_sub, borrow = sub_mul_to(u, dn, j, qhat)
        u_after_sub[j + d_len] = u2 - borrow

        need_adjust = ULT(u2, borrow)
        qhat = If(need_adjust, qhat - ONE64, qhat)

        u_added, carry = add_to(u_after_sub, dn, j)
        u = [Z64] * len(u_after_sub)
        for i in range(len(u_after_sub)):
            if j <= i < j + d_len:
                u[i] = If(need_adjust, u_added[i], u_after_sub[i])
            elif i == j + d_len:
                u[i] = If(need_adjust, u_after_sub[i] + carry, u_after_sub[i])
            else:
                u[i] = u_after_sub[i]

        quot[j] = qhat

    return quot, u


def udivrem_by1(u_len, un, d):
    quot = [Z64] * u_len
    reciprocal = reciprocal2by1(d)
    rem = un[u_len]

    for j in range(u_len - 1, -1, -1):
        qj, rem = udivrem2by1(rem, un[j], d, reciprocal)
        quot[j] = qj

    return quot, rem


def normalize_d(d_len, dlimbs, shift):
    dn = [Z64] * d_len
    dn[0] = dlimbs[0] << shift
    for i in range(1, d_len):
        dn[i] = (dlimbs[i] << shift) | LShR(dlimbs[i - 1], W64 - shift)
    return dn


def normalize_u(u_len, ulimbs, shift):
    un = [Z64] * (u_len + 1)
    un[u_len] = LShR(ulimbs[u_len - 1], W64 - shift)
    for i in range(u_len - 1, 0, -1):
        un[i] = (ulimbs[i] << shift) | LShR(ulimbs[i - 1], W64 - shift)
    un[0] = ulimbs[0] << shift
    return un


def denormalize_rem(d_len, un, shift):
    rem = [Z64] * 4
    for i in range(d_len):
        if i < d_len - 1:
            rem[i] = LShR(un[i], shift) | (un[i + 1] << (W64 - shift))
        else:
            rem[i] = LShR(un[i], shift)
    return rem


def algorithm_quot_rem(d_len, u_len, xlimbs, ylimbs):
    shift = leading_zeros64(ylimbs[d_len - 1])
    dn = normalize_d(d_len, ylimbs, shift)
    un = normalize_u(u_len, xlimbs, shift)

    if d_len == 1:
        quot, r = udivrem_by1(u_len, un, dn[0])
        rem = [Z64] * 4
        rem[0] = LShR(r, shift)
    else:
        quot, un_after = udivrem_knuth(u_len, d_len, un, dn)
        rem = denormalize_rem(d_len, un_after, shift)

    q4 = [Z64] * 4
    for i in range(min(u_len - d_len + 1, 4)):
        q4[i] = quot[i]

    return (Concat(q4[3], q4[2], q4[1], q4[0]),
            Concat(rem[3], rem[2], rem[1], rem[0]))


def length_case_condition(d_len, u_len, xlimbs, ylimbs):
    x0, x1, x2, x3 = xlimbs
    y0, y1, y2, y3 = ylimbs
    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(y3, y2, y1, y0)

    conds = [UGE(x_bv, y_bv), y_bv != Z256]

    if u_len == 1:
        conds.append(And(x1 == Z64, x2 == Z64, x3 == Z64))
    elif u_len == 2:
        conds.append(And(x1 != Z64, x2 == Z64, x3 == Z64))
    elif u_len == 3:
        conds.append(And(x2 != Z64, x3 == Z64))
    else:
        conds.append(x3 != Z64)

    if d_len == 1:
        conds.append(And(y0 != Z64, y1 == Z64, y2 == Z64, y3 == Z64))
    elif d_len == 2:
        conds.append(And(y1 != Z64, y2 == Z64, y3 == Z64))
    elif d_len == 3:
        conds.append(And(y2 != Z64, y3 == Z64))
    else:
        conds.append(y3 != Z64)

    return And(*conds)


def go_div(d_len, u_len, xlimbs, ylimbs):
    x0, x1, x2, x3 = xlimbs
    y0 = ylimbs[0]
    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(ylimbs[3], ylimbs[2], ylimbs[1], y0)
    y0_alg = If(y_bv == Z256, ONE64, y0)
    q_alg, _ = algorithm_quot_rem(
        d_len, u_len, xlimbs, (y0_alg, ylimbs[1], ylimbs[2], ylimbs[3])
    )
    x_is_u64 = And(x1 == Z64, x2 == Z64, x3 == Z64)

    return If(Or(y_bv == Z256, ULT(x_bv, y_bv)), Z256,
              If(x_bv == y_bv, ONE256,
              If(x_is_u64, Concat(Z64, Z64, Z64, UDiv(x0, y0)),
                 q_alg)))


def go_mod(d_len, u_len, xlimbs, ylimbs):
    x0, x1, x2, x3 = xlimbs
    y0 = ylimbs[0]
    x_bv = Concat(x3, x2, x1, x0)
    y_bv = Concat(ylimbs[3], ylimbs[2], ylimbs[1], y0)
    y0_alg = If(y_bv == Z256, ONE64, y0)
    _, r_alg = algorithm_quot_rem(
        d_len, u_len, xlimbs, (y0_alg, ylimbs[1], ylimbs[2], ylimbs[3])
    )
    x_is_u64 = And(x1 == Z64, x2 == Z64, x3 == Z64)

    return If(Or(y_bv == Z256, x_bv == y_bv), Z256,
              If(ULT(x_bv, y_bv), x_bv,
              If(x_is_u64, Concat(Z64, Z64, Z64, URem(x0, y0)),
                 r_alg)))
