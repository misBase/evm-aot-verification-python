theory uint512
  imports
    EVMCommType
    uint256
begin

record uint512 =
  p0 :: "u64"
  p1 :: "u64" 
  p2 :: "u64"
  p3 :: "u64"
  p4 :: "u64"
  p5 :: "u64"
  p6 :: "u64"
  p7 :: "u64"

definition uint512_zero :: "uint512" where
  "uint512_zero \<equiv> \<lparr> p0 = 0, p1 = 0, p2 = 0, p3 = 0, p4 = 0, p5 = 0, p6 = 0, p7 = 0 \<rparr>"

definition extract_low256 :: "uint512 \<Rightarrow> uint256" where
"extract_low256 p = \<lparr> z0 = p0 p, z1 = p1 p, z2 = p2 p, z3 = p3 p \<rparr>"

definition extract_high256 :: "uint512 \<Rightarrow> uint256" where  
"extract_high256 p = \<lparr> z0 = p4 p, z1 = p5 p, z2 = p6 p, z3 = p7 p \<rparr>"

definition IsZero_high256 :: "uint512 \<Rightarrow> bool" where
"IsZero_high256 p \<equiv> extract_high256 p = uint256_zero"

definition umul :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint512" where
"umul x y = (
  let 
    (carry, res0) = mul64 (z0 x) (z0 y);
    (carry, res1) = umulHop carry (z1 x) (z0 y);
    (carry, res2) = umulHop carry (z2 x) (z0 y);
    (carry4, res3) = umulHop carry (z3 x) (z0 y);
    (carry, res1') = umulHop res1 (z0 x) (z1 y);
    (carry, res2') = umulStep res2 (z1 x) (z1 y) carry;
    (carry, res3') = umulStep res3 (z2 x) (z1 y) carry;
    (carry5, res4) = umulStep carry4 (z3 x) (z1 y) carry;
    (carry, res2'') = umulHop res2' (z0 x) (z2 y);
    (carry, res3'') = umulStep res3' (z1 x) (z2 y) carry;
    (carry, res4') = umulStep res4 (z2 x) (z2 y) carry;
    (carry6, res5) = umulStep carry5 (z3 x) (z2 y) carry;
    (carry, res3''') = umulHop res3'' (z0 x) (z3 y);
    (carry, res4'') = umulStep res4' (z1 x) (z3 y) carry;
    (carry, res5') = umulStep res5 (z2 x) (z3 y) carry;
    (res7, res6) = umulStep carry6 (z3 x) (z3 y) carry
  in
    \<lparr> p0 = res0, p1 = res1', p2 = res2'', p3 = res3''', 
       p4 = res4'', p5 = res5', p6 = res6, p7 = res7 \<rparr>
)"

definition update_word_uint512 :: "uint512 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> uint512" where
  "update_word_uint512 num pos new_val \<equiv>
    (if pos = 0 then \<lparr> p0 = new_val, p1 = p1 num, p2 = p2 num, p3 = p3 num, p4 = p4 num, p5 = p5 num, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 1 then \<lparr> p0 = p0 num, p1 = new_val, p2 = p2 num, p3 = p3 num, p4 = p4 num, p5 = p5 num, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 2 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = new_val, p3 = p3 num, p4 = p4 num, p5 = p5 num, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 3 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = p2 num, p3 = new_val, p4 = p4 num, p5 = p5 num, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 4 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = p2 num, p3 = p3 num, p4 = new_val, p5 = p5 num, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 5 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = p2 num, p3 = p3 num, p4 = p4 num, p5 = new_val, p6 = p6 num, p7 = p7 num \<rparr>
     else if pos = 6 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = p2 num, p3 = p3 num, p4 = p4 num, p5 = p5 num, p6 = new_val, p7 = p7 num \<rparr>
     else if pos = 7 then \<lparr> p0 = p0 num, p1 = p1 num, p2 = p2 num, p3 = p3 num, p4 = p4 num, p5 = p5 num, p6 = p6 num, p7 = new_val \<rparr>
     else num)"

definition getword512 :: "uint512 \<Rightarrow> nat \<Rightarrow> u64" where
"getword512 p n = (
  if n = 0 then p0 p
  else if n = 1 then p1 p
  else if n = 2 then p2 p
  else if n = 3 then p3 p
  else if n = 4 then p4 p
  else if n = 5 then p5 p
  else if n = 6 then p6 p
  else if n = 7 then p7 p
  else 0
)"

definition dLen512 :: "uint512 \<Rightarrow> nat" where
"dLen512 p = (
  if p7 p \<noteq> 0 then 8
  else if p6 p \<noteq> 0 then 7
  else if p5 p \<noteq> 0 then 6
  else if p4 p \<noteq> 0 then 5
  else if p3 p \<noteq> 0 then 4
  else if p2 p \<noteq> 0 then 3
  else if p1 p \<noteq> 0 then 2
  else if p0 p \<noteq> 0 then 1
  else 0
)"

definition getword_u512 :: "uint512 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64" where
"getword_u512 u n u8 = (
  if n < 8 then getword512 u n else u8
)"

fun subMulTo_aux512 :: 
  "uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint512 \<times> u64" 
where
  "subMulTo_aux512 x u8 y multiplier 0 j borrow = (borrow, x, u8)" |
  "subMulTo_aux512 x u8 y multiplier (Suc n) j borrow = (
      let 
        x_i = getword_u512 x ((dLen y - (Suc n)) + j) u8;
        (s, carry1) = Sub64_borrow x_i borrow 0;
        y_i = getword y (dLen y - (Suc n));
        (ph, pl) = mul64 y_i multiplier;
        (t, carry2) = Sub64_borrow s pl 0;
        new_x = update_word_uint512 x ((dLen y - (Suc n)) + j) t;
        new_borrow = ph + carry1 + carry2
      in 
        subMulTo_aux512 new_x u8 y multiplier n j new_borrow 
  )"

definition subMulTo512 :: "uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint512 \<times> u64" where
"subMulTo512 x u8 y j multiplier = subMulTo_aux512 x u8 y multiplier (dLen y) j 0"

fun addTo_aux512 :: 
  "uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint512 \<times> u64" 
where
  "addTo_aux512 x u8 y 0 j carry = (carry, x, u8)" |
  "addTo_aux512 x u8 y (Suc n) j carry = (
      let 
        x_i = getword_u512 x ((dLen y - (Suc n)) + j) u8;
        y_i = getword y (dLen y - (Suc n));
        (s, new_carry) = Add64_carry x_i y_i carry;
        new_x = update_word_uint512 x ((dLen y - (Suc n)) + j) s
      in 
        addTo_aux512 new_x u8 y n j new_carry 
  )"

definition addTo512 :: "uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> u64 \<times> uint512 \<times> u64" where
"addTo512 x u8 y j = addTo_aux512 x u8 y (dLen y) j 0"

fun udivrem_knuth_loop512 :: "nat \<Rightarrow> uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> uint512 \<Rightarrow> uint512 \<times> uint512 \<times> u64" 
where
  "udivrem_knuth_loop512 0 u u8 d dh dl reciprocal quot = (
      let
        u2 = getword512 u (0 + dLen d);
        u1 = getword512 u (0 + dLen d - 1);
        u0 = getword512 u (0 + dLen d - 2);
        (qhat, rhat) = (
          if u2 \<ge> dh then (2^64-1, 0)
          else udivrem2by1 u2 u1 dh reciprocal
        );
        qhat_adj = (
          let (ph, pl) = mul64 qhat dl in
          if ph > rhat \<or> (ph = rhat \<and> pl > u0) then qhat - 1 else qhat
        );
        (borrow, u_s, u8_s) = subMulTo512 u u8 d 0 qhat_adj;
        (u_new, u8_new) = (
          if u2 < borrow then
            let (carry, u_add, u8_add) = addTo512 u_s u8_s d 0 in
            (update_word_uint512 u_add (0 + dLen d) carry, u8_add)
          else (u_s, u8_s)
        );
        qhat_final = if u2 < borrow then qhat_adj - 1 else qhat_adj;
        quot_update = update_word_uint512 quot 0 qhat_final
      in
        (quot_update, u_new, u8_new)
  )" |
  "udivrem_knuth_loop512 (Suc n) u u8 d dh dl reciprocal quot = (
      let
        u2 = getword512 u ((Suc n) + dLen d);
        u1 = getword512 u ((Suc n) + dLen d - 1);
        u0 = getword512 u ((Suc n) + dLen d - 2);
        (qhat, rhat) = (
          if u2 \<ge> dh then (2^64-1, 0)
          else udivrem2by1 u2 u1 dh reciprocal
        );
        qhat_adj = (
          let (ph, pl) = mul64 qhat dl in
          if ph > rhat \<or> (ph = rhat \<and> pl > u0) then qhat - 1 else qhat
        );
        (borrow, u_s, u8_s) = subMulTo512 u u8 d (Suc n) qhat_adj;
        (u_new, u8_new) = (
          if u2 < borrow then
            let (carry, u_add, u8_add) = addTo512 u_s u8_s d (Suc n) in
            (update_word_uint512 u_add ((Suc n) + dLen d) carry, u8_add)
          else (u_s, u8_s)
        );
        qhat_final = if u2 < borrow then qhat_adj - 1 else qhat_adj;
        quot_update = update_word_uint512 quot (Suc n) qhat_final
      in
        udivrem_knuth_loop512 n u_new u8_new d dh dl reciprocal quot_update
  )"

definition udivremKnuth512 :: "uint512 \<Rightarrow> uint512 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> uint512 \<times> uint512 \<times> u64" where
"udivremKnuth512 quot u u8 d =(
  let 
  dh = getword d (dLen d - 1);
  dl = getword d (dLen d - 2);
  reciprocal = reciprocal2by1 dh
  in
  udivrem_knuth_loop512 (dLen512 u - dLen d - 1) u u8 d dh dl reciprocal quot
)"

fun udivremBy1_loop512 :: "uint512 \<Rightarrow> uint512 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> uint512 \<times> u64" where
"udivremBy1_loop512 quot u 0 rem d reciprocal = (
  let u_j = getword512 u 0;
  (quot_j, rem_update) = udivrem2by1 rem u_j d reciprocal;
  quot_update = update_word_uint512 quot 0 quot_j
  in
  (quot_update, rem_update)
)" |
"udivremBy1_loop512 quot u (Suc n) rem d reciprocal = (
  let u_j = getword512 u (Suc n);
  (quot_j, rem_update) = udivrem2by1 rem u_j d reciprocal;
  quot_update = update_word_uint512 quot (Suc n) quot_j
  in
  udivremBy1_loop512 quot_update u n rem_update d reciprocal 
)"

definition udivremBy1512 :: "uint512 \<Rightarrow> uint512 \<Rightarrow> u64 \<Rightarrow> uint512 \<times> u64" where
"udivremBy1512 quot u d =(
  let reciprocal = reciprocal2by1 d;
      rem = getword512 u (dLen512 u - 1)      
  in
  udivremBy1_loop512 quot u (dLen512 u - 2) rem d reciprocal
)"

fun rem_loop512 :: "uint256 \<Rightarrow> uint512 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint256" where
"rem_loop512 rem un u8 0 cnt shift = rem" |
"rem_loop512 rem un u8 i cnt shift = (
  let
    un_i = getword_u512 un (cnt - i) u8;
    un_i1 = getword_u512 un ((cnt - i) + 1) u8;
    rem_i = ((un_i >> shift) OR ((un_i1 << (64 - shift))));
    rem_update = update_word_uint256 rem (cnt - i) rem_i
  in
    rem_loop512 rem_update un u8 (i - 1) cnt shift
)"

definition dnStorage512 :: "uint512 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint512" where
"dnStorage512 d l shift = (
  \<lparr> p0 = (p0 d << shift),
    p1 = (if l \<ge> 2 then (p1 d << shift) OR (p0 d >> (64 - shift)) else 0),
    p2 = (if l \<ge> 3 then (p2 d << shift) OR (p1 d >> (64 - shift)) else 0),
    p3 = (if l \<ge> 4 then (p3 d << shift) OR (p2 d >> (64 - shift)) else 0),
    p4 = (if l \<ge> 5 then (p4 d << shift) OR (p3 d >> (64 - shift)) else 0),
    p5 = (if l \<ge> 6 then (p5 d << shift) OR (p4 d >> (64 - shift)) else 0),
    p6 = (if l \<ge> 7 then (p6 d << shift) OR (p5 d >> (64 - shift)) else 0),
    p7 = (if l \<ge> 8 then (p7 d << shift) OR (p6 d >> (64 - shift)) else 0)
  \<rparr>
)"

definition udivrem512 :: "uint512 \<Rightarrow> uint512 \<Rightarrow> uint256 \<Rightarrow> uint512 \<times> uint256" where
"udivrem512 quot u d = ( 
  let 
    dlen = dLen d;
    shift = LeadingZeros64 (getword d (dlen - 1));
    dn = dnStorage d dlen shift;
    ulen = dLen512 u;
    un = dnStorage512 u ulen shift;
    u8 = 0;
    rem = uint256_zero
  in
    if ulen < dlen then (quot, extract_low256 u)
    else if dlen = 1 then
      let (quot_new, r) = udivremBy1512 quot un (getword dn 0);
          rem_new = SetUint64 (r >> shift)
      in
        (quot_new, rem_new)
    else
      let (quot_new, un_new, u8_new) = udivremKnuth512 quot un u8 dn;
          rem_new = rem_loop512 rem un_new u8_new (dlen - 1) (dlen - 1) shift
      in                                      
        (quot_new, rem_new)
)"

definition uint256_mulmod :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
"uint256_mulmod x y m = (
  if (IsZero x \<or> IsZero y \<or> IsZero m) then uint256_zero 
  else
      let 
      (carry, res0) = mul64 (z0 x) (z0 y);
      (carry, res1) = umulHop carry (z1 x) (z0 y);
      (carry, res2) = umulHop carry (z2 x) (z0 y);
      (carry4, res3) = umulHop carry (z3 x) (z0 y);
      
      (carry, res1') = umulHop res1 (z0 x) (z1 y);
      (carry, res2') = umulStep res2 (z1 x) (z1 y) carry;
      (carry, res3') = umulStep res3 (z2 x) (z1 y) carry;
      (carry5, res4) = umulStep carry4 (z3 x) (z1 y) carry;
      
      (carry, res2'') = umulHop res2' (z0 x) (z2 y);
      (carry, res3'') = umulStep res3' (z1 x) (z2 y) carry;
      (carry, res4') = umulStep res4 (z2 x) (z2 y) carry;
      (carry6, res5) = umulStep carry5 (z3 x) (z2 y) carry;
      
      (carry, res3''') = umulHop res3'' (z0 x) (z3 y);
      (carry, res4'') = umulStep res4' (z1 x) (z3 y) carry;
      (carry, res5') = umulStep res5 (z2 x) (z3 y) carry;
      (res7, res6) = umulStep carry6 (z3 x) (z3 y) carry;
      p0 = res0;
      p1 = res1';
      p2 = res2'';
      p3 = res3''';
      p4 = res4'';
      p5 = res5';
      p6 = res6;
      p7 = res7;
      pl = \<lparr>z0 = p0, z1 = p1, z2 = p2, z3 = p3\<rparr>;
      ph = \<lparr>z0 = p4, z1 = p5, z2 = p6, z3 = p7\<rparr>;
      p = \<lparr>p0 = p0, p1 = p1, p2 = p2, p3 = p3,p4 = p4, p5 = p5, p6 = p6, p7 = p7  \<rparr>
      in
      if IsZero ph then Mod pl m
      else
      let
     (_ ,rem) = udivrem512 uint512_zero p m
      in
      rem
)
"

end