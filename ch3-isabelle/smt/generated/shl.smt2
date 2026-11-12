(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(declare-fun result () (_ BitVec 256))
(assert (= result (ite (bvuge b
            #x0000000000000000000000000000000000000000000000000000000000000100)
     #x0000000000000000000000000000000000000000000000000000000000000000
     (bvshl a b))))
(check-sat)
