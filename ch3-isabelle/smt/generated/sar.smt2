(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(declare-fun result () (_ BitVec 256))
(assert (= result (ite (bvuge b
            #x0000000000000000000000000000000000000000000000000000000000000100)
     (ite (= #b1 ((_ extract 255 255) a))
          #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
          #x0000000000000000000000000000000000000000000000000000000000000000)
     (bvashr a b))))
(check-sat)
