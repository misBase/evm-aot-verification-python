(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(declare-fun result () (_ BitVec 256))
(assert (= result (let ((a!1 (ite (= #x000000000000000000000000000000000000000000000000000000000000001f
                   a)
                (ite (= #b1 ((_ extract 255 255) b))
                     (bvor b
                           (bvnot #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                b)))
(let ((a!2 (ite (= #x000000000000000000000000000000000000000000000000000000000000001e
                   a)
                (ite (= #b1 ((_ extract 247 247) b))
                     (bvor b
                           (bvnot #x00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!1)))
(let ((a!3 (ite (= #x000000000000000000000000000000000000000000000000000000000000001d
                   a)
                (ite (= #b1 ((_ extract 239 239) b))
                     (bvor b
                           (bvnot #x0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!2)))
(let ((a!4 (ite (= #x000000000000000000000000000000000000000000000000000000000000001c
                   a)
                (ite (= #b1 ((_ extract 231 231) b))
                     (bvor b
                           (bvnot #x000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!3)))
(let ((a!5 (ite (= #x000000000000000000000000000000000000000000000000000000000000001b
                   a)
                (ite (= #b1 ((_ extract 223 223) b))
                     (bvor b
                           (bvnot #x00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!4)))
(let ((a!6 (ite (= #x000000000000000000000000000000000000000000000000000000000000001a
                   a)
                (ite (= #b1 ((_ extract 215 215) b))
                     (bvor b
                           (bvnot #x0000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x0000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!5)))
(let ((a!7 (ite (= #x0000000000000000000000000000000000000000000000000000000000000019
                   a)
                (ite (= #b1 ((_ extract 207 207) b))
                     (bvor b
                           (bvnot #x000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!6)))
(let ((a!8 (ite (= #x0000000000000000000000000000000000000000000000000000000000000018
                   a)
                (ite (= #b1 ((_ extract 199 199) b))
                     (bvor b
                           (bvnot #x00000000000000ffffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x00000000000000ffffffffffffffffffffffffffffffffffffffffffffffffff))
                a!7)))
(let ((a!9 (ite (= #x0000000000000000000000000000000000000000000000000000000000000017
                   a)
                (ite (= #b1 ((_ extract 191 191) b))
                     (bvor b
                           (bvnot #x0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff))
                     (bvand b
                            #x0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff))
                a!8)))
(let ((a!10 (ite (= #x0000000000000000000000000000000000000000000000000000000000000016
                    a)
                 (ite (= #b1 ((_ extract 183 183) b))
                      (bvor b
                            (bvnot #x000000000000000000ffffffffffffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x000000000000000000ffffffffffffffffffffffffffffffffffffffffffffff))
                 a!9)))
(let ((a!11 (ite (= #x0000000000000000000000000000000000000000000000000000000000000015
                    a)
                 (ite (= #b1 ((_ extract 175 175) b))
                      (bvor b
                            (bvnot #x00000000000000000000ffffffffffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x00000000000000000000ffffffffffffffffffffffffffffffffffffffffffff))
                 a!10)))
(let ((a!12 (ite (= #x0000000000000000000000000000000000000000000000000000000000000014
                    a)
                 (ite (= #b1 ((_ extract 167 167) b))
                      (bvor b
                            (bvnot #x0000000000000000000000ffffffffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x0000000000000000000000ffffffffffffffffffffffffffffffffffffffffff))
                 a!11)))
(let ((a!13 (ite (= #x0000000000000000000000000000000000000000000000000000000000000013
                    a)
                 (ite (= #b1 ((_ extract 159 159) b))
                      (bvor b
                            (bvnot #x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff))
                 a!12)))
(let ((a!14 (ite (= #x0000000000000000000000000000000000000000000000000000000000000012
                    a)
                 (ite (= #b1 ((_ extract 151 151) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000ffffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x00000000000000000000000000ffffffffffffffffffffffffffffffffffffff))
                 a!13)))
(let ((a!15 (ite (= #x0000000000000000000000000000000000000000000000000000000000000011
                    a)
                 (ite (= #b1 ((_ extract 143 143) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000ffffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x0000000000000000000000000000ffffffffffffffffffffffffffffffffffff))
                 a!14)))
(let ((a!16 (ite (= #x0000000000000000000000000000000000000000000000000000000000000010
                    a)
                 (ite (= #b1 ((_ extract 135 135) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000ffffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x000000000000000000000000000000ffffffffffffffffffffffffffffffffff))
                 a!15)))
(let ((a!17 (ite (= #x000000000000000000000000000000000000000000000000000000000000000f
                    a)
                 (ite (= #b1 ((_ extract 127 127) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000ffffffffffffffffffffffffffffffff))
                      (bvand b
                             #x00000000000000000000000000000000ffffffffffffffffffffffffffffffff))
                 a!16)))
(let ((a!18 (ite (= #x000000000000000000000000000000000000000000000000000000000000000e
                    a)
                 (ite (= #b1 ((_ extract 119 119) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000000000ffffffffffffffffffffffffffffff))
                      (bvand b
                             #x0000000000000000000000000000000000ffffffffffffffffffffffffffffff))
                 a!17)))
(let ((a!19 (ite (= #x000000000000000000000000000000000000000000000000000000000000000d
                    a)
                 (ite (= #b1 ((_ extract 111 111) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000000000ffffffffffffffffffffffffffff))
                      (bvand b
                             #x000000000000000000000000000000000000ffffffffffffffffffffffffffff))
                 a!18)))
(let ((a!20 (ite (= #x000000000000000000000000000000000000000000000000000000000000000c
                    a)
                 (ite (= #b1 ((_ extract 103 103) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000000000ffffffffffffffffffffffffff))
                      (bvand b
                             #x00000000000000000000000000000000000000ffffffffffffffffffffffffff))
                 a!19)))
(let ((a!21 (ite (= #x000000000000000000000000000000000000000000000000000000000000000b
                    a)
                 (ite (= #b1 ((_ extract 95 95) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000000000000000ffffffffffffffffffffffff))
                      (bvand b
                             #x0000000000000000000000000000000000000000ffffffffffffffffffffffff))
                 a!20)))
(let ((a!22 (ite (= #x000000000000000000000000000000000000000000000000000000000000000a
                    a)
                 (ite (= #b1 ((_ extract 87 87) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000000000000000ffffffffffffffffffffff))
                      (bvand b
                             #x000000000000000000000000000000000000000000ffffffffffffffffffffff))
                 a!21)))
(let ((a!23 (ite (= #x0000000000000000000000000000000000000000000000000000000000000009
                    a)
                 (ite (= #b1 ((_ extract 79 79) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000000000000000ffffffffffffffffffff))
                      (bvand b
                             #x00000000000000000000000000000000000000000000ffffffffffffffffffff))
                 a!22)))
(let ((a!24 (ite (= #x0000000000000000000000000000000000000000000000000000000000000008
                    a)
                 (ite (= #b1 ((_ extract 71 71) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000000000000000000000ffffffffffffffffff))
                      (bvand b
                             #x0000000000000000000000000000000000000000000000ffffffffffffffffff))
                 a!23)))
(let ((a!25 (ite (= #x0000000000000000000000000000000000000000000000000000000000000007
                    a)
                 (ite (= #b1 ((_ extract 63 63) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000000000000000000000ffffffffffffffff))
                      (bvand b
                             #x000000000000000000000000000000000000000000000000ffffffffffffffff))
                 a!24)))
(let ((a!26 (ite (= #x0000000000000000000000000000000000000000000000000000000000000006
                    a)
                 (ite (= #b1 ((_ extract 55 55) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000000000000000000000ffffffffffffff))
                      (bvand b
                             #x00000000000000000000000000000000000000000000000000ffffffffffffff))
                 a!25)))
(let ((a!27 (ite (= #x0000000000000000000000000000000000000000000000000000000000000005
                    a)
                 (ite (= #b1 ((_ extract 47 47) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000000000000000000000000000ffffffffffff))
                      (bvand b
                             #x0000000000000000000000000000000000000000000000000000ffffffffffff))
                 a!26)))
(let ((a!28 (ite (= #x0000000000000000000000000000000000000000000000000000000000000004
                    a)
                 (ite (= #b1 ((_ extract 39 39) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000000000000000000000000000ffffffffff))
                      (bvand b
                             #x000000000000000000000000000000000000000000000000000000ffffffffff))
                 a!27)))
(let ((a!29 (ite (= #x0000000000000000000000000000000000000000000000000000000000000003
                    a)
                 (ite (= #b1 ((_ extract 31 31) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000000000000000000000000000ffffffff))
                      (bvand b
                             #x00000000000000000000000000000000000000000000000000000000ffffffff))
                 a!28)))
(let ((a!30 (ite (= #x0000000000000000000000000000000000000000000000000000000000000002
                    a)
                 (ite (= #b1 ((_ extract 23 23) b))
                      (bvor b
                            (bvnot #x0000000000000000000000000000000000000000000000000000000000ffffff))
                      (bvand b
                             #x0000000000000000000000000000000000000000000000000000000000ffffff))
                 a!29)))
(let ((a!31 (ite (= #x0000000000000000000000000000000000000000000000000000000000000001
                    a)
                 (ite (= #b1 ((_ extract 15 15) b))
                      (bvor b
                            (bvnot #x000000000000000000000000000000000000000000000000000000000000ffff))
                      (bvand b
                             #x000000000000000000000000000000000000000000000000000000000000ffff))
                 a!30)))
(let ((a!32 (ite (= #x0000000000000000000000000000000000000000000000000000000000000000
                    a)
                 (ite (= #b1 ((_ extract 7 7) b))
                      (bvor b
                            (bvnot #x00000000000000000000000000000000000000000000000000000000000000ff))
                      (bvand b
                             #x00000000000000000000000000000000000000000000000000000000000000ff))
                 a!31)))
  (ite (bvuge a
              #x0000000000000000000000000000000000000000000000000000000000000020)
       b
       a!32)))))))))))))))))))))))))))))))))))
(check-sat)
