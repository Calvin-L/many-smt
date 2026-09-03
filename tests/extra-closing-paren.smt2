(set-logic QF_UF)

(declare-const f0 Bool)
(declare-const f1 Bool)
(declare-const f2 Bool)
(declare-const f3 Bool)
(declare-const x0 Bool)
(declare-const x1 Bool)
(declare-const x2 Bool)

(assert f0)
(assert (= f1 (= (not f0) x0))))
(assert (= f2 (= (not f1) x1)))
(assert (= f3 (= (not false) x2)))

(assert (and f0 f1 f2 f3))

(check-sat)
(get-model)
