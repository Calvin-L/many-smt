(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (distinct x y))
(check-sat)
(get-model)
(echo "Done!")
