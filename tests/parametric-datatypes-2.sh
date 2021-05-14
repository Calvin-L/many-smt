# 2021/5/13: Adding this as a regression test.  This input caused CVC4 1.8 to
# crash and output simply "error".  Many-SMT misinterpreted that as the output
# from (check-sat).  It should have killed CVC4 and kept running.

OUT="$(many-smt <<EOF
(set-option :print-success false)
(set-option :timeout 10000)
(set-option :produce-models false)
(set-logic ALL)
(declare-datatypes ((Unit 0)) (((unit))))
(declare-datatypes ((Pair 2)) ((par (A B) ((make-pair (pair-first A) (pair-second B))))))
(assert (forall ((__a Int) (__b Int)) (or (= __a __b) (distinct __a __b))))
(assert (forall ((__a (Pair Int (Pair Unit Bool))) (__b (Pair Int (Pair Unit Bool)))) (=> (= (pair-first __a) (pair-first __b)) (=> (= (pair-second (pair-second __a)) (pair-second (pair-second __b))) (= __a __b)))))
(assert (forall ((__a (Pair Int (Pair Int Int)))) (exists ((__b (Pair Int (Pair Int Int)))) (distinct __a __b))))
(assert (forall ((__a Unit) (__b Unit)) (= __a __b)))
(assert (not (forall ((__a (Pair Unit (Pair (Pair Unit Unit) Unit))) (__b (Pair Unit (Pair (Pair Unit Unit) Unit)))) (= __a __b))))
(check-sat)
EOF)"

EXPECTED="$(cat <<EOF
unsat
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
