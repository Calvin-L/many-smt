# 2021/5/14: Adding this as a regression test.  This input caused Many-SMT to
# hang when using Boolector as a back-end solver.

HASH='#'

OUT="$(many-smt <<EOF
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (distinct x ${HASH}x00))
(check-sat)
(assert (distinct x ${HASH}xFF))
(check-sat)
EOF)"

EXPECTED="$(cat <<EOF
success
success
success
success
sat
success
sat
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
