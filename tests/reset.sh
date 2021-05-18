# 2021/5/17: the standard is a little ambiguous about whether solvers should
# output "success" after a (reset) command.  Many-SMT DOES output "success",
# with the following justification:
#  - (reset) is a command like any other
#  - (reset) restores the initial value of :print-success, which is true
#  - section 4.2.1 of the SMT-LIB 2.6 standard says that "In particular, for
#    options that affect the solver’s output [...] the effect applies already
#    to the output of the very command that is setting the option."

OUT="$(many-smt <<EOF
(set-option :print-success false)
(set-logic ALL)
(declare-datatypes ((Unit 0)) (((unit))))
(declare-const a Unit)
(declare-const b Unit)
(assert (distinct a b))
(check-sat)
(reset)
(set-logic QF_LIA)
(declare-const x Int)
(assert (distinct x 0))
(check-sat)
EOF)"

EXPECTED="$(cat <<EOF
unsat
success
success
success
success
sat
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
