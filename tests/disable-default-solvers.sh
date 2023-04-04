# Without any solvers, many-smt should fail.

export MANYSMT_SOLVERS=''

OUT="$(many-smt <<EOF
(set-logic ALL)
(check-sat)
EOF)"

RETCODE=$?
echo "Exit status was $RETCODE"

echo "$OUT"

if [[ $RETCODE == 0 ]]; then
    echo "Exit status should have been nonzero"
    exit 1
fi
