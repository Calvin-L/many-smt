OUT="$(many-smt <<EOF
(set-logic ALL)
(assert false)
(exit)
EOF)"

RETCODE=$?
echo "Exit status was $RETCODE"

if [[ $RETCODE != 0 ]]; then
    echo "Exit status should have been zero"
    exit 1
fi

EXPECTED="$(cat <<EOF
success
success
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
