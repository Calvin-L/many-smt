OUT="$(many-smt <<EOF
(set-logic ALL)
(set-option :produce-assertions true)
(set-option :interactive-mode true)
(get-assertions)
EOF)"

RETCODE=$?
echo "Exit status was $RETCODE"

if [[ $RETCODE == 0 ]]; then
    echo "Exit status should have been nonzero"
    exit 1
fi

EXPECTED="$(cat <<EOF
success
unsupported
unsupported
(error ":produce-assertions mode is not supported")
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
