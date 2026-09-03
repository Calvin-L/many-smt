# 2026/9/2: This test checks Many-SMT's behavior when it there is an extra
# closing paren in the file.  Previously it would either silently drop the
# paren or it would throw an ugly `IndexError`.

OUT="$(many-smt <extra-closing-paren.smt2)"
RETCODE=$?
echo "$OUT"
echo "Exit status was $RETCODE"

if [[ $RETCODE == 0 ]]; then
    echo "Exit status should have been nonzero"
    exit 1
fi

EXPECTED="$(cat <<EOF
(error "Extra ')' on line 12")
EOF)"

if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
