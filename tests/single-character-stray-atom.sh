OUT="$(many-smt <<EOF
(set-logic ALL)
x
(check-sat)
EOF)"

EXPECTED="$(cat <<EOF
success
(error "Not a legal command: 'x'")
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
