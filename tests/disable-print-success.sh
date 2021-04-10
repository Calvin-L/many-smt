OUT="$(many-smt <<EOF
(set-option :print-success false)
(set-logic ALL)
(check-sat)
EOF)"

EXPECTED="$(cat <<EOF
sat
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
