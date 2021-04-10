OUT="$(many-smt <<EOF
(echo "(")
EOF)"

echo "$OUT"
if [[ "$OUT" != '"("' ]]; then
    exit 1
fi
