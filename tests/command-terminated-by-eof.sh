OUT="$(echo -n '(set-logic ALL)' | many-smt)"

echo "$OUT"
if [[ "$OUT" != "success" ]]; then
    exit 1
fi
