F=$(mktemp)
trap 'rm "$F"' EXIT

cat >$F <<EOF
while read line; do
    if [[ "\$line" == "(check-sat)" ]]; then
        echo "sat"
    else
        echo "success"
    fi
done
EOF

export MANYSMT_SOLVERS=''
export MANYSMT_EXTRA_SOLVERS="bash '$F'"

OUT="$(many-smt <<EOF
(assert false)
(check-sat)
EOF
)"

EXPECTED="$(cat <<EOF
success
sat
EOF
)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
