OUT="$(many-smt <<EOF
; (get-info :all-statistics) ; output varies
(get-info :assertion-stack-levels)
(get-info :authors)
(get-info :error-behavior)
(get-info :name)
; (get-info :reason-unknown) ; only legal after (check-sat) returned unknown
(get-info :version)
EOF)"

EXPECTED="$(cat <<EOF
unsupported
(:authors "Calvin Loncaric")
(:error-behavior immediate-exit)
(:name "Many-SMT")
(:version "??.??.??")
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
