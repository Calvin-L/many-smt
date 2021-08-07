# 2021/8/6: I noticed Boolector was causing the tool to hang when the input
# included `(push)` with no numeral.  Z3 and CVC4 accept it, but the standard
# officially says that you must always call `(push N)` with N >= 0.  This
# appears to be a problem in Boolector: in incremental mode, it hangs waiting
# for a numeral that's never coming, even though `(push)` is a complete
# (malformed!) command.
#
# Many of my own SMT-backed tools use `(push)`, so I'm going to have many-smt
# silently rewrite `(push)` to `(push 1)` and `(pop)` to `(pop 1)`.

OUT="$(many-smt <<EOF
(set-option :produce-models true)
(set-logic QF_BV)
(push)
(push 1)
(push 0)
(pop)
(pop)
(pop 0)
EOF)"

EXPECTED="$(cat <<EOF
success
success
success
success
success
success
success
success
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
