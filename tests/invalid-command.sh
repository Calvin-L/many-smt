# 2021/5/17: This test checks Many-SMT's behavior when it receives an illegal
# command.  The SMT-LIB 2.6 standard has this to say:
#
# > Solvers have two options when encountering errors.  For both options, they
# > first print an error message in the <general_response> format.  Then, they
# > may either immediately exit with a non-zero exit status, or continue
# > accepting commands.  In the second case, the solver’s state remains
# > unmodified by the error-generating command, except possibly for timing and
# > diagnostic information. In particular, the assertion stack, discussed in
# > Section 4.1.4, is unchanged.
#
# Tracking the assertion stack would make Many-SMT substantially more complex,
# so we opt for the first choice (exit with a nonzero status).

OUT="$(many-smt <<EOF
"hello"
(reset)
EOF)"

RETCODE=$?
echo "Exit status was $RETCODE"

if [[ $RETCODE == 0 ]]; then
    echo "Exit status should have been nonzero"
    exit 1
fi

EXPECTED="$(cat <<EOF
(error "Not a legal command: '""hello""'")
EOF)"

echo "$OUT"
if [[ "$OUT" != "$EXPECTED" ]]; then
    exit 1
fi
