#!/bin/bash

cd "$(dirname "$0")"
export PATH="$(pwd):$PATH"
unset MANYSMT_SOLVERS
unset MANYSMT_EXTRA_SOLVERS

N=0
PASS=0

for f in ./tests/*.sh; do
    let N=N+1
    echo -n "$f... "
    bash "$f" >"$f.log" 2>&1
    if [[ $? == 0 ]]; then
        let PASS=PASS+1
        echo "OK"
    else
        echo "FAIL"
    fi
done

if [[ $PASS -lt $N ]]; then
    echo "There were failures."
    exit 1
fi
