#!/usr/bin/env bash

OCAML_FSTAR="../bin/fstar.ocaml"
FSHARP_FSTAR="../bin/fstar.fsharp"

QUERIES_FLAG="--log_queries"
ANALYZE_FLAG="--analyze_proof"

INPUT_FILES="Trivial ListStuff Recursive"

cleanup() {
    rm -rfv queries-*.smt2 *.query.smt2
}

run_each() {
    for FN in $INPUT_FILES; do
        $1 $QUERIES_FLAG $ANALYZE_FLAG $FN.fst
        mv queries-$FN.smt2 $FN.$2.query.smt2
    done
}

if [[ "$1" == "clean" ]]; then
    cleanup
elif [[ "$1" == "fsharp" ]]; then
    run_each $FSHARP_FSTAR fstar
elif [[ "$1" == "ocaml" ]];  then
    run_each $OCAML_FSTAR ocaml
fi
