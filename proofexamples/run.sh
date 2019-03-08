#!/usr/bin/env bash

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

OCAML_FSTAR="../bin/fstar.ocaml"
FSHARP_FSTAR="../bin/fstar.fsharp"

OCAML_OUT="ocaml-output.out"
FSHARP_OUT="fsharp-output.out"

QUERIES_FLAG="--log_queries"
ANALYZE_FLAG="--analyze_proof"

INPUT_FILES="Trivial ListStuff Recursive"

cleanup() {
    rm -rfv queries-*.smt2 *.query.smt2
}

run_each() {
    rm -f $3
    for FN in $INPUT_FILES; do
        $1 $QUERIES_FLAG $ANALYZE_FLAG $FN.fst >> $3
        mv queries-$FN.smt2 $FN.$2.query.smt2
    done
}

main() {
    if [[ "$1" == "clean" ]]; then
        cleanup
    elif [[ "$1" == "fsharp" ]]; then
        run_each $FSHARP_FSTAR fstar $FSHARP_OUT
    elif [[ "$1" == "ocaml" ]];  then
        run_each $OCAML_FSTAR ocaml $OCAML_OUT
    elif [[ "$1" == "both" ]]; then
        run_each $FSHARP_FSTAR fstar $FSHARP_OUT
        run_each $OCAML_FSTAR ocaml $OCAML_OUT
    fi
}

(cd $SCRIPT_DIR 
main "$1")