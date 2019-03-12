#!/usr/bin/env bash

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

OCAML_FSTAR="../bin/fstar.ocaml"
FSHARP_FSTAR="../bin/fstar.fsharp"
FSTAR_FSTAR="../bin/fstar.exe"

OCAML_OUT="ocaml-output.out"
FSHARP_OUT="fsharp-output.out"
FSTAR_OUT="fstar-output.out"
ULIB_OUT="ulib.out"

QUERIES_FLAG="--log_queries"
PROFILE_FLAG="--report_qi"
PROOF_FLAG="--smt_proof"

INPUT_FILES="Trivial ListStuff Recursive"

cleanup() {
    rm -rfv queries-*.smt2 *.query.smt2 *.out
}

run_each() {
    rm -f $3
    for FN in $INPUT_FILES; do
        $1 $4 $FN.fst >> $3
        mv queries-$FN.smt2 $FN.$2.query.smt2
    done
}

main() {
    if [[ "$1" == "clean" ]]; then
        cleanup
    elif [[ "$1" == "fsharp" ]]; then
        run_each $FSHARP_FSTAR fstar $FSHARP_OUT "$QUERIES_FLAG $PROFILE_FLAG"
    elif [[ "$1" == "ocaml" ]];  then
        run_each $OCAML_FSTAR ocaml $OCAML_OUT "$QUERIES_FLAG $PROFILE_FLAG"
    elif [[ "$1" == "both" ]]; then
        run_each $FSHARP_FSTAR fstar $FSHARP_OUT "$QUERIES_FLAG $PROFILE_FLAG"
        run_each $OCAML_FSTAR ocaml $OCAML_OUT "$QUERIES_FLAG $PROFILE_FLAG"
    elif [[ "$1" == "fstar" ]]; then
        run_each $FSTAR_FSTAR exe $EXE_OUT "$QUERIES_FLAG $PROFILE_FLAG"
    elif [[ "$1" == "ulib" ]]; then
        rm -rfv ../ulib/*.hints ../ulib/*.checked ../ulib/*.queries
        OTHERFLAGS="$QUERIES_FLAG $PROFILE_FLAG" make -C ../ulib/
    fi
}

(cd $SCRIPT_DIR 
main "$1")