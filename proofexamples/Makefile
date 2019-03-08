FSTAR_OCAML_BIN=../bin/fstar.ocaml
FSTAR_FSHARP_BIN=../bin/fstar.fsharp

FSTAR_FLAG_ANALYZE=--analyze_proof
FSTAR_FLAG_QUERIES=--log_queries

INPUT_FILES=Trivial \
			ListStuff \
			Recursive

SMT_FILES=$(foreach f,$(INPUT_FILES),queries-$(f).smt2)

fsharp : $(SMT_FILES)

queries-%.smt2 : %.fst
	$(FSTAR_FSHARP_BIN) $(FSTAR_FLAG_ANALYZE) $<