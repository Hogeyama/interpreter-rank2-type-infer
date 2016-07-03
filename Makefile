SOURCES = syntax.ml myLexer.mll myParser.mly typecheck.ml eval.ml main.ml
RESULT  = main

PACKS = str
YFLAGS = -v

all: byte-code byte-code-library
run: all
	rlwrap ./$(RESULT)

-include OCamlMakefile

