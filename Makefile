
SOURCES = syntax.ml myLexer.mll myParser.mly typecheck.ml rank2.ml eval.ml main.ml
#SOURCES = rank2.ml
RESULT  = main

YFLAGS = -v

all: byte-code byte-code-library

run: all
	rlwrap ./$(RESULT)

-include OCamlMakefile
