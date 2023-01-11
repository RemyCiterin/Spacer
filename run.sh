#!/bin/sh

# fstar.exe fstar/ast_transformation.fst --codegen OCaml --record_hints --use_hints --odir fstar_out
ocamlbuild -use-ocamlfind main.native -package fstarlib,batteries,z3 -cflag -thread -tag -thread
