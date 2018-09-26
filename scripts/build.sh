#!/bin/bash

cp ./src/scanner.mll ./scanner.mll
cp ./src/parser.mly ./parser.mly
cp ./src/ast.ml ./ast.ml
cp ./src/sast.ml ./sast.ml
cp ./src/semant.ml ./semant.ml
cp ./src/codegen.ml ./codegen.ml
cp ./src/m2.ml ./m2.ml

ocamlbuild -j 0 -r -use-ocamlfind -pkgs str,llvm,llvm.analysis,llvm.bitwriter,llvm.bitreader,llvm.linker,llvm.target m2.native