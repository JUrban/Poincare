#!/bin/bash
# build_hl.sh COMMIT DIR: a scratch bytecode HOL Light at COMMIT (this machine has no zarith: use bignum_num.ml)
set -eu
C=$1; D=$2
rm -rf $D; mkdir -p $D
git -C /project/repos/hol-light archive $C | tar -x -C $D
cd $D
sed -i 's/${OCAML_VERSION} = "4.14"/${OCAML_VERSION} = "x"/g' Makefile
make > make.log 2>&1 || { echo MAKE_FAILED; tail -n 20 make.log; exit 1; }
ocamlfind ocamlmktop -package num -linkall -o ocaml-hol nums.cma bignum.cmo hol_loader.cmo >> make.log 2>&1 || ocamlmktop -linkall -o ocaml-hol nums.cma bignum.cmo hol_loader.cmo >> make.log 2>&1
cp hol_4.14.sh hol.sh 2>/dev/null || true
sed -i "s#__DIR__#$D#" hol.sh
ln -s /project/repos/Poincare pc
echo BUILD_DONE $C
