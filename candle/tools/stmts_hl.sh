#!/bin/bash
# stmts_hl.sh HLDIR OUT: the short session on HOL Light (with the type definition recorder): the library of
# make.ml, candle/statements.ml, then the dumps (all definitions; those of candle/dump_final.ml; type definitions)
set -u
cd /project/repos/Poincare
ulimit -s unlimited
printf 'needs "Multivariate/cauchy.ml";;\nneeds "Multivariate/lpspaces.ml";;\nneeds "100/green.ml";;\nloadt "candle/statements.ml";;\nloadt "candle/dump_defs.ml";;\nloadt "candle/dump_final.ml";;\nloadt "candle/dump_tydefs.ml";;\n' > $2.in
LINE_EDITOR=env $1/hol.sh < $2.in > $2 2>&1
echo HL_RUN_DONE rc=$? >> $2
