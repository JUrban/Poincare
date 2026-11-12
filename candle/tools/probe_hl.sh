#!/bin/bash
# probe_hl.sh HLDIR OUT: the library prerequisites of make.ml, then the types of the identifiers in probe_idents.ml
set -u
cd /project/repos/Poincare
ulimit -s unlimited
{ printf 'needs "Multivariate/cauchy.ml";;\nneeds "Multivariate/lpspaces.ml";;\nneeds "100/green.ml";;\nprint_string "PROBE_START\\n";;\n'; grep -v '^----$' /project/work/pc/probe_idents.ml; printf 'print_string "PROBE_END\\n";;\n'; } > $2.in
LINE_EDITOR=env $1/hol.sh < $2.in > $2 2>&1
echo HL_RUN_DONE rc=$? >> $2
