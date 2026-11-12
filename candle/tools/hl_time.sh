#!/bin/bash
# hl_time.sh HLDIR OUTDIR: HOL Light (bytecode toplevel) loads the library of make.ml and src/ files in the
# order of the lane, printing the CPU and wall time of each (OUTDIR/in.ml), for a same-machine comparison
set -u
cd /project/repos/Poincare
ulimit -s unlimited
LINE_EDITOR=env $1/hol.sh < $2/in.ml > $2/out 2>&1
echo HL_RUN_DONE rc=$? >> $2/out
