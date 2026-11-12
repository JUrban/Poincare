#!/bin/bash
# stmts_candle.sh: the short session on Candle master with the recorder (pc-rec worktree): the library, then
# candle/statements.ml, then every definition, constant, type operator and type definition theorem
cd /project/work
CANDLE_ROOT=/project/work/wt/pc-rec python3 pc/tools/cdriver.py --nodmtcp --heap 10000 --log logs/pc/stmts_candle.log \
  pc/candle/prelude.ml Multivariate/cauchy.ml Multivariate/lpspaces.ml 100/green.ml 'cmd:loads "pc/candle/compat.ml"' \
  pc/candle/statements.ml 'cmd:loads "pc/candle/dump_defs.ml"' 'cmd:loads "pc/candle/dump_tydefs.ml"' > logs/pc/stmts_candle.out 2>&1
echo STMTS_DONE rc=$? >> logs/pc/stmts_candle.out
