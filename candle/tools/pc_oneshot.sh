#!/bin/bash
# The commands of candle/README.md in one fresh session on Candle master (with the larger code buffer), without
# DMTCP, then the dumps that link the session to the short HOL Light sessions
cd /project/work
CANDLE_ROOT=/project/work/wt/pc-big python3 pc/tools/cdriver.py --nodmtcp --heap 46000 --log logs/pc/oneshot.log \
  'cmd:loads "pc/candle/check.ml"' 'cmd:loads "pc/candle/audit.ml"' \
  'cmd:loads "pc/candle/dump_final.ml"' 'cmd:loads "pc/candle/dump_thms.ml"' > logs/pc/oneshot.out 2>&1
