#!/bin/bash
# chain_lane.sh: wait for the pc_base_big checkpoint, then start the main lane from it
cd /project/work
until grep -qE '^CKPT .*pc_base_big|^FAIL|BOOT FAILED|CHECKPOINT FAILED' logs/pc/base_big.out; do sleep 20; done
grep -qE '^FAIL|BOOT FAILED|CHECKPOINT FAILED' logs/pc/base_big.out && { echo "BASE FAILED" >> logs/pc/base_big.out; exit 1; }
# the driver kills its process tree at exit; wait until the base's Candle is gone
while ps -eo args --no-headers | grep -q '^./cake --candle'; do sleep 10; done
python3 pc/tools/pc_lane.py
