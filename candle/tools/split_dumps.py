#!/usr/bin/env python3
"""split_dumps.py LOG PREFIX: write the parts of LOG ending at each DUMP_DONE line to PREFIX.1, PREFIX.2, ..."""
import re, sys
parts, cur = [], []
for line in open(sys.argv[1], errors="replace"):
    cur.append(line)
    if re.sub(r"^[#>] +", "", re.sub(r"\x1b\[[0-9;]*m", "", line).strip()) == "DUMP_DONE":
        parts.append(cur); cur = []
for i, p in enumerate(parts, 1):
    open("%s.%d" % (sys.argv[2], i), "w").writelines(p)
print("%d parts" % len(parts))
