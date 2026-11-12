#!/usr/bin/env python3
"""codewatch.py PID: Private_Dirty (MB) of each mapping of the cake binary, i.e. how much of the code buffer
(in the text mapping) and data buffer the dynamic compiler has written."""
import sys, re
pid = sys.argv[1]
cur = None
for line in open("/proc/%s/smaps" % pid):
    m = re.match(r"^([0-9a-f]+)-([0-9a-f]+) (\S+) \S+ \S+ \S+\s*(.*)$", line)
    if m:
        cur = (m.group(3), m.group(4).strip(), (int(m.group(2), 16) - int(m.group(1), 16)) >> 20)
    elif line.startswith("Private_Dirty:") and cur and cur[1].endswith("/cake"):
        print("%s size %6d MB  private_dirty %8.1f MB" % (cur[0], cur[2], int(line.split()[1]) / 1024))
