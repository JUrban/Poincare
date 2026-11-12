#!/usr/bin/env python3
"""bufproj.py LANE_OUT...: from the driver's BUFFERS lines, code and data buffer use against the source bytes of the
src/ files loaded so far (each OK item counts its file and the files it loaded with needs), and a linear projection
to the whole of src/ (file sizes; the library files that src/ loads itself are not counted)."""
import os, re, sys
src = "/project/repos/Poincare/src/"
total = sum(os.path.getsize(src + f) for f in os.listdir(src))
loaded, pts = set(), []
for path in sys.argv[1:]:
    for l in open(path):
        m = re.search(r"finished (src/\S+)", l)
        if m:
            loaded.add(m.group(1))
        m = re.search(r"BUFFERS code ([\d.]+) MB data ([\d.]+) MB", l)
        if m:
            b = sum(os.path.getsize("/project/repos/Poincare/" + f) for f in loaded)
            pts.append((b, float(m.group(1)), float(m.group(2))))
if len(pts) < 2:
    sys.exit("not enough points")
(b0, c0, d0), (b1, c1, d1) = pts[0], pts[-1]
rc, rd = (c1 - c0) / max(1, (b1 - b0) / 1e6), (d1 - d0) / max(1, (b1 - b0) / 1e6)
print("src loaded %.1f of %.1f MB (%d files); code %.1f MB, data %.1f MB" % (b1 / 1e6, total / 1e6, len(loaded), c1, d1))
print("per MB of source: code %.2f MB, data %.2f MB" % (rc, rd))
print("projected at the end of src/: code %.0f of 1048 MB (524 in the default build), data %.0f of 655 MB"
      % (c1 + rc * (total - b1) / 1e6, d1 + rd * (total - b1) / 1e6))
