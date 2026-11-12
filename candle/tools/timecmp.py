#!/usr/bin/env python3
"""timecmp.py HLTIME_OUT LANE_OUT: compare the per-file times of HOL Light on this machine (hl_time.sh), of the
Candle lane, and of upstream's doc/timing.tsv, on the files present in all three."""
import re, sys, statistics
hl, ca, up = {}, {}, {}
for l in open(sys.argv[1], errors="replace"):
    if l.startswith("TIMING\t"):
        _, f, cpu, wall = l.rstrip("\n").split("\t"); hl[f] = (float(cpu), float(wall))
for l in open(sys.argv[2]):
    m = re.match(r"OK\s+(\S+\.ml)\s+([\d.]+)s", l)
    if m: ca[m.group(1)] = float(m.group(2))
for l in open("/project/repos/Poincare/doc/timing.tsv").readlines()[1:]:
    f, s, c = l.rstrip("\n").split("\t"); up[f] = float(s)
for f in ["Multivariate/cauchy.ml", "Multivariate/lpspaces.ml", "100/green.ml"]:
    if f in hl and f in ca:
        print("%-26s HOL Light here %7.1f s, Candle %7.1f s (x%.2f), upstream %7.1f s" % (f, hl[f][1], ca[f], ca[f] / hl[f][1], up[f]))
src = [f for f in hl if f.startswith("src/") and f in ca and f in up]
h = sum(hl[f][1] for f in src); c = sum(ca[f] for f in src); u = sum(up[f] for f in src)
print("src: %d files; HOL Light here %.0f s (CPU %.0f), Candle %.0f s, upstream %.0f s" % (len(src), h, sum(hl[f][0] for f in src), c, u))
print("  Candle / HOL Light here %.2f; HOL Light here / upstream %.2f; Candle / upstream %.2f" % (c / h, h / u, c / u))
big = [f for f in src if hl[f][1] >= 10]
r = sorted(ca[f] / hl[f][1] for f in big)
print("  files of 10 s or more in HOL Light: %d; ratio median %.2f, quartiles %.2f to %.2f, range %.2f to %.2f"
      % (len(big), statistics.median(r), r[len(r) // 4], r[3 * len(r) // 4], r[0], r[-1]))
fam = {}
for f in src:
    k = "_".join(f[4:].split("_")[:2]) if f[4:].startswith("pc_") else f[4:].split("_")[0]
    a = fam.setdefault(k, [0, 0, 0]); a[0] += 1; a[1] += hl[f][1]; a[2] += ca[f]
print("  by family (HOL Light here 300 s or more): " + ", ".join("%s %.2f" % (k, v[2] / v[1]) for k, v in sorted(fam.items(), key=lambda kv: -kv[1][1]) if v[1] >= 300))
print("  highest ratios (10 s or more): " + ", ".join("%s %.1f/%.1f" % (f[4:], ca[f], hl[f][1]) for f in sorted(big, key=lambda f: -ca[f] / hl[f][1])[:6]))
print("  lowest ratios (10 s or more): " + ", ".join("%s %.1f/%.1f" % (f[4:], ca[f], hl[f][1]) for f in sorted(big, key=lambda f: ca[f] / hl[f][1])[:4]))
