#!/usr/bin/env python3
"""idents.py: library identifiers that src/ and audit/ use in ML code (outside comments, terms, strings),
i.e. used there but not bound at top level there, and bound at top level in the HOL Light files loaded."""
import re, sys, glob, subprocess
sys.path.insert(0, "/project/work/pc/tools")
from mlscan import strip
KW = set("""let rec and in if then else match with function fun try when as begin end not true false raise
of type val open include module struct sig mod land lor lxor lsl lsr asr or ref failwith""".split())
used, bound = {}, set()
for f in glob.glob("/project/repos/Poincare/src/*.ml") + glob.glob("/project/repos/Poincare/audit/*.ml"):
    t = strip(open(f, errors="replace").read())
    for m in re.finditer(r"^(?:let|and)\s+(?:rec\s+)?([A-Za-z_][\w']*)", t, re.M):
        bound.add(m.group(1))
    for m in re.finditer(r"(?<![\w.'])([A-Z][a-z]\w*\.)?([A-Za-z_][\w']*)", t):
        n = (m.group(1) or "") + m.group(2)
        used.setdefault(n, f.split("/")[-1])
lib = set()
hl = "/project/repos/hol-light"
files = subprocess.run(["git", "-C", hl, "ls-tree", "-r", "--name-only", "31fe213"], capture_output=True, text=True).stdout.split()
for f in files:
    if f.endswith(".ml") and (f.count("/") == 0 or f.startswith(("Multivariate/", "Library/", "100/"))):
        t = strip(subprocess.run(["git", "-C", hl, "show", "31fe213:" + f], capture_output=True, text=True, errors="replace").stdout)
        for m in re.finditer(r"^(?:let|and)\s+(?:rec\s+)?([A-Za-z_][\w']*|\([^)]*\))", t, re.M):
            lib.add(m.group(1))
cands = sorted(n for n in used if n not in KW and n not in bound and (n in lib or "." in n))
print(len(used), len(bound), len(lib), len(cands), file=sys.stderr)
for n in cands:
    print(n, used[n])
