#!/usr/bin/env python3
"""closure.py FILE...: the needs-closure (within src/ and audit/) of the given files, in make.ml order, with
HOL Light times from doc/timing.tsv.  --list prints the files."""
import re, sys
R = "/project/repos/Poincare/"
order = re.findall(r'^needs "([^"]+)"', open(R + "make.ml").read(), re.M)
t = {}
for l in open(R + "doc/timing.tsv").read().split("\n")[1:]:
    p = l.split("\t")
    if len(p) >= 2:
        try: t[p[0]] = float(p[1])
        except ValueError: pass
deps = {}
def needs(f):
    if f not in deps:
        try:
            s = open(R + f, errors="replace").read()
        except FileNotFoundError:
            s = ""
        s = re.sub(r"\(\*.*?\*\)", "", s, flags=re.S)
        deps[f] = [d for d in re.findall(r'^\s*needs\s+"([^"]+)"', s, re.M) if d.startswith(("src/", "audit/"))]
    return deps[f]
def closure(fs):
    seen, todo = set(), list(fs)
    while todo:
        f = todo.pop()
        if f in seen: continue
        seen.add(f); todo += needs(f)
    return seen
if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    c = closure(args)
    lst = [f for f in order if f in c] + sorted(c - set(order))
    print("%d files, %.0f s in HOL Light" % (len(lst), sum(t.get(f, 0) for f in lst)), file=sys.stderr)
    if "--list" in sys.argv:
        print("\n".join(lst))
