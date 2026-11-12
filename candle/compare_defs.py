#!/usr/bin/env python3
"""compare_defs.py [--final | --tydefs | --results] [--allow-only NAME,...] LOG_A LOG_B: compare two sessions' dumps.

Default: both logs have candle/dump_defs.ml's output (every kernel definition, constant and type operator), for
example the short sessions of candle/statements.ml on HOL Light and on Candle with the recorder.  Every
definition on both sides must be identical; so must the dependency cones of the statement constants, and the
constants and type operators of both sessions, apart from those expected on one side only.
--final: LOG_A as above; LOG_B from candle/dump_final.ml in a proving session, which prints the definitions of
the statement files only, and all constants and type operators (of the much larger session).  Each definition of
LOG_B must be LOG_A's, and every constant and type operator of the cones (from LOG_A) must have the same type
and arity in LOG_B.
--tydefs: both logs have candle/dump_tydefs.ml's output; the type definition theorems are compared.
--results: both logs have candle/dump_thms.ml's output; the results must be identical, with no hypotheses.

Names numbered by the session are renamed, injectively within each line.  A log may hold several dumps; each
mode reads the lines it needs.  The exit code is 0 only if the verdict is positive."""
import re, sys

ROOTS = ["POINCARE_STATEMENT", "POINCARE_SMOOTH_STATEMENT", "POINCARE_EMBEDDED_STATEMENT",
         "MOISE_SMOOTHING_STATEMENT"]
AUDIT_ROOTS = ["BLIND_POINCARE_TOP", "BLIND_POINCARE_SMOOTH"]  # audit/poincare_blind.ml
RESULTS = 38  # the 4 headline theorems, 4 audit results and 30 sanity theorems
HOL_LIGHT_ONLY = {"hashek"}  # thecops.ml, which Candle's hol_lib.ml does not load
CANDLE_ONLY = re.compile(r"Cexp_\w+|_dest_cval|_mk_cval|cval\w*|generated:.*cval.*")  # candle/compute.ml
ANSI = re.compile(r"\x1b\[[0-9;]*m")
GENERATED = re.compile(r"\?\d+|GEN%PVAR%\d+|(?<=[( ])_[1-9]\d*(?= )")  # not _0, HOL Light's real constant
MARKERS = ("DEFDUMP ", "CONSTDUMP ", "TYPEDUMP ", "TYDEFDUMP ", "THMDUMP ")


def canon(text):
    """Rename parser-invented type variables (?123) and variables (GEN%PVAR%123) and generated names
    (_123), whose numbers depend on the session's history, by first occurrence within one line."""
    seen = {}
    return GENERATED.sub(lambda m: seen.setdefault(m.group(0), "%sG%d" % (m.group(0).rstrip("0123456789"), len(seen))),
                         text)


def term(path, raw):
    if raw.count("(") != raw.count(")"):
        sys.exit("%s: truncated line: %s" % (path, raw[:200]))
    return canon(raw)


def read(path):
    defs, consts, types, thms, tydefs, done = {}, {}, {}, {}, set(), False
    for line in open(path, errors="replace"):
        line = re.sub(r"^[#>] +", "", ANSI.sub("", line).strip())  # a toplevel prompt may precede the first line
        if line == "DUMP_DONE" or line == "THMDUMP_DONE":
            done = True
        if not line.startswith(MARKERS):
            if any(m in line for m in MARKERS) and not line.startswith(("print_string", "do_list")):
                sys.exit("%s: a marker inside a line: %s" % (path, line[:200]))
        elif line.startswith("DEFDUMP "):
            names = re.findall(r"\(C (\S+) ", line)
            if len(names) < 2 or names[0] != "=":
                sys.exit("%s: unexpected definition shape: %s" % (path, line[:200]))
            body = term(path, line[8:])
            # a generated constant has no stable name: key it by its whole definition
            key = body if re.fullmatch(r"_[1-9]\d*", names[1]) else names[1]
            if body not in defs.setdefault(key, []):  # a log may hold the same definition twice
                defs[key].append(body)
        elif line.startswith("TYDEFDUMP "):
            tydefs.add(term(path, line[10:]))
        elif line.startswith("THMDUMP "):
            _, n, hyps, body = line.split(" ", 3)
            thms[n] = (hyps, term(path, body))
        elif line.startswith("CONSTDUMP "):
            _, n, ty = line.split(" ", 2)
            # a generated constant has no stable name: compare the number of such constants of each type
            if re.fullmatch(r"_[1-9]\d*", n):
                n = "generated:%s:%d" % (canon(ty), sum(k.startswith("generated:" + canon(ty) + ":") for k in consts))
            consts[n] = term(path, ty)
        else:
            _, n, k = line.split(" ")
            types[n] = k
    if not done:
        sys.exit("%s: no DUMP_DONE or THMDUMP_DONE, so the dump is incomplete" % path)
    return defs, consts, types, thms, tydefs


def show(label, xs):
    xs = sorted(xs)
    print("%s: %d%s" % (label, len(xs), (" " + " ".join(xs[:40]) + (" ..." if len(xs) > 40 else "")) if xs else ""))


def finish(word, ok):
    print(word + ("_IDENTICAL" if ok else "_DIFFER"))
    return ok


def cone(defs, root):
    """The constants that root depends on through the definitions in defs, and those of them without one."""
    seen, todo, undefined = set(), [root], set()
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        if n not in defs:
            undefined.add(n)
            continue
        for body in defs[n]:
            todo += re.findall(r"\(C (\S+) ", body)
    return seen, undefined


def tyops(text):
    """The type operators occurring in a dumped term or type."""
    return set(re.findall(r"\((?!C |V |A |L )([^\s()]+)", text))


flags = ("--final", "--tydefs", "--results")
args = [a for a in sys.argv[1:] if a not in flags]
allow = set()
if "--allow-only" in args:
    i = args.index("--allow-only"); allow = set(args[i + 1].split(",")); del args[i:i + 2]
mode = ([f for f in flags if f in sys.argv] or ["--defs"])[0]
ad, ac, at, athm, atd = read(args[0])
bd, bc, bt, bthm, btd = read(args[1])

if mode == "--tydefs":
    print("type definition theorems: A %d, B %d, on both sides %d" % (len(atd), len(btd), len(atd & btd)))
    extra = btd - atd
    print("only in A: %d; only in B: %d, of which about Candle's cval: %d"
          % (len(atd - btd), len(extra), sum("cval" in x for x in extra)))
    sys.exit(0 if finish("TYDEFS", bool(atd) and not atd - btd and all("cval" in x for x in extra)) else 1)

if mode == "--results":
    same = [n for n in athm if bthm.get(n) == athm[n]]
    print("results: A %d, B %d, identical %d; with hypotheses: A %d, B %d"
          % (len(athm), len(bthm), len(same), sum(h != "0" for h, _ in athm.values()),
             sum(h != "0" for h, _ in bthm.values())))
    show("results that differ", (set(athm) | set(bthm)) - set(same))
    ok = len(same) == RESULTS == len(athm) == len(bthm) and all(h == "0" for h, _ in bthm.values())
    sys.exit(0 if finish("RESULTS", ok) else 1)

print("definitions: A %d constants, B %d" % (len(ad), len(bd)))
print("constants: A %d, B %d; types: A %d, B %d" % (len(ac), len(bc), len(at), len(bt)))
if not ad or not bd:
    sys.exit("empty dump")
roots = ROOTS + [r for r in AUDIT_ROOTS if r in ad]
diff = [n for n in set(ad) & set(bd) if sorted(ad[n]) != sorted(bd[n])]
show("defined on both sides, with different definitions", diff)

if mode == "--final":
    ok = not diff and bool(bd)
    show("defined in B only", set(bd) - set(ad))
    ok = ok and not (set(bd) - set(ad))
    for r in roots:
        seen, undefined = cone(ad, r)
        consts_bad = [n for n in seen if ac.get(n) is None or bc.get(n) != ac[n]]
        ops = set()
        for n in seen:
            ops |= tyops(ac.get(n, "")) | set().union(*(tyops(b) for b in ad.get(n, [])))
        ops_bad = [o for o in ops if at.get(o) is None or bt.get(o) != at[o]]
        good = not consts_bad and not ops_bad and r in bd
        ok = ok and good
        print("cone of %-28s %4d constants, %2d type operators: in B %s, same types%s"
              % (r, len(seen), len(ops), "defined" if r in bd else "NOT DEFINED",
                 "" if good else " NO: " + " ".join(sorted(consts_bad + ops_bad)[:20])))
    sys.exit(0 if finish("FINAL", ok) else 1)

show("defined only in A", set(ad) - set(bd))
show("defined only in B", set(bd) - set(ad))
only_a, only_b = set(ac) - set(bc), set(bc) - set(ac)
show("constants only in A", only_a)
show("constants only in B", only_b)
unexpected = (only_a - HOL_LIGHT_ONLY - allow) | {n for n in only_b if not CANDLE_ONLY.fullmatch(n) and n not in allow}
show("of those, not expected on one side only", unexpected)
tydiff = [n for n in set(ac) & set(bc) if ac[n] != bc[n]]
show("constants with different types", tydiff)
show("types only in A", set(at) - set(bt))
show("types only in B", set(bt) - set(at))
arity = [n for n in set(at) & set(bt) if at[n] != bt[n]]
show("types with different arity", arity)
ok = not (diff or unexpected or tydiff or arity or (set(at) - set(bt) - allow) or (set(bt) - set(at) - {"cval"} - allow))
no_def = set()
for root in roots:
    seen, undefined = cone(bd, root)
    no_def |= undefined
    same = all(n in ad and sorted(ad[n]) == sorted(bd[n]) for n in seen - undefined)
    same = same and all(n not in ad and n in ac and ac[n] == bc.get(n) for n in undefined)
    ok = ok and same and root in bd and root in ad
    print("cone of %-28s %5d constants, %3d without a definition on either side, identical: %s"
          % (root, len(seen), len(undefined), same))
show("constants in the cones without a term definition (same type on both sides)", no_def)
sys.exit(0 if finish("CONES", ok) else 1)
