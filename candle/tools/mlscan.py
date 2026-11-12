#!/usr/bin/env python3
"""mlscan.py FILE...: strip OCaml comments, `term` quotations and strings, then count ML features per file."""
import re, sys, collections
def strip(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith("(*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if s.startswith("(*", i): depth += 1; i += 2
                elif s.startswith("*)", i): depth -= 1; i += 2
                else: i += 1
            out.append(" ")
        elif s[i] == "`":
            j = s.find("`", i + 1); i = n if j < 0 else j + 1; out.append(" TERM ")
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(' "STR" '); i = j + 1
        else:
            out.append(s[i]); i += 1
    return "".join(out)
FEATS = {k: re.compile(v) for k, v in {
    "when": r"\bwhen\b", "function": r"\bfunction\b", "for": r"\bfor\b", "while": r"\bwhile\b",
    "begin": r"\bbegin\b", "raise": r"\braise\b", "try": r"\btry\b", "lazy": r"\blazy\b", "<-": r"<-",
    "record": r"\{[^}]*=", "Printf": r"\bPrintf\.", "Hashtbl": r"\bHashtbl\.", "List.": r"\bList\.\w+",
    "String.": r"\bString\.\w+", "Char.": r"\bChar\.\w+", "Gc": r"\bGc\.", "Array": r"\bArray\.",
    "mutable": r"\bmutable\b", "module": r"\bmodule\b", "exception": r"\bexception\b", "as": r"\bas\b",
    "char": r"'[^' ]'|'\\.'", "assert": r"\bassert\b", "match": r"\bmatch\b", "label": r"[~?][a-z_]+:",
    "polyvar": r"`[A-Z]", "obj": r"\bObj\.", "Sys": r"\bSys\.", "ignore": r"\bignore\b", "lsl": r"\b(lsl|lsr|land|lor|lxor|mod)\b",
    "float": r"\b\d+\.\d*\b|\bfloat_of|\+\.|\*\.", "Num": r"\bNum\.|\b(num_of_int|int_of_num|Int|power_num)\b", "%!": r"%!"}.items()}
files = collections.Counter(); names = collections.defaultdict(collections.Counter); where = collections.defaultdict(list)
for f in sys.argv[1:]:
    t = strip(open(f, errors="replace").read())
    for k, rx in FEATS.items():
        ms = rx.findall(t)
        if ms:
            files[k] += 1; where[k].append(f)
            if k in ("List.", "String.", "Char.", "Hashtbl"): names[k].update(ms)
for k in FEATS:
    if files[k]:
        print("%-9s %4d files  e.g. %s" % (k, files[k], " ".join(w.split("/")[-1] for w in where[k][:4])))
for k, c in names.items():
    print(k, dict(c))
