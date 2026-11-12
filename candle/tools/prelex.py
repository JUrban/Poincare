#!/usr/bin/env python3
"""prelex.py FILE...: emulate the phrase scanner of Candle's REPL (cakeml candle/prover/candle_boot.ml, Lexer.scan and
the scan loop) on each file, and report what makes it split phrases differently from OCaml:

* a comment that starts inside a run of symbol characters (as in "[(*" or ",(*"): Candle reads the run as one symbol,
  so the comment's words become tokens.  Harmless unless they include a keyword that changes the nesting level
  (begin, end, struct, sig), a backquote (a quotation), a string quote, ";;" or a load directive;
* a ";;" at a nonzero level (phrases merged), a level below 0, a directive at a nonzero level (not loaded),
  and a file that ends at a nonzero level or with an unterminated phrase.

Exit code 1 if any file has a problem that changes how it loads."""
import re, sys

SYMCHARS = set("#$&*+-/=>@^|~!?%<:.()[]{},")
KEYWORDS = {"begin": "begin", "end": "end", "struct": "struct", "sig": "sig", "use": "dir", "needs": "dir",
            "loads": "dir"}


def is_name_char(c):
    return c.isascii() and (c.isalnum() or c in "_'")


def tokens(s):
    """(kind, text, line) as Candle's Lexer.scan produces them."""
    i, n, line = 0, len(s), 1
    while i < n:
        c, start, l0 = s[i], i, line
        i += 1
        if c == ";" and i < n and s[i] == ";":
            i += 1; kind = "semis"
        elif c == "(" and i < n and s[i] == "*":
            i += 1; level = 1
            while i < n and level:
                if s.startswith("(*", i): level += 1; i += 2
                elif s.startswith("*)", i): level -= 1; i += 2
                else: i += 1
            kind = "comment"
        elif c == "'":
            if i < n and s[i] == "\\":
                i += 1
                while i < n and s[i] != "'":
                    i += 2 if s[i] == "\\" else 1
                i += 1; kind = "char"
            elif i < n and s[i] in " \n\t\r": kind = "other"
            elif i < n and s[i] == "'": kind = "symb"   # Candle does not consume the second tick
            elif i < n:
                i += 1
                if i < n and s[i] == "'": i += 1; kind = "char"
                else:
                    while i < n and is_name_char(s[i]): i += 1
                    kind = "other"
            else: kind = "symb"
        elif c == '"':
            while i < n and s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1; kind = "string"
        elif c == "#":
            while i < n and is_name_char(s[i]): i += 1
            kind = KEYWORDS.get(s[start:i], "name")
        elif c == "\n": kind = "newline"
        elif c == "`":
            while i < n and s[i] != "`": i += 1
            i += 1; kind = "quote"
        elif c.isdigit():
            while i < n and (s[i].isdigit() or s[i] in "_lLn"): i += 1
            kind = "number"
        elif c in SYMCHARS:
            while i < n and s[i] in SYMCHARS: i += 1
            kind = "symb"
        elif c.isascii() and (c.isalpha() or c == "_"):
            while i < n and is_name_char(s[i]): i += 1
            kind = KEYWORDS.get(s[start:i], "name")
        elif c.isspace():
            while i < n and s[i] != "\n" and s[i].isspace(): i += 1
            kind = "spaces"
        else: kind = "other"
        text = s[start:i]
        line += text.count("\n")
        yield kind, text, l0


def check(path):
    src = open(path, errors="replace").read()
    toks = list(tokens(src))
    problems, notes = [], []
    # comments that Candle does not see: a symbol token containing "(*"
    for k, (kind, text, line) in enumerate(toks):
        if kind == "symb" and "(*" in text:
            # the words up to the matching "*)" in OCaml's reading
            j = src.index("(*", sum(len(t) for _, t, _ in toks[:k]) + text.index("(*"))
            d, e = 1, j + 2
            while e < len(src) and d:
                if src.startswith("(*", e): d += 1; e += 2
                elif src.startswith("*)", e): d -= 1; e += 2
                else: e += 1
            body = src[j:e]
            bad = sorted(set(re.findall(r"\b(begin|end|struct|sig|use|needs|loads)\b", body)) |
                         ({"`"} if "`" in body else set()) | ({'"'} if '"' in body else set()) |
                         ({";;"} if ";;" in body else set()))
            (problems if bad else notes).append("%d: comment after %r read as code%s: %s" % (
                line, text[:text.index("(*")], " (contains %s)" % " ".join(bad) if bad else "",
                body[:80].replace("\n", " ")))
    # the scan loop
    level, content, start = 0, False, None
    k = 0
    while k < len(toks):
        kind, text, line = toks[k]
        if kind == "dir" and level == 0:
            # a directive: string then semis (the file is loaded in place; the phrase goes on)
            rest = [t for t in toks[k + 1:k + 6] if t[0] != "spaces"]
            if len(rest) >= 2 and rest[0][0] == "string" and rest[1][0] == "semis":
                k = toks.index(rest[1], k + 1) + 1
                continue
        if kind == "dir" and level != 0:
            problems.append("%d: %s at level %d, not loaded" % (line, text, level))
        if kind not in ("spaces", "newline", "comment"):
            if not content: start = line
            content = True
        if kind in ("begin", "struct", "sig"): level += 1
        elif kind == "end":
            level -= 1
            if level < 0: problems.append("%d: level %d after 'end'" % (line, level))
        elif kind == "semis":
            if level == 0: content = False
            else: problems.append("%d: ';;' at level %d does not end the phrase" % (line, level))
        k += 1
    if level != 0: problems.append("end of file at level %d" % level)
    elif content: problems.append("end of file inside a phrase (from line %s)" % start)
    return problems, notes


bad = 0
quiet = "-q" in sys.argv
for p in [a for a in sys.argv[1:] if a != "-q"]:
    problems, notes = check(p)
    for m in problems:
        print("%s:%s" % (p, m)); bad += 1
    if not quiet:
        for m in notes: print("%s:%s (harmless)" % (p, m))
sys.exit(1 if bad else 0)
