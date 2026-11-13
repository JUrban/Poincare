#!/usr/bin/env python3
"""prelex.py FILE...: check that Candle's REPL splits each file into the same phrases as OCaml.

Candle's REPL splits its input into phrases with a lexer of its own before parsing them (Lexer.scan and the scan
loop of cakeml candle/prover/candle_boot.ml, ported here).  It differs from OCaml's: for example a run of symbol
characters is one token, and "(" and "*" are symbol characters, so in "[(* ... *)" Candle sees no comment and
counts the words of the comment.  An "end" there lowers the nesting level, and then no ";;" ends a phrase: Candle
waits for input forever.  This compares, for each file, Candle's phrase ends, directives (needs, loads, #use) and
quotations with those of an OCaml-like lexer, and reports every difference.  Exit code 1 if any file differs.
(Written by an independent review of the port, replacing a heuristic check.)"""
import sys

SYM = set("#$&*+-/=>@^|~!?%<:.()[]{},")
def alpha(c): return ('a' <= c <= 'z') or ('A' <= c <= 'Z')
def digit(c): return '0' <= c <= '9'
def namec(c): return alpha(c) or digit(c) or c == '_' or c == "'"
def intc(c): return digit(c) or c in "_lLn"
def space(c): return c in " \t\n\r\x0b\x0c"
KW = {"begin": "begin", "end": "end", "struct": "struct", "sig": "sig", "#use": "dir", "needs": "dir", "loads": "dir"}

class S:
    def __init__(s, b): s.b, s.i = b, 0
    def peek(s): return s.b[s.i] if s.i < len(s.b) else None
    def next(s):
        if s.i < len(s.b):
            s.i += 1; return s.b[s.i - 1]
        return None

def candle_tokens(src):
    st = S(src)
    def scan_while(pred):
        while True:
            c = st.peek()
            if c is None: return False   # Candle returns None at EOF: token lost, scan ends
            if pred(c): st.next()
            else: return True
    out = []
    while True:
        a = st.i
        c = st.next()
        if c is None: break
        kind = None
        if c == ';':
            if st.peek() == ';': st.next(); kind = "semis"
            else:
                if not scan_while(lambda x: x in SYM): break
                kind = "symb"
        elif c == '(':
            if st.peek() == '*':
                st.next(); lvl = 1; ok = True
                while lvl:
                    d = st.next()
                    if d is None: ok = False; break
                    if d == '(' and st.peek() == '*': st.next(); lvl += 1
                    elif d == '*' and st.peek() == ')': st.next(); lvl -= 1
                kind = "comment" if ok else "symb"
            else: kind = "symb"
        elif c == "'":
            p = st.peek()
            if p == '\\':
                st.next()
                # scan_escaped '\''
                ok = True
                while True:
                    d = st.next()
                    if d is None: ok = False; break
                    if d == '\\': st.next(); continue
                    if d == "'": break
                if not ok: break
                kind = "char"
            elif p in (' ', '\n', '\t', '\r'): kind = "other"
            elif p is None: kind = "symb"
            else:
                st.next()
                q = st.peek()
                if q == "'": st.next(); kind = "char"
                elif q is None: kind = "other"
                else:
                    if not scan_while(namec): break
                    kind = "other"
        elif c == '"':
            ok = True
            while True:
                d = st.next()
                if d is None: ok = False; break
                if d == '\\': st.next(); continue
                if d == '"': break
            if not ok: break
            kind = "string"
        elif c == '#':
            if not scan_while(namec): break
            kind = KW.get(src[a:st.i], "other")
        elif c == '\n': kind = "newline"
        elif c == '`':
            if not scan_while(lambda x: x != '`'): break
            st.next(); kind = "quote"
        elif digit(c):
            if not scan_while(intc): break
            kind = "number"
        elif c in SYM:
            if not scan_while(lambda x: x in SYM): break
            kind = "symb"
        elif alpha(c) or c == '_':
            if not scan_while(namec): break
            kind = KW.get(src[a:st.i], "name")
        elif space(c):
            if not scan_while(lambda x: x != '\n' and space(x)): break
            kind = "spaces"
        else: kind = "other"
        out.append((kind, a, st.i))
    return out, st.i

def candle_phrases(src):
    toks, endpos = candle_tokens(src)
    level, content = 0, False
    bounds, dirs, issues, quotes = [], [], [], []
    k = 0
    while k < len(toks):
        kind, a, b = toks[k]
        if kind == "quote": quotes.append((a, b))
        if kind == "dir" and level == 0:
            j = k + 1
            while j < len(toks) and toks[j][0] == "spaces": j += 1
            if j < len(toks) and toks[j][0] == "string":
                j2 = j + 1
                while j2 < len(toks) and toks[j2][0] == "spaces": j2 += 1
                if j2 < len(toks) and toks[j2][0] == "semis":
                    dirs.append((a, src[toks[j][1]:toks[j][2]], content))
                    if content: issues.append("directive inside a phrase at %d" % a)
                    bounds.append(toks[j2][1])
                    k = j2 + 1; continue
            issues.append("REPL error: malformed directive %r at %d" % (src[a:b], a))
            k += 1; continue
        if kind not in ("spaces", "newline", "comment"): content = True
        if kind in ("begin", "struct", "sig"): level += 1
        elif kind == "end": level -= 1
        elif kind == "semis" and level == 0:
            bounds.append(a); content = False
        k += 1
    if endpos < len(src): issues.append("Candle lexer stopped at %d of %d (token at EOF)" % (endpos, len(src)))
    if level != 0: issues.append("EOF at level %d" % level)
    elif content: issues.append("EOF inside a phrase")
    return bounds, dirs, quotes, issues, toks

def ocaml_tokens(src):
    """OCaml-ish (camlp5/HOL Light) lexing: returns semis offsets, quote spans, directive calls."""
    n = len(src); i = 0; level = 0  # OCaml too ends a phrase only at a ;; outside begin/struct/sig/object ... end
    semis, quotes, dirs, comments, strings = [], [], [], [], []
    def charlit(i):
        # i at the opening tick; return end index if a char literal, else None
        if i + 2 < n + 1 and i + 2 <= n - 1 and src[i + 2] == "'" and src[i + 1] not in "\\'\n\r": return i + 3
        if i + 2 <= n - 1 and src[i + 1] == '\n' and src[i + 2] == "'": return i + 3
        if i + 1 < n and src[i + 1] == '\\':
            if i + 3 < n and src[i + 2] in "\\\"'ntbr " and src[i + 3] == "'": return i + 4
            if i + 5 < n and src[i + 2:i + 5].isdigit() and src[i + 5] == "'": return i + 6
            if i + 5 < n and src[i + 2] == 'x' and src[i + 5] == "'": return i + 6
            if i + 5 < n and src[i + 2] == 'o' and src[i + 5] == "'": return i + 6
        return None
    def string_end(i):
        # i just after opening quote
        while i < n and src[i] != '"':
            i += 2 if src[i] == '\\' else 1
        return i + 1
    def comment_end(i):
        # i just after "(*"
        lvl = 1
        while i < n and lvl:
            if src.startswith("(*", i): lvl += 1; i += 2
            elif src.startswith("*)", i): lvl -= 1; i += 2
            elif src[i] == '"': i = string_end(i + 1)
            elif src[i] == "'":
                e = charlit(i)
                i = e if e else i + 1
            else: i += 1
        return i
    while i < n:
        c = src[i]
        if src.startswith("(*", i):
            e = comment_end(i + 2); comments.append((i, e)); i = e
        elif c == '"':
            e = string_end(i + 1); strings.append((i, e)); i = e
        elif c == "'":
            e = charlit(i); i = e if e else i + 1
        elif c == '`':
            e = src.find('`', i + 1); e = n if e < 0 else e + 1
            quotes.append((i, e)); i = e
        elif src.startswith(";;", i):
            if level == 0: semis.append(i)
            i += 2
        elif alpha(c) or c == '_':
            j = i
            while j < n and namec(src[j]): j += 1
            w = src[i:j]
            if w in ("needs", "loads") and level == 0: dirs.append(i)
            elif w in ("begin", "struct", "sig", "object"): level += 1
            elif w == "end": level -= 1
            i = j
        elif c == '#' and src.startswith("#use", i):
            dirs.append(i); i += 4
        elif digit(c):
            j = i
            while j < n and (namec(src[j])): j += 1
            i = j
        else: i += 1
    return semis, quotes, dirs, comments, strings

def check(path):
    src = open(path, encoding="latin-1").read()
    bounds, cdirs, cquotes, issues, toks = candle_phrases(src)
    semis, oquotes, odirs, comments, strings = ocaml_tokens(src)
    out = list(issues)
    if bounds != semis:
        sb, so = set(bounds), set(semis)
        out.append("phrase ends differ: only Candle %s, only OCaml %s" % (sorted(sb - so)[:5], sorted(so - sb)[:5]))
    if cquotes != oquotes:
        out.append("quotes differ: only Candle %s only OCaml %s" % (sorted(set(cquotes) - set(oquotes))[:3], sorted(set(oquotes) - set(cquotes))[:3]))
    if sorted(d[0] for d in cdirs) != sorted(odirs):
        out.append("directives differ: Candle %s OCaml %s" % (sorted(set(d[0] for d in cdirs) ^ set(odirs))[:5], ""))
    # Candle comment tokens that differ from OCaml comments
    ccom = [(a, b) for k, a, b in toks if k == "comment"]
    if ccom != comments:
        d1 = sorted(set(ccom) - set(comments)); d2 = sorted(set(comments) - set(ccom))
        out.append("comments differ: %d Candle-only, %d OCaml-only; first OCaml-only %s" % (len(d1), len(d2), [src[a:b][:50] for a, b in d2[:2]]))
    return out, len(set(comments) - set(ccom))

if __name__ == "__main__":
    bad = 0; tot_ca = 0
    for p in sys.argv[1:]:
        o, ca = check(p)
        tot_ca += ca
        for msg in o:
            if msg.startswith("comments differ"): continue
            print("%s: %s" % (p, msg)); bad += 1
    print("files %d, problems %d, OCaml comments that Candle does not see as comments (harmless unless a "
          "problem is reported) %d" % (len(sys.argv) - 1, bad, tot_ca))
    sys.exit(1 if bad else 0)
