#!/usr/bin/env python3
"""convert_printf.py SRC DST: copy SRC to DST, replacing each Printf.printf "fmt" a1 ... an by
print_string ("..." ^ string_of_bool (a1) ^ ...), for the conversions %b, %d, %s and %! that src/ uses.
Candle has no Printf.  Arguments are split at depth 0 (parentheses, brackets, term quotations, strings)."""
import re, sys

def args_until_end(s, i):
    """Parse whitespace-separated arguments from s[i:] up to the ';;' or ' in' ending the expression."""
    args, depth, cur, j = [], 0, "", i
    while j < len(s):
        c = s[j]
        if depth == 0 and s.startswith(";;", j):
            break
        if depth == 0 and re.match(r"\bin\b", s[j:j + 3]) and (j == 0 or s[j - 1].isspace()):
            break
        if c == "`":
            k = s.index("`", j + 1); cur += s[j:k + 1]; j = k + 1; continue
        if c == '"':
            k = j + 1
            while s[k] != '"':
                k += 2 if s[k] == "\\" else 1
            cur += s[j:k + 1]; j = k + 1; continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        if depth == 0 and c.isspace():
            if cur.strip():
                args.append(cur.strip())
            cur = ""
        else:
            cur += c
        j += 1
    if cur.strip():
        args.append(cur.strip())
    return args, j

def convert(fmt, args):
    pieces, ai, lit = [], 0, ""
    k = 0
    while k < len(fmt):
        if fmt[k] == "%":
            d = fmt[k + 1]
            if d == "!":
                k += 2; continue
            if lit:
                pieces.append('"%s"' % lit); lit = ""
            a = args[ai]; ai += 1
            pieces.append({"b": "string_of_bool (%s)", "d": "string_of_int (%s)", "s": "(%s)"}[d] % a)
            k += 2
        else:
            lit += fmt[k]; k += 1
    if lit:
        pieces.append('"%s"' % lit)
    assert ai == len(args), (fmt, args)
    return "print_string (" + " ^\n   ".join(pieces) + ")"

src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
out, pos, n = [], 0, 0
for m in re.finditer(r'Printf\.printf\s*"((?:[^"\\]|\\.)*)"', s):
    if m.start() < pos:
        continue
    args, end = args_until_end(s, m.end())
    out.append(s[pos:m.start()]); out.append(convert(m.group(1), args)); pos = end; n += 1
out.append(s[pos:])
open(dst, "w").write("".join(out))
print("%s: %d calls converted" % (src, n))
