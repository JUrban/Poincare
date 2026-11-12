#!/usr/bin/env python3
"""gen_make.py: write candle/make.ml from make.ml: the same needs lines in the same order, without the Gc.set line
(Candle has no Gc module and no records), with candle/prelude.ml before the library and candle/compat.ml after it.
gen_make.py --check: exit 1 if candle/make.ml is not what this would write."""
import re, sys
R = "/project/repos/Poincare/"
needs = re.findall(r'^needs "([^"]+)";;', open(R + "make.ml").read(), re.M)
lib = [f for f in needs if not f.startswith("src/")]
assert needs[:len(lib)] == lib == ["Multivariate/cauchy.ml", "Multivariate/lpspaces.ml", "100/green.ml"], lib
out = ["(* ========================================================================= *)",
       "(* make.ml for Candle, written by candle/tools/gen_make.py from make.ml:     *)",
       "(* the same files in the same order, without make.ml's Gc.set line (Candle  *)",
       "(* has no Gc module), with prelude.ml before the library and compat.ml     *)",
       "(* after it.  Run from the Candle root after candle/setup.sh.               *)",
       "(* ========================================================================= *)", "",
       'loads "pc/candle/prelude.ml";;'] + ['needs "%s";;' % f for f in lib] + ['loads "pc/candle/compat.ml";;'] + \
      ['needs "%s";;' % f for f in needs[len(lib):]]
text = "\n".join(out) + "\n"
if "--check" in sys.argv:
    sys.exit(0 if open(R + "candle/make.ml").read() == text else 1)
open(R + "candle/make.ml", "w").write(text)
print("candle/make.ml: %d library files, %d src files" % (len(lib), len(needs) - len(lib)))
