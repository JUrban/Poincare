#!/bin/sh
# candle/setup.sh CANDLE_ROOT: make this repository visible from the Candle root, whose needs and loads are
# relative to the current directory.  Creates there
#   pc     -> this repository
#   src/, audit/  directories of symlinks to this repository's src/*.ml and audit/*.ml, except that each file
#          in candle/src/ or candle/audit/ (the files that Candle needs changed; see candle/REPORT.md) is linked
#          in place of its namesake.
# src/ and audit/ themselves are not changed, and still load in HOL Light.
set -eu
[ $# -eq 1 ] || { echo "usage: $0 CANDLE_ROOT" >&2; exit 2; }
C=$1
P=$(cd "$(dirname "$0")/.." && pwd)
[ -f "$C/candle.sh" ] || { echo "$C does not look like a Candle root (no candle.sh)" >&2; exit 2; }
for l in pc; do
  if [ -e "$C/$l" ] || [ -L "$C/$l" ]; then
    [ -L "$C/$l" ] || { echo "$C/$l exists and is not a symlink" >&2; exit 2; }
    rm "$C/$l"
  fi
done
ln -s "$P" "$C/pc"
for d in src audit; do
  if [ -e "$C/$d" ] || [ -L "$C/$d" ]; then
    [ -f "$C/$d/.poincare_candle" ] || { echo "$C/$d exists and was not made by this script" >&2; exit 2; }
    rm -r "$C/$d"
  fi
  mkdir "$C/$d"
  touch "$C/$d/.poincare_candle"
  for f in "$P/$d"/*.ml; do
    b=$(basename "$f")
    if [ -f "$P/candle/$d/$b" ]; then ln -s "$P/candle/$d/$b" "$C/$d/$b"; else ln -s "$f" "$C/$d/$b"; fi
  done
  for f in "$P/candle/$d"/*.ml; do
    [ -f "$P/$d/$(basename "$f")" ] || { echo "candle/$d/$(basename "$f") has no namesake in $d/" >&2; exit 2; }
  done
  echo "$d/: $(ls "$P/$d"/*.ml | wc -l) files, $(ls "$P/candle/$d"/*.ml | wc -l) of them from candle/$d/"
done
