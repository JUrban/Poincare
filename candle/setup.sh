#!/bin/sh
# candle/setup.sh CANDLE_ROOT: make this repository visible from the Candle root, whose needs and loads are
# relative to the current directory.  Creates there
#   pc     -> this repository
#   audit  -> this repository's audit/
#   src/   a directory of symlinks to this repository's src/*.ml, except that each file in candle/src/ (the
#          files that Candle needs changed; see candle/REPORT.md) is linked in place of its src/ namesake.
# src/ itself is not changed, and still loads in HOL Light.
set -eu
[ $# -eq 1 ] || { echo "usage: $0 CANDLE_ROOT" >&2; exit 2; }
C=$1
P=$(cd "$(dirname "$0")/.." && pwd)
[ -f "$C/candle.sh" ] || { echo "$C does not look like a Candle root (no candle.sh)" >&2; exit 2; }
for l in pc audit; do
  if [ -e "$C/$l" ] || [ -L "$C/$l" ]; then
    [ -L "$C/$l" ] || { echo "$C/$l exists and is not a symlink" >&2; exit 2; }
    rm "$C/$l"
  fi
done
ln -s "$P" "$C/pc"
ln -s "$P/audit" "$C/audit"
if [ -e "$C/src" ] || [ -L "$C/src" ]; then
  [ -f "$C/src/.poincare_candle" ] || { echo "$C/src exists and was not made by this script" >&2; exit 2; }
  rm -r "$C/src"
fi
mkdir "$C/src"
touch "$C/src/.poincare_candle"
for f in "$P"/src/*.ml; do
  b=$(basename "$f")
  if [ -f "$P/candle/src/$b" ]; then ln -s "$P/candle/src/$b" "$C/src/$b"; else ln -s "$f" "$C/src/$b"; fi
done
for f in "$P"/candle/src/*.ml; do
  [ -f "$P/src/$(basename "$f")" ] || { echo "candle/src/$(basename "$f") has no namesake in src/" >&2; exit 2; }
done
echo "set up $C: $(ls "$P"/src/*.ml | wc -l) files in src/, $(ls "$P"/candle/src/*.ml | wc -l) of them from candle/src/"
