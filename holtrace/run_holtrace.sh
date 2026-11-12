#!/bin/bash
# Re-check the development with HOLTrace (https://holtrace.cr.yp.to/), in parts: trace each part, check each
# trace with HOLTrace's C checker, then replay all traces through HOL Light's kernel in one session.
#
# usage (from the repository root):   holtrace/run_holtrace.sh HOL_LIGHT_DIR WORK_DIR
#   HOL_LIGHT_DIR  a built HOL Light checkout (it must contain ocaml-hol); it is NOT modified
#   WORK_DIR       a new directory for HOLTrace, two HOLTrace copies of HOL Light, the traces and the logs
# Environment:
#   HT_SPINE       1 (default on Linux): parts 1, 2, ... are traced by processes forked from one session that
#                  loads the earlier files only once (trace_spine.ml); 0: each part in a fresh session
#   HT_JOBS        with HT_SPINE=0, the number of part traces run at the same time (default 1)
#   SETUP_ONLY     if set, stop after setting up WORK_DIR
# See holtrace/README.md for time and memory.
# A part whose trace is complete in WORK_DIR (partK.50 and a PART_DONE line in traceK.log) is not traced again,
# and a complete record of the parser's counter (WORK_DIR/counts.txt, RECORD_DONE in record.log) is not made
# again, so the script can be rerun after an interruption (remove incomplete traces and records first).
# The parts are part 0 (HOL Light's core and the base library) and holtrace/parts/part1.txt, part2.txt, ...
set -e
[ $# -eq 2 ] || { echo "usage: $0 HOL_LIGHT_DIR WORK_DIR" >&2; exit 2; }
REPO=$(pwd)
[ -f "$REPO/holtrace/trace_part.ml" ] && [ -f "$REPO/holtrace/replay.ml" ] ||
  { echo "run this from the repository root" >&2; exit 2; }
HOL=$(cd "$1" && pwd); mkdir -p "$2"; WORK=$(cd "$2" && pwd -P)
V=20250714
HT="$WORK/holtrace-$V"; HLT="$WORK/hol-light-trace"; HLR="$WORK/hol-light-replay"

echo "== 1. HOLTrace $V"
cd "$WORK"
[ -f "holtrace-$V.tar.gz" ] || curl -sSLO "https://holtrace.cr.yp.to/holtrace-$V.tar.gz"
echo "3c5f8be726d3b3c9f06b93f7a58ce49d624f9e36dcfdf6e9e9cdb9fe64528972  holtrace-$V.tar.gz" | sha256sum -c -
[ -d "$HT" ] || tar -xzf "holtrace-$V.tar.gz"
(cd "$HT" && make holtrace-verify)

echo "== 2. two HOLTrace copies of HOL Light (the original is left alone)"
OV=$(ocaml -vnum 2>/dev/null || ocaml -version | sed 's/.* //')
OLD_OCAML=; [ "$(printf '%s\n' "$OV" 5.2 | sort -V | head -1)" != "5.2" ] && OLD_OCAML=1
if [ ! -f "$HLT/INSTALLED-HOLTrace+hashtt" ]; then
  # For tracing: HOLTrace with its hashtt patch, which speeds up tracing by changing the kernel.
  rsync -a --exclude .git --exclude 'hol-*.ckpt' "$HOL"/ "$HLT"/
  (cd "$HT" && python3 install-worker install+hashtt "$HLT")
  [ -n "$OLD_OCAML" ] && { cat "$REPO/holtrace/dynarray_shim.ml" "$HLT/holtrace.ml" > "$HLT/holtrace.ml.new" &&
                           mv "$HLT/holtrace.ml.new" "$HLT/holtrace.ml"; }
fi
if [ ! -f "$HLR/INSTALLED-HOLTrace" ]; then
  # For the replay: HOLTrace's plain install, which leaves the kernel files unchanged, plus link.patch, which
  # lets the restore match a stub axiom with a theorem restored earlier in the same session.
  rsync -a --exclude .git --exclude 'hol-*.ckpt' "$HOL"/ "$HLR"/
  (cd "$HT" && python3 install-worker install "$HLR")
  [ -n "$OLD_OCAML" ] && { cat "$REPO/holtrace/dynarray_shim.ml" "$HLR/holtrace.ml" > "$HLR/holtrace.ml.new" &&
                           mv "$HLR/holtrace.ml.new" "$HLR/holtrace.ml"; }
  patch "$HLR/holtrace.ml" < "$REPO/holtrace/link.patch"
fi
[ -n "$OLD_OCAML" ] && echo "   OCaml $OV < 5.2: the Dynarray shim is prepended to holtrace.ml in both copies"

# run_hol COPY: HOLLIGHT_USE_MODULE must NOT be set, so that the copy's sources (with HOLTrace) are loaded
# instead of the precompiled library.
run_hol () { env -u HOLLIGHT_USE_MODULE HOLLIGHT_DIR="$1" "$1/ocaml-hol" -init "$1/hol.ml" -I "$1"; }
[ -n "$SETUP_ONLY" ] && { echo "setup done (SETUP_ONLY is set)"; exit 0; }

echo "== 3. record the parser's counter in the base library and the statements proved after it (untraced full"
echo "   load; see link_prelude.ml)"
cd "$REPO"
recorded () { grep -aq "$1" "$WORK/record.log" 2>/dev/null; }
if recorded RECORD_DONE; then
  echo "complete record found, not recorded again"
else
  HT_RECORD="$WORK/counts.txt" run_hol "$HLT" < holtrace/record_counter.ml > "$WORK/record.log" 2>&1 &
  RECORD_PID=$!
fi

echo "== 4. trace the parts (each starts when the record has passed the files before it)"
NPARTS=$(ls holtrace/parts | sed -n 's/^part\([0-9]*\)\.txt$/\1/p' | sort -n | tail -n 1)
PARTS="0 $(seq 1 "$NPARTS" | tr '\n' ' ')"
complete () { [ -f "$WORK/part$1.50" ] && grep -aq "PART_DONE part=$1 " "$WORK/trace$1.log" 2>/dev/null; }
until recorded RECORD_BASE_DONE || recorded RECORD_DONE; do
  { [ -n "${RECORD_PID:-}" ] && kill -0 "$RECORD_PID" 2>/dev/null; } || { echo "the record failed"; exit 1; }
  sleep 60
done
if complete 0; then echo "part 0: complete trace found, not traced again"
else HOLTRACE_SAVE="$WORK/part0.50" run_hol "$HLT" < holtrace/trace_part0.ml > "$WORK/trace0.log" 2>&1 & fi
if [ "${HT_SPINE:-1}" = 1 ] && [ -d /proc/self/fd ]; then
  # One session loads the base library and the files of the parts in stub mode, waiting for the record file by
  # file, and forks the trace of each part that is not complete yet (WORK/partK.50, WORK/traceK.log).
  HOLTRACE_SAVE="$WORK/spine.50" HT_COUNTS="$WORK/counts.txt" HT_RECORD_LOG="$WORK/record.log" HT_WORK="$WORK" \
    HT_FIRST=1 HT_LAST="$NPARTS" run_hol "$HLT" < holtrace/trace_spine.ml > "$WORK/spine.log" 2>&1
  # The forked traces outlive the spine session: wait for each to finish (or to stop writing for two hours).
  for K in $(seq 1 "$NPARTS"); do
    until complete "$K" || grep -aq "PART_FAILED part=$K " "$WORK/trace$K.log" 2>/dev/null; do
      [ $(( $(date +%s) - $(stat -c %Y "$WORK/trace$K.log" 2>/dev/null || date +%s) )) -gt 7200 ] &&
        { echo "part $K: no progress for two hours"; break; }
      sleep 60
    done
  done
else
  trace_one () {
    K=$1
    if complete "$K"; then echo "part $K: complete trace found, not traced again"; return 0; fi
    if [ "$K" = 1 ]; then NEED=RECORD_BASE_DONE
    else NEED="RECORD_FILE_DONE $(tail -n 1 "holtrace/parts/part$((K - 1)).txt") "; fi
    until recorded "$NEED" || recorded RECORD_DONE; do
      { [ -n "${RECORD_PID:-}" ] && kill -0 "$RECORD_PID" 2>/dev/null; } ||
        { echo "part $K: the record ended without reaching this part"; return 1; }
      sleep 60
    done
    HT_PART=$K HT_COUNTS="$WORK/counts.txt" HOLTRACE_SAVE="$WORK/part$K.50" run_hol "$HLT" \
      < holtrace/trace_part.ml > "$WORK/trace$K.log" 2>&1
  }
  N=0
  for K in $(seq 1 "$NPARTS"); do
    trace_one "$K" &
    N=$((N + 1))
    if [ "$N" -ge "${HT_JOBS:-1}" ]; then wait -n || true; N=$((N - 1)); fi
  done
fi
wait
recorded RECORD_DONE || echo "the record did not finish"
for K in $PARTS; do grep -a "PART_DONE part=$K " "$WORK/trace$K.log" || echo "part $K: no PART_DONE line"; done

echo "== 5. HOLTrace's C checker"
for K in $PARTS; do "$HT/holtrace-verify" < "$WORK/part$K.50"; done

echo "== 6. replay all parts through HOL Light's kernel (the replay copy), in one session"
TRACES=""; for K in $PARTS; do TRACES="$TRACES $WORK/part$K.50"; done
HT_TRACES="$TRACES" run_hol "$HLR" < holtrace/replay.ml > "$WORK/replay.log" 2>&1
grep -a "PRE_RESTORE\|RESTORED\|AXIOM \|REPLAY_DONE" "$WORK/replay.log" || true
