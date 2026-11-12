# Re-checking the development with HOLTrace

[HOLTrace](https://holtrace.cr.yp.to/) (D. J. Bernstein) records a trace of every primitive inference of a HOL
Light session and checks traces independently. This directory re-checks the whole development, from HOL Light's
core through the Multivariate library to every file in `src/`, in two ways:

1. **HOLTrace's C checker** (`holtrace-verify`). It is written independently of HOL Light and verifies every
   inference in a trace.
2. **A replay through HOL Light's own kernel**, in one fresh session where the base library and the
   human-readable statement files (`src/poincare_statement.ml`, `src/pc_interfaces.ml`) have been loaded first.
   The replay *matches* every constant of a trace that already exists in the session: for each one, the kernel
   checks that the trace's definition is alpha-equivalent to the session's. So the restored headline theorems are
   theorems about exactly the constants defined in those files.

## Why in parts

A trace of a session keeps every term and theorem of the session, and so do the checker and the replay. The
whole development in one session would give a trace of about 16 GB (the proofs in the traces of our parts add up
to 16.0 GB). Recording took about 20 bytes of memory per byte of trace, so a single session would need about
300 GiB. The development is therefore traced in parts:

- **part 0**: HOL Light's core and the base library (Multivariate up to `cauchy.ml`, `lpspaces.ml` and
  `100/green.ml`);
- **parts 1 to 10**: consecutive pieces of the load order of `make.ml` (the files are listed in
  `parts/partK.txt`).

In the trace of part k, the files of part k are proved in full. The base library and the files of parts 1 to
k-1 come before them, in the order of `make.ml`, loaded in *stub mode*: every theorem they prove (with `prove`,
`MESON`, `REAL_ARITH` and a few other derived rules) is introduced as an axiom of the same statement instead of
being proved again (`link_prelude.ml`). In full mode every such theorem is named `HTLINK_k` in the trace. Each
part's trace is complete in itself: the C checker checks it, taking its stub axioms as given.

Stub mode keeps the files' own control flow, so that it defines the same constants and states the same theorems
as a full load:

- After the base library, a statement is stubbed only if it was proved in a full load of the same files (the
  *record*, below); any other statement is proved in full. So a file that tries a proof and catches its failure
  takes the same branch in stub mode as in a full load. A `MESON` call given a theorem with hypotheses is always
  run: its result has hypotheses, which an axiom cannot have.
- The parser names the type variables it invents `?N`, with N from a counter, and `define_type` names its
  auxiliary constants `_N` with the counter of `genvar`. 171 constants of the base library have such type
  variables, as do four constants of `100/pick.ml` and `100/polyhedron.ml` (which files of `src/` load with type
  invention allowed), and every `define_type` has auxiliary constants. A skipped proof does not parse or
  build what its tactic would, so these counters would fall behind and the constants would be defined with other
  names, which the replay rejects. So in the base library, after each skipped proof, the parser's counter is set
  to its value in a full load at that point; after the base library, each library file that is loaded starts
  with the parser's counter at a fixed value, and each `define_type` with the `genvar` counter at a fixed value
  (larger than either counter otherwise gets). Both counters are local to HOL Light, so the prelude reaches them
  through the closures of `retypecheck` and `genvar` (OCaml's `Obj` module). This affects only names: a wrong
  value would make the replay reject a trace, not accept a wrong theorem.
- `record_counter.ml` makes the record: an untraced full load of everything in the order of `make.ml` that
  writes the parser's counter after each proof of the base library and a hash of the statement of every proof
  that succeeds after it.

Much of the time of stub mode goes into parsing terms. To save the parsing of tactics that are never run, a file of
`src/` is loaded in stub mode from a copy in which each `prove (t, tac)` reads
`ht_prove_lazy (t, (fun () -> tac))`, so that the tactic is built only if the proof is done in full. Files
proved in full are loaded unchanged.

On Linux, the parts are traced by processes forked from one session (`trace_spine.ml`). This *spine* loads the
base library and the files of parts 1, 2, ... in stub mode once, as each trace of a part would, and at the start
of part k forks a process that copies the spine's trace so far to `partk.50`, continues the trace there and loads
the files of part k in full. So each file is loaded in stub mode only once, and each part's trace is the one that
a fresh session of part k would write (we checked that the two are byte for byte the same on a small partition).
The spine runs alongside the record: before loading a file it waits until the record has passed that file.
Elsewhere (`HT_SPINE=0`), each part is traced in a fresh session (`trace_part.ml`).

Stub mode only splits the work: nothing is left unchecked. The replay restores the parts in order, part 0 first,
in one session. When a trace introduces an axiom, the restore first looks for it among HOL Light's axioms, as
usual. Failing that, it now looks for a theorem with the same statement among the `HTLINK` theorems restored from
the earlier parts, and uses that theorem. The statements must agree exactly, up to the names of bound variables
(the parser numbers the bound variable of a set comprehension with a counter); `ALPHA` then gives exactly the
axiom's statement. This is the only change to HOLTrace, a 9-line patch to its restore function (`link.patch`);
HOLTrace's kernel files, its tracer and its checker are used unchanged. No axiom can be created by the replay:
the restores run with new axioms disallowed (new definitions allowed), and the session's list of axioms is
printed at the end.

## Files

- `run_holtrace.sh HOL_LIGHT_DIR WORK_DIR` (run from the repository root) does everything:
  1. downloads and builds HOLTrace 20250714;
  2. installs it into two copies of your HOL Light, one with the `hashtt` speed-up for tracing, one plain for the
     replay, to which it applies `link.patch` (your HOL Light is not modified);
  3. makes the record (in the background);
  4. traces part 0, and the other parts with the spine (or, with `HT_SPINE=0`, in fresh sessions, `HT_JOBS` at
     a time), each part as soon as the record has passed the files before it;
  5. runs the C checker on each trace;
  6. replays all traces in one session.
- `link_prelude.ml`: full and stub mode, loaded right after HOL Light's core in each tracing session and in the
  record.
- `record_counter.ml`: the record (see above).
- `trace_part0.ml`: the tracing session of part 0; `trace_spine.ml`: the spine; `trace_part.ml`: the tracing
  session of one part k >= 1 (with `HT_SPINE=0`); `name_headlines.ml` names the headline theorems in the trace of
  the last part.
- `parts/partK.txt`: the files proved in full in part k.
- `replay.ml`: the replay session; it checks the headline theorems and prints the axioms. With `HT_WAIT` set it
  restores each trace once the file `TRACE.done` exists, so that it can run while later parts are traced.
- `link.patch`: the change to HOLTrace's restore described above.
- `dynarray_shim.ml`: the five `Dynarray` operations HOLTrace uses, for OCaml older than 5.2.

## Requirements and resources

- A built HOL Light, with the `ocaml-hol` toplevel and camlp5. We used HOL Light commit `2828953e` (2026-11-10),
  the parent of the commit `e5236a58` that the main README recommends, with OCaml 4.14.1. Also gcc, python3, rsync, curl and patch; the spine needs Linux (`fork`, `/proc`).
- Measured on our machine (each session uses one core; wall-clock times include waiting for memory on a shared
  machine):

  | step | time | peak memory |
  |---|---|---|
  | record (untraced full load) | 7.6 h | 23 GiB |
  | part 0 (fresh session) | 1.8 h | 47 GiB |
  | part 1 (fresh session) | 2.9 h | 49 GiB |
  | spine (stub mode, parts 2-10 forked as the record advanced) | 6.0 h | 39 GiB |
  | each of parts 2-10 (forked; CPU time of the process) | 0.9-2.1 h | 35-59 GiB, including the pages it shares with the spine |
  | C checker, per part | 25-48 s | 9-17 GiB |
  | replay of all parts (one session, checkpointed once) | about 16 h (CPU) | 46 GiB (up to the checkpoint) |

  The record, the spine and the parts ran at the same time: all eleven traces were done 8.2 h after parts 0
  and 1 started (9.1 h after the record started).

- `HOLLIGHT_USE_MODULE` must not be set. The patched sources have to be loaded, so HOL Light is started with
  `ocaml-hol -init hol.ml`, not through `hol.sh`.
- Tracing cannot be combined with checkpointing: each tracing session (part 0, the spine, the record) starts from
  HOL Light's sources, and the traces of the other parts start in processes forked from the spine.

## Results of our run

HOL Light commit `2828953e`, OCaml 4.14.1, HOLTrace 20250714; parts 0 and 1 in fresh sessions, parts 2 to 10
forked from the spine. Each line of the C checker is `verified N bytes, ... infs, ... thms, K typedefs`.

| part | files | trace | inferences | types | terms | type definitions | stub axioms | `HTLINK` theorems |
|---|---|---|---|---|---|---|---|---|
| 0 | the base library | 2.43 GB | 86,672,596 | 349,434 | 163,426,712 | 25 | 0 | 31,560 |
| 1 | 337 | 2.27 GB | 77,479,311 | 273,548 | 137,970,002 | 29 | 30,740 | 13,907 |
| 2 | 203 | 1.74 GB | 57,231,149 | 260,622 | 107,159,626 | 29 | 40,140 | 10,916 |
| 3 | 121 | 1.24 GB | 39,925,718 | 225,020 | 79,723,065 | 29 | 44,735 | 8,222 |
| 4 | 113 | 1.35 GB | 43,321,596 | 245,004 | 85,198,353 | 29 | 49,017 | 6,211 |
| 5 | 87 | 1.44 GB | 46,145,665 | 224,753 | 95,074,946 | 29 | 52,391 | 6,279 |
| 6 | 39 | 1.73 GB | 57,993,379 | 193,972 | 107,440,698 | 29 | 55,970 | 5,237 |
| 7 | 65 | 2.02 GB | 66,275,432 | 204,666 | 134,674,827 | 29 | 58,669 | 5,088 |
| 8 | 47 | 2.31 GB | 77,446,605 | 209,577 | 148,091,511 | 29 | 61,105 | 4,012 |
| 9 | 55 | 2.19 GB | 72,066,634 | 205,284 | 147,615,813 | 29 | 63,114 | 4,139 |
| 10 | 23 | 1.36 GB | 42,043,370 | 199,495 | 94,529,596 | 29 | 65,197 | 2,267 |
| all | 1,090 | 20.09 GB | 666,601,455 | | | | | |

The C checker accepted every trace. In every part no statement had to be proved in full for lack of a record
(`unproved=0`) and the counters agreed with the record at every proof of the base library
(`counter_corrections=0`). The stub-mode prefixes account for 4.07 GB of the 20.09 GB.

The replay restored the eleven traces in order, in one session of the replay copy (HOLTrace's plain install and
`link.patch`), after the base library and the statement files had been loaded. The session ran under DMTCP: it
was checkpointed once and restored after a reboot of the machine, during part 6.

| part | constants matched | constants created | types matched | types created | `HTLINK` theorems | stub axioms linked |
|---|---|---|---|---|---|---|
| 0 | 848 | 0 | 25 | 0 | 31,560 | 0 |
| 1 | 858 | 1,393 | 25 | 4 | 13,907 | 27,719 |
| 2 | 2,251 | 466 | 29 | 0 | 10,916 | 36,981 |
| 3 | 2,717 | 552 | 29 | 0 | 8,222 | 41,415 |
| 4 | 3,269 | 260 | 29 | 0 | 6,211 | 45,580 |
| 5 | 3,529 | 358 | 29 | 0 | 6,279 | 48,860 |
| 6 | 3,887 | 233 | 29 | 0 | 5,237 | 52,392 |
| 7 | 4,120 | 183 | 29 | 0 | 5,088 | 54,942 |
| 8 | 4,303 | 159 | 29 | 0 | 4,012 | 57,345 |
| 9 | 4,462 | 167 | 29 | 0 | 4,139 | 59,316 |
| 10 | 4,629 | 39 | 29 | 0 | 2,267 | 61,344 |
| all | 34,873 | 3,810 | 311 | 4 | 97,838 | 485,894 |

No axiom was created: every stub axiom was matched with a theorem restored from an earlier part, and the three
axioms that each trace introduces for HOL Light's own axioms were found among the session's axioms. The traces'
definitions of `POINCARE_STATEMENT`, `POINCARE_SMOOTH_STATEMENT`, `POINCARE_EMBEDDED_STATEMENT` and
`MOISE_SMOOTHING_STATEMENT` were matched, in each of parts 1 to 10, with the constants defined by the statement
files. At the end the replay printed

```
RESTORED_CHECK POINCARE_TOP hyps=0 concl_is_POINCARE_STATEMENT_at_a_type_variable=true
RESTORED_CHECK POINCARE_SMOOTH hyps=0 concl_is_POINCARE_SMOOTH_STATEMENT_at_a_type_variable=true
RESTORED_CHECK POINCARE_EMBEDDED hyps=0 concl_is_POINCARE_EMBEDDED_STATEMENT_at_a_type_variable=true
RESTORED_CHECK MOI_SST_HEADLINE hyps=0 concl=forall u. MOISE_SMOOTHING_STATEMENT u
AXIOM exists f. ONE_ONE f /\ ~ONTO f
AXIOM forall P x. P x ==> P ((@) P)
AXIOM forall t. (\x. t x) = t
REPLAY_DONE
```

