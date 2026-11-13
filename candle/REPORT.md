# Poincare on Candle: interim report

Status (2026-11-13): steps 1 to 4 of the plan are done: the development loads on Candle, and its checks, audit,
definitions and results agree with HOL Light (see "The main run").  Step 5, the fresh session, is under way.

## Plan

1. Survey `src/` and `audit/` for what Candle's OCaml dialect and library lack, and adapt only that.
2. Load the development on Candle `master` (`6a9acd5`) file by file from a checkpoint of the library, fixing what
   fails.  The files that Candle needs changed go in `candle/src/`; `src/` stays as it is and still loads in
   HOL Light (`candle/setup.sh` builds Candle's view of `src/`).
3. Run the checks of `check.ml` and the audit of `audit/check.ml`.
4. Compare the statements with HOL Light at `31fe213` (the commit merged into Candle `master`) and `e5236a58` (the
   commit upstream tested), as for Navier_Stokes.
5. Reproduce everything in a fresh session with the commands of `candle/README.md`.

## Survey (2026-11-12)

Candle (HOL Light on CakeML) has its own OCaml front end and library layer (`candle/ocaml.ml`).  Comments, term
quotations and strings removed, `src/` and `audit/` use the following that Candle lacks or treats differently:

| what | where | change |
|---|---|---|
| `Gc.set { ... with ... }` (no `Gc`, no records) | `make.ml` | `candle/make.ml` is `make.ml` without that line (it changes memory use only) |
| `Printf.printf` (no `Printf`) | 20 files, 23 calls, diagnostic prints; `check.ml`, `audit/check.ml` | `print_string` with `string_of_bool` and `string_of_int`, converted by `candle/tools/convert_printf.py` |
| `string_of_bool`, `List.for_all2` | 20 files; 2 files | defined in `candle/compat.ml` |
| `Hashtbl.create n`, `add`, `reset`, `hash_param` | caches in `pc_rfa_h3d.ml` (`pc_rfa_hext.ml` and `pc_rfa_hpsd.ml` only reset them) | `compat.ml` adds `add`, `reset` and a term hash; the six tables are created with a hash and an order, as Candle's tables require, and with a type annotation, because CakeML has no weak type variables |
| `setify` of a list of terms (Candle's takes an order) | 4 files | `setify Term.(<)`, as in Candle's own library; `Term.compare` follows OCaml's order on terms, so the result is the same |
| `<` on pairs (Candle's is on `int` only) | `pc_moi_s2628_stmt.ml` | an explicit lexicographic order, the same as OCaml's |
| `loadt` (Candle has `loads`, relative to the current directory) | `pc_moi_pl2.ml` (of `100/pick.ml`), `audit/pc_audit_equiv.ml` | `loads` |
| `<`, `>`, `<=` on pairs and lists of `int` | `pc_rfa_htens.ml`, `pc_rfa_hpush.ml` | explicit lexicographic orders, the same as OCaml's |
| handlers for `Match_failure` (CakeML raises `Bind` when a pattern does not match) | 6 `pc_rfa_*` files | `Bind` |
| a comment right after a symbol character, `[(* ... end ... *)` (see below) | `pc_p3_s16prop5.ml`, `pc_moi_pd2_glob.ml` | a space: `[ (*` |

So 34 files of `src/` and one of `audit/` have Candle versions in `candle/src/` and `candle/audit/`.  The rest is
used unchanged.  Not needed: `Kernel.compute`, loops (`for`, `while`), `lazy`.  Supported as in OCaml: `when` guards, `as`
patterns, string patterns, `function`, `try`/`raise`, `Failure s` patterns, `ignore`, `begin`/`end`,
`type_invention_error`, identical redefinitions (`Benign redefinition`).  Of the 5,688 library identifiers that
`src/` and `audit/` use, all exist in Candle except some from library files that `src/` loads itself (for example
`Multivariate/homology.ml`), and none has a different type in Candle except `setify`.

An independent review of these changes (2026-11-12) found the last two rows of the table, which the survey of
identifiers could not see (polymorphic comparisons and the standard exceptions are not library definitions), before
the run reached them.  It also checked the converted prints, the caches, the orders, `make.ml`, the result
printers and `dump_final.ml`, and found no other problem.  CakeML's value restriction (it has no weak type
variables, so `let r = ref []` is an error) is not hit: the top-level references in `src/` are annotated.

**The hang at `pc_p3_s16len.ml` (2026-11-12).**  After 5 h the run stopped: Candle had read
`needs "src/pc_p3_s16len.ml";;` but did not load it, and waited for input, idle.  The cause is in the file before,
`pc_p3_s16prop5.ml`, and in Candle's REPL, which splits its input into phrases with a lexer of its own
(`candle/prover/candle_boot.ml` in CakeML) before parsing them.  That lexer reads a run of symbol characters as
one token, and `(` and `*` are symbol characters, so in `[(* the core ball persists through tc: closed end *)` it
sees no comment: `[(*` is a symbol, and the comment's words are tokens.  The scanner counts `begin`, `struct`,
`sig` and `end` to find the phrases, and a phrase ends only at a `;;` at level 0.  After this `end` the level is
-1, so the rest of the file and the next `needs` were held as one unfinished phrase, which never ran.  In OCaml,
`[(*` is `[` and a comment.  `tools/prelex.py` ports Candle's scanner and compares, file by file, its phrase
ends, directives and quotations with those of an OCaml-like lexer (the second review below wrote this version; it
replaces a narrower check of mine, which missed cases that none of these files has).  Of the 1,191 files that the
run loaded (HOL Light's library, `src/`, `audit/`, `candle/` and the 39 library files that `src/` loads itself),
only these two differ: the other is `pc_moi_pd2_glob.ml` (`[(* inner end: inside the faded zone *)`).  (Candle's
own `firstorder.ml` ends without `;;`, which Candle's loading of its library allows.)  The 616 other comments that
Candle does not see as comments split into the same phrases.  The Candle versions of the two files add a space
after the `[`.  Nothing before the hang was affected, so the run went on from its last checkpoint before
`pc_p3_s16prop5.ml`.  The run's driver had reported that file OK, although its last 25 phrases had not run: it
took the prompt after `- Finished loading` as the end of the file.  The driver now has Candle print a marker after
each item, which a phrase that the scanner did not end takes in, so that the item fails instead of the next; and
it fails when Candle uses under 1 s of CPU in 10 minutes while it waits for output (seen 10 to 20 minutes after
Candle stops), instead of waiting until its 24 h time-out.  Neither the survey nor the first review could find
this: the files are correct OCaml, and the difference is in how Candle splits them into phrases.

A second stop, at `pc_moi_lt_cutb.ml`, was the driver's: a read of Candle's output ended inside the name in
`- Finished loading src/pc_moi_lt_cutb.ml`, the driver matched `src/pc_moi_lt`, so its stack of loads was not
popped and it went on waiting at the prompt, although the file had loaded.  The idle check, then in a first
version that took any clock tick as work, did not fire in 20 minutes; it now needs 1 s of CPU.  The driver now
matches a name only once its line has ended, and the run went on from the checkpoint before (item 1012), with
the driver of that time (the idle check in its first version, without the marker).

**Second review (2026-11-13).**  An independent review of the work since the first one checked the two new
Candle versions (each differs from `src/` by the one space), the driver changes, and the claims of this report
against the logs: every one of the 1,090 files of `src/` has an `OK` in its last attempt, the two restarts went on
at the right items, nothing loaded before a checkpoint depends on a file loaded only after it, and the numbers of
"The main run" and "Time" are those of the logs.  It found the driver's false `OK` above, the gaps of my first
`prelex.py`, and the details corrected here.  Since the driver's `OK` alone does not show that a file ran to its
end, the logs were also checked for that: in the last attempt at each file, the last top-level `let` printed its
value (1,089 files; `pc_geo_iface.ml` has none, and the last phrase of `pc_moi_s34_residstmt.ml` printed
`RESIDSTMT_GLUE true`).

`pc_moi_s2628_stmt.ml` breaks ties by `string_of_term`, which prints differently in Candle (`true` for `T`), so it
may order the conjuncts of some `MOI_SDD_*` antecedents differently from HOL Light; they are used in ways that do
not depend on the order.  Candle's kernel also orders hypotheses differently from HOL Light's (a variable before a
constant), which changes the order of `hyp` lists; this is Candle's, not the port's.

## The statements (first results)

The statement constants depend only on `src/poincare_statement.ml` and `src/pc_interfaces.ml`, which `make.ml`
loads first, and the audit's on `audit/poincare_blind.ml` and a few early files.  So short sessions compare them:
the library of `make.ml`, then `candle/statements.ml`, then every definition, constant, type operator and type
definition theorem (`dump_defs.ml`, `dump_tydefs.ml`).  HOL Light `e5236a58` against Candle `master` with the
recorder of the Navier_Stokes port:

* 0 of the 920 definitions on both sides differ; 0 constants differ in type.
* The dependency cones of `POINCARE_STATEMENT`, `POINCARE_SMOOTH_STATEMENT`, `POINCARE_EMBEDDED_STATEMENT`,
  `MOISE_SMOOTHING_STATEMENT`, `BLIND_POINCARE_TOP` and `BLIND_POINCARE_SMOOTH` (135 to 186 constants) are
  identical.
* All 50 type definition theorems of the HOL Light session are in Candle's; Candle has 2 more, for its `cval`.
* One-sided: `hashek` (HOL Light's `thecops.ml`) and Candle's `Cexp_*` and `cval` constants, none in a cone.

The same at HOL Light `31fe213` (the commit in Candle `master`): 0 of 920 shared definitions differ, the six cones
are identical, all 50 type definition theorems agree.  The short sessions also load the files that prove the 30
sanity theorems of `audit/check.ml` (`src/pc_audit_sanity.ml` and two files above); their statements are
identical in both systems, all without hypotheses.

The short sessions also print the conclusions that the 8 headline and audit results must have, parsed from the
quotations with which `src/` and `audit/` prove them (`dump_expected.ml`; `prove` returns exactly its goal), for
comparison with the proving session's results (`compare_defs.py --results`).

The proving session prints the definitions of the statement files and all constants (`dump_final.ml`), to link it
to these.  It has no list of definitions, so it rebuilds each one from the theorem `new_definition` returns, as
`new_definition` (of `pair.ml`, which binds fresh variables) builds it; it also prints the theorems of the two
constants defined with `define` (`continuously_differentiable` and the audit's `blind_ck`).  Checked in both HOL
Light sessions: the 28 rebuilt definitions are the session's own.

## The main run (2026-11-12 and 13)

Candle `master` with the larger code buffer (`pc-big`), heap 46 GB, driven file by file (`tools/pc_lane.py`)
from a checkpoint of the library: `compat.ml`, the 1,090 files of `src/` in the order of `candle/make.ml`, then
`check_results.ml` and `audit.ml`, with a DMTCP checkpoint every 30 minutes or so of HOL Light time (14 in all).
It stopped twice and went on each time from the checkpoint before (both described above): at
`pc_p3_s16len.ml` (the comment after `[`) and at `pc_moi_lt_cutb.ml` (the driver).  No file failed to load.

`check_results.ml` printed (Candle prints `T` as `true` and `!` as `forall`):

```
POINCARE_TOP hypotheses 0  conclusion is POINCARE_STATEMENT (:A), A a type variable: true
POINCARE_SMOOTH hypotheses 0  conclusion is POINCARE_SMOOTH_STATEMENT (:A), A a type variable: true
POINCARE_EMBEDDED hypotheses 0  conclusion is POINCARE_EMBEDDED_STATEMENT (:A), A a type variable: true
MOI_SST_HEADLINE hypotheses 0  conclusion is !u:A->bool. MOISE_SMOOTHING_STATEMENT u: true
AXIOMS_COUNT 3
AXIOM exists f. ONE_ONE f /\ ~ONTO f
AXIOM forall P x. P x ==> P ((@) P)
AXIOM forall t. (\x. t x) = t
POINCARE_CHECK_DONE
```

and `audit.ml` printed `POINCARE_TOP_BLIND_EQUIV`, `POINCARE_SMOOTH_BLIND_EQUIV`, `BLIND_POINCARE_TOP_PROVED` and
`BLIND_POINCARE_SMOOTH_PROVED` with 0 hypotheses and the expected conclusions (`true`), the 30 sanity theorems
each with 0 hypotheses, `SANITY_THEOREMS 30`, the same three axioms, and `POINCARE_AUDIT_CHECK_DONE`.

From the final checkpoint, `dump_final.ml` and `dump_thms.ml`, compared with both short HOL Light sessions
(`31fe213` and `e5236a58`):

* `compare_defs.py --final`: the 28 definitions of the statement files and the two `define` theorems are
  identical to HOL Light's; in the six cones (135 to 186 constants), every constant and type operator has the
  same type and arity.  `FINAL_IDENTICAL` for both.
* `compare_defs.py --results`: the 38 results (4 headline theorems, 4 audit results, 30 sanity theorems) are
  identical to HOL Light's (for the 8, the conclusions of the quotations that prove them), and none has
  hypotheses.  `RESULTS_IDENTICAL` for both.

Loading `src/` took 36,830 s (10.2 h) in all, 1.57x the times upstream published (see "Time" for why these are
not comparable); the checkpoints took 246 s each, and each restore about 3 minutes.  The slowest files were
`pc_sch_b1canc.ml` (596 s), `pc_moi_s35_minc.ml` (551 s) and `pc_moi_lt_seam.ml` (468 s).  At the end the code
buffer held 656 MB and the data buffer 227 MB.

## Resources

* Candle's heap is fixed when it starts, and the process touches all of it within a minute, so each session costs
  its whole heap.  HOL Light peaks at 17.5 GiB for this development (23.3 GiB without the `Gc.set`; upstream's
  measurements, `doc/REPORT.md`), against 7.4 GiB for Navier_Stokes, which ran in a 24 GB Candle heap.  The main lane uses 46 GB, so only one such session
  runs at a time.
* Candle compiles every top-level phrase into a code buffer and a data buffer whose sizes are fixed when the binary
  is built (Candle's `candle/cake.S.patch`: 500 MiB and 625 MiB).  The driver logs how much of each is used, by
  reading the Candle process's memory (both buffers start zeroed and fill from the start; `tools/codehw_lib.py`).
  The library (to `100/green.ml`) uses 94.5 MB of code and 46.3 MB of data.  In the first 11.5 MB of `src/` the
  code grew by 4.9 MB per MB of source (2.7 to 6.6 by family of files), which projects to about 562 MB for all of
  `src/`, more than the buffer holds.  So the run was stopped after an hour and restarted with Candle built with a code buffer of
  1000 MiB (`CODE_BUFFER_SIZE 1048576000` in `cake.S`; the data buffer is unchanged, and doubling both does not
  link, because the text and data must stay within 2 GB of each other).  The binary is otherwise built from the
  same `cake.S` and `basis_ffi.c`.  This is the one change to Candle; its sources are `master`'s.  The whole
  development, with the checks and the audit, used 656 MB of code (5.9 MB per MB of source over all of `src/`)
  and 227 MB of data, so the default build could not have loaded it.

## Time

The times that upstream published (`doc/timing.tsv`) are not comparable with a run here: HOL Light `e5236a58`
(bytecode toplevel, OCaml 4.14.1, with `make.ml`'s `Gc.set`) took 1.61x their time on the first 500 files of
`src/` on this machine.  So HOL Light loaded the library and those files here, timing each
(`tools/hl_time.sh`), while the Candle run was loading the same files in the same order; both run on one core of a
machine with many idle cores, and CPU and wall-clock times of HOL Light agree within 0.2%.  Compared file by file
(`tools/timecmp.py`):

| | HOL Light here | Candle | Candle / HOL Light |
|---|---|---|---|
| library (`cauchy.ml`, `lpspaces.ml`, `green.ml`) | 2,424 s | 2,891 s | 1.19 |
| first 500 files of `src/` | 7,848 s | 9,921 s | 1.26 |

Of the 219 files that take 10 s or more in HOL Light, the median ratio is 1.30 (quartiles 1.07 and 1.52, from
0.54 to 2.50).  By family of files, from 1.01 (`pc_apx`) to 1.45 (`pc_cmp`).  Candle's times exclude the
checkpoints.  For all of `src/`, Candle took 1.57x upstream's times, against 2.04x on the first 500 files, so the
later files are relatively faster in Candle; HOL Light was not timed here on them.
