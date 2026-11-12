# Poincare on Candle: interim report

Status: in progress, on branch `candle-port`.  Nothing below is a final result.

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
`[(*` is `[` and a comment.  `tools/prelex.py` emulates Candle's scanner: of all files that Candle loads, only
two have such a comment with a word that changes the phrases, this one and `pc_moi_pd2_glob.ml`
(`[(* inner end: inside the faded zone *)`); 421 other comments after symbol characters contain no such word and
load as in OCaml.  The Candle versions of the two files add a space after the `[`.  Nothing before the hang was
affected (the files before `pc_p3_s16prop5.ml` pass the check), so the run went on from its last checkpoint
before that file.  The driver now also fails when Candle uses no CPU for 10 minutes while it waits for output,
instead of waiting until its 24 h time-out.  Neither the survey nor the review could find this: the files are
correct OCaml, and the difference is in how Candle splits them into phrases.

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

## Resources

* Candle's heap is fixed when it starts, and the process touches all of it within a minute, so each session costs
  its whole heap.  HOL Light peaks at 17.5 GiB for this development (23.3 GiB without the `Gc.set`), against
  7.4 GiB for Navier_Stokes, which ran in a 24 GB Candle heap.  The main lane uses 46 GB, so only one such session
  runs at a time.
* Candle compiles every top-level phrase into a code buffer and a data buffer whose sizes are fixed when the binary
  is built (`candle/cake.S.patch`: 500 MiB and 625 MiB).  The driver logs how much of each is used, by reading the
  Candle process's memory (both buffers start zeroed and fill from the start; `tools/codehw_lib.py`).  The library
  (to `100/green.ml`) uses 92 MB of code and 45 MB of data.  In the first 11 MB of `src/` the code grew by 4.8 MB
  per MB of source (2.7 to 6.6 by family of files), which projects to about 554 MB for all of `src/`, more than
  the buffer holds.  So the run was stopped after an hour and restarted with Candle built with a code buffer of
  1000 MiB (`CODE_BUFFER_SIZE 1048576000` in `cake.S`; the data buffer is unchanged, and doubling both does not
  link, because the text and data must stay within 2 GB of each other).  The binary is otherwise built from the
  same `cake.S` and `basis_ffi.c`.  This is the one change to Candle; its sources are `master`'s.  On this
  binary the code grows by about 5.2 MB per MB of source, which projects to about 590 MB for all of `src/`.

## Time (interim)

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
checkpoints.
