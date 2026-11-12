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
| `Printf.printf` (no `Printf`) | 20 files, 24 calls, diagnostic prints; `check.ml`, `audit/check.ml` | `print_string` with `string_of_bool` and `string_of_int`, converted by `candle/tools/convert_printf.py` |
| `string_of_bool`, `List.for_all2` | 20 files; 2 files | defined in `candle/compat.ml` |
| `Hashtbl.create n`, `add`, `reset`, `hash_param` | caches in `pc_rfa_h3d.ml` (`pc_rfa_hext.ml` and `pc_rfa_hpsd.ml` only reset them) | `compat.ml` adds `add`, `reset` and a term hash; the six tables are created with a hash and an order, as Candle's tables require, and with a type annotation, because CakeML has no weak type variables |
| `setify` of a list of terms (Candle's takes an order) | 4 files | `setify Term.(<)`, as in Candle's own library; `Term.compare` follows OCaml's order on terms, so the result is the same |
| `<` on pairs (Candle's is on `int` only) | `pc_moi_s2628_stmt.ml` | an explicit lexicographic order, the same as OCaml's |
| `loadt` (Candle has `loads`, relative to the current directory) | `pc_moi_pl2.ml` (of `100/pick.ml`), `audit/pc_audit_equiv.ml` | `loads` |

So 26 files of `src/` and one of `audit/` have Candle versions in `candle/src/` and `candle/audit/`.  The rest is
used unchanged.  Not needed:
`Kernel.compute`, loops (`for`, `while`), `lazy`, polymorphic `compare` (no other uses found).  Supported as in
OCaml: `when` guards, `as` patterns, `function`, `try`/`raise`, `ignore`, `begin`/`end`,
`type_invention_error`.  Of the 5,688 library identifiers that `src/` and `audit/` use, all exist in Candle
except some from library files that `src/` loads itself (for example `Multivariate/homology.ml`).

Two things may still fail only at load time: top-level values whose type keeps a type variable (CakeML's value
restriction has no weak variables, so `let r = ref []` is an error), and comparisons with `<` on non-integers.
`pc_moi_s2628_stmt.ml` also breaks ties by `string_of_term`, which prints differently in Candle (`true` for `T`),
so it may order some terms differently from HOL Light.

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

The proving session prints the definitions of the statement files and all constants (`dump_final.ml`), to link it
to these.  It has no list of definitions, so it rebuilds each one from the theorem `new_definition` returns, as
`new_definition` (of `pair.ml`, which binds fresh variables) builds it.  Checked in the HOL Light session: the 28
rebuilt definitions are the session's own.

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
  same `cake.S` and `basis_ffi.c`.  This is the one change to Candle; its sources are `master`'s.
