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

So 25 files of `src/` have Candle versions in `candle/src/`.  The rest of `src/` is used unchanged.  Not needed:
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

The proving session prints the definitions of the statement files and all constants (`dump_final.ml`), to link it
to these.  A first version rebuilt the definitions wrongly (`new_definition` of `pair.ml` binds fresh variables);
the HOL Light session showed this, and it is fixed.

## Resources

* Candle's heap is fixed when it starts, and the process touches all of it within a minute, so each session costs
  its whole heap.  HOL Light peaks at 17.5 GiB for this development (23.3 GiB without the `Gc.set`), against
  7.4 GiB for Navier_Stokes, which ran in a 24 GB Candle heap.  The main lane uses 46 GB, so only one such session
  runs at a time.
* Candle compiles every top-level phrase into a code buffer (500 MB) and a data buffer (625 MB) fixed when the
  binary is built.  `Multivariate/vectors.ml` (468 KB) took 2.1 MB and 1.7 MB of them; `src/` is 93 MB, so the code
  buffer could be close to full.  The main lane's use of both buffers is logged (from `/proc/PID/smaps`), to see
  early whether Candle needs to be built with larger buffers.
