# Poincare on Candle

This directory runs the development on [Candle](https://github.com/CakeML/candle)
(HOL Light on CakeML).  `src/`, `audit/` and `make.ml` are not changed and still load in
HOL Light: the 35 files that Candle needs changed have Candle versions in `candle/src/`
and `candle/audit/`, and `candle/make.ml` is `make.ml` without its `Gc.set` line.
`REPORT.md` describes the changes, the results and how they were checked.

## Set-up

Use Candle `master` (tested at `6a9acd5`), built as its README describes, but with a
larger code buffer: in Candle's `candle/build/cake.S` (after Candle's `candle/cake.S.patch`),
set `CODE_BUFFER_SIZE` to `1048576000` and run `make` there.  The development compiles to
more code than the 500 MiB of the default build (see `REPORT.md`).  Candle's
`needs` and `loads` look for files in Candle's `loadPath`, which is the current
directory, so make the repository visible from the Candle root:

```
candle/setup.sh CANDLE_ROOT
```

This creates there a symlink `pc` to this repository and directories `src/` and `audit/`
of symlinks to this repository's files, with the Candle versions in place of the
originals.  Run it again after changing the set of files.

## Running

Start Candle with a large heap (46 GB was used; Candle's heap is fixed at start-up, and
smaller heaps were not tried for the whole development):

```
CML_HEAP_SIZE=46000 ./candle.sh
```

Then:

```
#use "hol.ml";;
loads "pc/candle/check.ml";;
loads "pc/candle/audit.ml";;
```

`check.ml` loads the development and prints the main results and the axioms, ending
with `POINCARE_CHECK_DONE`.  `audit.ml` loads the statement audit and prints its
results, ending with `POINCARE_AUDIT_CHECK_DONE`.  To load the development without the
output, use `loads "pc/candle/make.ml";;`.

## Files

| file | purpose |
|---|---|
| `setup.sh` | makes the repository visible from the Candle root, with the Candle versions of files |
| `src/`, `audit/` | Candle versions of the files of `src/` and `audit/` that use what Candle lacks; see `REPORT.md` |
| `make.ml` | `make.ml` without `Gc.set`, with `prelude.ml` and `compat.ml` (written by `tools/gen_make.py`) |
| `prelude.ml` | removes the overloads of `+`, `-` and `*` that Candle adds for its compute primitive |
| `compat.ml` | `string_of_bool`, `List.for_all2` and the `Hashtbl` functions that `src/` uses |
| `check.ml`, `check_results.ml` | `check.ml` of the main repository, without `Printf` |
| `audit.ml`, `audit_results.ml` | `audit/make.ml` and `audit/check.ml`, without `Printf` and without loading `make.ml`; run after `make.ml` |
| `statements.ml`, `dump_*.ml`, `compare_defs.py` | compare the statements and results with HOL Light; see `REPORT.md` |
| `INCOMPATIBILITIES.md` | what differs between HOL Light and Candle, how the port handles it, and what Candle could change |
| `tools/` | the scripts behind the runs in `REPORT.md`; paths are those of the machine they ran on |
