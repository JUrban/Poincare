# HOL Light developments on Candle: incompatibilities and how to remove them

A memo from porting two developments to Candle `master` (`6a9acd5`): Navier_Stokes, which needed no source changes,
and Poincare (1,090 files), which needs Candle versions of 33 files (in progress; see `REPORT.md`).

## What differs, and what the ports do now

**Language (Candle's OCaml front end compiles to CakeML)**

| difference | effect | what the port does |
|---|---|---|
| no `Printf` (or `Format`) | every `Printf.printf` is an error | rewrite to `print_string` with `string_of_int`/`string_of_bool`, mechanically (`tools/convert_printf.py`; 23 calls in 20 files) |
| `<`, `>`, `compare` only on `int` (`compare` on `num`) | comparing terms, pairs or lists is a type error | explicit orders: `setify Term.(<)` (Candle's `Term.compare` follows OCaml's order, so results are unchanged), lexicographic orders written out for pairs and lists (6 files) |
| no polymorphic hashing; Candle's `Hashtbl.create` takes a hash and an order | OCaml-style caches do not compile | `compat.ml` adds `add`, `reset`, a term hash for `hash_param`, and typed table constructors; the tables are created with them (1 file) |
| no weak type variables (CakeML's value restriction) | `let t = Hashtbl.create 10;;` or `let r = ref [];;` at top level is an error | type annotations where needed (the same file; elsewhere `src/` already annotates) |
| no `Match_failure` (CakeML raises `Bind`) | handlers name an undefined constructor | `Bind` (6 files) |
| no records, no `Gc` | `Gc.set { ... with ... }` in `make.ml` fails | `candle/make.ml` without that line |
| no `include` | a module cannot be extended | `compat.ml` re-lists every member of Candle's `List` and `Hashtbl` and adds the missing ones |
| no `string_of_bool`, `List.for_all2` (also no `for`/`while` loops or `lazy`, unused here) | undefined names | `compat.ml` |

**Library (Candle's copy of HOL Light)**

| difference | effect | what the port does |
|---|---|---|
| `setify`, finite-map functions (`undefined`, `graph`, ...) take explicit orders; `increasing`, `decreasing`, `qmap` are absent | type errors or undefined names | the `setify` calls above (the others are not used) |
| `compute.ml` overloads `+`, `-`, `*` with its `Cexp_*` operations | arithmetic terms could parse differently | `prelude.ml` removes the overloads before the library loads |
| `thecops.ml` is not loaded | `hashek` is missing | nothing needed |
| terms print differently (`true` for `T`, `forall`) | code that sorts by `string_of_term` can order ties differently | accepted; the one use found does not depend on the order |
| the kernel orders hypotheses differently (a variable before a constant) | `hyp` lists come in another order | accepted; no proof found that depends on it |

**Loading**

| difference | what the port does |
|---|---|
| `needs`/`loads` are lexer directives that search `loadPath`, by default only the current directory; no `loadt` | `setup.sh` puts symlinks in the Candle root (and directories of symlinks, so that the Candle versions of files replace the originals without changing `src/`); `loadt` becomes `loads` (2 files) |
| `needs` records a file even when its load fails, and only answers "Already loaded" afterwards | the driver reloads failed files with `loads` |

**Resources**

| difference | what the port does |
|---|---|
| the heap is fixed at start-up and touched at once, so a session costs its whole heap; no heap statistics | heap sized from HOL Light's peak with a margin (24 GB for Navier_Stokes, 46 GB for Poincare); one large session at a time |
| the code buffer is fixed in the binary (500 MiB); Poincare needs more | the binary is rebuilt with 1000 MiB; both buffers cannot be doubled, because text and data must stay within 2 GB of each other (32-bit PC-relative relocations); use is measured by reading the process memory |

Speed was not a problem: about 1.2x bytecode HOL Light on the same machine for Navier_Stokes, with a few files up
to 5x.  Poincare's first 237 files took 2.0x the HOL Light times that upstream published (measured on a shared
machine); a measurement of HOL Light on the same machine is under way.

## Long-term solutions in Candle, from least to most ambitious

1. **Small additions to `candle/ocaml.ml` and the front end.**
   * The missing standard functions: `string_of_bool`, the rest of OCaml's `List` (`for_all2`, `iter2`, `exists2`,
     `mapi`, `init`, ...), and `Hashtbl.add`, `reset`, `mem`, `length`.
   * `loadt` as an alias of `loads`.
   * `Match_failure _` handlers read as `Bind`, next to the constructor renamings the front end already has
     (`compatCons` in `cakeml/candle/parser/conversion_support.cml`).
   * Make the `Cexp_*` overloads of `compute.ml` opt-in, since overloads silently change parsing.
2. **Build and runtime configuration.**
   * A larger default code buffer, or a documented build option for it.
   * A clear error message when the code buffer fills.
   * A way to see heap and code-buffer use, for example the existing GC hooks of `basis_ffi.c` (now compiled out)
     or a `Candle.memory_stats ()`, so that users can size heaps instead of guessing.
3. **Front-end desugarings.**
   * `Printf.printf` and `sprintf` with a literal format string turned into string concatenation at parse time;
     this covers every use seen in these developments.
   * Records, at least enough for a no-op `Gc` stub.
   * `include` in structures.
4. **A porting tool built on OCaml's own type checker (`compiler-libs`).** HOL Light developments type-check in
   OCaml, so a tool can find the type at every `<`, `compare`, `setify` or `Hashtbl` use and emit Candle's typed
   versions, or at least list them.  That would make ports mechanical.  It would also replace the manual survey,
   probes and review that found the problems above before the long run reached them.
5. **New runtime primitives: polymorphic structural compare and hash.** These would work like CakeML's existing
   polymorphic equality.  Candle's library could then keep HOL Light's signatures (`setify`, `<` on terms and
   tuples, OCaml's `Hashtbl`), which removes most of the library differences at once.  This touches the verified
   compiler and its semantics.
6. **Memory that grows.**
   * A code space allocated on demand instead of a buffer fixed in the binary; its bounds are part of the compiler's
     installation model, so this too touches verified parts.
   * A heap that grows, or is touched only as it is used, so that memory reflects the live data.
7. **OCaml's top-level typing (weak type variables).** Top-level values whose types are fixed by later uses would
   then work: `ref []`, `Hashtbl.create n`, partial applications.  This changes CakeML's type inference at the REPL.
8. **Full compatibility with HOL Light's OCaml.** Unmodified developments would load, with `Format`, records,
   modules and the rest.  This is the end point of the items above, and a long project.
