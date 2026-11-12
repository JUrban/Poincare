(* ========================================================================= *)
(* HOLTrace replay of all parts in ONE session of the replay copy of HOL     *)
(* Light (HOLTrace's plain install, kernel files unchanged, plus link.patch). *)
(* Run in the repository root with HT_TRACES set to the trace files in part   *)
(* order (part 0 first); holtrace/run_holtrace.sh does this.                  *)
(*                                                                            *)
(* The base library and the human-readable statement files are loaded first. *)
(* Each restore then MATCHES every constant of the trace that already exists  *)
(* (the kernel checks that the definitions are alpha-equivalent), so the      *)
(* restored theorems are about exactly the constants of those files.  A stub  *)
(* axiom of a part (see link_prelude.ml) is matched with the theorem of the   *)
(* same statement restored from an earlier part; no axiom is created.         *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;
loadt "src/poincare_statement.ml";;
loadt "src/pc_interfaces.ml";;
Printf.printf "PRE_RESTORE cpu=%.0f axioms=%d\n%!" (Sys.time()) (List.length (axioms()));;

(* The table is keyed by a hash that ignores the names of bound variables:  *)
(* the parser names the bound variable of a set comprehension by a counter,  *)
(* so the same statement parsed in two sessions can differ in those names.   *)
(* A stub axiom is matched only by a theorem whose statement is the same up  *)
(* to the names of bound variables (aconv); ALPHA then gives a theorem with  *)
(* exactly the statement of the axiom line.                                  *)
let rec ht_ahash bvs tm =
  if is_var tm then
    (try 2 * index tm bvs + 1 with Failure _ -> 2 * Hashtbl.hash (fst (dest_var tm)))
  else if is_const tm then 2 * Hashtbl.hash (fst (dest_const tm))
  else if is_comb tm then
    let f, x = dest_comb tm in (31 * ht_ahash bvs f + 17 * ht_ahash bvs x + 3) land max_int
  else let v, b = dest_abs tm in (13 * ht_ahash (v :: bvs) b + 5) land max_int;;

let ht_table = (Hashtbl.create 1000000 : (int, thm) Hashtbl.t);;
let ht_linked = ref 0;;
holtrace_link_hook := (fun t ->
  try let th = List.find (fun th -> hyp th = [] && aconv (concl th) t)
                         (Hashtbl.find_all ht_table (ht_ahash [] t)) in
      incr ht_linked;
      Some (if concl th = t then th else EQ_MP (ALPHA (concl th) t) th)
  with Not_found -> (Printf.printf "LINK_FAILED %s\n%!" (string_of_term t); None));;

let ht_collect () =
  let rec go k =
    match (try Some (holtrace_restore_name2thm (Printf.sprintf "HTLINK_%d" k)) with Not_found -> None) with
    | Some th -> Hashtbl.add ht_table (ht_ahash [] (concl th)) th; go (k + 1)
    | None -> k - 1 in
  go 1;;

let ht_restore f =
  ht_linked := 0;
  holtrace_restore_worker (fun () -> 0.0) false true true [] f;
  let n = ht_collect () in
  Printf.printf "RESTORED %s theorems_for_later_parts=%d stub_axioms_linked=%d axioms=%d cpu=%.0f\n%!"
    f n !ht_linked (List.length (axioms())) (Sys.time());
  Gc.compact ();;

let ht_traces = List.filter (fun s -> s <> "") (String.split_on_char ' ' (Sys.getenv "HT_TRACES"));;
(* With HT_WAIT set, each trace is restored once the file TRACE.done exists, *)
(* so the replay can run while later parts are still being traced.          *)
let ht_wait f =
  if Sys.getenv_opt "HT_WAIT" <> None then
    while not (Sys.file_exists (f ^ ".done")) do ignore (Sys.command "sleep 60") done;;
List.iter (fun f -> ht_wait f; ht_restore f) ht_traces;;

let ht_univ_of_tyvar tm =
  is_const tm && fst(dest_const tm) = "UNIV" &&
  (match dest_type(type_of tm) with "fun",[a;b] -> is_vartype a && b = bool_ty | _ -> false);;
let ht_check (name,stmt) =
  let th = holtrace_restore_name2thm name in
  let ok = try let c,u = dest_comb(concl th) in
               is_const c && fst(dest_const c) = stmt && ht_univ_of_tyvar u
           with Failure _ -> false in
  Printf.printf "RESTORED_CHECK %s hyps=%d concl_is_%s_at_a_type_variable=%b\n%!"
    name (List.length (hyp th)) stmt ok;;
List.iter ht_check ["POINCARE_TOP","POINCARE_STATEMENT";
                    "POINCARE_SMOOTH","POINCARE_SMOOTH_STATEMENT";
                    "POINCARE_EMBEDDED","POINCARE_EMBEDDED_STATEMENT"];;
let ht_moise = holtrace_restore_name2thm "MOI_SST_HEADLINE";;
Printf.printf "RESTORED_CHECK MOI_SST_HEADLINE hyps=%d concl=%s\n%!"
  (List.length (hyp ht_moise)) (string_of_term (concl ht_moise));;
List.iter (fun th -> print_string ("AXIOM " ^ string_of_term (concl th) ^ "\n")) (axioms());;
print_string "REPLAY_DONE\n";;
