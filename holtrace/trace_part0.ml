(* ========================================================================= *)
(* HOLTrace part 0: HOL Light's core (loaded at start-up) and the base       *)
(* library of the development, Multivariate up to cauchy.ml, lpspaces.ml and *)
(* 100/green.ml, all proved in full; every theorem proved at the top level   *)
(* is named HTLINK_k.  Run in the repository root with HOLTRACE_SAVE set;    *)
(* holtrace/run_holtrace.sh does this.                                        *)
(* ========================================================================= *)

loadt "holtrace/link_prelude.ml";;
ht_base_full := true;;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;
ht_after_base ();;
Printf.printf "PART_DONE part=0 links=%d stubs=%d axioms=%d cpu=%.0f\n%!"
  !ht_count !ht_stubs (List.length (axioms())) (Sys.time());;
holtrace_stop();;
