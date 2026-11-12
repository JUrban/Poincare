(* ========================================================================= *)
(* HOLTrace part k >= 1 (k given by the environment variable HT_PART).  The  *)
(* base library and the files of parts 1 to k-1 are loaded in stub mode, the  *)
(* files of part k in full mode (link_prelude.ml); all in the order of        *)
(* make.ml, so that the counter values of HT_COUNTS (record_counter.ml) apply.*)
(* If the part contains src/pc_poincare_top.ml, the headline theorems are     *)
(* named too.  Run in the repository root with HOLTRACE_SAVE and HT_COUNTS    *)
(* set; holtrace/run_holtrace.sh does this.                                   *)
(* ========================================================================= *)

loadt "holtrace/link_prelude.ml";;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;
ht_after_base ();;
let VECTOR_ARITH = ht_rule1 VECTOR_ARITH;;
let NORM_ARITH = ht_rule1 NORM_ARITH;;

let ht_part = int_of_string (Sys.getenv "HT_PART");;
ht_home := ht_part_list ht_part;;
for k = 1 to ht_part do List.iter needs (ht_part_list k) done;;

if List.mem "src/pc_poincare_top.ml" !ht_home then
  loadt "holtrace/name_headlines.ml";;

Printf.printf "PART_DONE part=%d links=%d stubs=%d axioms=%d proofs=%d counter_corrections=%d unproved=%d cpu=%.0f\n%!"
  ht_part !ht_count !ht_stubs (List.length (axioms())) !ht_seq !ht_tv_off !ht_unproved (Sys.time());;
holtrace_stop();;
