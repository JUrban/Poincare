(* ========================================================================= *)
(* Untraced full load of the base library and of every file of src/ in the   *)
(* order of make.ml, recording after each top-level proof the parser's       *)
(* counter of invented type variables (see link_prelude.ml) into the file    *)
(* named by the environment variable HT_RECORD.  Run in the repository root  *)
(* in the tracing copy of HOL Light, WITHOUT HOLTRACE_SAVE;                  *)
(* holtrace/run_holtrace.sh does this.                                        *)
(* ========================================================================= *)

loadt "holtrace/link_prelude.ml";;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;
ht_after_base ();;
let VECTOR_ARITH = ht_rule1 VECTOR_ARITH;;
let NORM_ARITH = ht_rule1 NORM_ARITH;;
Printf.printf "RECORD_BASE_DONE proofs=%d cpu=%.0f\n%!" !ht_seq (Sys.time());;

let ht_nparts =
  let rec go k = if Sys.file_exists (Printf.sprintf "holtrace/parts/part%d.txt" (k + 1)) then go (k + 1) else k in
  go 0;;
for k = 1 to ht_nparts do
  List.iter (fun f -> needs f;
                      Printf.printf "RECORD_FILE_DONE %s proofs=%d cpu=%.0f\n%!" f !ht_seq (Sys.time()))
            (ht_part_list k)
done;;
(match ht_rec_out with Some oc -> Stdlib.close_out oc | None -> ());;
Printf.printf "RECORD_DONE proofs=%d cpu=%.0f\n%!" !ht_seq (Sys.time());;
