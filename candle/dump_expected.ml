(* ========================================================================= *)
(* For a short session of candle/statements.ml: the conclusions that the     *)
(* proving session's headline and audit results must have, parsed from the   *)
(* quotations with which src/ and audit/ prove them (prove returns exactly   *)
(* its goal), in the form of candle/dump_thms.ml.  The headline ones are     *)
(* POINCARE_TOP and MOI_SST_HEADLINE (src/pc_poincare_top.ml,               *)
(* src/pc_moi_status.ml), POINCARE_SMOOTH (src/pc_smt_smooth.ml) and         *)
(* POINCARE_EMBEDDED; the audit ones are in audit/pc_audit_equiv.ml and       *)
(* audit/pc_audit_blind_proved.ml.                                           *)
(* ========================================================================= *)

loads "pc/candle/dump_terms.ml";;

do_list (fun (n,tm) -> print_string ("THMDUMP " ^ n ^ " 0 " ^ dump_tm tm ^ "\n"))
  [("POINCARE_TOP", `POINCARE_STATEMENT (:A)`);
   ("POINCARE_SMOOTH", `POINCARE_SMOOTH_STATEMENT (:A)`);
   ("POINCARE_EMBEDDED", `POINCARE_EMBEDDED_STATEMENT (:N)`);
   ("MOI_SST_HEADLINE", `!u:A->bool. MOISE_SMOOTHING_STATEMENT u`);
   ("POINCARE_TOP_BLIND_EQUIV", `!u:A->bool. POINCARE_STATEMENT u <=> BLIND_POINCARE_TOP u`);
   ("POINCARE_SMOOTH_BLIND_EQUIV", `!u:A->bool. POINCARE_SMOOTH_STATEMENT u <=> BLIND_POINCARE_SMOOTH u`);
   ("BLIND_POINCARE_TOP_PROVED", `BLIND_POINCARE_TOP (:A)`);
   ("BLIND_POINCARE_SMOOTH_PROVED", `BLIND_POINCARE_SMOOTH (:A)`)];;
print_string "THMDUMP_DONE\n";;
