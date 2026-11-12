(* ========================================================================= *)
(* Unit pc_p2a_t81u: MT Thm 8.1 (noncollapsing for Ricci flows with surgery) *)
(* in the form P2_THM_8_1_STATEMENT of pc_p3_iface, with no hypotheses       *)
(* (P2AT_THM_8_1).  Assembly only: C1 FIX from its leaves by                 *)
(* P2A_THM_8_1_FIX_REDUCED (pc_p2a_t81, the route O4), then the history      *)
(* bridge O3 by P2AX_T1 (pc_p2a_defs4) with P2AB_HIST_VIEW_X (pc_p2a_brg).   *)
(* Leaves:                                                                   *)
(*   L5 P2A_RVI_MONO (pc_p2a_lsv),                                           *)
(*   L6 P2AV_RVI_ASYMP (pc_p2a_rva),                                         *)
(*   L8 P2AP_PARABOLIC (pc_p2a_par),                                         *)
(*   L9 P2AZ_SMALLZ (pc_p2a_smz),                                            *)
(*   L10 P2AG_GAUSS_TAIL (pc_p2a_gtail),                                     *)
(*   the area formula P2AB_REQ_AREA (pc_p2a_brg, from MFD_AREA_FORMULA).     *)
(* ========================================================================= *)

needs "src/pc_p2a_t81.ml";;
needs "src/pc_p2a_lsv.ml";;
needs "src/pc_p2a_rva.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2a_smz.ml";;
needs "src/pc_p2a_gtail.ml";;
needs "src/pc_p2a_brg.ml";;
needs "src/pc_p2a_defs4.ml";;

prioritize_real();;
type_invention_error := true;;

(* C1 FIX (MT Thm 8.1 for smooth view settings) from its leaves.            *)

let P2AT_THM_8_1_VIEW_FIX = prove
 (`!u:A->bool. P2A_THM_8_1_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC P2A_THM_8_1_FIX_REDUCED THEN
  REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP; P2AP_PARABOLIC; P2AZ_SMALLZ; P2AG_GAUSS_TAIL;
              P2AB_REQ_AREA]);;

(* MT Thm 8.1 for Ricci flows with surgery (the statement of pc_p3_iface).   *)

let P2AT_THM_8_1 = prove
 (`!u:A->bool. P2_THM_8_1_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC P2AX_T1 THEN
  REWRITE_TAC[P2AT_THM_8_1_VIEW_FIX; P2AB_HIST_VIEW_X]);;

