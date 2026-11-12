(* ========================================================================= *)
(* Unit pc_p2c_final (Part 2C): every hypothesis of P2C_FULL_CHAIN proved at *)
(* the instance used by the main theorem.  The three hypotheses of           *)
(* P2CX2_CHAIN_OPEN5 (pc_p2c_chainx2), Part 2B statements at real^3, are     *)
(* proved by pc_p2b_close9 (P2BZ9_ASYM_SOLITON,                              *)
(* P2BZ9_KAPPA_NECKS_ROUND_L_FIX) and pc_p2b_close95                         *)
(* (P2BZ5_COR_9_95_VIEW_FIX).  The P2_ forms that P3_FULL_CHAIN uses follow  *)
(* where their text is that of the P2C_ form, plus P2_THM_10_2 from the view *)
(* form and history regularity, P2_PROP_9_79_NECK (P2B_PROP_9_79_NECK_FIX)   *)
(* and P2_COR_9_95 at (:real^3) (P2BZ5_COR_9_95 of pc_p2b_close95), all in   *)
(* P2CFN_P2_ALL.  P2_LEMMA_11_23 is not among them: as written in            *)
(* pc_p3_iface it is false, and P3_FULL_CHAIN_2 of pc_p3_route2 does not use *)
(* it.                                                                       *)
(* ========================================================================= *)

needs "src/pc_p2c_chainx2.ml";;
needs "src/pc_p2b_close9.ml";;
needs "src/pc_p2b_close95.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Part 2C chain with no hypotheses.                                     *)
(* ------------------------------------------------------------------------- *)

let P2CFN_CHAIN = prove
 (`!(u:A->bool).
     P2_THM_5_11_STATEMENT u (:real^3) /\
     P2C_THM_5_15_STATEMENT u (:real^3) /\
     P2C_LEMMA_11_2_STATEMENT u /\
     P2C_THM_11_8_STATEMENT u (:real^3) /\
     P2C_LEMMA_11_23_STATEMENT u /\
     P2C_THM_11_19_STATEMENT u /\
     P2C_LEMMA_11_30_STATEMENT u /\
     P2C_THM_11_31_STATEMENT u /\
     P2_LEMMA_12_3_STATEMENT /\
     P2_THM_12_5_STATEMENT /\
     P2_STD_EXTEND_STATEMENT /\
     P2_PROP_12_7_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\
     P2C_THM_12_32_STATEMENT /\
     P2_LEMMA_12_37_STATEMENT`,
  GEN_TAC THEN MATCH_MP_TAC P2CX2_CHAIN_OPEN5 THEN
  REWRITE_TAC[P2BZ5_COR_9_95_VIEW_FIX; P2BZ9_KAPPA_NECKS_ROUND_L_FIX; P2BZ9_ASYM_SOLITON]);;

(* ------------------------------------------------------------------------- *)
(* The P2_ forms for P3_FULL_CHAIN.  Seven P2C_ statements have the same     *)
(* text as their P2_ forms (P2CFN_SAME); P2_THM_10_2 from P2B_THM_10_2_HIST  *)
(* with the view form P2BT_THM_10_2_VIEW and history regularity              *)
(* P2CY_HISTORY_REGULAR.                                                     *)
(* ------------------------------------------------------------------------- *)

let P2CFN_SAME = prove
 (`(!(u:A->bool) (w:B->bool). P2C_THM_5_15_STATEMENT u w <=> P2_THM_5_15_STATEMENT u w) /\
   (!(u:A->bool). P2C_LEMMA_11_2_STATEMENT u <=> P2_LEMMA_11_2_STATEMENT u) /\
   (!(u:A->bool) (w:B->bool). P2C_THM_11_8_STATEMENT u w <=> P2_THM_11_8_STATEMENT u w) /\
   (!(u:A->bool). P2C_THM_11_19_STATEMENT u <=> P2_THM_11_19_STATEMENT u) /\
   (!(u:A->bool). P2C_LEMMA_11_30_STATEMENT u <=> P2_LEMMA_11_30_STATEMENT u) /\
   (!(u:A->bool). P2C_THM_11_31_STATEMENT u <=> P2_THM_11_31_STATEMENT u) /\
   (P2C_THM_12_32_STATEMENT <=> P2_THM_12_32_STATEMENT)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_THM_5_15_STATEMENT; P2_THM_5_15_STATEMENT;
              P2C_LEMMA_11_2_STATEMENT; P2_LEMMA_11_2_STATEMENT;
              P2C_THM_11_8_STATEMENT; P2_THM_11_8_STATEMENT;
              P2C_THM_11_19_STATEMENT; P2_THM_11_19_STATEMENT;
              P2C_LEMMA_11_30_STATEMENT; P2_LEMMA_11_30_STATEMENT;
              P2C_THM_11_31_STATEMENT; P2_THM_11_31_STATEMENT;
              P2C_THM_12_32_STATEMENT; P2_THM_12_32_STATEMENT]);;

let P2CFN_P2_TARGETS = prove
 (`!(u:A->bool).
     P2_THM_5_11_STATEMENT u (:real^3) /\
     P2_THM_5_15_STATEMENT u (:real^3) /\
     P2_LEMMA_11_2_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3) /\
     P2_THM_11_19_STATEMENT u /\
     P2_LEMMA_11_30_STATEMENT u /\
     P2_THM_11_31_STATEMENT u /\
     P2_LEMMA_12_3_STATEMENT /\
     P2_THM_12_5_STATEMENT /\
     P2_STD_EXTEND_STATEMENT /\
     P2_PROP_12_7_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\
     P2_THM_12_32_STATEMENT /\
     P2_LEMMA_12_37_STATEMENT /\
     P2_THM_10_2_STATEMENT u`,
  GEN_TAC THEN MP_TAC(ISPEC `u:A->bool` P2CFN_CHAIN) THEN
  REWRITE_TAC[P2CFN_SAME] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2B_THM_10_2_HIST THEN
  REWRITE_TAC[P2BT_THM_10_2_VIEW; P2CY_HISTORY_REGULAR]);;

(* P2_PROP_9_79_NECK has the text of P2B_PROP_9_79_NECK_FIX. *)

let P2CFN_PROP_9_79_NECK = prove
 (`!(u:A->bool) (w:B->bool). P2_PROP_9_79_NECK_STATEMENT u w`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] P2B_PROP_9_79_NECK_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_NECK_FIX_STATEMENT; P2_PROP_9_79_NECK_STATEMENT]);;


(* ------------------------------------------------------------------------- *)
(* All the P2_ forms of P3_FULL_CHAIN_2 that Part 2 gives, in one theorem:   *)
(* P2CFN_P2_TARGETS, Prop 9.79 in neck form for every w, and MT Cor 9.95 at  *)
(* w = (:real^3) from pc_p2b_close95 (P2BZ5_COR_9_95, by the route           *)
(* P2BCV_COR_9_95 of pc_p2b_canonv).                                         *)
(* ------------------------------------------------------------------------- *)

let P2CFN_P2_ALL = prove
 (`!(u:A->bool).
     P2_THM_5_11_STATEMENT u (:real^3) /\
     P2_THM_5_15_STATEMENT u (:real^3) /\
     P2_LEMMA_11_2_STATEMENT u /\
     P2_THM_11_8_STATEMENT u (:real^3) /\
     P2_THM_11_19_STATEMENT u /\
     P2_LEMMA_11_30_STATEMENT u /\
     P2_THM_11_31_STATEMENT u /\
     P2_LEMMA_12_3_STATEMENT /\
     P2_THM_12_5_STATEMENT /\
     P2_STD_EXTEND_STATEMENT /\
     P2_PROP_12_7_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\
     P2_THM_12_32_STATEMENT /\
     P2_LEMMA_12_37_STATEMENT /\
     P2_THM_10_2_STATEMENT u /\
     (!w:B->bool. P2_PROP_9_79_NECK_STATEMENT u w) /\
     P2_COR_9_95_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P2CFN_P2_TARGETS; P2CFN_PROP_9_79_NECK; P2BZ5_COR_9_95]);;

