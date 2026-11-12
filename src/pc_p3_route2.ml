(* ========================================================================= *)
(* pc_p3_route2: the Prop 17.1 route without the P2_LEMMA_11_23 hypothesis.  *)
(* P2_LEMMA_11_23_STATEMENT (pc_p3_iface) is false as written (at event      *)
(* times next to new caps), and P3H_PROP_17_1_CORE (pc_p3_c171d) does not    *)
(* need it: its 14 hypotheses do not include it, so the 11.23 conjunct of    *)
(* P3_PROP_17_1_ROUTE is not needed.  This file adds                         *)
(*   P3_PROP_17_1_ROUTE_2_STATEMENT : P3_PROP_17_1_ROUTE_STATEMENT without   *)
(*     the conjunct P2_LEMMA_11_23_STATEMENT u (proved at (:real^3) in       *)
(*     pc_p3_c171e);                                                         *)
(*   P3S2_PROP_17_1_ROUTE_BRIDGE : ROUTE_2 ==> P3_PROP_17_1_ROUTE_STATEMENT; *)
(*   P3_FULL_CHAIN_2 : P3_FULL_CHAIN (same statement and proof) with the     *)
(*     17.1 route replaced by ROUTE_2 and without the hypothesis             *)
(*     P2_LEMMA_11_23_STATEMENT (:A+num#num#real^3).                         *)
(* ========================================================================= *)

needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The route statement, the bridge to P3_PROP_17_1_ROUTE and the full chain. *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_17_1_ROUTE_2_STATEMENT = new_definition
 `P3_PROP_17_1_ROUTE_2_STATEMENT (u:A->bool) (w:B->bool) <=>
    P3_LEMMA_17_2_STATEMENT u /\ P3_LEMMA_17_7_STATEMENT u /\
    P3_PROP_16_1_STATEMENT u /\
    P2_THM_11_8_STATEMENT u w /\ P2_COR_9_95_STATEMENT u w /\
    P2_THM_10_2_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u /\
    P2_THM_5_11_STATEMENT u w /\
    P2_PROP_9_79_SLICE_STATEMENT u w /\
    RFS_CUTCAP_SC_STATEMENT u u /\ APX_SC_SPHERE_SEP_STATEMENT u /\
    P3_PROP_16_5_STATEMENT u /\ P3_THM_13_2_STATEMENT /\
    P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\
    P2_PROP_9_79_SLICE_STATEMENT (:real^3) u /\
    P2_PROP_2_19_SEP_STATEMENT w /\ P2_SEP_LIMIT_STATEMENT u w /\
    P3_HIST_C2_BOUND_STATEMENT u /\ P3_STD_C2_BOUND_STATEMENT /\
    P2_PROP_12_31_STATEMENT /\ P2C_HISTORY_REGULAR_STATEMENT u /\
    P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
    ==> P3_PROP_17_1_STATEMENT u`;;

let P3S2_PROP_17_1_ROUTE_BRIDGE = prove
 (`!(u:A->bool) (w:B->bool).
     P3_PROP_17_1_ROUTE_2_STATEMENT u w ==> P3_PROP_17_1_ROUTE_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P3_PROP_17_1_ROUTE_2_STATEMENT; P3_PROP_17_1_ROUTE_STATEMENT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3_FULL_CHAIN_2 = prove
 (`!(u:A->bool) (w:B->bool).
     P3_START_ROUTE_STATEMENT u /\
     P3_FLOW_EXTENSION_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_THM_13_2_ROUTE_STATEMENT /\
     P3_LEMMA_14_11_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_15_11_ROUTE_STATEMENT u /\
     P3_PROP_15_2_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_5_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_13_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_16_15_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_21_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_COR_16_24_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_4_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_1_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_17_2_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_17_7_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_17_1_ROUTE_2_STATEMENT (:A+num#num#real^3) w /\
     P3_LEMMA_17_12_ROUTE_STATEMENT u /\
     P3N_SMALL_SCALE_STATEMENT (:A+num#num#real^3) /\
     PDE_CURVATURE_TIME_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_MAXIMAL_FLOW_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_UNIQUENESS_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_GLUE_STATEMENT (:A+num#num#real^3) (:3) /\
     P2_THM_3_28_STATEMENT (:A+num#num#real^3) /\
     P2_THM_3_29_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_3_14_STATEMENT (:real^3) /\
     P2_PROP_4_11_VOLUME_STATEMENT (:A+num#num#real^3) /\
     P2_THM_4_32_STATEMENT (:A+num#num#real^3) /\
     P2_VOLUME_GROWTH_STATEMENT (:A+num#num#real^3) /\
     P2_THM_5_11_STATEMENT (:A+num#num#real^3) w /\
     P2_THM_5_15_STATEMENT (:A+num#num#real^3) (:real^3) /\
     P2_THM_8_1_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_7_2_STATEMENT (:A+num#num#real^3) /\
     P2_COR_7_12_STATEMENT (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:A+num#num#real^3) w /\
     P2_PROP_9_79_NECK_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_NECK_STATEMENT (:real^3) (:A+num#num#real^3) /\
     P2_COR_9_95_STATEMENT (:A+num#num#real^3) w /\
     P2_THM_10_2_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_11_2_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_8_STATEMENT (:A+num#num#real^3) w /\
     P2_THM_11_19_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_11_30_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_31_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_12_3_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_STD_EXTEND_STATEMENT /\
     P2_PROP_12_7_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\ P2_THM_12_32_STATEMENT /\ P2_LEMMA_12_37_STATEMENT /\
     P2C_PROP_5_14_STATEMENT (:A+num#num#real^3) (:real^3) /\
     P2C_HISTORY_REGULAR_STATEMENT (:A+num#num#real^3) /\
     RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     APX_SC_SPHERE_SEP_STATEMENT (:A+num#num#real^3) /\
     P2_PROP_2_19_SEP_STATEMENT w /\
     P2_SEP_LIMIT_STATEMENT (:A+num#num#real^3) w /\
     P2_PROP_9_79_OPEN_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P3_HIST_C2_BOUND_STATEMENT (:A+num#num#real^3) /\ P3_STD_C2_BOUND_STATEMENT /\
     P4_EXTINCTION_STATEMENT u /\ P2_NORMALIZE_STATEMENT u /\
     SMT_ORIENTABLE_STATEMENT u (:3)
     ==> RFS_EXTINCTION_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P3_START_ROUTE_STATEMENT; P3_FLOW_EXTENSION_ROUTE_STATEMENT;
              P3_THM_13_2_ROUTE_STATEMENT; P3_LEMMA_14_11_ROUTE_STATEMENT;
              P3_LEMMA_15_11_ROUTE_STATEMENT; P3_PROP_15_2_ROUTE_STATEMENT;
              P3_PROP_16_5_ROUTE_STATEMENT; P3_PROP_16_13_ROUTE_STATEMENT;
              P3_LEMMA_16_15_ROUTE_STATEMENT; P3_PROP_16_21_ROUTE_STATEMENT;
              P3_COR_16_24_ROUTE_STATEMENT; P3_PROP_16_4_ROUTE_STATEMENT;
              P3_PROP_16_1_ROUTE_STATEMENT; P3_LEMMA_17_2_ROUTE_STATEMENT;
              P3_LEMMA_17_7_ROUTE_STATEMENT; P3_PROP_17_1_ROUTE_2_STATEMENT;
              P3_LEMMA_17_12_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `P3_THM_13_2_STATEMENT` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_14_11_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_15_2_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_5_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_13_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_16_15_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_21_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_COR_16_24_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_4_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_1_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_2_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_7_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_17_1_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_15_11_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_FLOW_EXTENSION_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_12_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_START_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P3_RFS_EXTINCTION THEN ASM_REWRITE_TAC[]);;

