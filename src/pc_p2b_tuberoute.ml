(* ========================================================================= *)
(* pc_p2b_tuberoute: the route theorem of the bad-tube half of MT Thm 10.2   *)
(* (MT Sec 10.3) and the leaf P2C_REQ_THM_10_2_VIEW_STATEMENT.  Part I       *)
(* (P2BT_PART1_CUT, pc_p2b_tube2), the limit (P2BT_LIMIT_EXISTS,             *)
(* pc_p2b_tube2), the five limit-side statements of pc_p2b_tubelimst (proved *)
(* in pc_p2b_tubelim, pc_p2b_tubelim2 and pc_p2b_tubelim3) and the bad tube  *)
(* in the limit (P2BT_LIMIT_BAD_TUBE, pc_p2b_tube4) give                     *)
(* P2B_BAD_TUBE_FROM_FAILURE_STATEMENT from the route inputs                 *)
(* (P2BT_BAD_TUBE_ROUTE); with the no-bad-tube route P2BK_NO_BAD_TUBE_ROUTE  *)
(* and the inputs proved elsewhere this is the leaf (P2BT_THM_10_2_VIEW).    *)
(* ========================================================================= *)

needs "src/pc_p2b_tube4.ml";;
needs "src/pc_p2b_tubelim3.ml";;  (* the five P2BTL_LIM theorems (loads tubelim2, tubelim) *)
needs "src/pc_p2b_cone10.ml";;    (* P2BK_NO_BAD_TUBE_ROUTE *)
needs "src/pc_p2c_lcg.ml";;       (* P2GH_LOCAL_COMPACT_G *)
needs "src/pc_p2c_lcn.ml";;       (* P2CD_LOCAL_COMPACT_N *)
needs "src/pc_apx_short.ml";;     (* APX_A1 *)
needs "src/pc_apx_mincs.ml";;     (* APXM_A6_CS, APXM_A8_CS *)
needs "src/pc_apx_a21ch.ml";;     (* APXH_A21_CH *)
needs "src/pc_apx_chchart.ml";;   (* APXC_CHAIN_CHART *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The route theorem.  The five limit-side statements are discharged by the  *)
(* theorems P2BTL_LIM_BOXES, P2BTL_LIM_SEC (pc_p2b_tubelim), P2BTL_LIM_ENECK *)
(* (pc_p2b_tubelim2), P2BTL_LIM_CHAIN, P2BTL_LIM_SUMMABLE (pc_p2b_tubelim3), *)
(* each |- !u w. P2BT_LIM_..._STATEMENT u w.                                 *)
(* ========================================================================= *)

let P2BT_BAD_TUBE_ROUTE = prove
 (`!(u:A->bool) (w:B->bool). P2B_BAD_TUBE_ROUTE_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_BAD_TUBE_ROUTE_STATEMENT; P2B_BAD_TUBE_FROM_FAILURE_STATEMENT] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BT_PART1_CUT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1"))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] P2BT_LIMIT_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "le"))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] P2BT_LIMIT_BAD_TUBE) THEN
  ASM_REWRITE_TAC[P2BTL_LIM_CHAIN; P2BTL_LIM_SUMMABLE; P2BTL_LIM_BOXES; P2BTL_LIM_SEC;
                  P2BTL_LIM_ENECK] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bt"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2bt_fail (u:A->bool) eps C A` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bt_fail]; ALL_TAC] THEN
  USE_THEN "p1" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:num->real`; `Q:num->real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
    `A1:real`] THEN
  STRIP_TAC THEN
  USE_THEN "le" (MP_TAC o SPECL
   [`eps:real`; `C:real`; `A:real`; `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:num->real`; `Q:num->real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
    `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`sub:num->num`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:B->real^3^3`; `zl:B`; `W:num->B->bool`; `phi:num->B->A`;
    `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`] THEN
  DISCH_TAC THEN USE_THEN "bt" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`C:real`; `A:real`; `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:num->real`; `Q:num->real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
    `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`; `W:num->B->bool`;
    `phi:num->B->A`; `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The leaf P2C_REQ_THM_10_2_VIEW_STATEMENT (MT Thm 10.2, view form) at      *)
(* every type, by P2BT_THM_10_2_FROM_ROUTE (pc_p2b_tubestmts) with the limit *)
(* type real^3: the bad-tube route above, the no-bad-tube route              *)
(* P2BK_NO_BAD_TUBE_ROUTE with the local compactness N                       *)
(* (P2CD_LOCAL_COMPACT_N), the local compactness G at real^3                 *)
(* (P2GH_LOCAL_COMPACT_G), and MT A.1, A.6, A.8, A.21 with chains and the    *)
(* infinite chain chart (the pc_apx units).                                  *)
(* ========================================================================= *)

let P2BT_THM_10_2_VIEW = prove
 (`!u:A->bool. P2C_REQ_THM_10_2_VIEW_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC (INST_TYPE [`:real^3`,`:B`] P2BT_THM_10_2_FROM_ROUTE) THEN
  EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[P2BT_BAD_TUBE_ROUTE; P2GH_LOCAL_COMPACT_G; APX_A1; APXM_A6_CS; APXM_A8_CS;
              APXH_A21_CH; APXC_CHAIN_CHART] THEN
  MP_TAC(ISPEC `(:real^3)` P2BK_NO_BAD_TUBE_ROUTE) THEN
  REWRITE_TAC[P2B_NO_BAD_TUBE_ROUTE_STATEMENT; P2CD_LOCAL_COMPACT_N]);;

