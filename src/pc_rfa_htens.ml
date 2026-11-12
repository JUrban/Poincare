(* ========================================================================= *)
(* Unit pc_rfa_htens: the Harnack tensors of Hamilton's matrix Harnack       *)
(* quadratic as chart tensor fields along a chart Ricci flow, and their heat *)
(* defects (D_t - Lap) by the rules of pc_rfa_hcalc: nabla Ric, nabla^2 Ric, *)
(* P (CLN 10.36), Lap Ric, the scalar curvature and its Hessian, Ric         *)
(* squared, and (in dimension 3) Rm = h(Ric), the Ricci action term rfa_hric *)
(* and M with time origin s (CLN 10.37).                                     *)
(* ========================================================================= *)

needs "src/pc_rfa_hcalc.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Definitions and the general heat statements.                              *)
(* ========================================================================= *)

(* P(a,b,c) = (nabla_a Ric)(b,c) - (nabla_b Ric)(a,c)  (CLN 10.36; the last *)
(* slot of lnabla is the derivative direction).                             *)

let rfa_hP = new_definition
 `rfa_hP (G:real^N->real^N^N) y (u:num->real^N) =
    lnabla 2 G (lric2 G) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
    lnabla 2 G (lric2 G) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2)`;;

(* The scalar curvature as a field of degree 0.                             *)

let rfa_sc = new_definition
 `rfa_sc (G:real^N->real^N^N) (y:real^N) (u:num->real^N) = lscalar G y`;;

(* Ric squared, Ric(u1,e_p) g^pq Ric(e_q,u2), as a contracted product.      *)

let rfa_ric2sq = new_definition
 `rfa_ric2sq (G:real^N->real^N^N) =
    ltcontr G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2
                           else m)
                      (ltprod 2 (lric2 G) (lric2 G)))`;;

(* M with time origin s at time t (CLN 10.37):                              *)
(*   Lap Ric - (1/2) nabla nabla R + 2 Rm.Ric - Ric^2 + Ric / (2 (t - s)).   *)

let rfa_hM = new_definition
 `rfa_hM s t (G:real^N->real^N^N) y (u:num->real^N) =
    ltlap 2 G (lric2 G) y u - inv(&2) * lnabla 1 G (lnabla 0 G (rfa_sc G)) y u +
    rfa_hric G y u - rfa_ric2sq G y u + inv(&2 * (t - s)) * lric2 G y u`;;

(* h(T): the algebraic curvature tensor determined in dimension 3 by its    *)
(* Ricci contraction T, in the slot convention of lrm4.                     *)

let rfa_h3 = new_definition
 `rfa_h3 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (u:num->real^N) =
    tf y (\m. if m = 1 then u 1 else u 3) * lmetric2 G y (\m. if m = 1 then u 2 else u 4) +
    tf y (\m. if m = 1 then u 2 else u 4) * lmetric2 G y (\m. if m = 1 then u 1 else u 3) -
    tf y (\m. if m = 1 then u 1 else u 4) * lmetric2 G y (\m. if m = 1 then u 2 else u 3) -
    tf y (\m. if m = 1 then u 2 else u 3) * lmetric2 G y (\m. if m = 1 then u 1 else u 4) -
    inv(&2) * ltcontr G tf y u *
    (lmetric2 G y (\m. if m = 1 then u 1 else u 3) *
     lmetric2 G y (\m. if m = 1 then u 2 else u 4) -
     lmetric2 G y (\m. if m = 1 then u 1 else u 4) *
     lmetric2 G y (\m. if m = 1 then u 2 else u 3))`;;

(* The heat defects of nabla Ric and of nabla^2 Ric (rule R5 applied to     *)
(* RFA_HEAT_RIC), as fields.                                                *)

let rfa_hdr = new_definition
 `rfa_hdr (G:real^N->real^N^N) y (u:num->real^N) =
    lnabla 2 G (rfa_hric G) y u + rfa_rmcomm 2 G (lric2 G) y u`;;

let rfa_hddr = new_definition
 `rfa_hddr (G:real^N->real^N^N) y (u:num->real^N) =
    lnabla 3 G (rfa_hdr G) y u + rfa_rmcomm 3 G (lnabla 2 G (lric2 G)) y u`;;


(* ========================================================================= *)
(* Heat statements for nabla Ric, nabla^2 Ric and P.                         *)
(* ========================================================================= *)

let RFA_HEAT_DRIC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 3 U a b G (\t. lnabla 2 (G t) (lric2 (G t))) (\t. rfa_hdr (G t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LNABLA) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; rfa_hdr]);;

let RFA_HEAT_DDRIC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 4 U a b G (\t. lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t))))
           (\t. rfa_hddr (G t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`;
                 `\t. rfa_hdr ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LNABLA) THEN
  ASM_SIMP_TAC[RFA_HEAT_DRIC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; rfa_hddr]);;

(* Tactics: explicit permutations (given the inverse) and slot agreement of *)
(* two tuples on the first slots by case analysis.                          *)

let RFA_HT_PERM_TAC inv =
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN EXISTS_TAC inv THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;;

let RFA_HT_SLOTS_TAC n =
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (list_mk_disj (map (fun i -> mk_eq(`m:num`, mk_small_numeral i)) (1--n)))
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH; swap];;

let RFA_CYC123_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m) permutes 1..3`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m`);;

let RFA_SWAP23_PERMUTES3 = prove
 (`swap(2,3) permutes 1..3`,
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

(* The heat defect of P.                                                     *)

let RFA_HEAT_HP = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 3 U a b G (\t. rfa_hP (G t))
           (\t y u. rfa_hdr (G t) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
                    rfa_hdr (G t) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_DRIC) THEN
  MP_TAC(ISPECL [`3`; `\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`;
                 `\t. rfa_hdr ((G:real->real^N->real^N^N) t)`] RFA_HEAT_PERM) THEN
  MP_TAC(ISPECL [`3`; `swap(2,3)`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`;
                 `\t. rfa_hdr ((G:real->real^N->real^N^N) t)`] RFA_HEAT_PERM) THEN
  ASM_REWRITE_TAC[RFA_CYC123_PERMUTES; RFA_SWAP23_PERMUTES3] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1
                                  else m)
                        (lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)))`;
                 `\t. ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1
                                  else m)
                        (rfa_hdr ((G:real->real^N->real^N^N) t))`;
                 `\t. ltperm (swap(2,3))
                        (lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)))`;
                 `\t. ltperm (swap(2,3)) (rfa_hdr ((G:real->real^N->real^N^N) t))`;
                 `&1`; `-- &1`] RFA_HEAT_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t y u. &1 * (\t. ltperm (\m. if m = 1 then 2 else if m = 2 then 3
                                            else if m = 3 then 1 else m)
                          (lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)))) t y u +
                      -- &1 * (\t. ltperm (swap(2,3)) (lnabla 2 (G t) (lric2 (G t)))) t y u` THEN
  EXISTS_TAC `\t y u. &1 * (\t. ltperm (\m. if m = 1 then 2 else if m = 2 then 3
                                            else if m = 3 then 1 else m)
                          (rfa_hdr ((G:real->real^N->real^N^N) t))) t y u +
                      -- &1 * (\t. ltperm (swap(2,3)) (rfa_hdr (G t))) t y u` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 3 U (rfa_hdr ((G:real->real^N->real^N^N) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_heat 3 U a b (G:real->real^N->real^N^N)
                   (\t. lnabla 2 (G t) (lric2 (G t))) (\t. rfa_hdr (G t))` THEN
    REWRITE_TAC[rfa_heat] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 3 U (lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lric2 ((G:real->real^N->real^N^N) t)`] LNABLA_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hP; ltperm] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; GSYM real_sub] THEN
  CONJ_TAC THEN BINOP_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  RFA_HT_SLOTS_TAC 3);;


(* ========================================================================= *)
(* The rough Laplacian of Ric, the scalar curvature, its                     *)
(* gradient and Hessian, and Ric squared.                                    *)
(* ========================================================================= *)

let RFA_TAU34_PERMUTES = prove
 (`(\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1 else if m = 4 then 2
        else m) permutes 1..4`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                       else if m = 4 then 2 else m`);;

let RFA_HEAT_LAPRIC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. ltlap 2 (G t) (lric2 (G t)))
           (\t y u. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                      matrix_inv(G t y)$p$q *
                      rfa_hddr (G t) y (\m. if m = 3 then basis p else if m = 4 then basis q
                                            else u m))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_DDRIC) THEN
  MP_TAC(ISPECL [`4`; `\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                           else if m = 4 then 2 else m`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 3 ((G:real->real^N->real^N^N) t) (lnabla 2 (G t) (lric2 (G t)))`;
                 `\t. rfa_hddr ((G:real->real^N->real^N^N) t)`] RFA_HEAT_PERM) THEN
  ASM_REWRITE_TAC[RFA_TAU34_PERMUTES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                  else if m = 4 then 2 else m)
                        (lnabla 3 ((G:real->real^N->real^N^N) t)
                           (lnabla 2 (G t) (lric2 (G t))))`;
                 `\t. ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                  else if m = 4 then 2 else m)
                        (rfa_hddr ((G:real->real^N->real^N^N) t))`] RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t. ltcontr ((G:real->real^N->real^N^N) t)
                    (ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                 else if m = 4 then 2 else m)
                       (lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t)))))` THEN
  EXISTS_TAC `\t. ltcontr ((G:real->real^N->real^N^N) t)
                    (ltperm (\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 1
                                 else if m = 4 then 2 else m)
                       (rfa_hddr (G t)))` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 U (rfa_hddr ((G:real->real^N->real^N^N) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_heat 4 U a b (G:real->real^N->real^N^N)
                   (\t. lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t)))) (\t. rfa_hddr (G t))` THEN
    REWRITE_TAC[rfa_heat] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 U (lnabla 3 ((G:real->real^N->real^N^N) t)
                                     (lnabla 2 (G t) (lric2 (G t))))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_heat 4 U a b (G:real->real^N->real^N^N)
                   (\t. lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t)))) (\t. rfa_hddr (G t))` THEN
    REWRITE_TAC[rfa_heat] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ltcontr; ltperm; ltlap; RFA_LNABLA_ITER_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THEN RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  RFA_HT_SLOTS_TAC 4);;

(* The scalar curvature, its gradient and its Hessian.                      *)

let RFA_HEAT_SC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 0 U a b G (\t. rfa_sc (G t)) (\t. ltcontr (G t) (rfa_hric (G t)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t. ltcontr ((G:real->real^N->real^N^N) t) (lric2 (G t))` THEN
  EXISTS_TAC `\t. ltcontr ((G:real->real^N->real^N^N) t) (rfa_hric (G t))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfa_sc; lscalar; ltcontr; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let RFA_RMCOMM_0 = prove
 (`!(G:real^N->real^N^N) tf y u. rfa_rmcomm 0 G tf y u = &0`,
  REWRITE_TAC[rfa_rmcomm; SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO; SUM_0]);;

let RFA_HEAT_DSC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 1 U a b G (\t. lnabla 0 (G t) (rfa_sc (G t)))
           (\t. lnabla 0 (G t) (ltcontr (G t) (rfa_hric (G t))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. rfa_sc ((G:real->real^N->real^N^N) t)`;
                 `\t. ltcontr ((G:real->real^N->real^N^N) t) (rfa_hric (G t))`]
         RFA_HEAT_LNABLA) THEN
  ASM_SIMP_TAC[RFA_HEAT_SC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RFA_RMCOMM_0; REAL_ADD_RID; ETA_AX]);;

let RFA_HEAT_HESSSC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. lnabla 1 (G t) (lnabla 0 (G t) (rfa_sc (G t))))
           (\t y u. lnabla 1 (G t) (lnabla 0 (G t) (ltcontr (G t) (rfa_hric (G t)))) y u +
                    rfa_rmcomm 1 (G t) (lnabla 0 (G t) (rfa_sc (G t))) y u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (rfa_sc (G t))`;
                 `\t. lnabla 0 ((G:real->real^N->real^N^N) t)
                        (ltcontr (G t) (rfa_hric (G t)))`] RFA_HEAT_LNABLA) THEN
  ASM_SIMP_TAC[RFA_HEAT_DSC] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Ric squared.                                                              *)

let RFA_SIG312_PERMUTES = prove
 (`(\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m) permutes 1..4`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m`);;

let rfa_hric2sq = new_definition
 `rfa_hric2sq (G:real^N->real^N^N) =
    ltcontr G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2
                           else m)
                      (\y u. ltprod 2 (rfa_hric G) (lric2 G) y u +
                             ltprod 2 (lric2 G) (rfa_hric G) y u -
                             &2 * rfa_xgrad 2 2 G (lric2 G) (lric2 G) y u))`;;

let RFA_HEAT_RIC2SQ = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. rfa_ric2sq (G t)) (\t. rfa_hric2sq (G t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `2`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LTPROD) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltprod 2 (lric2 ((G:real->real^N->real^N^N) t)) (lric2 (G t))`;
                 `\t y u. ltprod 2 (rfa_hric ((G:real->real^N->real^N^N) t)) (lric2 (G t)) y u +
                          ltprod 2 (lric2 (G t)) (rfa_hric (G t)) y u -
                          &2 * rfa_xgrad 2 2 (G t) (lric2 (G t)) (lric2 (G t)) y u`]
         RFA_HEAT_PERM) THEN
  ASM_REWRITE_TAC[RFA_SIG312_PERMUTES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2
                                  else m)
                        (ltprod 2 (lric2 ((G:real->real^N->real^N^N) t)) (lric2 (G t)))`;
                 `\t. ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2
                                  else m)
                        (\y u. ltprod 2 (rfa_hric ((G:real->real^N->real^N^N) t))
                                 (lric2 (G t)) y u +
                               ltprod 2 (lric2 (G t)) (rfa_hric (G t)) y u -
                               &2 * rfa_xgrad 2 2 (G t) (lric2 (G t)) (lric2 (G t)) y u)`]
         RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfa_ric2sq; rfa_hric2sq]);;


(* ========================================================================= *)
(* Products with a parallel factor of defect 0, and the heat                 *)
(* rule for h(T).                                                            *)
(* ========================================================================= *)

let RFA_XGRAD_PAR = prove
 (`!p q (G:real^N->real^N^N) A B y u.
     (!w. lnabla q G B y w = &0) ==> rfa_xgrad p q G A B y u = &0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rfa_xgrad; REAL_MUL_RZERO; SUM_0]);;

let RFA_HEAT_LTPROD_PAR = prove
 (`!p q U a b (G:real->real^N->real^N^N) A HA B.
     lricci_flow U a b G /\ rfa_heat p U a b G A HA /\
     rfa_heat q U a b G B (\t y u. &0) /\
     (!t y w. a < t /\ t < b /\ y IN U ==> lnabla q (G t) (B t) y w = &0)
     ==> rfa_heat (p + q) U a b G (\t. ltprod p (A t) (B t)) (\t. ltprod p (HA t) (B t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `A:real->real^N->(num->real^N)->real`;
                 `HA:real->real^N->(num->real^N)->real`;
                 `B:real->real^N->(num->real^N)->real`;
                 `\t:real. \y:real^N. \u:num->real^N. &0`] RFA_HEAT_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t. ltprod p ((A:real->real^N->(num->real^N)->real) t) (B t)` THEN
  EXISTS_TAC `\t y u. ltprod p ((HA:real->real^N->(num->real^N)->real) t) (B t) y u +
                      ltprod p (A t) ((\t:real. \y:real^N. \u:num->real^N. &0) t) y u -
                      &2 * rfa_xgrad p q ((G:real->real^N->real^N^N) t) (A t) (B t) y u` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_XGRAD_PAR] THEN REWRITE_TAC[ltprod] THEN REAL_ARITH_TAC);;

let RFA_HEAT_TIMES_METRIC = prove
 (`!p U a b (G:real->real^N->real^N^N) A HA.
     lricci_flow U a b G /\ rfa_heat p U a b G A HA
     ==> rfa_heat (p + 2) U a b G (\t. ltprod p (A t) (lmetric2 (G t)))
                                  (\t. ltprod p (HA t) (lmetric2 (G t)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_HEAT_LTPROD_PAR THEN
  ASM_SIMP_TAC[RFA_HEAT_METRIC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LNABLA_METRIC THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]);;

let RFA_SIGB_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1 else if m = 4 then 3
        else m) permutes 1..4`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 4
                       else if m = 4 then 2 else m`);;

let RFA_SIGC_PERMUTES = prove
 (`(\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3
        else m) permutes 1..4`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 1 else if m = 2 then 3 else if m = 3 then 4
                       else if m = 4 then 2 else m`);;

let RFA_SIGD_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m) permutes 1..4`,
  RFA_HT_PERM_TAC `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m`);;

let RFA_SWAP23_PERMUTES4 = prove
 (`swap(2,3) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

(* The heat rule for h(T): its defect is h(H_T).                            *)

let RFA_HEAT_H3 = prove
 (`!U a b (G:real->real^N->real^N^N) Tf Hf.
     lricci_flow U a b G /\ rfa_heat 2 U a b G Tf Hf
     ==> rfa_heat 4 U a b G (\t. rfa_h3 (G t) (Tf t)) (\t. rfa_h3 (G t) (Hf t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (* A = T (x) g and C = (tr T) g (x) g *)
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Tf:real->real^N->(num->real^N)->real`;
                 `Hf:real->real^N->(num->real^N)->real`] RFA_HEAT_TIMES_METRIC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Tf:real->real^N->(num->real^N)->real`;
                 `Hf:real->real^N->(num->real^N)->real`] RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltcontr ((G:real->real^N->real^N^N) t)
                        ((Tf:real->real^N->(num->real^N)->real) t)`;
                 `\t. ltcontr ((G:real->real^N->real^N^N) t)
                        ((Hf:real->real^N->(num->real^N)->real) t)`]
         RFA_HEAT_TIMES_METRIC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltprod 0 (ltcontr ((G:real->real^N->real^N^N) t)
                                 ((Tf:real->real^N->(num->real^N)->real) t))
                        (lmetric2 (G t))`;
                 `\t. ltprod 0 (ltcontr ((G:real->real^N->real^N^N) t)
                                 ((Hf:real->real^N->(num->real^N)->real) t))
                        (lmetric2 (G t))`] RFA_HEAT_TIMES_METRIC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `A = \t. ltprod 2 ((Tf:real->real^N->(num->real^N)->real) t)
                                (lmetric2 ((G:real->real^N->real^N^N) t))` THEN
  ABBREV_TAC `HA = \t. ltprod 2 ((Hf:real->real^N->(num->real^N)->real) t)
                                 (lmetric2 ((G:real->real^N->real^N^N) t))` THEN
  ABBREV_TAC `C = \t. ltprod 2 (ltprod 0 (ltcontr ((G:real->real^N->real^N^N) t)
                                  ((Tf:real->real^N->(num->real^N)->real) t))
                                (lmetric2 (G t))) (lmetric2 (G t))` THEN
  ABBREV_TAC `HC = \t. ltprod 2 (ltprod 0 (ltcontr ((G:real->real^N->real^N^N) t)
                                  ((Hf:real->real^N->(num->real^N)->real) t))
                                 (lmetric2 (G t))) (lmetric2 (G t))` THEN
  SUBGOAL_THEN `rfa_heat 4 U a b (G:real->real^N->real^N^N) A HA /\
                rfa_heat 4 U a b G C HC`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "HA"; "C"; "HC"] THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the six permuted terms *)
  MAP_EVERY (fun (s,th) ->
    MP_TAC(ISPECL [`4`; s; `U:real^N->bool`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`;
                   `A:real->real^N->(num->real^N)->real`;
                   `HA:real->real^N->(num->real^N)->real`] RFA_HEAT_PERM) THEN
    ASM_REWRITE_TAC[th] THEN DISCH_TAC)
   [`swap(2,3)`, RFA_SWAP23_PERMUTES4;
    `(\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1 else if m = 4 then 3 else m)`, RFA_SIGB_PERMUTES; `(\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m)`, RFA_SIGC_PERMUTES; `(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)`, RFA_SIGD_PERMUTES] THEN
  MAP_EVERY (fun (s,th) ->
    MP_TAC(ISPECL [`4`; s; `U:real^N->bool`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`;
                   `C:real->real^N->(num->real^N)->real`;
                   `HC:real->real^N->(num->real^N)->real`] RFA_HEAT_PERM) THEN
    ASM_REWRITE_TAC[th] THEN DISCH_TAC)
   [`swap(2,3)`, RFA_SWAP23_PERMUTES4; `(\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m)`, RFA_SIGC_PERMUTES] THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t (y:real^N) (u:num->real^N). &1 * (&1 * (&1 * ltperm (swap(2,3)) ((A:real->real^N->(num->real^N)->real) t) y u + &1 * ltperm (\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1 else if m = 4 then 3 else m) (A t) y u) + -- &1 * (&1 * ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) (A t) y u + &1 * ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m) (A t) y u)) + --(inv(&2)) * (&1 * ltperm (swap(2,3)) ((C:real->real^N->(num->real^N)->real) t) y u + -- &1 * ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) (C t) y u)` THEN
  EXISTS_TAC `\t (y:real^N) (u:num->real^N). &1 * (&1 * (&1 * ltperm (swap(2,3)) ((HA:real->real^N->(num->real^N)->real) t) y u + &1 * ltperm (\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1 else if m = 4 then 3 else m) (HA t) y u) + -- &1 * (&1 * ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) (HA t) y u + &1 * ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m) (HA t) y u)) + --(inv(&2)) * (&1 * ltperm (swap(2,3)) ((HC:real->real^N->(num->real^N)->real) t) y u + -- &1 * ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) (HC t) y u)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC RFA_HEAT_LINCOMB THEN ASM_REWRITE_TAC[ETA_AX]; CONJ_TAC]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 2 U ((Tf:real->real^N->(num->real^N)->real) t) /\
                ltensor_field 2 U ((Hf:real->real^N->(num->real^N)->real) t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_heat 2 U a b (G:real->real^N->real^N^N) Tf Hf` THEN
    REWRITE_TAC[rfa_heat] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. (Tf:real->real^N->(num->real^N)->real) t y w =
         Tf t y (\m. if m = 1 then w 1 else w 2)) /\
    (!w. (Hf:real->real^N->(num->real^N)->real) t y w =
         Hf t y (\m. if m = 1 then w 1 else w 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    RFA_HT_SLOTS_TAC 2;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. ltcontr ((G:real->real^N->real^N^N) t)
           ((Tf:real->real^N->(num->real^N)->real) t) y w =
         ltcontr (G t) (Tf t) y u) /\
    (!w. ltcontr ((G:real->real^N->real^N^N) t)
           ((Hf:real->real^N->(num->real^N)->real) t) y w =
         ltcontr (G t) (Hf t) y u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[ltcontr] THEN
    RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    RFA_HT_SLOTS_TAC 2;
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["A"; "HA"; "C"; "HC"] THEN
  REWRITE_TAC[rfa_h3; ltperm; ltprod] THEN BETA_TAC THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lmetric2; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Dimension 3.  An array with the symmetries of Rm (the Bianchi             *)
(* identity is automatic in dimension 3) is h of its Ricci contraction.     *)
(* ========================================================================= *)

(* Canonical form of X i j k l (numerals) under the three symmetries th1    *)
(* (antisymmetry in the first pair), th2 (in the second pair), th3 (pair    *)
(* symmetry): pairs increasing, first pair not after the second, and 0 for  *)
(* a pair with equal entries.  Fails on terms that are already canonical.   *)

let RFA_X_ZERO12 = prove
 (`!(X:num->num->num->num->real). (!a b c d. X a b c d = --(X b a c d))
      ==> !a c d. X a a c d = &0`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `a:num`; `c:num`; `d:num`]) THEN
  REAL_ARITH_TAC);;

let RFA_X_ZERO34 = prove
 (`!(X:num->num->num->num->real). (!a b c d. X a b c d = --(X a b d c))
      ==> !a b c. X a b c c = &0`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `c:num`]) THEN
  REAL_ARITH_TAC);;

let RFA_X_CANON_CONV th1 th2 th3 =
  let z12 = MATCH_MP RFA_X_ZERO12 th1 and z34 = MATCH_MP RFA_X_ZERO34 th2 in
  let rec conv tm =
    let x, args = strip_comb tm in
    let [i; j; k; l] = map dest_small_numeral args in
    if i = j then SPECL [hd args; el 2 args; el 3 args] z12
    else if k = l then SPECL [hd args; el 1 args; el 2 args] z34
    else if i > j then CONV_RULE (RAND_CONV (RAND_CONV conv)) (SPECL args th1)
    else if k > l then CONV_RULE (RAND_CONV (RAND_CONV conv)) (SPECL args th2)
    else if (i, j) > (k, l) then CONV_RULE (RAND_CONV conv) (SPECL args th3)
    else REFL tm in
  fun tm ->
    let x, args = strip_comb tm in
    if length args <> 4 || not (forall is_numeral args) then failwith "RFA_X_CANON_CONV" else
    let [i; j; k; l] = map dest_small_numeral args in
    if i < j && k < l && (i, j) <= (k, l) then failwith "RFA_X_CANON_CONV" else
    CONV_RULE (RAND_CONV (REWRITE_CONV[REAL_NEG_NEG; REAL_NEG_0])) (conv tm);;

let RFA_H3_ALG = prove
 (`!X:num->num->num->num->real.
     (!a b c d. X a b c d = --(X b a c d)) /\ (!a b c d. X a b c d = --(X a b d c)) /\
     (!a b c d. X a b c d = X c d a b)
     ==> !a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                   1 <= d /\ d <= 3
                   ==> X a b c d =
                       sum(1..3) (\s. X s a s c) * (if b = d then &1 else &0) +
                       sum(1..3) (\s. X s b s d) * (if a = c then &1 else &0) -
                       sum(1..3) (\s. X s a s d) * (if b = c then &1 else &0) -
                       sum(1..3) (\s. X s b s c) * (if a = d then &1 else &0) -
                       inv(&2) * sum(1..3) (\i. sum(1..3) (\s. X s i s i)) *
                       ((if a = c then &1 else &0) * (if b = d then &1 else &0) -
                        (if a = d then &1 else &0) * (if b = c then &1 else &0))`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    let [th1; th2; th3] = CONJUNCTS th in
    let xv = `X:num->num->num->num->real` in
    let cv = RFA_X_CANON_CONV th1 th2 th3 in
    let canon tm = let f, args = strip_comb tm in
                   if f = xv then cv tm else failwith "canon" in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY (fun v ->
      SUBGOAL_THEN (mk_disj(mk_eq(v,`1`),mk_disj(mk_eq(v,`2`),mk_eq(v,`3`)))) MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC))
     [`a:num`; `b:num`; `c:num`; `d:num`] THEN
    REWRITE_TAC[SUM_3; ARITH] THEN CONV_TAC(DEPTH_CONV canon) THEN
    REAL_ARITH_TAC));;

(* h(T) as a combination of permuted products of T, its trace and the       *)
(* metric; hence a tensor field.                                            *)

let RFA_H3_COMB = prove
 (`!U (G:real^N->real^N^N) tf y u.
     ltensor_field 2 U tf /\ y IN U
     ==> rfa_h3 G tf y u =
         (ltperm (swap(2,3)) (ltprod 2 tf (lmetric2 G)) y u +
          ltperm (\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1
                      else if m = 4 then 3 else m) (ltprod 2 tf (lmetric2 G)) y u) -
         (ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2
                      else if m = 4 then 3 else m) (ltprod 2 tf (lmetric2 G)) y u +
          ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)
                 (ltprod 2 tf (lmetric2 G)) y u) -
         inv(&2) *
         (ltperm (swap(2,3))
            (ltprod 2 (ltprod 0 (ltcontr G tf) (lmetric2 G)) (lmetric2 G)) y u -
          ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2
                      else if m = 4 then 3 else m)
            (ltprod 2 (ltprod 0 (ltcontr G tf) (lmetric2 G)) (lmetric2 G)) y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. (tf:real^N->(num->real^N)->real) y w = tf y (\m. if m = 1 then w 1 else w 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    RFA_HT_SLOTS_TAC 2;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ltcontr (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y w =
        ltcontr G tf y u`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ltcontr] THEN
    RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    RFA_HT_SLOTS_TAC 2;
    ALL_TAC] THEN
  REWRITE_TAC[rfa_h3; ltperm; ltprod] THEN BETA_TAC THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lmetric2; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let RFA_H3_FIELD = prove
 (`!U (G:real^N->real^N^N) tf.
     metric_field U G /\ ltensor_field 2 U tf ==> ltensor_field 4 U (rfa_h3 G tf)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_FIELD_EQ THEN
  EXISTS_TAC
   `\y u. (ltperm (swap(2,3)) (ltprod 2 tf (lmetric2 (G:real^N->real^N^N))) y u +
           ltperm (\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 1
                       else if m = 4 then 3 else m) (ltprod 2 tf (lmetric2 G)) y u) -
          (ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2
                       else if m = 4 then 3 else m) (ltprod 2 tf (lmetric2 G)) y u +
           ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)
                  (ltprod 2 tf (lmetric2 G)) y u) -
          inv(&2) *
          (ltperm (swap(2,3))
             (ltprod 2 (ltprod 0 (ltcontr G tf) (lmetric2 G)) (lmetric2 G)) y u -
           ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2
                       else if m = 4 then 3 else m)
             (ltprod 2 (ltprod 0 (ltcontr G tf) (lmetric2 G)) (lmetric2 G)) y u)` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC RFA_H3_COMB THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 2 U (lmetric2 (G:real^N->real^N^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_LMETRIC2_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 4 U (ltprod 2 (tf:real^N->(num->real^N)->real)
                        (lmetric2 (G:real^N->real^N^N))) /\
    ltensor_field 4 U (ltprod 2 (ltprod 0 (ltcontr G tf) (lmetric2 G)) (lmetric2 G))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MP_TAC(ISPECL [`2`; `2`; `U:real^N->bool`] RFA_LTPROD_FIELD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`0`; `2`; `U:real^N->bool`] RFA_LTPROD_FIELD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`] RFA_LTCONTR_FIELD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST
   [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC;
    MATCH_MP_TAC RFA_TENSOR_FIELD_SUB THEN CONJ_TAC;
    MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL;
    CHANGED_TAC(REWRITE_TAC[ETA_AX]);
    MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RFA_SWAP23_PERMUTES4; RFA_SIGB_PERMUTES; RFA_SIGC_PERMUTES;
                RFA_SIGD_PERMUTES]]) THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]);;

(* In dimension 3, Rm = h(Ric).                                              *)

let RFA_LRM4_H3 = prove
 (`!U (G:real^3->real^3^3) y u.
     metric_field U G /\ y IN U ==> lrm4 G y u = rfa_h3 G (lric2 G) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INV_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `U:real^3->bool`; `G:real^3->real^3^3`; `lrm4 (G:real^3->real^3^3)`;
                 `y:real^3`; `S:real^3^3`; `u:num->real^3`] RFA_FRAME_EXPAND) THEN
  MP_TAC(ISPECL [`4`; `U:real^3->bool`; `G:real^3->real^3^3`;
                 `rfa_h3 (G:real^3->real^3^3) (lric2 G)`;
                 `y:real^3`; `S:real^3^3`; `u:num->real^3`] RFA_FRAME_EXPAND) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD; RFA_H3_FIELD; LRG_LRIC2_FIELD] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN
  REWRITE_TAC[index_tuples; IN_ELIM_THM; DIMINDEX_3] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN
  ABBREV_TAC `X = \a b c d. lrm4 (G:real^3->real^3^3) y
                  (\m. if m = 1 then transp (S:real^3^3) ** basis a else if m = 2 then transp (S:real^3^3) ** basis b
                       else if m = 3 then transp (S:real^3^3) ** basis c else transp (S:real^3^3) ** basis d)` THEN
  SUBGOAL_THEN
   `!a c. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis a) (transp (S:real^3^3) ** basis c) =
          sum(1..3) (\s. (X:num->num->num->num->real) s a s c)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `transp (S:real^3^3) ** basis a:real^3`; `transp (S:real^3^3) ** basis c:real^3`]
           RFA_RIC_FRAME_RM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ltcontr (G:real^3->real^3^3) (lric2 G) y w =
        sum(1..3) (\i. sum(1..3) (\s. (X:num->num->num->num->real) s i s i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ltcontr; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`;
                   `lricci (G:real^3->real^3^3) y`] RFA_TRACE_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
             LRG_LRICCI_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
          ==> (transp (S:real^3^3) ** basis a) dot ((G:real^3->real^3^3) y ** (transp (S:real^3^3) ** basis b)) =
              if a = b then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  MP_TAC(SPEC `X:num->num->num->num->real` RFA_H3_ALG) THEN ANTS_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[lrm4] THEN BETA_TAC THEN REWRITE_TAC[ARITH] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_MP_TAC LRG_RM_ANTI1; MATCH_MP_TAC LRG_RM_ANTISYM;
      MATCH_MP_TAC LRIEMANN_PAIR_SYM] THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(i:num->num) 1`; `(i:num->num) 2`; `(i:num->num) 3`;
                             `(i:num->num) 4`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lrm4 (G:real^3->real^3^3) y (\m. transp (S:real^3^3) ** basis((i:num->num) m)) =
    (X:num->num->num->num->real) (i 1) (i 2) (i 3) (i 4)`
  SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`4`; `U:real^3->bool`] THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN RFA_HT_SLOTS_TAC 4;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_h3; lric2; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH] THEN REAL_ARITH_TAC);;

(* The heat defect of Rm in dimension 3: h(2 Rm.Ric).                       *)

let RFA_HEAT_RM3 = prove
 (`!U a b (G:real->real^3->real^3^3).
     lricci_flow U a b G
     ==> rfa_heat 4 U a b G (\t. lrm4 (G t)) (\t. rfa_h3 (G t) (rfa_hric (G t)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `\t. lric2 ((G:real->real^3->real^3^3) t)`;
                 `\t. rfa_hric ((G:real->real^3->real^3^3) t)`] RFA_HEAT_H3) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t. rfa_h3 ((G:real->real^3->real^3^3) t) (lric2 (G t))` THEN
  EXISTS_TAC `\t. rfa_h3 ((G:real->real^3->real^3^3) t) (rfa_hric (G t))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_LRM4_H3 THEN EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* In dimension 3, 2 Rm.Ric = 3 R Ric - 4 Ric^2 + (2|Ric|^2 - R^2) g         *)
(* (from RFA_RMRIC_3D), written with the tensor-algebra generators, and its   *)
(* heat defect.                                                              *)
(* ========================================================================= *)

let rfa_nric2 = new_definition
 `rfa_nric2 (G:real^N->real^N^N) =
    ltcontr G (ltcontr G (ltperm (swap(2,3)) (ltprod 2 (lric2 G) (lric2 G))))`;;

let rfa_hric3 = new_definition
 `rfa_hric3 (G:real^N->real^N^N) y (u:num->real^N) =
    &3 * ltprod 0 (rfa_sc G) (lric2 G) y u - &4 * rfa_ric2sq G y u +
    (&2 * ltprod 0 (rfa_nric2 G) (lmetric2 G) y u -
     ltprod 0 (ltprod 0 (rfa_sc G) (rfa_sc G)) (lmetric2 G) y u)`;;

(* The defects: of R, of |Ric|^2 and of rfa_hric3.                           *)

let rfa_hsc = new_definition
 `rfa_hsc (G:real^N->real^N^N) = ltcontr G (rfa_hric G)`;;

let rfa_hnric2 = new_definition
 `rfa_hnric2 (G:real^N->real^N^N) =
    ltcontr G (ltcontr G (ltperm (swap(2,3))
      (\y u. ltprod 2 (rfa_hric G) (lric2 G) y u + ltprod 2 (lric2 G) (rfa_hric G) y u -
             &2 * rfa_xgrad 2 2 G (lric2 G) (lric2 G) y u)))`;;

let rfa_hhric3 = new_definition
 `rfa_hhric3 (G:real^N->real^N^N) y (u:num->real^N) =
    &3 * (ltprod 0 (rfa_hsc G) (lric2 G) y u + ltprod 0 (rfa_sc G) (rfa_hric G) y u -
          &2 * rfa_xgrad 0 2 G (rfa_sc G) (lric2 G) y u) -
    &4 * rfa_hric2sq G y u +
    (&2 * ltprod 0 (rfa_hnric2 G) (lmetric2 G) y u -
     ltprod 0 (\y u. ltprod 0 (rfa_hsc G) (rfa_sc G) y u + ltprod 0 (rfa_sc G) (rfa_hsc G) y u -
                     &2 * rfa_xgrad 0 0 G (rfa_sc G) (rfa_sc G) y u)
       (lmetric2 G) y u)`;;

let RFA_HEAT_NRIC2 = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 0 U a b G (\t. rfa_nric2 (G t)) (\t. rfa_hnric2 (G t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `2`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LTPROD) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `swap(2,3)`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltprod 2 (lric2 ((G:real->real^N->real^N^N) t)) (lric2 (G t))`;
                 `\t y u. ltprod 2 (rfa_hric ((G:real->real^N->real^N^N) t)) (lric2 (G t)) y u +
                          ltprod 2 (lric2 (G t)) (rfa_hric (G t)) y u -
                          &2 * rfa_xgrad 2 2 (G t) (lric2 (G t)) (lric2 (G t)) y u`]
         RFA_HEAT_PERM) THEN
  ASM_REWRITE_TAC[RFA_SWAP23_PERMUTES4] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltperm (swap(2,3))
                        (ltprod 2 (lric2 ((G:real->real^N->real^N^N) t)) (lric2 (G t)))`;
                 `\t. ltperm (swap(2,3))
                        (\y u. ltprod 2 (rfa_hric ((G:real->real^N->real^N^N) t))
                                 (lric2 (G t)) y u +
                               ltprod 2 (lric2 (G t)) (rfa_hric (G t)) y u -
                               &2 * rfa_xgrad 2 2 (G t) (lric2 (G t)) (lric2 (G t)) y u)`]
         RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltcontr ((G:real->real^N->real^N^N) t) (ltperm (swap(2,3))
                        (ltprod 2 (lric2 (G t)) (lric2 (G t))))`;
                 `\t. ltcontr ((G:real->real^N->real^N^N) t) (ltperm (swap(2,3))
                        (\y u. ltprod 2 (rfa_hric (G t)) (lric2 (G t)) y u +
                               ltprod 2 (lric2 (G t)) (rfa_hric (G t)) y u -
                               &2 * rfa_xgrad 2 2 (G t) (lric2 (G t)) (lric2 (G t)) y u))`]
         RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfa_nric2; rfa_hnric2]);;

let RFA_HEAT_HRIC3 = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. rfa_hric3 (G t)) (\t. rfa_hhric3 (G t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `rfa_heat 0 U a b (G:real->real^N->real^N^N) (\t. rfa_sc (G t))
                  (\t. rfa_hsc (G t))` ASSUME_TAC THENL
   [REWRITE_TAC[rfa_hsc] THEN MATCH_MP_TAC RFA_HEAT_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* (i) R Ric *)
  MP_TAC(ISPECL [`0`; `2`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `\t. rfa_sc ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hsc ((G:real->real^N->real^N^N) t)`;
                 `\t. lric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hric ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LTPROD) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (* (iv) R R and its product with g *)
  MP_TAC(ISPECL [`0`; `0`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `\t. rfa_sc ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hsc ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_sc ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hsc ((G:real->real^N->real^N^N) t)`] RFA_HEAT_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. ltprod 0 (rfa_sc ((G:real->real^N->real^N^N) t)) (rfa_sc (G t))`;
                 `\t y u. ltprod 0 (rfa_hsc ((G:real->real^N->real^N^N) t)) (rfa_sc (G t)) y u +
                          ltprod 0 (rfa_sc (G t)) (rfa_hsc (G t)) y u -
                          &2 * rfa_xgrad 0 0 (G t) (rfa_sc (G t)) (rfa_sc (G t)) y u`]
         RFA_HEAT_TIMES_METRIC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (* (iii) |Ric|^2 g *)
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. rfa_nric2 ((G:real->real^N->real^N^N) t)`;
                 `\t. rfa_hnric2 ((G:real->real^N->real^N^N) t)`]
         RFA_HEAT_TIMES_METRIC) THEN
  ASM_SIMP_TAC[RFA_HEAT_NRIC2] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (* (ii) Ric^2 *)
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_RIC2SQ) THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC
   `\t (y:real^N) (u:num->real^N).
      &1 * (&3 * ltprod 0 (rfa_sc ((G:real->real^N->real^N^N) t)) (lric2 (G t)) y u +
            -- &4 * rfa_ric2sq (G t) y u) +
      &1 * (&2 * ltprod 0 (rfa_nric2 (G t)) (lmetric2 (G t)) y u +
            -- &1 * ltprod 0 (ltprod 0 (rfa_sc (G t)) (rfa_sc (G t))) (lmetric2 (G t)) y u)` THEN
  EXISTS_TAC
   `\t (y:real^N) (u:num->real^N).
      &1 * (&3 * (ltprod 0 (rfa_hsc ((G:real->real^N->real^N^N) t)) (lric2 (G t)) y u +
                  ltprod 0 (rfa_sc (G t)) (rfa_hric (G t)) y u -
                  &2 * rfa_xgrad 0 2 (G t) (rfa_sc (G t)) (lric2 (G t)) y u) +
            -- &4 * rfa_hric2sq (G t) y u) +
      &1 * (&2 * ltprod 0 (rfa_hnric2 (G t)) (lmetric2 (G t)) y u +
            -- &1 * ltprod 0 (\y u. ltprod 0 (rfa_hsc (G t)) (rfa_sc (G t)) y u +
                                   ltprod 0 (rfa_sc (G t)) (rfa_hsc (G t)) y u -
                                   &2 * rfa_xgrad 0 0 (G t) (rfa_sc (G t)) (rfa_sc (G t)) y u)
                    (lmetric2 (G t)) y u)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC RFA_HEAT_LINCOMB THEN ASM_REWRITE_TAC[ETA_AX]; CONJ_TAC]);
    REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hric3; rfa_hhric3] THEN REAL_ARITH_TAC]);;

let RFA_SUM4_CABD = prove
 (`!n (f:num->num->num->num->real).
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d. f a b c d)))) =
     sum(1..n) (\c. sum(1..n) (\a. sum(1..n) (\d. sum(1..n) (\b. f a b c d))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
  BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

let RFA_NRIC2_LTNORM2 = prove
 (`!(G:real^N->real^N^N) y u. rfa_nric2 G y u = ltnorm2 2 G (lric2 G) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfa_nric2; ltcontr; ltperm; ltprod; swap; ltnorm2;
              LRG_SUM_INDEX_TUPLES_2; PRODUCT_2; lric2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [RFA_SUM4_CABD] THEN
  RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
  RFA_SUM_EQ_TAC `r:num` THEN RFA_SUM_EQ_TAC `s:num` THEN REAL_ARITH_TAC);;

(* In dimension 3: rfa_hric = rfa_hric3.                                     *)

let RFA_HRIC_3D = prove
 (`!U (G:real^3->real^3^3) y u.
     metric_field U G /\ y IN U ==> rfa_hric G y u = rfa_hric3 G y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hric] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `(u:num->real^3) 1`; `(u:num->real^3) 2`] RFA_RMRIC_3D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_hric3; RFA_NRIC2_LTNORM2] THEN
  REWRITE_TAC[ltprod; RFA_NRIC2_LTNORM2] THEN
  REWRITE_TAC[rfa_sc; lric2; lmetric2; rfa_ric2sq; ltcontr; ltperm; ltprod] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  ABBREV_TAC `QQ = sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
                     matrix_inv((G:real^3->real^3^3) y)$p$q *
                     lricci G y ((u:num->real^3) 1) (basis p) * lricci G y (basis q) (u 2)))` THEN
  REAL_ARITH_TAC);;

let RFA_HEAT_HRIC_3D = prove
 (`!U a b (G:real->real^3->real^3^3).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. rfa_hric (G t)) (\t. rfa_hhric3 (G t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_HRIC3) THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC `\t. rfa_hric3 ((G:real->real^3->real^3^3) t)` THEN
  EXISTS_TAC `\t. rfa_hhric3 ((G:real->real^3->real^3^3) t)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_HRIC_3D THEN EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* M with time origin s and its heat defect (dimension 3).                   *)
(* ========================================================================= *)

let rfa_hhM = new_definition
 `rfa_hhM s t (G:real^N->real^N^N) y (u:num->real^N) =
    sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
      matrix_inv(G y)$p$q *
      rfa_hddr G y (\m. if m = 3 then basis p else if m = 4 then basis q else u m))) -
    inv(&2) * (lnabla 1 G (lnabla 0 G (ltcontr G (rfa_hric G))) y u +
               rfa_rmcomm 1 G (lnabla 0 G (rfa_sc G)) y u) +
    rfa_hhric3 G y u - rfa_hric2sq G y u +
    (--(inv(&2 * (t - s) pow 2)) * lric2 G y u + inv(&2 * (t - s)) * rfa_hric G y u)`;;

let RFA_ORIGIN_COEFF = prove
 (`!a b s. s <= a
           ==> (!t. a < t /\ t < b
                    ==> ((\t. inv(&2 * (t - s))) has_real_derivative
                         --(inv(&2 * (t - s) pow 2))) (atreal t)) /\
               smooth_map_on (interval(lift a,lift b)) (\x. lift(inv(&2 * (drop x - s))))`,
  REPEAT STRIP_TAC THENL
   [REAL_DIFF_TAC THEN
    SUBGOAL_THEN `~(t - s = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b)) (\x:real^1. lift(&2 * (drop x - s)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interval(lift a,lift b)`; `&2`; `\x:real^1. lift(drop x - s)`]
           SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`interval(lift a,lift b)`; `\x:real^1. x`; `\x:real^1. lift s`]
           SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_INTERVAL; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `\x:real^1. lift(&2 * (drop x - s))`]
         SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let RFA_HEAT_HM3 = prove
 (`!U a b (G:real->real^3->real^3^3) s.
     lricci_flow U a b G /\ s <= a
     ==> rfa_heat 2 U a b G (\t. rfa_hM s t (G t)) (\t. rfa_hhM s t (G t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_LAPRIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_HESSSC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_HRIC_3D) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HEAT_RIC2SQ) THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `s:real`] RFA_ORIGIN_COEFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `\t. lric2 ((G:real->real^3->real^3^3) t)`;
                 `\t. rfa_hric ((G:real->real^3->real^3^3) t)`;
                 `\t. inv(&2 * (t - s))`; `\t. --(inv(&2 * (t - s) pow 2))`] RFA_HEAT_TMUL) THEN
  ASM_SIMP_TAC[RFA_HEAT_RIC; ETA_AX] THEN BETA_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  EXISTS_TAC
   `\t (y:real^3) (u:num->real^3).
      &1 * (&1 * (&1 * ltlap 2 ((G:real->real^3->real^3^3) t) (lric2 (G t)) y u +
                  --(inv(&2)) * lnabla 1 (G t) (lnabla 0 (G t) (rfa_sc (G t))) y u) +
            &1 * (&1 * rfa_hric (G t) y u + -- &1 * rfa_ric2sq (G t) y u)) +
      &1 * (inv(&2 * (t - s)) * lric2 (G t) y u)` THEN
  EXISTS_TAC
   `\t (y:real^3) (u:num->real^3).
      &1 * (&1 * (&1 * sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
                         matrix_inv((G:real->real^3->real^3^3) t y)$p$q *
                         rfa_hddr (G t) y (\m. if m = 3 then basis p else if m = 4 then basis q
                                               else u m))) +
                  --(inv(&2)) *
                  (lnabla 1 (G t) (lnabla 0 (G t) (ltcontr (G t) (rfa_hric (G t)))) y u +
                   rfa_rmcomm 1 (G t) (lnabla 0 (G t) (rfa_sc (G t))) y u)) +
            &1 * (&1 * rfa_hhric3 (G t) y u + -- &1 * rfa_hric2sq (G t) y u)) +
      &1 * (--(inv(&2 * (t - s) pow 2)) * lric2 (G t) y u +
            inv(&2 * (t - s)) * rfa_hric (G t) y u)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC RFA_HEAT_LINCOMB THEN ASM_REWRITE_TAC[ETA_AX]; CONJ_TAC]);
    REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hM; rfa_hhM] THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Static fields, and the heat rule for the Harnack-type                     *)
(* quadratic M(W,W) + 2 P(U,W) + R(U,U) of static fields U, W.              *)
(* ========================================================================= *)

let RFA_HEAT_STATIC = prove
 (`!k U a b (G:real->real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     lricci_flow U a b G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> rfa_heat k U a b G (\t. tf)
           (\t y u. rfa_rcact k (G t) tf y u - ltlap k (G t) tf y u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  REWRITE_TAC[rfa_heat] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `tf:real^N->(num->real^N)->real`] RFA_RCACT_FIELD) THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `tf:real^N->(num->real^N)->real`] RFA_LTLAP_FIELD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:num->real^N` THEN
    SUBGOAL_THEN `(\z:real^(1,N)finite_sum. lift((tf:real^N->(num->real^N)->real)
                     (sndcart z) u)) = (\y. lift(tf y u)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[];
      MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
                     `\z:real^(1,N)finite_sum. z`; `sndcart:real^(1,N)finite_sum->real^N`]
             SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[LINEAR_SNDCART; SMOOTH_MAP_ON_ID] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(x - y) + (y - x) = &0`; HAS_REAL_DERIVATIVE_CONST]]);;

(* The defect of a tensor product, as a constant (RFA_HEAT_LTPROD).          *)

let rfa_hprod = new_definition
 `rfa_hprod p q (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) HA B HB =
    \y u. ltprod p HA B y u + ltprod p A HB y u - &2 * rfa_xgrad p q G A B y u`;;

let RFA_HEAT_PROD = prove
 (`!p q U a b (G:real->real^N->real^N^N) A HA B HB.
     lricci_flow U a b G /\ rfa_heat p U a b G A HA /\ rfa_heat q U a b G B HB
     ==> rfa_heat (p + q) U a b G (\t. ltprod p (A t) (B t))
           (\t. rfa_hprod p q (G t) (A t) (HA t) (B t) (HB t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hprod] THEN
  MATCH_MP_TAC RFA_HEAT_LTPROD THEN ASM_REWRITE_TAC[]);;

(* The three parts of the quadratic and their defects.                       *)

let RFA_SIGP_PERMUTES = prove
 (`(\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 2 else if m = 5 then 4
        else m) permutes 1..6`,
  RFA_HT_PERM_TAC `\m. if m = 3 then 2 else if m = 5 then 3 else if m = 2 then 4
                       else if m = 4 then 5 else m`);;

let RFA_SIGR_PERMUTES = prove
 (`(\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 7 else if m = 5 then 2
        else if m = 6 then 4 else if m = 7 then 6 else m) permutes 1..8`,
  RFA_HT_PERM_TAC `\m. if m = 3 then 2 else if m = 5 then 3 else if m = 7 then 4
                       else if m = 2 then 5 else if m = 4 then 6 else if m = 6 then 7
                       else m`);;

let rfa_qform = new_definition
 `rfa_qform (G:real^N->real^N^N) (M:real^N->(num->real^N)->real) P R U W =
    \y u. ltcontr G (ltcontr G (ltperm (swap(2,3)) (ltprod 2 M (ltprod 1 W W)))) y u +
          &2 * ltcontr G (ltcontr G (ltcontr G
                 (ltperm (\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 2
                              else if m = 5 then 4 else m)
                         (ltprod 3 P (ltprod 2 U W))))) y u +
          ltcontr G (ltcontr G (ltcontr G (ltcontr G
            (ltperm (\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 7
                         else if m = 5 then 2 else if m = 6 then 4 else if m = 7 then 6
                         else m)
                    (ltprod 4 R (ltprod 2 U U)))))) y u`;;

let rfa_hqform = new_definition
 `rfa_hqform (G:real^N->real^N^N) (M:real^N->(num->real^N)->real) HM P HP R HR U HU W HW =
    \y u. ltcontr G (ltcontr G (ltperm (swap(2,3))
            (rfa_hprod 2 2 G M HM (ltprod 1 W W) (rfa_hprod 1 1 G W HW W HW)))) y u +
          &2 * ltcontr G (ltcontr G (ltcontr G
                 (ltperm (\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 2
                              else if m = 5 then 4 else m)
                    (rfa_hprod 3 3 G P HP (ltprod 2 U W) (rfa_hprod 2 1 G U HU W HW))))) y u +
          ltcontr G (ltcontr G (ltcontr G (ltcontr G
            (ltperm (\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 7
                         else if m = 5 then 2 else if m = 6 then 4 else if m = 7 then 6
                         else m)
               (rfa_hprod 4 4 G R HR (ltprod 2 U U) (rfa_hprod 2 2 G U HU U HU)))))) y u`;;

(* Forward versions of the heat rules (theorem -> theorem).                 *)

let rfa_heat_args th = snd(strip_comb(concl th));;

let RFA_HPROD_RULE flow th1 th2 =
  let p = hd(rfa_heat_args th1) and q = hd(rfa_heat_args th2) in
  CONV_RULE NUM_REDUCE_CONV
    (BETA_RULE (MATCH_MP (ISPECL [p; q] RFA_HEAT_PROD) (CONJ flow (CONJ th1 th2))));;

let RFA_HPERM_RULE flow s pth th =
  let k = hd(rfa_heat_args th) in
  BETA_RULE (MATCH_MP (ISPECL [k; s] RFA_HEAT_PERM) (CONJ flow (CONJ th pth)));;

let RFA_HCONTR_RULE flow th =
  let k = hd(rfa_heat_args th) in
  let k' = mk_small_numeral(dest_small_numeral k - 2) in
  BETA_RULE (MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPEC k' RFA_HEAT_LTCONTR))
                      (CONJ flow th));;

let RFA_HLIN_RULE flow c1 c2 th1 th2 =
  let th = SPEC_ALL RFA_HEAT_LINCOMB in
  let th' = INST [c1, `c1:real`; c2, `c2:real`] th in
  BETA_RULE (MATCH_MP th' (CONJ flow (CONJ th1 th2)));;

let RFA_HEAT_QUAD = prove
 (`!U a b (G:real->real^N->real^N^N) Mf HMf Pf HPf Rf HRf Uf HUf Wf HWf.
     lricci_flow U a b G /\ rfa_heat 2 U a b G Mf HMf /\ rfa_heat 3 U a b G Pf HPf /\
     rfa_heat 4 U a b G Rf HRf /\ rfa_heat 2 U a b G Uf HUf /\ rfa_heat 1 U a b G Wf HWf
     ==> rfa_heat 0 U a b G (\t. rfa_qform (G t) (Mf t) (Pf t) (Rf t) (Uf t) (Wf t))
           (\t. rfa_hqform (G t) (Mf t) (HMf t) (Pf t) (HPf t) (Rf t) (HRf t)
                           (Uf t) (HUf t) (Wf t) (HWf t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (fun g ->
    let flow = ASSUME `lricci_flow U a b (G:real->real^N->real^N^N)`
    and thM = ASSUME `rfa_heat 2 U a b (G:real->real^N->real^N^N) Mf HMf`
    and thP = ASSUME `rfa_heat 3 U a b (G:real->real^N->real^N^N) Pf HPf`
    and thR = ASSUME `rfa_heat 4 U a b (G:real->real^N->real^N^N) Rf HRf`
    and thU = ASSUME `rfa_heat 2 U a b (G:real->real^N->real^N^N) Uf HUf`
    and thW = ASSUME `rfa_heat 1 U a b (G:real->real^N->real^N^N) Wf HWf` in
    let thWW = RFA_HPROD_RULE flow thW thW in
    let thMWW = RFA_HPROD_RULE flow thM thWW in
    let thMp = RFA_HPERM_RULE flow `swap(2,3)` RFA_SWAP23_PERMUTES4 thMWW in
    let thMc = RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow thMp) in
    let thUW = RFA_HPROD_RULE flow thU thW in
    let thPUW = RFA_HPROD_RULE flow thP thUW in
    let thPp = RFA_HPERM_RULE flow
      `\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 2 else if m = 5 then 4
           else m` RFA_SIGP_PERMUTES thPUW in
    let thPc = RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow thPp)) in
    let thUU = RFA_HPROD_RULE flow thU thU in
    let thRUU = RFA_HPROD_RULE flow thR thUU in
    let thRp = RFA_HPERM_RULE flow
      `\m. if m = 2 then 3 else if m = 3 then 5 else if m = 4 then 7 else if m = 5 then 2
           else if m = 6 then 4 else if m = 7 then 6 else m` RFA_SIGR_PERMUTES thRUU in
    let thRc = RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow
                 (RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow thRp))) in
    let thMP = RFA_HLIN_RULE flow `&1` `&2` thMc thPc in
    let thAll = RFA_HLIN_RULE flow `&1` `&1` thMP thRc in
    let args = rfa_heat_args thAll in
    (MATCH_MP_TAC RFA_HEAT_CONG THEN MAP_EVERY EXISTS_TAC [el 5 args; el 6 args] THEN
     ASM_REWRITE_TAC[thAll]) g) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_qform; rfa_hqform] THEN REAL_ARITH_TAC);;

