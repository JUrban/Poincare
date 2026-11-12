(* ========================================================================= *)
(* Unit pc_rfa_htrace: Hamilton's trace Harnack inequality in dimension 3,   *)
(* the statement P2B_REQ_RFA_HARNACK_STATEMENT of pc_p2b_defs, proved as     *)
(* RFA_P2B_REQ_RFA_HARNACK.  On a complete flow on                           *)
(* (a,b] with sec >= 0 and bounded curvature: the frame bounds of rfa_hset   *)
(* follow from Shi's estimates (RFA_P2_THM_3_28) on each time slice, the     *)
(* positivity conditions from sec >= 0 (every bivector in dimension 3 is    *)
(* decomposable), the matrix Harnack RFA_HARNACK_MATRIX of pc_rfa_hmax holds *)
(* from s = a + eps, its trace over U = W wedge X gives                      *)
(*   dR/dt + R/(t - s) + 2 dR(X) + 2 Ric(X,X) >= 0,                          *)
(* and eps -> 0 gives the statement with t - a.                             *)
(* ========================================================================= *)

needs "src/pc_rfa_hmax.ml";;
needs "src/pc_rfa_shi328.ml";;
needs "src/pc_rfa_secmin.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Frame values are bounded by tensor norms (RFA_HT_FRAME_ABS),              *)
(* and the norms of Ric, nabla Ric, nabla^2 Ric are at most dimindex times   *)
(* those of Rm, nabla Rm, nabla^2 Rm (Ric is a contraction of Rm and nabla   *)
(* commutes with contractions and slot permutations).                       *)
(* ========================================================================= *)

let RFA_HT_GRAM = prove
 (`!(G:real^N->real^N^N) y (S:real^N^N).
     invertible S /\ matrix_inv(G y) = transp S ** S
     ==> G y = transp(matrix_inv(transp S)) ** matrix_inv(transp S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y = matrix_inv(transp (S:real^N^N) ** S)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_INV_TRANSP; TRANSP_TRANSP]);;

let RFA_HT_FRAME_ABS = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (S:real^N^N) l D.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\ invertible S /\
     matrix_inv(G y) = transp S ** S /\ ltnorm2 k G tf y <= D /\
     LENGTH l = k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> abs(tf y (rfa_ft S l)) <= sqrt D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `matrix_inv(transp(S:real^N^N))`; `rfa_ft (S:real^N^N) l`; `D:real`]
         LRG_FRAME_BOUND_DELTA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_HT_GRAM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..k) (\m. norm(matrix_inv(transp(S:real^N^N)) ** rfa_ft S l m)) = &1`
   (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
  MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ft] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_VECTOR_MUL_LID] THEN
  MATCH_MP_TAC NORM_BASIS THEN
  UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:N)) (l:num list)` THEN
  REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `m - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let RFA_HT_RIC_NORM = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ltnorm2 2 G (lric2 G) y <= &(dimindex(:N)) * lrm_deriv_norm2 0 G y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `ltnorm2 2 G (lric2 G) y =
    ltnorm2 2 G (ltcontr G (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N)))) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC RFA_LRIC2_CONTR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..4` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 4 U (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N)))` MP_TAC THENL
   [MATCH_MP_TAC RFA_SF_LTPERM THEN ASM_SIMP_TAC[RFA_SF_LRM4]; ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))`; `y:real^N`]
           RFA_LTNORM2_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`; `swap(2,3)`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN REAL_ARITH_TAC);;

let RFA_HT_SWAP23_PERMUTES = prove
 (`!k. 3 <= k ==> swap(2,3) permutes 1..k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

let RFA_HT_DRIC_EQON = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> rfa_eqon U (lnabla 2 G (lric2 G))
                    (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 4 U (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N)))` MP_TAC THENL
   [MATCH_MP_TAC RFA_SF_LTPERM THEN ASM_SIMP_TAC[RFA_SF_LRM4; RFA_HT_SWAP23_PERMUTES; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_EQON_TRANS THEN
  EXISTS_TAC `lnabla 2 G (ltcontr G (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_EQON_LNABLA THEN ASM_REWRITE_TAC[rfa_eqon] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LRIC2_CONTR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))`; `y:real^N`; `u:num->real^N`]
           RFA_LNABLA_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr] THEN
  MP_TAC(ISPECL [`4`; `swap(2,3)`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`]
         RFA_LNABLA_LTPERM) THEN
  ASM_SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH]);;

let RFA_HT_DDRIC_EQON = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> rfa_eqon U (lnabla 3 G (lnabla 2 G (lric2 G)))
                    (ltcontr G (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 G)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 5 U (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_SF_LTPERM THEN
    SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRM4; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_EQON_TRANS THEN
  EXISTS_TAC `lnabla 3 G (ltcontr G (ltperm (swap(2,3))
                (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_EQON_LNABLA THEN ASM_SIMP_TAC[RFA_HT_DRIC_EQON]; ALL_TAC] THEN
  REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`; `y:real^N`;
            `u:num->real^N`] RFA_LNABLA_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr] THEN
  MP_TAC(ISPECL [`5`; `swap(2,3)`; `G:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`] RFA_LNABLA_LTPERM) THEN
  ASM_SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH]);;

let RFA_HT_DRIC_NORM = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ltnorm2 3 G (lnabla 2 G (lric2 G)) y <= &(dimindex(:N)) * lrm_deriv_norm2 1 G y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lrm_deriv_norm2; num_CONV `1`; lnabla_iter; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `ltnorm2 3 G (lnabla 2 G (lric2 G)) y =
    ltnorm2 3 G (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_HT_DRIC_EQON) THEN
    ASM_SIMP_TAC[rfa_eqon];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 5 U (lnabla 4 G (lrm4 (G:real^N->real^N^N)))` MP_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRM4; ARITH];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `rfa_sf 5 U (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_SF_LTPERM THEN ASM_SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`; `y:real^N`]
           RFA_LTNORM2_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`5`; `swap(2,3)`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  UNDISCH_TAC `rfa_sf 5 U (lnabla 4 G (lrm4 (G:real^N->real^N^N)))` THEN
  ASM_SIMP_TAC[rfa_sf; RFA_HT_SWAP23_PERMUTES; ARITH] THEN REAL_ARITH_TAC);;

let RFA_HT_DDRIC_NORM = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ltnorm2 4 G (lnabla 3 G (lnabla 2 G (lric2 G))) y <=
         &(dimindex(:N)) * lrm_deriv_norm2 2 G y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lrm_deriv_norm2; num_CONV `2`; num_CONV `1`; lnabla_iter; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `ltnorm2 4 G (lnabla 3 G (lnabla 2 G (lric2 G))) y =
    ltnorm2 4 G (ltcontr G (ltperm (swap(2,3))
                  (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_HT_DDRIC_EQON) THEN
    ASM_SIMP_TAC[rfa_eqon];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 6 U (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))` MP_TAC THENL
   [MP_TAC(ISPECL [`5`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 4 G (lrm4 (G:real^N->real^N^N))`] RFA_SF_LNABLA) THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRM4; ARITH];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `rfa_sf 6 U (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_SF_LTPERM THEN ASM_SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`;
            `y:real^N`] RFA_LTNORM2_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`6`; `swap(2,3)`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`; `y:real^N`]
                RFA_LTNORM2_LTPERM) THEN
  UNDISCH_TAC `rfa_sf 6 U (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))` THEN
  ASM_SIMP_TAC[rfa_sf; RFA_HT_SWAP23_PERMUTES; ARITH] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The rfa_hframe package from norm bounds and sec >= 0                      *)
(* (RFA_HT_HFRAME): bounds of the 3D frame arrays of Rm, P and M, the        *)
(* decomposition of antisymmetric 3x3 arrays (RFA_HT_ANTI3_DECOMP), the      *)
(* curvature operator and the Ricci form are nonnegative in frames.         *)
(* ========================================================================= *)

let RFA_HT_KD_BOUNDS = prove
 (`!i j. &0 <= rfa_kd i j /\ rfa_kd i j <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_kd] THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let RFA_HT_ABS_MUL_LE = prove
 (`!x y c d. abs x <= c /\ abs y <= d ==> abs(x * y) <= c * d`,
  REWRITE_TAC[REAL_ABS_MUL] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let RFA_HT_SUM3_ABS = prove
 (`!f c. (!e. 1 <= e /\ e <= 3 ==> abs(f e) <= c) ==> abs(sum(1..3) f) <= &3 * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..3`; `f:num->real`; `c:real`] SUM_ABS_BOUND) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1]);;

let RFA_HT_ARR_R_BOUND = prove
 (`!(ric:num->num->real) c0 a b c d.
     &0 <= c0 /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> abs(ric i j) <= c0) /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\ 1 <= d /\ d <= 3
     ==> abs(rfa_arr_r ric a b c d) <= &7 * c0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_arr_r] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\e. (ric:num->num->real) e e)) <= &3 * c0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j k l. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
              ==> abs((ric:num->num->real) i j * rfa_kd k l) <= c0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `l:num`] RFA_HT_KD_BOUNDS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(inv(&2) * sum(1..3) (\e. (ric:num->num->real) e e) *
        (rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d)) <= &3 * c0`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d) <= &1` MP_TAC THENL
     [MP_TAC(SPECL [`a:num`; `d:num`] RFA_HT_KD_BOUNDS) THEN
      MP_TAC(SPECL [`b:num`; `c:num`] RFA_HT_KD_BOUNDS) THEN
      MP_TAC(SPECL [`a:num`; `c:num`] RFA_HT_KD_BOUNDS) THEN
      MP_TAC(SPECL [`b:num`; `d:num`] RFA_HT_KD_BOUNDS) THEN
      SPEC_TAC(`rfa_kd a d`,`p:real`) THEN SPEC_TAC(`rfa_kd b c`,`q:real`) THEN
      SPEC_TAC(`rfa_kd a c`,`r:real`) THEN SPEC_TAC(`rfa_kd b d`,`w:real`) THEN
      REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= p * q /\ p * q <= &1 /\ &0 <= r * w /\ r * w <= &1` MP_TAC THENL
       [REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPEC `rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d` REAL_ABS_POS) THEN
    MP_TAC(SPEC `sum(1..3) (\e. (ric:num->num->real) e e)` REAL_ABS_POS) THEN
    UNDISCH_TAC `abs(sum(1..3) (\e. (ric:num->num->real) e e)) <= &3 * c0` THEN
    SPEC_TAC(`abs(sum(1..3) (\e. (ric:num->num->real) e e))`,`r:real`) THEN
    SPEC_TAC(`abs(rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d)`,`k:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `r * k <= (&3 * c0) * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((ric:num->num->real) a d * rfa_kd b c) <= c0 /\
    abs((ric:num->num->real) b c * rfa_kd a d) <= c0 /\
    abs((ric:num->num->real) a c * rfa_kd b d) <= c0 /\
    abs((ric:num->num->real) b d * rfa_kd a c) <= c0`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN NO_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `abs(inv(&2) * sum(1..3) (\e. (ric:num->num->real) e e) *
        (rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d)) <= &3 * c0` THEN
  REAL_ARITH_TAC);;

let RFA_HT_ARR_P_BOUND = prove
 (`!(dr:num->num->num->real) c1 a b c.
     (!i j k. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= k /\ k <= 3
              ==> abs(dr i j k) <= c1) /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
     ==> abs(rfa_arr_p dr a b c) <= &2 * c1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_arr_p] THEN
  SUBGOAL_THEN `abs((dr:num->num->num->real) b c a) <= c1 /\ abs(dr a c b) <= c1` MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let RFA_HT_ARR_M_BOUND = prove
 (`!(ric:num->num->real) (ddr:num->num->num->num->real) tau c0 c2 a b.
     &0 <= c0 /\ &0 <= c2 /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> abs(ric i j) <= c0) /\
     (!i j k l. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= k /\ k <= 3 /\
                1 <= l /\ l <= 3 ==> abs(ddr i j k l) <= c2) /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
     ==> abs(rfa_arr_m ric ddr tau a b - inv(&2 * tau) * ric a b) <=
         &5 * c2 + &51 * c0 pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_arr_m; REAL_POW_2] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\e. (ric:num->num->real) e e)) <= &3 * c0` MP_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\e. (ddr:num->num->num->num->real) a b e e)) <= &3 * c2`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\e. (ddr:num->num->num->num->real) e e a b)) <= &3 * c2`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sum(1..3) (\e. (ric:num->num->real) a e * ric e b)) <= &3 * (c0 * c0)`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(sum(1..3) (\e. sum(1..3) (\f. (ric:num->num->real) e f * ric e f))) <=
    &3 * (&3 * (c0 * c0))`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_HT_SUM3_ABS THEN REPEAT STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC RFA_HT_SUM3_ABS THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = sum(1..3) (\e. (ric:num->num->real) e e)` THEN
  ABBREV_TAC `A1 = sum(1..3) (\e. (ddr:num->num->num->num->real) a b e e)` THEN
  ABBREV_TAC `A2 = sum(1..3) (\e. (ddr:num->num->num->num->real) e e a b)` THEN
  ABBREV_TAC `A3 = sum(1..3) (\e. (ric:num->num->real) a e * ric e b)` THEN
  ABBREV_TAC `A4 = sum(1..3) (\e. sum(1..3) (\f. (ric:num->num->real) e f * ric e f))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs((ric:num->num->real) a b) <= c0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match [] `!i j. P i j ==> abs((ric:num->num->real) i j) <= c0`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(R * (ric:num->num->real) a b) <= (&3 * c0) * c0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(R * R) <= (&3 * c0) * (&3 * c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&2 * A4 - R * R) * rfa_kd a b) <= (&27 * (c0 * c0)) * &1` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HT_ABS_MUL_LE THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`a:num`; `b:num`] RFA_HT_KD_BOUNDS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_HT_SEC_NONNEG = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> !A B. &0 <= A dot (G y ** lriemann G y A B B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`A:real^N`; `B:real^N`] THEN
  ASM_CASES_TAC `collinear {vec 0,A:real^N,B}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_LEMMA]) THEN
    SUBGOAL_THEN `!c. lriemann (G:real^N->real^N^N) y A (c % A) (c % A) = vec 0` ASSUME_TAC THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`\v. lriemann (G:real^N->real^N^N) y A v (c % A)`; `c:real`; `A:real^N`]
             LINEAR_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`;
                     `c % A:real^N`] RFA_LRIEMANN_SELF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A:real^N`; `B:real^N`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "lsectional"
                                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`; `B:real^N`]
         APX_SECT_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO]);;

let RFA_HT_ANTI3_DECOMP = prove
 (`!u:num->num->real.
     (!i j. u i j = --(u j i))
     ==> ?p q:num->real. !a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
                               ==> u a b = p a * q b - p b * q a`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:num->num->real) 1 1 = &0 /\ u 2 2 = &0 /\ u 3 3 = &0 /\
                u 2 1 = --(u 1 2) /\ u 3 1 = --(u 1 3) /\ u 3 2 = --(u 2 3)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`1`; `1`] th) THEN
      MP_TAC(SPECL [`2`; `2`] th) THEN MP_TAC(SPECL [`3`; `3`] th) THEN
      MP_TAC(SPECL [`2`; `1`] th) THEN MP_TAC(SPECL [`3`; `1`] th) THEN
      MP_TAC(SPECL [`3`; `2`] th)) THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th)))] THEN
  SUBGOAL_THEN `!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 <=>
                      (a = 1 \/ a = 2 \/ a = 3) /\ (b = 1 \/ b = 2 \/ b = 3)`
  (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(u:num->num->real) 1 3 pow 2 + u 2 3 pow 2 = &0` THENL
   [SUBGOAL_THEN `(u:num->num->real) 1 3 = &0 /\ u 2 3 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(u:num->num->real) 1 3 pow 2 + u 2 3 pow 2 = &0` THEN
      REWRITE_TAC[REAL_SOS_EQ_0];
      ALL_TAC] THEN
    EXISTS_TAC `\a:num. if a = 1 then &1 else &0` THEN
    EXISTS_TAC `\b:num. if b = 2 then (u:num->num->real) 1 2 else &0` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = (u:num->num->real) 1 3 pow 2 + u 2 3 pow 2` THEN
  EXISTS_TAC `\a:num. if a = 1 then (u:num->num->real) 1 3 else if a = 2 then u 2 3
                      else &0` THEN
  EXISTS_TAC `\b:num. if b = 1 then --((u:num->num->real) 2 3 * u 1 2 / n)
                      else if b = 2 then u 1 3 * u 1 2 / n else &1` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `~(n = &0)` THEN EXPAND_TAC "n" THEN CONV_TAC REAL_FIELD);;

let RFA_HT_MULTI4_EXPAND = prove
 (`!(Fm:real^N->real^N->real^N->real^N->real) (e:num->real^N) al be ga de n.
     (!x2 x3 x4. linear (\x. lift(Fm x x2 x3 x4))) /\
     (!x1 x3 x4. linear (\x. lift(Fm x1 x x3 x4))) /\
     (!x1 x2 x4. linear (\x. lift(Fm x1 x2 x x4))) /\
     (!x1 x2 x3. linear (\x. lift(Fm x1 x2 x3 x)))
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           Fm (e a) (e b) (e d) (e c) * (al a * be b * ga d * de c))))) =
         Fm (vsum(1..n) (\a. al a % e a)) (vsum(1..n) (\a. be a % e a))
           (vsum(1..n) (\a. ga a % e a)) (vsum(1..n) (\a. de a % e a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = vsum(1..n) (\a. al a % (e:num->real^N) a)` THEN
  ABBREV_TAC `B = vsum(1..n) (\a. be a % (e:num->real^N) a)` THEN
  ABBREV_TAC `C = vsum(1..n) (\a. ga a % (e:num->real^N) a)` THEN
  ABBREV_TAC `D = vsum(1..n) (\a. de a % (e:num->real^N) a)` THEN
  SUBGOAL_THEN
   `!x1 x2 x3. (Fm:real^N->real^N->real^N->real^N->real) x1 x2 x3 D =
               sum(1..n) (\c. de c * Fm x1 x2 x3 (e c))` (LABEL_TAC "s4") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`\x. (Fm:real^N->real^N->real^N->real^N->real) x1 x2 x3 x`; `1..n`;
                   `de:num->real`; `e:num->real^N`] RFA_LINEAR_SUM_EXPAND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x1 x2 x4. (Fm:real^N->real^N->real^N->real^N->real) x1 x2 C x4 =
               sum(1..n) (\d. ga d * Fm x1 x2 (e d) x4)` (LABEL_TAC "s3") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "C" THEN
    MP_TAC(ISPECL [`\x. (Fm:real^N->real^N->real^N->real^N->real) x1 x2 x x4`; `1..n`;
                   `ga:num->real`; `e:num->real^N`] RFA_LINEAR_SUM_EXPAND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x1 x3 x4. (Fm:real^N->real^N->real^N->real^N->real) x1 B x3 x4 =
               sum(1..n) (\b. be b * Fm x1 (e b) x3 x4)` (LABEL_TAC "s2") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`\x. (Fm:real^N->real^N->real^N->real^N->real) x1 x x3 x4`; `1..n`;
                   `be:num->real`; `e:num->real^N`] RFA_LINEAR_SUM_EXPAND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x2 x3 x4. (Fm:real^N->real^N->real^N->real^N->real) A x2 x3 x4 =
               sum(1..n) (\a. al a * Fm (e a) x2 x3 x4)` (LABEL_TAC "s1") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "A" THEN
    MP_TAC(ISPECL [`\x. (Fm:real^N->real^N->real^N->real^N->real) x x2 x3 x4`; `1..n`;
                   `al:num->real`; `e:num->real^N`] RFA_LINEAR_SUM_EXPAND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s4" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s3" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

let RFA_HT_QUAD4_WEDGE = prove
 (`!(Fm:real^N->real^N->real^N->real^N->real) (e:num->real^N) p q n.
     (!x2 x3 x4. linear (\x. lift(Fm x x2 x3 x4))) /\
     (!x1 x3 x4. linear (\x. lift(Fm x1 x x3 x4))) /\
     (!x1 x2 x4. linear (\x. lift(Fm x1 x2 x x4))) /\
     (!x1 x2 x3. linear (\x. lift(Fm x1 x2 x3 x))) /\
     (!x1 x2 x3 x4. Fm x2 x1 x3 x4 = --(Fm x1 x2 x3 x4)) /\
     (!x1 x2 x3 x4. Fm x1 x2 x4 x3 = --(Fm x1 x2 x3 x4))
     ==> sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           Fm (e a) (e b) (e d) (e c) * (p a * q b - p b * q a) *
           (p d * q c - p c * q d))))) =
         &4 * Fm (vsum(1..n) (\a. p a % e a)) (vsum(1..n) (\a. q a % e a))
                (vsum(1..n) (\a. p a % e a)) (vsum(1..n) (\a. q a % e a))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    let lin = end_itlist CONJ (butlast(butlast ths)) in
    let a12 = el 4 ths and a34 = el 5 ths in
    REWRITE_TAC[REAL_ARITH
     `x * (pa * qb - pb * qa) * (pd * qc - pc * qd) =
      ((x * (pa * qb * pd * qc) - x * (pa * qb * qd * pc)) - x * (qa * pb * pd * qc)) +
      x * (qa * pb * qd * pc)`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
    REWRITE_TAC[MATCH_MP RFA_HT_MULTI4_EXPAND lin] THEN
    ABBREV_TAC `P = vsum(1..n) (\a. p a % (e:num->real^N) a)` THEN
    ABBREV_TAC `Q = vsum(1..n) (\a. q a % (e:num->real^N) a)` THEN
    MP_TAC(SPECL [`P:real^N`; `Q:real^N`; `P:real^N`; `Q:real^N`] a12) THEN
    MP_TAC(SPECL [`P:real^N`; `Q:real^N`; `Q:real^N`; `P:real^N`] a12) THEN
    MP_TAC(SPECL [`P:real^N`; `Q:real^N`; `P:real^N`; `Q:real^N`] a34) THEN
    REAL_ARITH_TAC));;

let RFA_HT_FT4 = prove
 (`!(G:real^N->real^N^N) y (S:real^N^N) a b c d.
     lrm4 G y (rfa_ft S [a; b; c; d]) =
     lrm4 G y (\m. if m = 1 then transp S ** basis a else if m = 2 then transp S ** basis b
                   else if m = 3 then transp S ** basis c else transp S ** basis d)`,
  REWRITE_TAC[lrm4; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_HT_FRAME_RM_NONNEG = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> !u. (!i j. u i j = --(u j i))
             ==> &0 <= sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                         lrm4 G y (rfa_ft S [a; b; d; c]) * u a b * u d c))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->num->real` THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` (X_CHOOSE_TAC `q:num->real`) o
             MATCH_MP RFA_HT_ANTI3_DECOMP) THEN
  SUBGOAL_THEN
   `sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
      lrm4 (G:real^3->real^3^3) y (rfa_ft S [a; b; d; c]) * u a b * u d c)))) =
    sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
      (\x1 x2 x3 x4. lrm4 G y (\m. if m = 1 then x1 else if m = 2 then x2
                                  else if m = 3 then x3 else x4))
        ((\i. transp S ** basis i) a) ((\i. transp S ** basis i) b)
        ((\i. transp S ** basis i) d) ((\i. transp S ** basis i) c) *
      (p a * q b - p b * q a) * (p d * q c - p c * q d)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[RFA_HT_FT4];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x1 x2 x3 x4. lrm4 (G:real^3->real^3^3) y
                     (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else x4)`;
    `\i. transp (S:real^3^3) ** basis i`; `p:num->real`; `q:num->real`; `3`]
   RFA_HT_QUAD4_WEDGE) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRM4_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `x1:real^3`;
                     `x2:real^3`; `x4:real^3`] LRIEMANN_ANTISYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG];
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRIEMANN_ALGEBRAIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MATCH_ACCEPT_TAC (el 5 (CONJUNCTS th)))];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_HT_SEC_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let RFA_HT_FRAME_RIC_NONNEG = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> !w. &0 <= sum(1..3) (\a. sum(1..3) (\b. lric2 G y (rfa_ft S [a; b]) * w a * w b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:num->real` THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = vsum(1..3) (\a. w a % (transp (S:real^3^3) ** basis a))` THEN
  SUBGOAL_THEN `!z. lricci (G:real^3->real^3^3) y W z =
                    sum(1..3) (\a. w a * lricci G y (transp (S:real^3^3) ** basis a) z)`
  (LABEL_TAC "e1") THENL
   [GEN_TAC THEN EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`\x. lricci (G:real^3->real^3^3) y x z`; `1..3`; `w:num->real`;
                   `\a. transp (S:real^3^3) ** basis a`] RFA_LINEAR_SUM_EXPAND) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. lricci (G:real^3->real^3^3) y x W =
                    sum(1..3) (\b. w b * lricci G y x (transp (S:real^3^3) ** basis b))`
  (LABEL_TAC "e2") THENL
   [GEN_TAC THEN EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`\z. lricci (G:real^3->real^3^3) y x z`; `1..3`; `w:num->real`;
                   `\a. transp (S:real^3^3) ** basis a`] RFA_LINEAR_SUM_EXPAND) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\a. sum(1..3) (\b. lric2 (G:real^3->real^3^3) y (rfa_ft S [a; b]) * w a * w b)) =
    lricci G y W W`
  SUBST1_TAC THENL
   [USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[lric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `W:real^3`; `W:real^3`] RFA_RIC_FRAME_RM) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_HT_SEC_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let RFA_HT_HFRAME = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t D0 D1 D2.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     &0 <= D0 /\ &0 <= D1 /\ &0 <= D2 /\
     ltnorm2 2 G (lric2 G) y <= D0 /\ ltnorm2 3 G (lnabla 2 G (lric2 G)) y <= D1 /\
     ltnorm2 4 G (lnabla 3 G (lnabla 2 G (lric2 G))) y <= D2 /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> rfa_hframe G s t y S (&7 * sqrt D0) (&2 * sqrt D1)
                    (&5 * sqrt D2 + &51 * sqrt D0 pow 2) (sqrt D0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 2 U (lric2 (G:real^3->real^3^3)) /\
                ltensor_field 3 U (lnabla 2 G (lric2 G)) /\
                ltensor_field 4 U (lnabla 3 G (lnabla 2 G (lric2 G)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfa_sf 2 U (lric2 (G:real^3->real^3^3)) /\
                  rfa_sf 3 U (lnabla 2 G (lric2 G)) /\
                  rfa_sf 4 U (lnabla 3 G (lnabla 2 G (lric2 G)))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`; `lric2 (G:real^3->real^3^3)`]
             RFA_SF_LNABLA) THEN
      MP_TAC(ISPECL [`3`; `U:real^3->bool`; `G:real^3->real^3^3`;
                     `lnabla 2 G (lric2 (G:real^3->real^3^3))`] RFA_SF_LNABLA) THEN
      ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH];
      SIMP_TAC[rfa_sf]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
           ==> abs(rfa_ric_a (G:real^3->real^3^3) y S i j) <= sqrt D0) /\
    (!i j k. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= k /\ k <= 3
             ==> abs(rfa_dr_a G y S i j k) <= sqrt D1) /\
    (!i j k l. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= k /\ k <= 3 /\
               1 <= l /\ l <= 3 ==> abs(rfa_ddr_a G y S i j k l) <= sqrt D2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfa_ric_a; rfa_dr_a; rfa_ddr_a] THEN REPEAT CONJ_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_HT_FRAME_ABS THENL
     [MAP_EVERY EXISTS_TAC [`2`; `U:real^3->bool`; `G:real^3->real^3^3`];
      MAP_EVERY EXISTS_TAC [`3`; `U:real^3->bool`; `G:real^3->real^3^3`];
      MAP_EVERY EXISTS_TAC [`4`; `U:real^3->bool`; `G:real^3->real^3^3`]] THEN
    ASM_REWRITE_TAC[LENGTH; ALL; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt D0 /\ &0 <= sqrt D1 /\ &0 <= sqrt D2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[rfa_hframe] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`; `c:num`; `d:num`] RFA_LRM4_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RFA_HT_ARR_R_BOUND THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`; `c:num`] RFA_HP_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RFA_HT_ARR_P_BOUND THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `s:real`; `t:real`; `a:num`; `b:num`] RFA_HM_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `lric2 (G:real^3->real^3^3) y (rfa_ft S [a; b]) = rfa_ric_a G y S a b`
    SUBST1_TAC THENL [REWRITE_TAC[rfa_ric_a]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_HT_ARR_M_BOUND THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `lric2 (G:real^3->real^3^3) y (rfa_ft S [a; b]) = rfa_ric_a G y S a b`
    SUBST1_TAC THENL [REWRITE_TAC[rfa_ric_a]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "rfa_ric_a" with Failure _ -> false))
          (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_HT_FRAME_RM_NONNEG) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_HT_FRAME_RIC_NONNEG) THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The trace.  Summing the matrix Harnack inequality over the                *)
(* frame with U = e_i wedge X, W = e_i (RFA_HT_HZ_TRACE3, RFA_HT_ARR_TRACES) *)
(* and identifying the frame traces (scalar curvature, |Ric|^2, Lap R, dR,   *)
(* the contracted Bianchi identity) gives the chart form                     *)
(* RFA_HT_TRACE_CHART.                                                       *)
(* ========================================================================= *)

let RFA_HT_HZ_TRACE3 = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real) (X:num->real).
     sum(1..3) (\i. rfa_hz 3 R P M (\a b. rfa_kd i a * X b - X a * rfa_kd i b)
                                    (\a. rfa_kd i a)) =
     sum(1..3) (\i. M i i) +
     &2 * sum(1..3) (\b. X b * sum(1..3) (\i. P i b i - P b i i)) +
     sum(1..3) (\b. sum(1..3) (\c. X b * X c *
       sum(1..3) (\i. R i b c i - R i b i c - R b i c i + R b i i c)))`,
  REWRITE_TAC[rfa_hz; SUM_3; rfa_kd] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFA_HT_ARR_TRACES = prove
 (`!(ric:num->num->real) (dr:num->num->num->real) (ddr:num->num->num->num->real) tau.
     (!i j. ric i j = ric j i)
     ==> sum(1..3) (\i. rfa_arr_m ric ddr tau i i) =
         inv(&2) * sum(1..3) (\i. sum(1..3) (\e. ddr i i e e)) +
         sum(1..3) (\e. sum(1..3) (\f. ric e f pow 2)) +
         inv(&2 * tau) * sum(1..3) (\e. ric e e) /\
         (!b. sum(1..3) (\i. rfa_arr_p dr i b i - rfa_arr_p dr b i i) =
              &2 * sum(1..3) (\i. dr b i i) - &2 * sum(1..3) (\i. dr i i b)) /\
         (!b c. 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
                ==> sum(1..3) (\i. rfa_arr_r ric i b c i - rfa_arr_r ric i b i c -
                                   rfa_arr_r ric b i c i + rfa_arr_r ric b i i c) =
                    &4 * ric b c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (i,j) -> ASSUME_TAC(SPECL [i; j] th))
    [(`2`,`1`); (`3`,`1`); (`3`,`2`)]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfa_arr_m; SUM_3; rfa_kd] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[rfa_arr_p; SUM_3] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN RFA_INDEX_CASES_TAC [`b:num`; `c:num`] THEN
    REWRITE_TAC[rfa_arr_r; SUM_3; rfa_kd] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let RFA_HT_FT3_EVAL = prove
 (`!(S:real^N^N) a b c m.
     1 <= m /\ m <= 3
     ==> rfa_ft S [a; b; c] m =
         (if m = 1 then transp S ** basis a else if m = 2 then transp S ** basis b
          else transp S ** basis c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_HT_DSC_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) b.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\i. lnabla 2 G (lric2 G) y (rfa_ft S [i; i; b])) =
         drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfa_sf 2 U (lric2 (G:real^N->real^N^N)) /\ rfa_sf 3 U (lnabla 2 G (lric2 G))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`; `lnabla 2 G (lric2 (G:real^N->real^N^N))`;
            `y:real^N`; `S:real^N^N`; `\m:num. transp (S:real^N^N) ** basis b`]
           RFA_LTCONTR_FRAMEV)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. lnabla 2 G (lric2 G) y (rfa_ft (S:real^N^N) [i; i; b])) =
    sum(1..dimindex(:N)) (\s. lnabla 2 G (lric2 (G:real^N->real^N^N)) y
      (\m. if m = 1 then transp S ** basis s else if m = 2 then transp S ** basis s
           else transp S ** basis b))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[RFA_HT_FT3_EVAL] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
            `y:real^N`; `\m:num. transp (S:real^N^N) ** basis b`] RFA_LNABLA_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM RFA_SC_CONTR] THEN
  REWRITE_TAC[lnabla; rfa_sc] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; ETA_AX]);;

let RFA_HT_SLOT_LINEAR = prove
 (`!k U (tf:real^N->(num->real^N)->real) y j (u:num->real^N).
     ltensor_field k U tf /\ y IN U /\ 1 <= j /\ j <= k
     ==> linear (\v. lift(tf y (\m. if m = j then v else u m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `j:num`; `\v:real^N. \m. if m = j then v else (u:num->real^N) m`]
         RFA_TF_LINEAR_SLOT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[]);;

let RFA_HT_BIANCHI_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) b.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\i. lnabla 2 G (lric2 G) y (rfa_ft S [b; i; i])) =
         inv(&2) * drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH; rfa_sf];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `transp (S:real^N^N) ** basis b`] LRG_CONTRACTED_BIANCHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
    `\p q. lnabla 2 G (lric2 (G:real^N->real^N^N)) y
             (\m. if m = 1 then p else if m = 2 then transp (S:real^N^N) ** basis b else q)`]
    RFA_TRACE_FRAME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
     [MP_TAC(ISPECL [`3`; `U:real^N->bool`; `lnabla 2 G (lric2 (G:real^N->real^N^N))`;
                     `y:real^N`; `1`;
                     `\m. if m = 2 then transp (S:real^N^N) ** basis b else (z:real^N)`]
                    RFA_HT_SLOT_LINEAR);
      MP_TAC(ISPECL [`3`; `U:real^N->bool`; `lnabla 2 G (lric2 (G:real^N->real^N^N))`;
                     `y:real^N`; `3`;
                     `\m. if m = 1 then (x:real^N) else transp (S:real^N^N) ** basis b`]
                    RFA_HT_SLOT_LINEAR)] THEN
    ASM_REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`;
                 `b:num`; `s:num`; `s:num`] RFA_FT_DRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[RFA_HT_FT3_EVAL] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RFA_HT_FT4_EVAL = prove
 (`!(S:real^N^N) a b c d m.
     1 <= m /\ m <= 4
     ==> rfa_ft S [a; b; c; d] m =
         (if m = 1 then transp S ** basis a else if m = 2 then transp S ** basis b
          else if m = 3 then transp S ** basis c else transp S ** basis d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_HT_LIN4 = prove
 (`!U (tf:real^N->(num->real^N)->real) y a1 a2 a3 a4.
     ltensor_field 4 U tf /\ y IN U
     ==> linear (\v. lift(tf y (\m. if m = 1 then v else if m = 2 then a2
                                   else if m = 3 then a3 else a4))) /\
         linear (\v. lift(tf y (\m. if m = 1 then a1 else if m = 2 then v
                                   else if m = 3 then a3 else a4))) /\
         linear (\v. lift(tf y (\m. if m = 1 then a1 else if m = 2 then a2
                                   else if m = 3 then v else a4))) /\
         linear (\v. lift(tf y (\m. if m = 1 then a1 else if m = 2 then a2
                                   else if m = 3 then a3 else v)))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`; `1`;
       `\v:real^N. \m. if m = 1 then v else if m = 2 then a2 else if m = 3 then a3
                       else (a4:real^N)`] RFA_TF_LINEAR_SLOT);
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`; `2`;
       `\v:real^N. \m. if m = 1 then a1 else if m = 2 then v else if m = 3 then a3
                       else (a4:real^N)`] RFA_TF_LINEAR_SLOT);
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`; `3`;
       `\v:real^N. \m. if m = 1 then a1 else if m = 2 then a2 else if m = 3 then v
                       else (a4:real^N)`] RFA_TF_LINEAR_SLOT);
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`; `4`;
       `\v:real^N. \m. if m = 1 then a1 else if m = 2 then a2 else if m = 3 then a3
                       else (v:real^N)`] RFA_TF_LINEAR_SLOT)] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  (ANTS_TAC THENL
    [REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ARITH]) THEN
     ASM_REWRITE_TAC[ARITH] THEN ASM_MESON_TAC[];
     DISCH_THEN ACCEPT_TAC]));;

let RFA_HT_LAP_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N).
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\e.
           lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; i; e; e]))) =
         llap G (lscalar G) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 4 U (lnabla 3 G (lnabla 2 G (lric2 (G:real^N->real^N^N))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 2 G (lric2 (G:real^N->real^N^N))`] RFA_SF_LNABLA) THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH; rfa_sf];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_N3_TRACE12) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ABBREV_TAC `T4 = lnabla 3 G (lnabla 2 G (lric2 (G:real^N->real^N^N)))` THEN
  SUBGOAL_THEN
   `!z1 z2. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv((G:real^N->real^N^N) y)$p$q *
              T4 y (\m. if m = 1 then basis p else if m = 2 then basis q
                        else if m = 3 then z1 else z2))) =
            sum(1..dimindex(:N)) (\i.
              T4 y (\m. if m = 1 then transp (S:real^N^N) ** basis i
                        else if m = 2 then transp S ** basis i
                        else if m = 3 then z1 else z2))`
  (LABEL_TAC "inner") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
      `\p q. (T4:real^N->(num->real^N)->real) y
               (\m. if m = 1 then p else if m = 2 then q else if m = 3 then z1 else z2)`]
      RFA_TRACE_FRAME) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `T4:real^N->(num->real^N)->real`; `y:real^N`] RFA_HT_LIN4) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "inner" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
    `\x z. sum(1..dimindex(:N)) (\i. (T4:real^N->(num->real^N)->real) y
             (\m. if m = 1 then transp (S:real^N^N) ** basis i
                  else if m = 2 then transp S ** basis i else if m = 3 then z else x))`]
    RFA_TRACE_FRAME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC RFA_LINEAR_LIFT_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `T4:real^N->(num->real^N)->real`; `y:real^N`] RFA_HT_LIN4) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_HT_FT4_EVAL]);;

let RFA_HT_DSC_EXPAND = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) V.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> drop(frechet_derivative (\x. lift(lscalar G x)) (at y) V) =
         sum(1..dimindex(:N)) (\b. ((transp S ** basis b) dot (G y ** V)) *
               drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\x. lift(lscalar (G:real^N->real^N^N) x)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`; `V:real^N`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`\v. drop(frechet_derivative (\x. lift(lscalar (G:real^N->real^N^N) x)) (at y) v)`;
                 `1..dimindex(:N)`;
                 `\r. (transp (S:real^N^N) ** basis r) dot ((G:real^N->real^N^N) y ** V)`;
                 `\r. transp (S:real^N^N) ** basis r`] RFA_LINEAR_SUM_EXPAND) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; FINITE_NUMSEG] THEN ASM_REWRITE_TAC[]);;

let RFA_HT_RTRACE_SUM = prove
 (`!(ric:num->num->real) (X:num->real).
     (!i j. ric i j = ric j i)
     ==> sum(1..3) (\b. sum(1..3) (\c. X b * X c *
           sum(1..3) (\i. rfa_arr_r ric i b c i - rfa_arr_r ric i b i c -
                          rfa_arr_r ric b i c i + rfa_arr_r ric b i i c))) =
         sum(1..3) (\b. sum(1..3) (\c. X b * X c * (&4 * ric b c)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MP_TAC(SPECL [`ric:num->num->real`; `\(i:num) (j:num) (k:num). &0`;
                  `\(i:num) (j:num) (k:num) (l:num). &0`; `&1`] RFA_HT_ARR_TRACES) THEN
    ANTS_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  DISCH_THEN(LABEL_TAC "rt" o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  USE_THEN "rt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_HT_TRACE_CHART = prove
 (`!U (G:real^3->real^3^3) y s t V.
     metric_field U G /\ y IN U /\ s < t /\ rfa_hpsd_cc G s t (&0) (&0) y
     ==> &0 <= (llap G (lscalar G) y + &2 * ltnorm2 2 G (lric2 G) y) + lscalar G y / (t - s) +
               &2 * drop(frechet_derivative (\x. lift(lscalar G x)) (at y) V) +
               &2 * lricci G y V V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `&0`; `&0`] RFA_HPSD_CC_FR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `rfa_hpsd_cc (G:real^3->real^3^3) s t (&0) (&0) y` THEN REWRITE_TAC[th]) THEN
  REWRITE_TAC[rfa_hpsd_fr; rfa_hza; REAL_MUL_LZERO; REAL_ADD_RID; ETA_AX] THEN
  DISCH_THEN(LABEL_TAC "psd") THEN
  (* identifications in frame arrays *)
  SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y = sum(1..3) (\e. rfa_ric_a G y S e e)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_SCAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIMINDEX_3; rfa_ric_a; lric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y =
                sum(1..3) (\e. sum(1..3) (\f. rfa_ric_a G y S e f pow 2))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_RICNORM_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIMINDEX_3; rfa_ric_a; lric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `llap (G:real^3->real^3^3) (lscalar G) y =
                sum(1..3) (\i. sum(1..3) (\e. rfa_ddr_a G y S i i e e))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_HT_LAP_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[DIMINDEX_3; rfa_ddr_a];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. sum(1..3) (\i. rfa_dr_a (G:real^3->real^3^3) y S i i b) =
        drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b)) /\
        sum(1..3) (\i. rfa_dr_a G y S b i i) =
        inv(&2) * drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b))`
  (LABEL_TAC "dsc") THENL
   [GEN_TAC THEN REWRITE_TAC[rfa_dr_a; GSYM DIMINDEX_3] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HT_DSC_FRAME; MATCH_MP_TAC RFA_HT_BIANCHI_FRAME] THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(frechet_derivative (\x. lift(lscalar (G:real^3->real^3^3) x)) (at y) V) =
    sum(1..3) (\b. ((transp (S:real^3^3) ** basis b) dot (G y ** V)) *
                   drop(frechet_derivative (\x. lift(lscalar G x)) (at y) (transp S ** basis b)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_3] THEN MATCH_MP_TAC RFA_HT_DSC_EXPAND THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci (G:real^3->real^3^3) y V V =
    sum(1..3) (\a. sum(1..3) (\b. ((transp (S:real^3^3) ** basis a) dot (G y ** V)) *
                                 ((transp S ** basis b) dot (G y ** V)) *
                                 rfa_ric_a G y S a b))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `lricci (G:real^3->real^3^3) y`;
                   `V:real^3`; `V:real^3`] RFA_BILIN_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIMINDEX_3; rfa_ric_a; lric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH];
    ALL_TAC] THEN
  (* the summed instances of the matrix Harnack inequality *)
  SUBGOAL_THEN `!i j. rfa_ric_a (G:real^3->real^3^3) y S i j = rfa_ric_a G y S j i`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfa_ric_a] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_FT_RIC_SYM THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..3) (\i. rfa_hz 3 (rfa_arr_r (rfa_ric_a (G:real^3->real^3^3) y S))
            (rfa_arr_p (rfa_dr_a G y S)) (rfa_arr_m (rfa_ric_a G y S) (rfa_ddr_a G y S) (t - s))
            (\a b. rfa_kd i a * --(inv(&2) * ((transp (S:real^3^3) ** basis b) dot (G y ** V))) -
                   --(inv(&2) * ((transp S ** basis a) dot (G y ** V))) * rfa_kd i b)
            (\a. rfa_kd i a))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "psd" MATCH_MP_TAC THEN REPEAT GEN_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RFA_HT_HZ_TRACE3] THEN
  MP_TAC(ISPECL [`rfa_ric_a (G:real^3->real^3^3) y S`; `rfa_dr_a (G:real^3->real^3^3) y S`;
                 `rfa_ddr_a (G:real^3->real^3^3) y S`; `t - s`] RFA_HT_ARR_TRACES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (fun th -> REWRITE_TAC[CONJUNCT1 th])) THEN
  MP_TAC(ISPECL [`rfa_ric_a (G:real^3->real^3^3) y S`;
                 `\b. --(inv(&2) * ((transp (S:real^3^3) ** basis b) dot
                                    ((G:real^3->real^3^3) y ** V)))`] RFA_HT_RTRACE_SUM) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "dsc" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SUM_3; real_div; REAL_INV_MUL] THEN
  SUBGOAL_THEN `&0 < inv(t - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The setting on [s,T2] for s = a + eps: sec >= 0 in every                  *)
(* chart (RFA_HT_SEC_CHART), the Ricci bound from the Ricci norm             *)
(* (RFA_HT_RIC_BOUND), Shi's estimates on each time slice                    *)
(* (RFA_HT_SHI_SLICE), the norms in any chart (RFA_HT_NORMS_CHART), and the  *)
(* package rfa_hset with the Ricci bound of RFA_HARNACK_MATRIX               *)
(* (RFA_HT_HSET).                                                            *)
(* ========================================================================= *)

let RFA_HT_SEC_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> !u v. ~collinear {vec 0,u,v}
               ==> &0 <= lsectional (metric_local atlas c g) (SND c x) u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] RFA_SECSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `lsectional (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) (SND c x) u v`) THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `v':real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_HT_RIC_BOUND = prove
 (`!U (G:real^N->real^N^N) y v D.
     metric_field U G /\ y IN U /\ ltnorm2 2 G (lric2 G) y <= D
     ==> abs(lricci G y v v) <= sqrt D * (v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `matrix_inv(transp(S:real^N^N))`; `\m:num. (v:real^N)`; `D:real`]
         LRG_FRAME_BOUND_DELTA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN MATCH_MP_TAC RFA_HT_GRAM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lric2; PRODUCT_2] THEN
  SUBGOAL_THEN `norm(matrix_inv(transp(S:real^N^N)) ** v) * norm(matrix_inv(transp S) ** v) =
                v dot ((G:real^N->real^N^N) y ** v)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2; NORM_POW_2] THEN MATCH_MP_TAC LRG_DOT_INV_TRANSP THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    REWRITE_TAC[]]);;

let RFA_HT_SHI_SLICE = prove
 (`!top atlas (g:real->A->real^3^3) a b K s l.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < s /\
     (!t. a < t /\ t < b ==> mfd_complete (top,atlas) (g t)) /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K)
     ==> ?C. &0 <= C /\
             !t x. s <= t /\ t < b /\ x IN topspace top ==> rfa_rmd2 l atlas (g t) x <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:A)` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `max K (&1)`; `&1`; `s - a`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `max Cl (&0)` THEN REWRITE_TAC[REAL_ARITH `&0 <= max c (&0)`] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= max c (&0)`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^3^3) t)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rmd2] THEN
  USE_THEN "shi" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `a:real`; `t:real`; `g:real->A->real^3^3`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t':real`; `z:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&1)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) t) x (&1)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[]]);;

let RFA_HT_NORMS_CHART = prove
 (`!top atlas (g:A->real^3^3) c x C0 C1 C2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     x IN FST c /\ metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c g) /\
     rfa_rmd2 0 atlas g x <= C0 /\ rfa_rmd2 1 atlas g x <= C1 /\ rfa_rmd2 2 atlas g x <= C2
     ==> ltnorm2 2 (metric_local atlas c g) (lric2 (metric_local atlas c g)) (SND c x)
           <= &3 * C0 /\
         ltnorm2 3 (metric_local atlas c g)
           (lnabla 2 (metric_local atlas c g) (lric2 (metric_local atlas c g))) (SND c x)
           <= &3 * C1 /\
         ltnorm2 4 (metric_local atlas c g)
           (lnabla 3 (metric_local atlas c g)
             (lnabla 2 (metric_local atlas c g) (lric2 (metric_local atlas c g)))) (SND c x)
           <= &3 * C2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^3)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun l ->
    MP_TAC(ISPECL [l; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `c:(A->bool)#(A->real^3)`; `x:A`] RFA_RMD2_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) [`0`; `1`; `2`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                   `SND (c:(A->bool)#(A->real^3)) x`] RFA_HT_RIC_NORM);
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                   `SND (c:(A->bool)#(A->real^3)) x`] RFA_HT_DRIC_NORM);
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                   `SND (c:(A->bool)#(A->real^3)) x`] RFA_HT_DDRIC_NORM)] THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ASM_REAL_ARITH_TAC);;

let RFA_HT_HSET = prove
 (`!top atlas (g:real->A->real^3^3) a b K s T2.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\
     a < s /\ s < T2 /\ T2 < b /\
     (!t. a < t /\ t < b ==> mfd_complete (top,atlas) (g t)) /\
     (!t x u v. a < t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K)
     ==> ?KR KP KM0 K' Kric.
           rfa_hset (top,atlas) g a b s T2 KR KP KM0 K' /\
           (!t x v. s <= t /\ t <= T2 /\ x IN topspace top
                    ==> abs(mfd_ricci atlas (g t) x v v) <= Kric * (v dot (g t x ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (l, cv) ->
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                  `g:real->A->real^3^3`; `a:real`; `b:real`; `K:real`; `s:real`; l]
                 RFA_HT_SHI_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN cv STRIP_ASSUME_TAC)])
   [(`0`, `C0:real`); (`1`, `C1:real`); (`2`, `C2:real`)] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x c. s <= t /\ t <= T2 /\ x IN topspace top /\ c IN atlas /\ x IN FST c
            ==> metric_field (IMAGE (SND c) (FST c))
                             (metric_local atlas c ((g:real->A->real^3^3) t)) /\
                ltnorm2 2 (metric_local atlas c (g t)) (lric2 (metric_local atlas c (g t)))
                  (SND c x) <= &3 * C0 /\
                ltnorm2 3 (metric_local atlas c (g t))
                  (lnabla 2 (metric_local atlas c (g t)) (lric2 (metric_local atlas c (g t))))
                  (SND c x) <= &3 * C1 /\
                ltnorm2 4 (metric_local atlas c (g t))
                  (lnabla 3 (metric_local atlas c (g t))
                    (lnabla 2 (metric_local atlas c (g t)) (lric2 (metric_local atlas c (g t)))))
                  (SND c x) <= &3 * C2`
  (LABEL_TAC "nrm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                               (metric_local atlas c ((g:real->A->real^3^3) t))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`]
                    LRG_RICCI_FLOW_ON_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
      BETA_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_HT_NORMS_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 * C0) /\ &0 <= sqrt(&3 * C1) /\ &0 <= sqrt(&3 * C2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`&7 * sqrt(&3 * C0)`; `&2 * sqrt(&3 * C1)`;
    `&5 * sqrt(&3 * C2) + &51 * sqrt(&3 * C0) pow 2`; `sqrt(&3 * C0)`; `sqrt(&3 * C0)`] THEN
  SUBGOAL_THEN `&0 <= &7 * sqrt(&3 * C0) /\ &0 <= &2 * sqrt(&3 * C1) /\
                &0 <= &5 * sqrt(&3 * C2) + &51 * sqrt(&3 * C0) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[rfa_hset] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`; `S:real^3^3`] THEN
    STRIP_TAC THEN
    USE_THEN "nrm" (MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC RFA_HT_HFRAME THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_HT_SEC_CHART THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "nrm" (MP_TAC o SPECL [`t:real`; `x:A`;
                                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                               ((g:real->A->real^3^3) t)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`; `v:real^3`;
                 `&3 * C0`] RFA_HT_RIC_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_ricci] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The trace Harnack inequality on the manifold from s = a + eps             *)
(* (RFA_HT_TRACE_S: dR/dt is identified by LSCALAR_EVOLUTION and uniqueness *)
(* of derivatives), the limit eps -> 0 (RFA_HT_DIV_LIM, RFA_AFFINE_LIM), and *)
(* the headline RFA_P2B_REQ_RFA_HARNACK: the statement                       *)
(* P2B_REQ_RFA_HARNACK_STATEMENT of pc_p2b_defs at every type.               *)
(* ========================================================================= *)

let RFA_HT_TRACE_S = prove
 (`!top atlas (g:real->A->real^3^3) a b K s t x dR V.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < s /\ s < t /\ t < b /\
     (!t. a < t /\ t < b ==> mfd_complete (top,atlas) (g t)) /\
     (!t x u v. a < t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
     x IN topspace top /\
     ((\s. mfd_scalar atlas (g s) x) has_real_derivative dR) (atreal t)
     ==> &0 <= dR + mfd_scalar atlas (g t) x / (t - s) +
               &2 * drop(frechet_derivative
                          (\y. lift(lscalar (metric_local atlas (chart_at atlas x) (g t)) y))
                          (at (SND(chart_at atlas x) x)) V) +
               &2 * mfd_ricci atlas (g t) x V V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `K:real`; `s:real`; `(t + b) / &2`] RFA_HT_HSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `KR:real` (X_CHOOSE_THEN `KP:real` (X_CHOOSE_THEN `KM0:real`
    (X_CHOOSE_THEN `K':real` (X_CHOOSE_THEN `Kric:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  SUBGOAL_THEN `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)) a b
                  (\t. metric_local atlas c ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (metric_local atlas c ((g:real->A->real^3^3) t)) /\
                SND c x IN IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC) THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the matrix Harnack inequality at (t,x) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `(t + b) / &2`; `KR:real`; `KP:real`;
                 `KM0:real`; `K':real`; `Kric:real`] RFA_HARNACK_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `s:real`; `t:real`; `V:real^3`]
                RFA_HT_TRACE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the time derivative of the scalar curvature *)
  SUBGOAL_THEN
   `dR = llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))
              (lscalar (metric_local atlas c (g t))) (SND c x) +
         &2 * ltnorm2 2 (metric_local atlas c (g t)) (lric2 (metric_local atlas c (g t)))
                (SND c x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. mfd_scalar atlas ((g:real->A->real^3^3) s) (x:A)` THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`;
                   `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                   `t:real`; `SND (c:(A->bool)#(A->real^3)) x`] LSCALAR_EVOLUTION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[mfd_scalar];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_scalar; mfd_ricci]);;

let RFA_HT_DIV_LIM = prove
 (`!R u e. &0 < u /\ &0 < e /\ &2 * e < u
           ==> R / (u - e) <= R / u + e * (&2 * abs R / u pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < u - e /\ &0 < u * (u - &2 * e)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `R / (u - e) - R / u = (R * e) * inv(u * (u - e))` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN UNDISCH_TAC `&0 < u - e` THEN UNDISCH_TAC `&0 < u` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(u * (u - e)) <= inv(u pow 2 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x - a <= y ==> x <= a + y`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(R * e) * inv(u * (u - e))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(R * e) * inv(u pow 2 / &2)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  SUBGOAL_THEN `abs e = e` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_HT_ZERO_TERMS = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> drop(frechet_derivative (\z. lift(lscalar G z)) (at y) (vec 0)) = &0 /\
         lricci G y (vec 0) (vec 0) = &0`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `linear(frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z)) (at y))`
    MP_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field];
      DISCH_THEN(SUBST1_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[DROP_VEC]];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0 o SPEC `vec 0:real^N` o CONJUNCT1) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]]);;

let RFA_P2B_REQ_RFA_HARNACK = prove
 (`!w:A->bool. P2B_REQ_RFA_HARNACK_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_RFA_HARNACK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:real->A->real^3^3`; `a:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `K:real`)))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `dR:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    SIMP_TAC[rfs_flow_upto];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X. &0 <= dR + mfd_scalar atlas ((g:real->A->real^3^3) t) x / (t - a) +
             &2 * drop(frechet_derivative
                    (\y. lift(lscalar (metric_local atlas (chart_at atlas x) (g t)) y))
                    (at (SND(chart_at atlas x) x)) X) +
             &2 * mfd_ricci atlas (g t) x X X`
  ASSUME_TAC THENL
   [X_GEN_TAC `X:real^3` THEN MATCH_MP_TAC RFA_AFFINE_LIM THEN
    EXISTS_TAC `&2 * abs(mfd_scalar atlas ((g:real->A->real^3^3) t) (x:A)) / (t - a) pow 2` THEN
    EXISTS_TAC `(t - a) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `K:real`; `a + e`; `t:real`;
                   `x:A`; `dR:real`; `X:real^3`] RFA_HT_TRACE_S) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`mfd_scalar atlas ((g:real->A->real^3^3) t) (x:A)`; `t - a`; `e:real`]
                  RFA_HT_DIV_LIM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `t - (a + e) = (t - a) - e`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) ((g:real->A->real^3^3) t)) /\
    SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^3^3`;
                     `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`]
                    LRG_RICCI_FLOW_ON_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
      BETA_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                               ((g:real->A->real^3^3) t)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
                RFA_HT_ZERO_TERMS) THEN
  ASM_REWRITE_TAC[mfd_ricci] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

