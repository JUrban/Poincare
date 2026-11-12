(* ========================================================================= *)
(* Unit pc_p2c_cderiv (Part 2C): P2C_CANON_DERIV_STATEMENT of pc_p2c_iface, *)
(* the derivative bounds |grad R| <= max C 2 R^(3/2) and                     *)
(* |Lap R + 2|Ric|^2| <= max C 2 R^2 at points with (C,eps)-canonical        *)
(* neighbourhoods, eps <= eps0.  Caps and C-components carry the bounds;     *)
(* necks and eps-round components are C^4-close to models with constant     *)
(* scalar curvature (the cylinder, the round metric), and the bounds follow  *)
(* from a covariant stability estimate for grad R and Hess R, built on the   *)
(* S . T calculus of pc_rfa_talg and pc_rfa_ricid (lbilin, lbilin_on), on    *)
(* pc_lrg_stab and on pc_apx_neck.                                           *)
(*                                                                           *)
(* The perturbation calculus is the unit pc_p2c_cdiff, loaded below; this    *)
(* unit has the point estimates, the models, the scaling, round components,  *)
(* caps and C-components, and the main theorem P2C_CANON_DERIV.              *)
(* ========================================================================= *)

needs "src/pc_p2c_cdiff.ml";;
needs "src/pc_p2c_iface.ml";;
needs "src/pc_rfa_ricid.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_rfa_lalg.ml";;
needs "src/pc_p2c_l112.ml";;
needs "src/pc_p2b_scalpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The point estimates.  For G0 with parallel curvature and G C^4-close to   *)
(* G0 at y: |grad R(G)|^2 and (Lap R(G))^2 at y are small, and |Ric(G)|_G is *)
(* at most |Ric(G0)|_G0 plus a small amount.                                 *)
(* ------------------------------------------------------------------------- *)

let P2C_PT_DERIV = prove
 (`!K alpha. &0 < alpha
     ==> ?eta. &0 < eta /\
           !s (G0:real^N->real^N^N) G y.
             metric_field s G0 /\ metric_field s G /\ y IN s /\
             (!z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0) /\
             ltnorm2 4 G0 (lrm4 G0) y <= K /\ lck_dist2 4 G0 G y <= eta
             ==> lgrad2 G (lscalar G) y <= alpha /\
                 llap G (lscalar G) y pow 2 <= alpha`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `CD:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "drm"))
   (SPEC `K:real` (INST_TYPE [`:N`,`:N`] P2C_DRM_BOUNDS)) THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 < &64 * n pow 3 * CD + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &100) (min (inv CD) (alpha / (&64 * n pow 3 * CD + &1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_LT_DIV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  ABBREV_TAC `d = lck_dist2 4 (G0:real^N->real^N^N) G y` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC P2C_LCK_DIST2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1 / &100 /\ CD * d <= &1 /\ (&64 * n pow 3 * CD + &1) * d <= alpha`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `d <= min (&1 / &100) (min (inv CD) (alpha / (&64 * n pow 3 * CD + &1)))` THEN
    REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      ASM_REWRITE_TAC[real_div; REAL_MUL_LID];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  (* the D bounds *)
  USE_THEN "drm" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                  `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "d" THEN
    REWRITE_TAC[p2c_hd] THEN
    MATCH_MP_TAC LRG_LCK_DIST2_TERM_LE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  (* comparison of the metrics *)
  MP_TAC(ISPECL [`2`; `4`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] LCK_DIST_MONO) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= dl /\ dl <= &1 / &10` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 / &100)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_UNIQUE THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_METRIC_LAM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&1 - dl) /\ inv(&1 - dl) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `G:real^N->real^N^N`; `G0:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `y:real^N`; `inv(&1 - dl)`]
                LRG_LTNORM2_COMPARE) THEN
  MP_TAC(ISPECL [`6`; `s:real^N->bool`; `G:real^N->real^N^N`; `G0:real^N->real^N^N`;
                 `lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`; `y:real^N`;
                 `inv(&1 - dl)`] LRG_LTNORM2_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  (* the trace bounds *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                P2C_SCALAR_DERIV_TRACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* arithmetic *)
  SUBGOAL_THEN `inv(&1 - dl) pow 5 <= &64 /\ inv(&1 - dl) pow 6 <= &64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&2 pow 5`; EXISTS_TAC `&2 pow 6`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
       CONV_TAC REAL_RAT_REDUCE_CONV]);
    ALL_TAC] THEN
  ABBREV_TAC `D1 = ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G (lrm4 G)) y` THEN
  ABBREV_TAC `D2 = ltnorm2 6 (G0:real^N->real^N^N) (lnabla 5 G (lnabla 4 G (lrm4 G))) y` THEN
  ABBREV_TAC `N1 = ltnorm2 5 (G:real^N->real^N^N) (lnabla 4 G (lrm4 G)) y` THEN
  ABBREV_TAC `N2 = ltnorm2 6 (G:real^N->real^N^N) (lnabla 5 G (lnabla 4 G (lrm4 G))) y` THEN
  SUBGOAL_THEN `&0 <= D1 /\ &0 <= D2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `N1 <= &64 * (CD * d) /\ N2 <= &64 * (CD * d)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `inv(&1 - dl) pow 5 * D1`; EXISTS_TAC `inv(&1 - dl) pow 6 * D2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `n pow 2 <= n pow 3 /\ &0 <= n pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= CD * d /\ &0 <= N1 /\ &0 <= N2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXPAND_TAC "N1" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "N2" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n pow 2 * N1 <= n pow 3 * (&64 * (CD * d)) /\
                n pow 3 * N2 <= n pow 3 * (&64 * (CD * d))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n pow 3 * (&64 * (CD * d)) <= alpha` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&64 * n pow 3 * CD + &1) * d` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The models.  A curvature tensor of the form c (B(u1,u4)B(u2,u3) -         *)
(* B(u2,u4)B(u1,u3)) with B parallel is parallel; the round case (B = G0,    *)
(* from APX_CONST_CURV_RIEMANN) and the cylinder case (B = Ric, from         *)
(* LRG_RADIAL_RIEMANN) with their R and |Ric|^2.                             *)
(* ------------------------------------------------------------------------- *)

let P2C_PERM_A_PERMUTES = prove
 (`!n. 4 <= n ==> (swap(3,4) o swap(2,3)) permutes 1..n /\
                  (swap(1,2) o swap(3,4) o swap(2,3)) permutes 1..n`,
  REPEAT STRIP_TAC THEN REPEAT(MATCH_MP_TAC PERMUTES_COMPOSE THEN CONJ_TAC) THEN
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let P2C_PARALLEL_RM = prove
 (`!s (G0:real^N->real^N^N) B c.
     metric_field s G0 /\ ltensor_field 2 s B /\
     (!u. smooth_map_on s (\y. lift(B y u))) /\
     (!z u. z IN s ==> lnabla 2 G0 B z u = &0) /\
     (!z u. z IN s
            ==> lrm4 G0 z u =
                c * (B z (\m. if m = 1 then u 1 else u 4) *
                     B z (\m. if m = 1 then u 2 else u 3) -
                     B z (\m. if m = 1 then u 2 else u 4) *
                     B z (\m. if m = 1 then u 1 else u 3)))
     ==> !z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(SPEC `4` P2C_PERM_A_PERMUTES) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `P = ltprod 2 (B:real^N->(num->real^N)->real) B` THEN
  SUBGOAL_THEN `ltensor_field 4 s (P:real^N->(num->real^N)->real) /\
                (!u. smooth_map_on s (\y. lift(P y u)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `B:real^N->(num->real^N)->real`;
                   `B:real^N->(num->real^N)->real`] RFA_LTPROD_FIELD) THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `B:real^N->(num->real^N)->real`;
                   `B:real^N->(num->real^N)->real`] RFA_LTPROD_SMOOTH) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z u. z IN s ==> lnabla 4 (G0:real^N->real^N^N) P z u = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "P" THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `B:real^N->(num->real^N)->real`; `B:real^N->(num->real^N)->real`;
                   `z:real^N`; `u:num->real^N`] RFA_LNABLA_LTPROD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s2 = swap(1,2) o swap(3,4) o swap(2,3)` THEN
  ABBREV_TAC `s1 = swap(3,4) o swap(2,3)` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 4 (G0:real^N->real^N^N)
                (\z u. c * (ltperm s1 P z u - ltperm s2 P z u)) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["s2"; "s1"; "P"] THEN
    REWRITE_TAC[ltperm; ltprod; o_THM; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_TERM_TAC THEN BINOP_TAC THEN BINOP_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
    MAP_EVERY EXISTS_TAC [`2`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    TRY ASM_ARITH_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. smooth_map_on s (\y. lift(ltperm s1 (P:real^N->(num->real^N)->real) y u)) /\
        smooth_map_on s (\y. lift(ltperm s2 (P:real^N->(num->real^N)->real) y u))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RFA_LTPERM_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `G0:real^N->real^N^N`;
                 `\z u. ltperm s1 (P:real^N->(num->real^N)->real) z u -
                        ltperm s2 P z u`; `c:real`; `z:real^N`; `u:num->real^N`]
                LRG_LNABLA_CMUL) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`4`; `G0:real^N->real^N^N`; `ltperm s1 (P:real^N->(num->real^N)->real)`;
                 `ltperm s2 (P:real^N->(num->real^N)->real)`; `z:real^N`; `u:num->real^N`]
                LRG_LNABLA_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RFA_LNABLA_LTPERM; ltperm] THEN REAL_ARITH_TAC);;

let P2C_PARALLEL_RM_NORM = prove
 (`!s (G0:real^N->real^N^N) B c z.
     metric_field s G0 /\ ltensor_field 2 s B /\ z IN s /\
     (!u. lrm4 G0 z u =
          c * (B z (\m. if m = 1 then u 1 else u 4) *
               B z (\m. if m = 1 then u 2 else u 3) -
               B z (\m. if m = 1 then u 2 else u 4) *
               B z (\m. if m = 1 then u 1 else u 3)))
     ==> ltnorm2 4 G0 (lrm4 G0) z <= &4 * c pow 2 * ltnorm2 2 G0 B z pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `4` P2C_PERM_A_PERMUTES) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `B:real^N->(num->real^N)->real`;
                 `B:real^N->(num->real^N)->real`] RFA_LTPROD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G0) z =
    ltnorm2 4 G0 (\y u. c * (\y u. ltperm (swap(3,4) o swap(2,3)) (ltprod 2 B B) y u -
                                   ltperm (swap(1,2) o swap(3,4) o swap(2,3))
                                          (ltprod 2 B B) y u) y u) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    REWRITE_TAC[ltperm; ltprod; o_THM; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_TERM_TAC THEN BINOP_TAC THEN BINOP_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
    MAP_EVERY EXISTS_TAC [`2`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    TRY ASM_ARITH_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_LTNORM2_CMUL] THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `ltprod 2 (B:real^N->(num->real^N)->real) B`;
                 `swap(3,4) o swap(2,3)`; `swap(1,2) o swap(3,4) o swap(2,3)`; `z:real^N`]
                P2C_PERM_DIFF_NORM) THEN
  MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `B:real^N->(num->real^N)->real`; `B:real^N->(num->real^N)->real`;
                 `z:real^N`] RFA_LTNORM2_LTPROD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(c * c) * (&4 * ltnorm2 2 (G0:real^N->real^N^N) B z * ltnorm2 2 G0 B z)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_SQUARE];
    REAL_ARITH_TAC]);;

(* The round model: constant sectional curvature 1 on an open set. *)

let P2C_ROUND_RIEMANN = prove
 (`!s (G0:real^N->real^N^N) z.
     metric_field s G0 /\ z IN s /\
     (!u v. ~collinear {vec 0,u,v} ==> lsectional G0 z u v = &1)
     ==> (!u v w. lriemann G0 z u v w = (v dot (G0 z ** w)) % u - (u dot (G0 z ** w)) % v) /\
         (!v w. lricci G0 z v w = (&(dimindex(:N)) - &1) * (v dot (G0 z ** w))) /\
         (!u. lrm4 G0 z u =
              --(&1) * (lmetric2 G0 z (\m. if m = 1 then u 1 else u 4) *
                        lmetric2 G0 z (\m. if m = 1 then u 2 else u 3) -
                        lmetric2 G0 z (\m. if m = 1 then u 2 else u 4) *
                        lmetric2 G0 z (\m. if m = 1 then u 1 else u 3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`; `&1`]
                APX_CONST_CURV_RIEMANN) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[lricci; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL] THEN
    SIMP_TAC[BASIS_COMPONENT; SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N)) (\i. (basis i dot ((G0:real^N->real^N^N) z ** w)) * (v:real^N)$i) =
      v dot (G0 z ** w)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\i. ((G0:real^N->real^N^N) z ** w)$i * (v:real^N)$i)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[DOT_BASIS];
        REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    GEN_TAC THEN ASM_REWRITE_TAC[lrm4; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 3`; `(u:num->real^N) 1`] LRG_METRIC_SYM) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 3`; `(u:num->real^N) 2`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2C_ROUND_MODEL = prove
 (`!s (G0:real^N->real^N^N).
     metric_field s G0 /\
     (!z u v. z IN s /\ ~collinear {vec 0,u,v} ==> lsectional G0 z u v = &1)
     ==> (!z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0) /\
         (!z. z IN s ==> lscalar G0 z = &(dimindex(:N)) * (&(dimindex(:N)) - &1)) /\
         (!z. z IN s ==> ltnorm2 2 G0 (lric2 G0) z =
                         (&(dimindex(:N)) - &1) pow 2 * &(dimindex(:N))) /\
         (!z. z IN s ==> ltnorm2 4 G0 (lrm4 G0) z <= &4 * &(dimindex(:N)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> (!u v w. lriemann (G0:real^N->real^N^N) z u v w =
                     (v dot (G0 z ** w)) % u - (u dot (G0 z ** w)) % v) /\
            (!v w. lricci G0 z v w = (&(dimindex(:N)) - &1) * (v dot (G0 z ** w))) /\
            (!u. lrm4 G0 z u =
                 --(&1) * (lmetric2 G0 z (\m. if m = 1 then u 1 else u 4) *
                           lmetric2 G0 z (\m. if m = 1 then u 2 else u 3) -
                           lmetric2 G0 z (\m. if m = 1 then u 2 else u 4) *
                           lmetric2 G0 z (\m. if m = 1 then u 1 else u 3)))`
  (LABEL_TAC "rr") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2C_ROUND_RIEMANN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2C_PARALLEL_RM THEN
    MAP_EVERY EXISTS_TAC [`lmetric2 (G0:real^N->real^N^N)`; `--(&1)`] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`0`; `z:real^N`; `u:num->real^N`] (MATCH_MP LRG_LNABLA_ITER_METRIC
      (ASSUME `metric_field s (G0:real^N->real^N^N)`))) THEN
    ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "rr" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(z:real^N) IN s`))) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`]
                  LRG_LSCALAR_TRACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `((lambda i j. (&(dimindex(:N)) - &1) *
                    (basis i dot ((G0:real^N->real^N^N) z ** basis j))):real^N^N) =
      (&(dimindex(:N)) - &1) %% G0 z`
    SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; DOT_BASIS] THEN
      SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA];
      ALL_TAC] THEN
    SUBGOAL_THEN `invertible((G0:real^N->real^N^N) z)` ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_MUL_RMUL; TRACE_CMUL; MATRIX_INV; TRACE_I] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "rr" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(z:real^N) IN s`))) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 2 (G0:real^N->real^N^N)
                  (\y u. (&(dimindex(:N)) - &1) * lmetric2 G0 y u) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_REWRITE_TAC[lric2; lmetric2];
      REWRITE_TAC[LRG_LTNORM2_CMUL; ETA_AX] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_LTNORM2_METRIC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "rr" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(z:real^N) IN s`))) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `lmetric2 (G0:real^N->real^N^N)`;
                   `--(&1)`; `z:real^N`] P2C_PARALLEL_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`]
                  LRG_LTNORM2_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID]]);;
(* The cylinder model: Ric is parallel. *)

let P2C_CYL_RIC_FD = prove
 (`!z v w h:real^3.
     ~(z = vec 0)
     ==> drop(frechet_derivative
               (\x. lift(((v dot w) - (v dot x) * (w dot x) / norm x pow 2) / norm x pow 2))
               (at z) h) =
         --(&2) * (z dot h) * (v dot w) / (norm z pow 2) pow 2 -
         ((v dot h) * (w dot z) + (v dot z) * (w dot h)) / (norm z pow 2) pow 2 +
         &4 * (z dot h) * (v dot z) * (w dot z) / (norm z pow 2) pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^3. lift(((v dot w) - (v dot x) * (w dot x) / norm x pow 2) / norm x pow 2)) =
    (\x. lift(--(v dot w) * (--(&1) / norm x pow 2) +
              --(&1) * ((v dot x) * ((w dot x) *
                        ((--(&1) / norm x pow 2) * (--(&1) / norm x pow 2))))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `z:real^3` LRG_CYL_M_DERIV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a:real^3. ((\x. lift(a dot x)) has_derivative (\h. lift(a dot h))) (at z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  ABBREV_TAC `dz = &2 / (norm(z:real^3) pow 2) pow 2` THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:real^3. --(&1) / norm x pow 2`; `\h:real^3. dz * (z dot h)`;
    `\x:real^3. --(&1) / norm x pow 2`; `\h:real^3. dz * (z dot h)`; `z:real^3`]
   LRG_HAS_DERIVATIVE_LIFT_MUL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:real^3. w dot x`; `\h:real^3. w dot h`;
    `\x:real^3. (--(&1) / norm x pow 2) * (--(&1) / norm x pow 2)`;
    `\h:real^3. (--(&1) / norm z pow 2) * dz * (z dot h) + (dz * (z dot h)) * (--(&1) / norm z pow 2)`; `z:real^3`]
   LRG_HAS_DERIVATIVE_LIFT_MUL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:real^3. v dot x`; `\h:real^3. v dot h`;
    `\x:real^3. (w dot x) * (--(&1) / norm x pow 2) * (--(&1) / norm x pow 2)`;
    `\h:real^3. (w dot z) * ((--(&1) / norm z pow 2) * dz * (z dot h) + (dz * (z dot h)) * (--(&1) / norm z pow 2)) +
                (w dot h) * (--(&1) / norm z pow 2) * (--(&1) / norm z pow 2)`; `z:real^3`]
   LRG_HAS_DERIVATIVE_LIFT_MUL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:real^3. --(&1) / norm x pow 2`; `\h:real^3. dz * (z dot h)`;
    `\x:real^3. (v dot x) * (w dot x) * (--(&1) / norm x pow 2) * (--(&1) / norm x pow 2)`;
    `\h:real^3. (v dot z) * ((w dot z) * ((--(&1) / norm z pow 2) * dz * (z dot h) + (dz * (z dot h)) * (--(&1) / norm z pow 2)) +
                             (w dot h) * (--(&1) / norm z pow 2) * (--(&1) / norm z pow 2)) +
                (v dot h) * (w dot z) * (--(&1) / norm z pow 2) * (--(&1) / norm z pow 2)`;
    `--((v:real^3) dot w)`; `--(&1)`; `z:real^3`]
   LRG_HAS_DERIVATIVE_LIFT_LINCOMB)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP] THEN EXPAND_TAC "dz" THEN
  SUBGOAL_THEN `~(norm(z:real^3) pow 2 = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P2C_CYL_RIC_PAR = prove
 (`!z u. ~(z = vec 0)
         ==> lnabla 2 (cylinder_flow (&0)) (lric2 (cylinder_flow (&0))) z u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift(lric2 (cylinder_flow (&0)) x u)) (at z) =
    frechet_derivative
      (\x:real^3. lift((((u:num->real^3) 1 dot u 2) - (u 1 dot x) * (u 2 dot x) /
                         norm x pow 2) / norm x pow 2)) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[lric2] THEN
    MATCH_MP_TAC RFB_CYL_RICCI THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2C_CYL_RIC_FD] THEN
  REWRITE_TAC[SUM_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`; LRG_CYL_FLOW_CHRISTOFFEL] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; NORM_POW_2] THEN
  SUBGOAL_THEN `~((z:real^3) dot z = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let P2C_CYL_RM = prove
 (`!z u. ~(z = vec 0)
         ==> lrm4 (cylinder_flow (&0)) z u =
             --(&2) * (lric2 (cylinder_flow (&0)) z (\m. if m = 1 then u 1 else u 4) *
                       lric2 (cylinder_flow (&0)) z (\m. if m = 1 then u 2 else u 3) -
                       lric2 (cylinder_flow (&0)) z (\m. if m = 1 then u 2 else u 4) *
                       lric2 (cylinder_flow (&0)) z (\m. if m = 1 then u 1 else u 3))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lrm4; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`] THEN
  REWRITE_TAC[LRG_CYL0_EQ] THEN
  MP_TAC(ISPECL [`(\z. (&2 / norm z pow 2) %% mat 1):real^3->real^3^3`;
                 `(:real^3) DELETE vec 0`; `\x:real^3. --(&1) / norm x pow 2`;
                 `&2 / (norm(z:real^3) pow 2) pow 2`; `z:real^3`; `(u:num->real^3) 1`;
                 `(u:num->real^3) 2`; `(u:num->real^3) 4`] LRG_RADIAL_RIEMANN) THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV; LRG_CYL_CHRISTOFFEL] THEN
    ASM_SIMP_TAC[LRG_CYL_M_DERIV];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; DOT_RADD; DOT_RSUB;
              DOT_LMUL; DOT_LADD; DOT_LSUB; NORM_POW_2] THEN
  SUBGOAL_THEN `~((z:real^3) dot z = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let P2C_CYL_RIC_NORM = prove
 (`!z:real^3. ~(z = vec 0)
              ==> ltnorm2 2 (cylinder_flow (&0)) (lric2 (cylinder_flow (&0))) z = &1 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&0` RFB_CYL_METRIC_FIELD) THEN REWRITE_TAC[REAL_ARITH `&0 < &1`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `c = sqrt(norm(z:real^3) pow 2 / &2)` THEN
  SUBGOAL_THEN `c * c = norm(z:real^3) pow 2 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                 `lric2 (cylinder_flow (&0))`; `z:real^3`; `c %% mat 1:real^3^3`]
                LRG_LTNORM2_SQUARES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV; LRG_CYL0_EQ] THEN
    REWRITE_TAC[MATRIX_INV_CMUL; MATRIX_INV_I; TRANSP_MATRIX_CMUL; TRANSP_MAT;
                MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < norm(z:real^3) pow 2` THEN CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; TRANSP_MATRIX_CMUL; TRANSP_MAT;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  UNDISCH_TAC `c * c = norm(z:real^3) pow 2 / &2` THEN
  UNDISCH_TAC `&0 < norm(z:real^3) pow 2` THEN
  REWRITE_TAC[NORM_POW_2; DOT_3] THEN CONV_TAC REAL_FIELD);;

let P2C_CYL_MODEL = prove
 (`(!z u. ~(z = vec 0)
          ==> lnabla 4 (cylinder_flow (&0)) (lrm4 (cylinder_flow (&0))) z u = &0) /\
   (!z. ~(z = vec 0) ==> lscalar (cylinder_flow (&0)) z = &1) /\
   (!z. ~(z = vec 0)
        ==> ltnorm2 2 (cylinder_flow (&0)) (lric2 (cylinder_flow (&0))) z = &1 / &2) /\
   (!z. ~(z = vec 0)
        ==> ltnorm2 4 (cylinder_flow (&0)) (lrm4 (cylinder_flow (&0))) z <= &4)`,
  MP_TAC(SPEC `&0` RFB_CYL_METRIC_FIELD) THEN REWRITE_TAC[REAL_ARITH `&0 < &1`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                   `lric2 (cylinder_flow (&0))`; `--(&2)`] P2C_PARALLEL_RM) THEN
    ASM_SIMP_TAC[IN_DELETE; IN_UNIV; P2C_CYL_RIC_PAR; P2C_CYL_RM];
    SIMP_TAC[RFB_CYL_SCALAR; REAL_ARITH `&0 < &1`] THEN REAL_ARITH_TAC;
    REWRITE_TAC[P2C_CYL_RIC_NORM];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                   `lric2 (cylinder_flow (&0))`; `--(&2)`; `z:real^3`]
                  P2C_PARALLEL_RM_NORM) THEN
    ASM_SIMP_TAC[IN_DELETE; IN_UNIV; P2C_CYL_RM; P2C_CYL_RIC_NORM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Scaling of lgrad2, llap and ltnorm2 under G -> c G, and the reading of R, *)
(* |grad R|^2, Lap R and |Ric|^2 of g at e y through the pullback            *)
(* rfs_pullback atlas e g at y.                                              *)
(* ------------------------------------------------------------------------- *)

let P2C_LGRAD2_METRIC_SCALE = prove
 (`!(G:real^N->real^N^N) c f y.
     lgrad2 (\z. c %% G z) f y = inv c * lgrad2 G f y`,
  REWRITE_TAC[lgrad2; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT; GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let P2C_LGRAD2_FUN_SCALE = prove
 (`!(G:real^N->real^N^N) a f y.
     (\z. lift(f z)) differentiable at y
     ==> lgrad2 G (\z. a * f z) y = a pow 2 * lgrad2 G f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lgrad2] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(a * (f:real^N->real) z)) (at y) =
    (\h. a % frechet_derivative (\z. lift(f z)) (at y) h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[lgrad2; DROP_CMUL; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2C_LLAP_METRIC_SCALE = prove
 (`!U (G:real^N->real^N^N) c f y.
     metric_field U G /\ y IN U /\ &0 < c
     ==> llap (\z. c %% G z) f y = inv c * llap G f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. christoffel (\z. c %% (G:real^N->real^N^N) z) y a b = christoffel G y a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[llap; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT; GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let P2C_LTNORM2_METRIC_SCALE = prove
 (`!k (G:real^N->real^N^N) c tf y.
     ltnorm2 k (\z. c %% G z) tf y = inv c pow k * ltnorm2 k G tf y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltnorm2; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC);;

(* The manifold quantities at e y through the pullback at y. *)

let P2C_PARAM_REP = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s
     ==> lscalar (rfs_pullback atlas e g) y = mfd_scalar atlas g (e y) /\
         lgrad2 (rfs_pullback atlas e g) (lscalar (rfs_pullback atlas e g)) y =
         rfs_scalar_grad2 atlas g (e y) /\
         llap (rfs_pullback atlas e g) (lscalar (rfs_pullback atlas e g)) y =
         rfs_scalar_lap atlas g (e y) /\
         ltnorm2 2 (rfs_pullback atlas e g) (lric2 (rfs_pullback atlas e g)) y =
         rfs_ric_norm2 atlas g (e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `(h:real^N->real^N) = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e` THEN
  ABBREV_TAC `G' = metric_local atlas (chart_at atlas ((e:real^N->A) y)) (g:A->real^N^N)` THEN
  SUBGOAL_THEN
   `!z. z IN N
        ==> lscalar (rfs_pullback (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A)
                                  (g:A->real^N^N)) z = lscalar G' ((h:real^N->real^N) z) /\
            llap (rfs_pullback atlas e g) (lscalar (rfs_pullback atlas e g)) z =
            llap G' (lscalar G') (h z) /\
            ltnorm2 2 (rfs_pullback atlas e g) (lric2 (rfs_pullback atlas e g)) z =
            ltnorm2 2 G' (lric2 G') (h z)`
  (LABEL_TAC "rep") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2C_REP_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `N':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) y = SND(chart_at atlas ((e:real^N->A) y)) (e y)`
  ASSUME_TAC THENL [EXPAND_TAC "h" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  USE_THEN "rep" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:real^N) IN N`))) THEN
  ASM_REWRITE_TAC[mfd_scalar; rfs_scalar_lap; rfs_ric_norm2; rfs_scalar_grad2;
                  P2C_LRIC2_ETA] THEN
  MP_TAC(ISPECL [`N':real^N->bool`; `G':real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lgrad2 (mpullback (h:real^N->real^N) G') (lscalar G' o h) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM];
    UNDISCH_TAC `(h:real^N->real^N) y =
                 SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) (e y)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LGRAD2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `N:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

(* The neck: the manifold quantities at e y through the scaled pullback. *)

let P2C_KREG_FOUR = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4 ==> 4 <= rfs_kreg eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[RFS_KREG; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

let P2C_NECK_SCALED = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
     y IN rfs_neck_dom eps
     ==> mfd_scalar atlas g (e y) =
         mfd_scalar atlas g x *
         lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y /\
         rfs_scalar_grad2 atlas g (e y) =
         mfd_scalar atlas g x pow 3 *
         lgrad2 (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)
                (lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)) y /\
         rfs_scalar_lap atlas g (e y) =
         mfd_scalar atlas g x pow 2 *
         llap (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)
              (lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)) y /\
         rfs_ric_norm2 atlas g (e y) =
         mfd_scalar atlas g x pow 2 *
         ltnorm2 2 (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)
                   (lric2 (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`] P2C_PARAM_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ABBREV_TAC `c = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `Gp = rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `open(rfs_neck_dom eps)` ASSUME_TAC THENL
   [REWRITE_TAC[APX_NECK_DOM_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `Gp:real^3->real^3^3`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN rfs_neck_dom eps
                    ==> lscalar (\z. c %% (Gp:real^3->real^3^3) z) z =
                        inv c * lscalar Gp z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `Gp:real^3->real^3^3`; `c:real`; `z:real^3`]
                  LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `c pow 3 * lgrad2 (\z. c %% (Gp:real^3->real^3^3) z)
                                 (\z. inv c * lscalar Gp z) y` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2C_LGRAD2_METRIC_SCALE] THEN
      MP_TAC(ISPECL [`Gp:real^3->real^3^3`; `inv c`; `lscalar (Gp:real^3->real^3^3)`;
                     `y:real^3`] P2C_LGRAD2_FUN_SCALE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
      AP_TERM_TAC THEN MATCH_MP_TAC LGRAD2_LOCAL THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `c pow 2 * llap (\z. c %% (Gp:real^3->real^3^3) z)
                               (\z. inv c * lscalar Gp z) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_neck_dom eps`; `Gp:real^3->real^3^3`; `c:real`;
                     `\z. inv c * lscalar (Gp:real^3->real^3^3) z`; `y:real^3`]
                    P2C_LLAP_METRIC_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `Gp:real^3->real^3^3`;
                     `lscalar (Gp:real^3->real^3^3)`; `inv c`; `y:real^3`] RFA_LLAP_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
      AP_TERM_TAC THEN MATCH_MP_TAC LLAP_LOCAL THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[P2C_LTNORM2_METRIC_SCALE] THEN
    SUBGOAL_THEN
     `ltnorm2 2 (Gp:real^3->real^3^3) (lric2 (\z. c %% Gp z)) y = ltnorm2 2 Gp (lric2 Gp) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[lric2] THEN GEN_TAC THEN
      MATCH_MP_TAC LRICCI_SCALE THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD]]);;

(* The derivative bounds at the centre of an eps-neck. *)

let P2C_ABS_LE_OF_SQ = prove
 (`!x y. x pow 2 <= y pow 2 /\ &0 <= y ==> abs x <= y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real`; `y:real`] REAL_LE_SQUARE_ABS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2C_NECK_DERIV = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A).
       riemannian_metric atlas g /\ &0 < eps /\ eps <= eps0 /\
       rfs_neck (top,atlas) g eps x e
       ==> &0 < mfd_scalar atlas g x /\
           sqrt(rfs_scalar_grad2 atlas g x) <=
           &2 * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
           abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
           &2 * mfd_scalar atlas g x pow 2`,
  MP_TAC(SPECL [`&4`; `&1 / &4`] (INST_TYPE [`:3`,`:N`] P2C_PT_DERIV)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  ABBREV_TAC `c2 = sqrt(&(CARD(index_tuples 2 (:3)))) * &(dimindex(:3)) * &5` THEN
  SUBGOAL_THEN `&0 <= c2` ASSUME_TAC THENL
   [EXPAND_TAC "c2" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &10) (min (sqrt eta) (inv(&1000 * (c2 + &1))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ eps <= sqrt eta /\ eps <= inv(&1000 * (c2 + &1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= min (&1 / &10) (min (sqrt eta) (inv(&1000 * (c2 + &1))))` THEN
    REWRITE_TAC[REAL_LE_MIN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ ~(y0 = vec 0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    ASM_REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN rfs_neck_dom eps ==> ~(z = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
                                                  lhs(concl th) = `x:A`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(e:real^3->A) y0`; `e:real^3->A`; `y0:real^3`]
                P2C_NECK_SCALED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = mfd_scalar atlas (g:A->real^3^3) (e(y0:real^3))` THEN
  ABBREV_TAC `G = \y. c %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y` THEN
  (* the distance at y0 *)
  SUBGOAL_THEN `lck_dist2 4 (cylinder_flow (&0)) G y0 < eps pow 2 /\
                lck_dist2 2 (cylinder_flow (&0)) G y0 < eps pow 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2C_KREG_FOUR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`4`; `rfs_kreg eps`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
                   `G:real^3->real^3^3`; `y0:real^3`] LCK_DIST_MONO) THEN
    MP_TAC(ISPECL [`2`; `4`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
                   `G:real^3->real^3^3`; `y0:real^3`] LCK_DIST_MONO) THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD; ARITH] THEN
    UNDISCH_TAC `!y. y IN rfs_neck_dom eps
                     ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                                   (G:real^3->real^3^3) y <= d` THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `d < eps pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 <= eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt eta pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the model *)
  MP_TAC P2C_CYL_MODEL THEN STRIP_TAC THEN
  (* the derivative estimate *)
  USE_THEN "pt" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                 `G:real^3->real^3^3`; `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[APX_NECK_CYL_FIELD] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  (* the Ricci bound *)
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`; `G:real^3->real^3^3`;
                 `y0:real^3`] P2C_RIC_NORM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (cylinder_flow (&0)) (G:real^3->real^3^3) y0)` THEN
  MP_TAC(ISPECL [`2`; `rfs_neck_dom eps`; `cylinder_flow (&0)`; `G:real^3->real^3^3`;
                 `y0:real^3`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= dl /\ dl < eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&(CARD(index_tuples 2 (:3)))) * &(dimindex(:3)) * &5 * dl = c2 * dl`
  SUBST1_TAC THENL [EXPAND_TAC "c2" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&1 / &2) <= &3 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `c2 * dl <= &1 / &1000 /\ dl <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c2 + &1) * dl <= &1 / &1000` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c2 + &1) * inv(&1000 * (c2 + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= c2` THEN CONV_TAC REAL_FIELD];
      SUBGOAL_THEN `&0 <= c2 * dl` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 <= c2` THEN UNDISCH_TAC `&0 <= dl` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y0 <= &3 / &4` ASSUME_TAC THENL
   [ABBREV_TAC `X = ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y0` THEN
    SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `G:real^3->real^3^3`] P2C_RIC_FIELD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt X <= &4 / &5` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&1 - dl) * (sqrt(&1 / &2) + c2 * dl)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &1 - dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 / &5) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt X pow 2` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  (* the final arithmetic *)
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = lgrad2 (G:real^3->real^3^3) (lscalar G) y0` THEN
  ABBREV_TAC `P = llap (G:real^3->real^3^3) (lscalar G) y0` THEN
  ABBREV_TAC `Q = ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y0` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `G:real^3->real^3^3`] P2C_RIC_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs P <= &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_ABS_LE_OF_SQ THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c pow 2 /\ &0 <= c pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c pow 3 * &1 / &4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 <= c pow 3` THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c pow 2 * (abs P + &2 * Q)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * x + &2 * a * y = a * (x + &2 * y)`] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ABS_POW; REAL_ARITH `&0 < c ==> abs c = c`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* eps-round components.  In the preferred chart at x the representative of  *)
(* g1 has constant sectional curvature 1 on the image of the chart domain    *)
(* inside the component (LSECTIONAL_CHART_TRANS), so the round model applies *)
(* on an open set; q g is C^4-close to it at x.                              *)
(* ------------------------------------------------------------------------- *)

(* The four quantities under G -> q G. *)

let P2C_SCALE_QUANTITIES = prove
 (`!U (G:real^N->real^N^N) q y.
     metric_field U G /\ y IN U /\ &0 < q
     ==> lscalar G y = q * lscalar (\z. q %% G z) y /\
         lgrad2 G (lscalar G) y =
         q pow 3 * lgrad2 (\z. q %% G z) (lscalar (\z. q %% G z)) y /\
         llap G (lscalar G) y = q pow 2 * llap (\z. q %% G z) (lscalar (\z. q %% G z)) y /\
         ltnorm2 2 G (lric2 G) y = q pow 2 * ltnorm2 2 (\z. q %% G z) (lric2 (\z. q %% G z)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN U ==> lscalar (\z. q %% (G:real^N->real^N^N) z) z =
                               inv q * lscalar G z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `q:real`; `z:real^N`]
                  LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC `~(q = &0)` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `q pow 3 * lgrad2 (\z. q %% (G:real^N->real^N^N) z)
                                 (\z. inv q * lscalar G z) y` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2C_LGRAD2_METRIC_SCALE] THEN
      MP_TAC(ISPECL [`G:real^N->real^N^N`; `inv q`; `lscalar (G:real^N->real^N^N)`;
                     `y:real^N`] P2C_LGRAD2_FUN_SCALE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `~(q = &0)` THEN CONV_TAC REAL_FIELD;
      AP_TERM_TAC THEN MATCH_MP_TAC LGRAD2_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `q pow 2 * llap (\z. q %% (G:real^N->real^N^N) z)
                               (\z. inv q * lscalar G z) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `q:real`;
                     `\z. inv q * lscalar (G:real^N->real^N^N) z`; `y:real^N`]
                    P2C_LLAP_METRIC_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `lscalar (G:real^N->real^N^N)`; `inv q`; `y:real^N`] RFA_LLAP_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `~(q = &0)` THEN CONV_TAC REAL_FIELD;
      AP_TERM_TAC THEN MATCH_MP_TAC LLAP_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[P2C_LTNORM2_METRIC_SCALE] THEN
    SUBGOAL_THEN
     `ltnorm2 2 (G:real^N->real^N^N) (lric2 (\z. q %% G z)) y = ltnorm2 2 G (lric2 G) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[lric2] THEN GEN_TAC THEN
      MATCH_MP_TAC LRICCI_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(q = &0)` THEN CONV_TAC REAL_FIELD]]);;

(* Constant curvature 1 of the chart representative on the component. *)

let P2C_COMPONENT_CONST_CURV = prove
 (`!top atlas (g1:A->real^N^N) (W:A->bool) (V:A->bool) (phi:A->real^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     (V,phi) IN atlas /\ W SUBSET topspace top /\
     (!x u v. x IN W /\ ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 x u v = &1)
     ==> !z u v. z IN IMAGE phi (V INTER W) /\ ~collinear {vec 0,u,v}
                 ==> lsectional (metric_local atlas (V,phi) g1) z u v = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `u:real^N`; `v:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V':A->bool` (X_CHOOSE_THEN `psi:A->real^N` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`;
                 `phi:A->real^N`; `V':A->bool`; `psi:A->real^N`; `g1:A->real^N^N`; `x:A`;
                 `u:real^N`; `v:real^N`] LSECTIONAL_CHART_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`x:A`; `chart_jac (V,phi) (V',psi) (x:A) (u:real^N)`;
     `chart_jac (V,phi) (V',psi) (x:A) (v:real^N)`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
          (concl th))) THEN
  ASM_REWRITE_TAC[mfd_sectional] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`;
                 `phi:A->real^N`; `V':A->bool`; `psi:A->real^N`; `x:A`]
                CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`;
                 `phi:A->real^N`; `V':A->bool`; `psi:A->real^N`; `x:A`]
                CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `~collinear {vec 0:real^N,u,v}` THEN
  MP_TAC(ISPECL [`chart_jac (V,phi) (V',psi) (x:A):real^N->real^N`;
                 `{vec 0:real^N,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `chart_jac (V',psi) (V,phi) (x:A):real^N->real^N`) THEN
    REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM]
      (ASSUME `chart_jac (V',psi) (V,phi) (x:A) o chart_jac (V,phi) (V',psi) x =
               (\h:real^N. h)`)] THEN
    BETA_TAC THEN REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN
    ASM_REWRITE_TAC[MATCH_MP LINEAR_0
      (ASSUME `linear(chart_jac (V,phi) (V',psi) (x:A):real^N->real^N)`)]]);;

(* The derivative bounds at the points of an eps-round component. *)

let P2C_ROUND_DERIV = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps W x.
       riemannian_metric atlas g /\ &0 < eps /\ eps <= eps0 /\
       rfs_round_component (top,atlas) g eps W /\ x IN W
       ==> &0 < mfd_scalar atlas g x /\
           sqrt(rfs_scalar_grad2 atlas g x) <=
           &2 * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
           abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
           &2 * mfd_scalar atlas g x pow 2`,
  MP_TAC(SPECL [`&36`; `&1`] (INST_TYPE [`:3`,`:N`] P2C_PT_DERIV)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  MP_TAC(SPECL [`&6`; `&1 / &2`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs"))) THEN
  ABBREV_TAC `c2 = sqrt(&(CARD(index_tuples 2 (:3)))) * &(dimindex(:3)) * &5` THEN
  SUBGOAL_THEN `&0 <= c2` ASSUME_TAC THENL
   [EXPAND_TAC "c2" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &10) (min (sqrt eta) (min eta2 (inv(&1000 * (c2 + &1)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `W:A->bool`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ eps <= sqrt eta /\ eps <= eta2 /\
                eps <= inv(&1000 * (c2 + &1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= min (&1 / &10) (min (sqrt eta) (min eta2 (inv(&1000 * (c2 + &1)))))` THEN
    REWRITE_TAC[REAL_LE_MIN];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps W` THEN
  REWRITE_TAC[rfs_round_component; rfs_mclose] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top /\ open_in top W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `W:A->bool`] APX_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `phi:A->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (phi:A->real^3) (V INTER W)` THEN
  SUBGOAL_THEN `open(S:real^3->bool) /\ (phi:A->real^3) x IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `V:A->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas (V,phi) (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas (V,phi) (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) V` THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [ALL_TAC; EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]) THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V,phi):(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (V,phi) (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas (V,phi) g z)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `W:A->bool`; `V:A->bool`; `phi:A->real^3`] P2C_COMPONENT_CONST_CURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G1 = metric_local atlas (V,phi) (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas (V,phi) (g:A->real^3^3)` THEN
  ABBREV_TAC `yc = (phi:A->real^3) x` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the quantities in the chart *)
  ASM_REWRITE_TAC[mfd_scalar; rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2;
                  P2C_LRIC2_ETA; SND] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `yc:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `G = \z. q %% (Gg:real^3->real^3^3) z` THEN
  (* the round model *)
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`] P2C_ROUND_MODEL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  (* the distance *)
  SUBGOAL_THEN `lck_dist2 4 (G1:real^3->real^3^3) G yc < eps pow 2 /\
                lck_dist2 2 (G1:real^3->real^3^3) G yc < eps pow 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2C_KREG_FOUR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`4`; `rfs_kreg eps`; `S:real^3->bool`; `G1:real^3->real^3^3`;
                   `G:real^3->real^3^3`; `yc:real^3`] LCK_DIST_MONO) THEN
    MP_TAC(ISPECL [`2`; `4`; `S:real^3->bool`; `G1:real^3->real^3^3`;
                   `G:real^3->real^3^3`; `yc:real^3`] LCK_DIST_MONO) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    UNDISCH_TAC `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) G yc <= d` THEN
    UNDISCH_TAC `d < eps pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 <= eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt eta pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 2 (G1:real^3->real^3^3) G yc < eta2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the derivative estimate *)
  USE_THEN "pt" (MP_TAC o SPECL [`S:real^3->bool`; `G1:real^3->real^3^3`;
                                 `G:real^3->real^3^3`; `yc:real^3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* the scalar curvature *)
  USE_THEN "cs" (MP_TAC o SPECL [`S:real^3->bool`; `G1:real^3->real^3^3`;
                                 `G:real^3->real^3^3`; `yc:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  (* the Ricci bound *)
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `yc:real^3`] P2C_RIC_NORM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G1:real^3->real^3^3) G yc)` THEN
  MP_TAC(ISPECL [`2`; `S:real^3->bool`; `G1:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `yc:real^3`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= dl /\ dl < eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&(CARD(index_tuples 2 (:3)))) * &(dimindex(:3)) * &5 * dl = c2 * dl`
  SUBST1_TAC THENL [EXPAND_TAC "c2" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&12) <= &7 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `c2 * dl <= &1 / &1000 /\ dl <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c2 + &1) * dl <= &1 / &1000` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c2 + &1) * inv(&1000 * (c2 + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= c2` THEN CONV_TAC REAL_FIELD];
      SUBGOAL_THEN `&0 <= c2 * dl` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 <= c2` THEN UNDISCH_TAC `&0 <= dl` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 2 (G:real^3->real^3^3) (lric2 G) yc <= &16` ASSUME_TAC THENL
   [ABBREV_TAC `X = ltnorm2 2 (G:real^3->real^3^3) (lric2 G) yc` THEN
    SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
      MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`] P2C_RIC_FIELD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt X <= &4` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&1 - dl) * (sqrt(&12) + c2 * dl)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &1 - dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt X pow 2` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  (* the final arithmetic *)
  ABBREV_TAC `L = lgrad2 (G:real^3->real^3^3) (lscalar G) yc` THEN
  ABBREV_TAC `P = llap (G:real^3->real^3^3) (lscalar G) yc` THEN
  ABBREV_TAC `Q = ltnorm2 2 (G:real^3->real^3^3) (lric2 G) yc` THEN
  ABBREV_TAC `R = lscalar (G:real^3->real^3^3) yc` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`] P2C_RIC_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs P <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_ABS_LE_OF_SQ THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&11 / &2 <= R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= q pow 2 /\ &0 <= q pow 3 /\ &1 <= &4 * R pow 3 /\ &33 <= &2 * R pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC) THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (&11 / &2) pow 3` THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&11 / &2) pow 2` THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 3 * (&4 * R pow 3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2 * (abs P + &2 * Q)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * x + &2 * a * y = a * (x + &2 * y)`] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ABS_POW; REAL_ARITH `&0 < c ==> abs c = c`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2 * &33` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 * a * b = a * (&2 * b)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Caps and C-components (the bounds are clauses of the definitions), and    *)
(* the headline P2C_CANON_DERIV.                                             *)
(* ------------------------------------------------------------------------- *)

let P2C_SUP_LT_BOUND = prove
 (`!U (f:A->real) h C x.
     rfs_sup_lt {f y / h y | y IN U} C /\ x IN U /\ &0 < h x ==> f x <= C * h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:A->real) x / h x`) THEN
  ANTS_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * (h:A->real) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

let P2C_TWO_BOUNDS = prove
 (`!U (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) C x.
     rfs_sup_lt {sqrt(rfs_scalar_grad2 atlas g y) /
                 (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) | y IN U} C /\
     rfs_sup_lt {abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                 mfd_scalar atlas g y pow 2 | y IN U} C /\
     x IN U /\ &0 < mfd_scalar atlas g x
     ==> sqrt(rfs_scalar_grad2 atlas g x) <=
         C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
         abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
         C * mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:A->bool`; `\y:A. sqrt(rfs_scalar_grad2 atlas (g:A->real^3^3) y)`;
                   `\y:A. mfd_scalar atlas (g:A->real^3^3) y * sqrt(mfd_scalar atlas g y)`;
                   `C:real`; `x:A`] P2C_SUP_LT_BOUND) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT];
    MP_TAC(ISPECL [`U:A->bool`;
                   `\y:A. abs(rfs_scalar_lap atlas (g:A->real^3^3) y +
                              &2 * rfs_ric_norm2 atlas g y)`;
                   `\y:A. mfd_scalar atlas (g:A->real^3^3) y pow 2`;
                   `C:real`; `x:A`] P2C_SUP_LT_BOUND) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]]);;

let P2C_CAP_DERIV = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x.
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> &0 < mfd_scalar atlas g x /\
         sqrt(rfs_scalar_grad2 atlas g x) <=
         C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
         abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
         C * mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN Y` THEN ASM_REWRITE_TAC[] THEN
    FIRST
     [UNDISCH_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET U` THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] SUBSET_BALL) THEN
      REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) SUBSET U` THEN
      SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET (annulus (&1 / &4) (&4):real^3->bool)`
      MP_TAC THENL
       [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_TWO_BOUNDS THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]));;

let P2C_CCOMP_DERIV = prove
 (`!top atlas (g:A->real^3^3) C U x.
     riemannian_metric atlas g /\ rfs_c_component (top,atlas) g C U /\ x IN U
     ==> &0 < mfd_scalar atlas g x /\
         sqrt(rfs_scalar_grad2 atlas g x) <=
         C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
         abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
         C * mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
    [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
     ASM_SIMP_TAC[] THEN ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_TWO_BOUNDS THEN
   EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]));;

(* The headline. *)

let P2C_MAX_BOUND = prove
 (`!a C X. a <= max C (&2) /\ &0 <= X ==> a * X <= max C (&2) * X`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let P2C_CANON_DERIV = prove
 (`!u:A->bool. P2C_CANON_DERIV_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "neck"))
   (INST_TYPE [`:A`,`:A`] P2C_NECK_DERIV) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "round"))
   (INST_TYPE [`:A`,`:A`] P2C_ROUND_DERIV) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `C:real`; `eps:real`; `x:A`; `U:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_MIN]; ALL_TAC] THEN
  SUBGOAL_THEN `!X. &0 <= X ==> &2 * X <= max C (&2) * X /\ C * X <= max C (&2) * X`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_MAX_BOUND THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_scalar atlas (g:A->real^3^3) x /\
    ((sqrt(rfs_scalar_grad2 atlas g x) <=
      &2 * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
      abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
      &2 * mfd_scalar atlas g x pow 2) \/
     (sqrt(rfs_scalar_grad2 atlas g x) <=
      C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
      abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
      C * mfd_scalar atlas g x pow 2))`
  MP_TAC THENL
   [UNDISCH_TAC `rfs_canonical_nbhd (top,atlas) (g:A->real^3^3) C eps x U` THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [USE_THEN "neck" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x:A`;
        `e:real^3->A`]) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                     `x:A`] P2C_CAP_DERIV) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `U:A->bool`; `x:A`] P2C_CCOMP_DERIV) THEN
      ASM_SIMP_TAC[];
      USE_THEN "round" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `U:A->bool`;
        `x:A`]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar atlas (g:A->real^3^3) x * sqrt(mfd_scalar atlas g x) /\
                &0 <= mfd_scalar atlas g x pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `mfd_scalar atlas (g:A->real^3^3) x * sqrt(mfd_scalar atlas g x)` th) THEN
    MP_TAC(SPEC `mfd_scalar atlas (g:A->real^3^3) x pow 2` th)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lemma 11.2 for histories, conditional only on P2C_HISTORY_REGULAR. *)

let P2C_LEMMA_11_2_FROM_REGULAR = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_STATEMENT u ==> P2C_LEMMA_11_2_STATEMENT u`,
  MESON_TAC[P2C_LEMMA_11_2_COND; P2C_CANON_DERIV]);;

