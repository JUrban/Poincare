(* ========================================================================= *)
(* Unit pc_p3_s13col (Part 3 proofs; MT Ch 13, Thm 13.2 item 3, in a         *)
(* smoothed form): the smooth radial collapse map xi of the neck annulus     *)
(* onto the capped model, xi(y) = rinv(lam(s)) y/|y| with s = sqrt 2 log|y|  *)
(* and the profile lam of pc_p3_s13fun.  Clauses (f), (g) and (h) of         *)
(* P3_THM_13_2_STATEMENT for xi and the surgery metric gS of pc_p3_s13met.   *)
(* ========================================================================= *)

needs "src/pc_p3_s13met.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The oriented radial profile.  orho(r) is the signed integral              *)
(* of sqrt a from 0 to r, smooth on r > -1 with derivative sqrt a, equal to *)
(* rho for r >= 0; its inverse orinv is smooth on u > orho(-1/2) and equals *)
(* rinv for u >= 0.  This makes rinv o lam smooth where lam reaches 0.      *)
(* ------------------------------------------------------------------------- *)

let p3s_orho = new_definition
 `p3s_orho (g0:real^3->real^3^3) (r:real) =
    real_integral (real_interval[-- &1,r]) (\u. sqrt(p3s_rad_a g0 u)) -
    real_integral (real_interval[-- &1,&0]) (\u. sqrt(p3s_rad_a g0 u))`;;

let p3s_orinv = new_definition
 `p3s_orinv (g0:real^3->real^3^3) (s:real) = @r. -- &1 < r /\ p3s_orho g0 r = s`;;

let P3S_SQRTA_CONT = prove
 (`!g0 A0 s. p3_std_initial g0 A0 ==> (\u. sqrt(p3s_rad_a g0 u)) real_continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_S1_CONTINUOUS THEN
  MATCH_MP_TAC P3S_SQRTA_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_SQRTA_POS = prove
 (`!g0 A0 r. p3_std_initial g0 A0 ==> &0 < sqrt(p3s_rad_a g0 r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN ASM_REWRITE_TAC[]);;

let P3S_ORHO_0 = prove
 (`!g0. p3s_orho g0 (&0) = &0`,
  REWRITE_TAC[p3s_orho; REAL_SUB_REFL]);;

let P3S_ORHO_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ -- &1 < r
             ==> (p3s_orho g0 has_real_derivative sqrt(p3s_rad_a g0 r)) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3s_orho g0 =
    (\r. real_integral (real_interval[-- &1,r]) (\u. sqrt(p3s_rad_a g0 u)) -
         real_integral (real_interval[-- &1,&0]) (\u. sqrt(p3s_rad_a g0 u)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_orho]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(p3s_rad_a g0 r) = sqrt(p3s_rad_a g0 r) - &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MP_TAC(ISPECL [`\u. sqrt(p3s_rad_a g0 u)`; `-- &1`; `r:real`] P2C_INTEGRAL_DERIV_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P3S_SQRTA_CONT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_ORHO_RHO = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r ==> p3s_orho g0 r = p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_orho; p3s_rad_rho] THEN
  MATCH_MP_TAC(REAL_ARITH `b + c = a ==> a - b = c:real`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC P3S_SQRTA_CONT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_ORHO_STRICT = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ -- &1 < r1 /\ r1 < r2
                 ==> p3s_orho g0 r1 < p3s_orho g0 r2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `\r. sqrt(p3s_rad_a g0 r)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC P3S_ORHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC P3S_SQRTA_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_ORHO_INJ = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ -- &1 < r1 /\ -- &1 < r2 /\
                 p3s_orho g0 r1 = p3s_orho g0 r2 ==> r1 = r2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(r1 < r2) /\ ~(r2 < r1) ==> r1 = r2:real`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r1:real`; `r2:real`] P3S_ORHO_STRICT);
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r2:real`; `r1:real`] P3S_ORHO_STRICT)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3S_ORINV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ -- &1 < r ==> p3s_orinv g0 (p3s_orho g0 r) = r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_orinv] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `t:real` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC P3S_ORHO_INJ THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let P3S_ORHO_RINV = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s
             ==> p3s_orho g0 (p3s_rad_rinv g0 s) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`] P3S_ORHO_RHO) THEN
  ASM_REWRITE_TAC[]);;

let P3S_ORINV_RINV = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s ==> p3s_orinv g0 s = p3s_rad_rinv g0 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_ORHO_RINV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
  MATCH_MP_TAC P3S_ORINV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_ORHO_CONT = prove
 (`!g0 A0 a b. p3_std_initial g0 A0 /\ -- &1 < a
               ==> p3s_orho g0 real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `sqrt(p3s_rad_a g0 x)` THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  MATCH_MP_TAC P3S_ORHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_ORHO_ONTO = prove
 (`!g0 A0 u. p3_std_initial g0 A0 /\ p3s_orho g0 (-- &1 / &2) < u
             ==> ?r. -- &1 < r /\ p3s_orho g0 r = u`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= u` THENL
   [EXISTS_TAC `p3s_rad_rinv g0 u` THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`] P3S_RINV) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`] P3S_ORHO_RINV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3s_orho g0`; `-- &1 / &2`; `&0`; `u:real`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[P3S_ORHO_0; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_ORHO_CONT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3S_ORHO_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {r | -- &1 < drop r} (lift o p3s_orho g0 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `\u. sqrt(p3s_rad_a g0 u)` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC P3S_ORHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3S_SQRTA_SMOOTH THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_ORINV_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ -- &1 < r
             ==> (p3s_orinv g0 has_real_derivative inv(sqrt(p3s_rad_a g0 r)))
                 (atreal (p3s_orho g0 r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_orinv g0 (p3s_orho g0 r) = r` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_ORINV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_INVERSE_STRONG_X THEN
  MAP_EVERY EXISTS_TAC [`p3s_orho g0`; `{x:real | x > -- &1}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; real_gt; REAL_OPEN_HALFSPACE_GT] THEN
  REWRITE_TAC[GSYM real_gt; REAL_OPEN_HALFSPACE_GT] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `sqrt(p3s_rad_a g0 x)` THEN
    MATCH_MP_TAC P3S_ORHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3S_ORINV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_ORHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC P3S_SQRTA_POS THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_ORINV_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {u | p3s_orho g0 (-- &1 / &2) < drop u}
                             (lift o p3s_orinv g0 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop y`] P3S_ORHO_ONTO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`lift o p3s_orho g0 o drop`; `{x:real^1 | -- &1 < drop x}`;
                 `lift r0`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_ORHO_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0:real`] P3S_ORHO_DERIV) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DET_1; matrix] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; ARITH; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC P3S_SQRTA_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1->bool`; `u:real^1->bool`; `g:real^1->real^1`] THEN
  STRIP_TAC THEN EXISTS_TAC `u:real^1->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(lift o p3s_orho g0 o drop) (lift r0) IN u` THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^1->real^1` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^1. z IN t /\ w = (lift o p3s_orho g0 o drop) z`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `-- &1 < drop(z:real^1)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop(z:real^1)`] P3S_ORINV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The collapse map xi(y) = rinv(lam(s)) y/|y|, s = sqrt 2                   *)
(* log|y|, lam = p3s_lam (A0 + 4) e.  Its distance profile d(xi y) = lam(s), *)
(* xi = ncinv for s <= 2, xi = 0 for s >= A0 + 4 - e, smoothness on the     *)
(* punctured space, and the range clauses (g) of Thm 13.2 on the neck.     *)
(* ------------------------------------------------------------------------- *)

let p3s_xi = new_definition
 `p3s_xi (g0:real^3->real^3^3) (A0:real) (e:real) (y:real^3) =
    (p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))) * inv(norm y)) % y`;;

let P3S_LAM_A0 = prove
 (`!g0 A0 e. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4
   ==> smooth_map_on (:real^1) (lift o p3s_lam (A0 + &4) e o drop) /\
       (!s. s <= &2 ==> p3s_lam (A0 + &4) e s = (A0 + &4) - s) /\
       (!s. (A0 + &4) - e <= s ==> p3s_lam (A0 + &4) e s = &0) /\
       (!s. &0 <= p3s_lam (A0 + &4) e s) /\
       (!s t. s <= t ==> p3s_lam (A0 + &4) e t <= p3s_lam (A0 + &4) e s) /\
       (!s. &0 <= s ==> p3s_lam (A0 + &4) e s <= A0 + &4) /\
       (!s. (p3s_lam (A0 + &4) e has_real_derivative --(p3s_lam_rho (A0 + &4) e s))
            (atreal s)) /\
       (!s. &0 <= p3s_lam_rho (A0 + &4) e s /\ p3s_lam_rho (A0 + &4) e s <= &1 + &4 * e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3S_LAM THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP P3S_A0_POS) THEN REAL_ARITH_TAC);;

let P3S_LAM_RHO1 = prove
 (`!g0 A0 e s. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ s <= &2
               ==> p3s_lam_rho (A0 + &4) e s = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0 + &4`; `e:real`] P3S_LAM_RHO) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_A0_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* Labels for the facts of P3S_LAM_A0 in the current goal. *)

let P3S_LAM_TAC =
  let lab = ["LS";"LLIN";"LZ";"LNN";"LMONO";"LLE";"LD";"LRB"] in
  fun g0 a0 e ->
    MP_TAC(SPECL [g0; a0; e] P3S_LAM_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC lab (CONJUNCTS th)));;

let P3S_RINV_0 = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> p3s_rad_rinv g0 (&0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[P3S_RHO_0; REAL_LE_REFL]);;

let P3S_NECK_DOM_S = prove
 (`!dl (y:real^3). &0 < dl
     ==> (y IN rfs_neck_dom dl <=>
          ~(y = vec 0) /\ --(inv dl) < sqrt(&2) * log(norm y) /\
          sqrt(&2) * log(norm y) < inv dl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THENL
   [MP_TAC(SPEC `--(inv(sqrt(&2) * dl))` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM(MATCH_MP EXP_LOG th)]) THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * dl) = inv dl / sqrt(&2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `--(a / b) = --a / b`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; P3S_SQRT2_POS] THEN
  REAL_ARITH_TAC);;

let P3S_XI_FACTS = prove
 (`!g0 A0 e (y:real^3). p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ ~(y = vec 0)
   ==> norm(p3s_xi g0 A0 e y) =
       p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))) /\
       p3_std_dist g0 (p3s_xi g0 A0 e y) = p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  ABBREV_TAC `l = p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))` THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN USE_THEN "LNN" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `l:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(p3s_xi g0 A0 e (y:real^3)) = p3s_rad_rinv g0 l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3s_xi; NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_xi g0 A0 e (y:real^3)`]
         P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[]);;

let P3S_XI_NCINV = prove
 (`!g0 A0 e (y:real^3). p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\
                        sqrt(&2) * log(norm y) <= &2
   ==> p3s_xi g0 A0 e y = p3s_ncinv g0 A0 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_xi; p3s_ncinv] THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  USE_THEN "LLIN" (MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - c = a + b - c:real`]);;

let P3S_XI_TIP = prove
 (`!g0 A0 e (y:real^3). p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\
                        A0 + &4 - e <= sqrt(&2) * log(norm y)
   ==> p3s_xi g0 A0 e y = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_xi] THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  USE_THEN "LZ" (MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_RINV_0 th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO]);;

let P3S_COMPOSE_1D = prove
 (`!s t (f:real^3->real) (g:real->real).
     open s /\ open t /\ (!x. x IN s ==> lift(f x) IN t) /\
     smooth_map_on s (\x. lift(f x)) /\ smooth_map_on t (lift o g o drop)
     ==> smooth_map_on s (\x. lift(g(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `t:real^1->bool`; `\x:real^3. lift(f x)`; `g:real->real`]
         SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let P3S_XI_SMOOTH = prove
 (`!g0 A0 e. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4
             ==> smooth_map_on ((:real^3) DELETE vec 0) (p3s_xi g0 A0 e)`,
  REPEAT STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  SUBGOAL_THEN `p3s_orho g0 (-- &1 / &2) < &0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `g0:real^3->real^3^3` P3S_ORHO_0)] THEN
    MATCH_MP_TAC P3S_ORHO_STRICT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0)
                  (\y:real^3. lift(sqrt(&2) * log(norm y)))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; P3S_LIFT_LOGNORM_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0)
                  (\y:real^3. lift(p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[P3S_OPEN_PUNCT; OPEN_UNIV; IN_UNIV] THEN
    USE_THEN "LS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((:real^3) DELETE vec 0)
      (\y:real^3. lift(p3s_orinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_COMPOSE_1D THEN
    EXISTS_TAC `{u:real^1 | p3s_orho g0 (-- &1 / &2) < drop u}` THEN
    ASM_REWRITE_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; IN_ELIM_THM; LIFT_DROP] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LNN" (fun th -> REWRITE_TAC[th]);
      MATCH_MP_TAC P3S_ORINV_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0) (\y:real^3. lift(inv(norm y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\x:real^3. lift(norm x)`]
           SMOOTH_MAP_ON_LIFT_INV) THEN
    BETA_TAC THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; P3S_LIFT_NORM_SMOOTH; IN_DELETE; IN_UNIV; LIFT_DROP;
                NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_xi g0 A0 e =
    (\y:real^3. drop((\y. lift(p3s_orinv g0 (p3s_lam (A0 + &4) e
                              (sqrt(&2) * log(norm y))))) y) %
                (drop((\y. lift(inv(norm y))) y) % y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^3` THEN BETA_TAC THEN
    REWRITE_TAC[p3s_xi; LIFT_DROP; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3S_ORINV_RINV THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "LNN" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[P3S_OPEN_PUNCT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_ID]);;

let P3S_NECK_DOM_PUNCT = prove
 (`!dl. &0 < dl ==> rfs_neck_dom dl SUBSET (:real^3) DELETE vec 0`,
  SIMP_TAC[SUBSET; P3S_NECK_DOM_S; IN_DELETE; IN_UNIV]);;

let P3S_XI_SMOOTH_NECK = prove
 (`!g0 A0 e dl. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ &0 < dl
                ==> smooth_map_on (rfs_neck_dom dl) (p3s_xi g0 A0 e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[P3S_NECK_DOM_PUNCT] THEN
  MATCH_MP_TAC P3S_XI_SMOOTH THEN ASM_REWRITE_TAC[]);;

let P3S_XI_RANGE = prove
 (`!g0 A0 e dl (y:real^3).
     p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ &0 < dl /\ y IN rfs_neck_dom dl
     ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (p3s_xi g0 A0 e y) /\
         (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (p3s_xi g0 A0 e y) = y) /\
         (&0 <= sqrt(&2) * log(norm y)
          ==> &0 <= A0 + &4 - p3_std_dist g0 (p3s_xi g0 A0 e y)) /\
         (A0 + &4 <= sqrt(&2) * log(norm y) ==> p3s_xi g0 A0 e y = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`dl:real`; `y:real^3`] P3S_NECK_DOM_S) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < inv dl` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `&0 <= sqrt(&2) * log(norm(y:real^3))` THENL
     [USE_THEN "LLE" (MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "LLIN" (MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_NCINV) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_NCINV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_TAC THEN
    USE_THEN "LLE" (MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC P3S_XI_TIP THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of xi and the bound                                       *)
(*   |D xi(y) v|^2_g0 <= K^2 |v|^2_cyl0   when 1 <= K and |lam'(s)| <= K,    *)
(* the smoothed form of MT Lemma 12.37 (D xi = 0 where lam = 0).             *)
(* ------------------------------------------------------------------------- *)

let P3S_RADMAP_GEN_DERIV = prove
 (`!(m:real->real) m' (y:real^3).
     ~(y = vec 0) /\ (m has_real_derivative m') (atreal (norm y))
     ==> ((\z. (m(norm z) * inv(norm z)) % z) has_derivative
          (\h. (m(norm y) * inv(norm y)) % h +
               ((m' * inv(norm y) + m(norm y) * --inv(norm y pow 2)) *
                ((y dot h) / norm y)) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (m:real->real) t * inv t) has_real_derivative
     (m' * inv(norm(y:real^3)) + m(norm y) * --inv(norm y pow 2))) (atreal (norm y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:real->real`; `m':real`; `inv:real->real`;
                   `--inv(norm(y:real^3) pow 2)`; `norm(y:real^3)`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `norm(y:real^3)` HAS_REAL_DERIVATIVE_INV_BASIC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (m:real->real) t * inv t`;
                 `m' * inv(norm(y:real^3)) + m(norm y) * --inv(norm y pow 2)`;
                 `\z:real^3. lift(norm z)`; `\h:real^3. lift((y dot h) / norm y)`;
                 `y:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; P2C_NORM_DERIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (m:real->real)(norm z) * inv(norm z)`;
                 `\h:real^3. (m' * inv(norm(y:real^3)) + m(norm y) * --inv(norm y pow 2)) *
                             ((y dot h) / norm y)`;
                 `\z:real^3. z`; `\h:real^3. h`; `y:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; o_DEF] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL];
    REWRITE_TAC[]]);;

let P3S_ORINV_DERIV_NN = prove
 (`!g0 A0 u. p3_std_initial g0 A0 /\ &0 <= u
             ==> (p3s_orinv g0 has_real_derivative
                  inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 u)))) (atreal u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 u`] P3S_ORINV_DERIV) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`] P3S_RINV) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`] P3S_ORHO_RINV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_XI_PROF_DERIV = prove
 (`!g0 A0 e t. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ &0 < t
   ==> ((\t. p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log t))) has_real_derivative
        (inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log t))))) *
         (--(p3s_lam_rho (A0 + &4) e (sqrt(&2) * log t)) * (sqrt(&2) * inv t))))
       (atreal t)`,
  REPEAT STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  SUBGOAL_THEN `(\t. p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log t))) =
                p3s_orinv g0 o (\t. p3s_lam (A0 + &4) e (sqrt(&2) * log t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `w:real` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_ORINV_RINV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LNN" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\t. sqrt(&2) * log t`; `p3s_lam (A0 + &4) e`;
                   `sqrt(&2) * inv t`; `--(p3s_lam_rho (A0 + &4) e (sqrt(&2) * log t))`;
                   `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[];
      USE_THEN "LD" (fun th -> REWRITE_TAC[th])];
    BETA_TAC THEN MATCH_MP_TAC P3S_ORINV_DERIV_NN THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "LNN" (fun th -> REWRITE_TAC[th])]);;

let P3S_XI_DERIV = prove
 (`!g0 A0 e (y:real^3). p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ ~(y = vec 0)
   ==> (p3s_xi g0 A0 e has_derivative
        (\h. (p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))) *
              inv(norm y)) % h +
             (((inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0
                  (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y)))))) *
                (--(p3s_lam_rho (A0 + &4) e (sqrt(&2) * log(norm y))) *
                 (sqrt(&2) * inv(norm y)))) * inv(norm y) +
               p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm y))) *
               --inv(norm y pow 2)) * ((y dot h) / norm y)) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3s_xi g0 A0 e =
    (\z:real^3. ((\t. p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log t))) (norm z) *
                 inv(norm z)) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_xi]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. p3s_rad_rinv g0 (p3s_lam (A0 + &4) e (sqrt(&2) * log t))`;
                 `inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0
                    (p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3))))))) *
                  (--(p3s_lam_rho (A0 + &4) e (sqrt(&2) * log(norm y))) *
                   (sqrt(&2) * inv(norm y)))`;
                 `y:real^3`] P3S_RADMAP_GEN_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_XI_PROF_DERIV THEN
    ASM_REWRITE_TAC[NORM_POS_LT];
    BETA_TAC THEN REWRITE_TAC[]]);;

let P3S_LAM_RHO_ZERO = prove
 (`!g0 A0 e s. p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\
               p3s_lam (A0 + &4) e s = &0
               ==> p3s_lam_rho (A0 + &4) e s = &0`,
  REPEAT STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  MATCH_MP_TAC(REAL_ARITH `--x = &0 ==> x = &0`) THEN
  MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
  MAP_EVERY EXISTS_TAC [`p3s_lam (A0 + &4) e`; `s:real`; `(:real)`] THEN
  REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV] THEN CONJ_TAC THENL
   [USE_THEN "LD" (fun th -> REWRITE_TAC[th]);
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "LNN" (fun th -> REWRITE_TAC[th])]);;

let P3S_JAC_APPLY = prove
 (`!(f:real^M->real^N) f' x v.
     (f has_derivative f') (at x) ==> jacobian f (at x) ** v = f' v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(f':real^M->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let P3S_CYL0_QUAD_POS = prove
 (`!(y:real^3) v. &0 <= v dot (cylinder_flow (&0) y ** v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]);;

let P3S_XI_G0_BOUND = prove
 (`!g0 A0 e K (y:real^3) v.
     p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ ~(y = vec 0) /\ &1 <= K /\
     p3s_lam_rho (A0 + &4) e (sqrt(&2) * log(norm y)) <= K
     ==> (jacobian (p3s_xi g0 A0 e) (at y) ** v) dot
         (g0 (p3s_xi g0 A0 e y) ** (jacobian (p3s_xi g0 A0 e) (at y) ** v)) <=
         K pow 2 * (v dot (cylinder_flow (&0) y ** v))`,
  REPEAT STRIP_TAC THEN
  P3S_LAM_TAC `g0:real^3->real^3^3` `A0:real` `e:real` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP P3S_JAC_APPLY th]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3))) /\
                &0 <= p3s_lam_rho (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "LNN" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "LRB" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:real^3`; `v:real^3`] P3S_CYL0_QUAD_POS) THEN DISCH_TAC THEN
  ABBREV_TAC `l = p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))` THEN
  ABBREV_TAC `rr = p3s_lam_rho (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))` THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 l` THEN
  ASM_CASES_TAC `l = &0` THENL
   [SUBGOAL_THEN `R = &0 /\ rr = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "R" THEN UNDISCH_TAC `l = &0` THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC P3S_RINV_0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "rr" THEN MATCH_MP_TAC P3S_LAM_RHO_ZERO THEN
        EXISTS_TAC `g0:real^3->real^3^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO; REAL_ADD_LID;
                    VECTOR_MUL_LZERO; VECTOR_ADD_LID; MATRIX_VECTOR_MUL_RZERO;
                    DOT_LZERO] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `l:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p3s_xi g0 A0 e (y:real^3) = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT; ASSUME `norm(p3s_xi g0 A0 e (y:real^3)) = R`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3s_xi g0 A0 e y = (R * inv(norm y)) % (y:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p3s_xi] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_xi g0 A0 e (y:real^3)`]
         P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ASSUME `norm(p3s_xi g0 A0 e (y:real^3)) = R`] THEN
  REWRITE_TAC[ASSUME `p3s_xi g0 A0 e y = (R * inv(norm y)) % (y:real^3)`] THEN
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN
  SUBGOAL_THEN `(y:real^3) dot y = norm y pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `R pow 2 * p3s_rad_b g0 R <= &2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `l:real`] P3S_WARP_LE) THEN
    ASM_REWRITE_TAC[p3s_warp] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(R * sqrt(p3s_rad_b g0 R)) pow 2 <= sqrt(&2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((v:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (v dot v)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rr pow 2 <= K pow 2 /\ &1 <= K pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`t = norm(y:real^3)`; `n = (v:real^3) dot v`; `p = (v:real^3) dot y`;
    `aa = p3s_rad_a g0 R`; `bb = p3s_rad_b g0 R`; `sa = sqrt aa`; `s2 = sqrt(&2)`] THEN
  MATCH_MP_TAC(REAL_ARITH `!c. x = b - c /\ &0 <= c ==> x <= b`) THEN
  EXISTS_TAC `&2 * (K pow 2 - rr pow 2) * (p pow 2 / t pow 4) +
              (&2 * K pow 2 - R pow 2 * bb) * ((n - p pow 2 / t pow 2) / t pow 2)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `sa pow 2 = aa` THEN UNDISCH_TAC `s2 pow 2 = &2` THEN
    SUBGOAL_THEN `~(t = &0) /\ ~(sa = &0) /\ ~(R = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]]]);;

(* ------------------------------------------------------------------------- *)
(* Clause (h) of Thm 13.2, |D xi v|^2_gS <= |v|^2_gN on the                  *)
(* neck.  The C^0 part of the closeness gives h^2 (1 - dl) cyl0 <= gN.  For  *)
(* s < 2, xi = ncinv near y, nc o xi = id, and gS is the NEAR form; for     *)
(* s >= 2, s1(xi y) >= 2, gS is the FAR form and phi <= exp(-2 f(2)) pays   *)
(* for the slope 1 + 4 e of lam.                                           *)
(* ------------------------------------------------------------------------- *)

let P3S_NECK_DOM_OPEN = prove
 (`!dl. open(rfs_neck_dom dl)`,
  GEN_TAC THEN REWRITE_TAC[rfs_neck_dom; annulus] THEN
  SUBGOAL_THEN
   `!r1 r2. {x:real^3 | r1 < norm x /\ norm x < r2} =
            {x | x IN (:real^3) /\ lift(norm x) IN {w:real^1 | r1 < drop w /\ drop w < r2}}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  REWRITE_TAC[OPEN_UNIV; REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM] THEN
  REWRITE_TAC[SET_RULE `{z:real^1 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
  MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_OPEN_DROP_LT]);;

let P3S_NECK_CYL_FIELD = prove
 (`!dl. &0 < dl ==> metric_field (rfs_neck_dom dl) (cylinder_flow (&0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; P3S_NECK_DOM_PUNCT;
               P3S_NECK_DOM_OPEN]);;

let P3S_NECK_C0_LOWER = prove
 (`!dl h (gN:real^3->real^3^3) y w.
     &0 < dl /\ &0 < h /\ metric_field (rfs_neck_dom dl) gN /\
     rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% gN y) /\
     y IN rfs_neck_dom dl
     ==> h pow 2 * (&1 - dl) * (w dot (cylinder_flow (&0) y ** w)) <= w dot (gN y ** w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_close_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg dl`; `rfs_neck_dom dl`; `cylinder_flow (&0)`;
                 `\y. inv(h pow 2) %% (gN:real^3->real^3^3) y`;
                 `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P3S_NECK_CYL_FIELD] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% (gN:real^3->real^3^3) y) y) <= dl`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(dl pow 2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:real^3`; `w:real^3`] P3S_CYL0_QUAD_POS) THEN
  BETA_TAC THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `L = lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                    (\y. inv(h pow 2) %% (gN:real^3->real^3^3) y) y` THEN
  ABBREV_TAC `Q0 = w dot (cylinder_flow (&0) y ** w)` THEN
  ABBREV_TAC `QN = w dot ((gN:real^3->real^3^3) y ** w)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `sqrt L * Q0 <= dl * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - dl) * Q0 <= inv(h pow 2) * QN` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `QN = h pow 2 * (inv(h pow 2) * QN)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let P3S_DOT_TRANSP = prove
 (`!(A:real^N^N) x y. x dot (transp A ** y) = (A ** x) dot y`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATRIX_VECTOR_MUL_TRANSP] THEN
  REWRITE_TAC[TRANSP_TRANSP] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  REWRITE_TAC[DOT_LMUL_MATRIX]);;

let P3S_XI_PULLBACK_NEAR = prove
 (`!g0 A0 e (gN:real^3->real^3^3) (y:real^3) v.
     p3_std_initial g0 A0 /\ &0 < e /\ e <= &1 / &4 /\ ~(y = vec 0) /\
     sqrt(&2) * log(norm y) < &2
     ==> (jacobian (p3s_xi g0 A0 e) (at y) ** v) dot
         (mpullback (p3_std_nc g0 A0) gN (p3s_xi g0 A0 e y) **
          (jacobian (p3s_xi g0 A0 e) (at y) ** v)) =
         v dot (gN y ** v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0) /\ sqrt(&2) * log(norm z) < &2}`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `-- &2` P3S_NCINV_DOM_OPEN) THEN
    REWRITE_TAC[REAL_ARITH `-- &2 + &4 = &2`];
    ALL_TAC] THEN
  ABBREV_TAC `W = {z:real^3 | ~(z = vec 0) /\ sqrt(&2) * log(norm z) < &2}` THEN
  SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN W ==> p3_std_nc g0 A0 (p3s_xi g0 A0 e z) = z`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `z:real^3`] P3S_XI_NCINV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_NCINV_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `x = p3s_xi g0 A0 e (y:real^3)` THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0) /\ p3_std_nc g0 A0 x = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_NCINV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_NCINV_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p3s_xi g0 A0 e has_derivative frechet_derivative (p3s_xi g0 A0 e) (at y))
                (at y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `p3s_xi g0 A0 e`]
           SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[P3S_OPEN_PUNCT; P3S_XI_SMOOTH; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p3_std_nc g0 A0 has_derivative frechet_derivative (p3_std_nc g0 A0) (at x))
                (at x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `p3_std_nc g0 A0`]
           SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[P3S_OPEN_PUNCT; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `Dx = frechet_derivative (p3s_xi g0 A0 e) (at (y:real^3))` THEN
  ABBREV_TAC `Dn = frechet_derivative (p3_std_nc g0 A0) (at (x:real^3))` THEN
  SUBGOAL_THEN `!w:real^3. Dn((Dx:real^3->real^3) w) = w` ASSUME_TAC THENL
   [SUBGOAL_THEN `((p3_std_nc g0 A0 o p3s_xi g0 A0 e) has_derivative
                   ((Dn:real^3->real^3) o (Dx:real^3->real^3))) (at y)` ASSUME_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((p3_std_nc g0 A0 o p3s_xi g0 A0 e) has_derivative (\h:real^3. h)) (at y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MP_TAC(ISPEC `W:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`\z:real^3. z`; `d:real`] THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z:real^3. z IN W ==> p z = z`) (concl th))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p3_std_nc g0 A0 o p3s_xi g0 A0 e`;
                   `(Dn:real^3->real^3) o (Dx:real^3->real^3)`; `\h:real^3. h`;
                   `y:real^3`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3s_xi g0 A0 e`; `Dx:real^3->real^3`; `y:real^3`; `v:real^3`]
         P3S_JAC_APPLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `linear(Dn:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[mpullback; P3S_DOT_TRANSP; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let P3S_NEAR_ARITH = prove
 (`!H ph al dl QN QG Q0.
     &0 <= H /\ &0 <= ph /\ ph <= &1 /\ &0 <= al /\ al <= &1 /\ dl <= &1 /\
     QG <= Q0 /\ &0 <= Q0 /\ H * (&1 - dl) * Q0 <= QN
     ==> (ph * al) * QN + (H * ph * (&1 - al) * (&1 - dl)) * QG <= QN`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= H * (&1 - dl) * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= QN` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H * ph * (&1 - al) * (&1 - dl)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(H * ph * (&1 - al) * (&1 - dl)) * QG <=
                (H * ph * (&1 - al) * (&1 - dl)) * Q0`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ph * (&1 - al)) * (H * (&1 - dl) * Q0) <= (ph * (&1 - al)) * QN`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ph * QN <= QN` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `ph * QN <= &1 * QN ==> ph * QN <= QN`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(H * ph * (&1 - al) * (&1 - dl)) * Q0 = (ph * (&1 - al)) * (H * (&1 - dl) * Q0) /\
    (ph * al) * QN + (ph * (&1 - al)) * QN = ph * QN`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_FAR_ARITH = prove
 (`!H ph dl K E QG Q0 QN.
     &0 <= H /\ &0 <= ph /\ ph <= E /\ K pow 2 * E <= &1 /\ dl <= &1 /\
     QG <= K pow 2 * Q0 /\ &0 <= Q0 /\ H * (&1 - dl) * Q0 <= QN
     ==> (H * ph * (&1 - dl)) * QG <= QN`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= H * ph * (&1 - dl)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(H * ph * (&1 - dl)) * QG <= (H * ph * (&1 - dl)) * (K pow 2 * Q0)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ph * K pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E * K pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H * (&1 - dl) * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph * K pow 2) * (H * (&1 - dl) * Q0) <= &1 * (H * (&1 - dl) * Q0)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(H * ph * (&1 - dl)) * (K pow 2 * Q0) =
                (ph * K pow 2) * (H * (&1 - dl) * Q0)`
  ASSUME_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_XI_GS_BOUND = prove
 (`!g0 A0 c q r0 dl h (gN:real^3->real^3^3) e (y:real^3) v.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\
     &0 < dl /\ dl < &1 /\ &0 < h /\ &0 < e /\ e <= &1 / &4 /\
     (&1 + &4 * e) pow 2 * exp(--(&2 * p3s_f c q (&2))) <= &1 /\
     metric_field (rfs_neck_dom dl) gN /\
     rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% gN y) /\
     y IN rfs_neck_dom dl
     ==> (jacobian (p3s_xi g0 A0 e) (at y) ** v) dot
         (p3s_gs g0 A0 c q r0 dl h gN (p3s_xi g0 A0 e y) **
          (jacobian (p3s_xi g0 A0 e) (at y) ** v)) <=
         v dot (gN y ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`dl:real`; `y:real^3`] P3S_NECK_DOM_S) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MP_TAC(SPECL [`dl:real`; `h:real`; `gN:real^3->real^3^3`; `y:real^3`; `v:real^3`]
         P3S_NECK_C0_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`y:real^3`; `v:real^3`] P3S_CYL0_QUAD_POS) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `y:real^3`] P3S_XI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`;
                `A0 + &4 - p3_std_dist g0 (p3s_xi g0 A0 e (y:real^3))`] P3S_PHI_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= p3s_phi c q A0 r0 (A0 + &4 - p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(&2 * p3s_f c q (A0 + &4)))` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `sqrt(&2) * log(norm(y:real^3)) < &2` THENL
   [SUBGOAL_THEN `A0 + &4 - p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3))) =
                  sqrt(&2) * log(norm y)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`] P3S_LAM_A0) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))` o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                  `dl:real`; `h:real`; `gN:real^3->real^3^3`; `p3s_xi g0 A0 e (y:real^3)`]
                 P3S_GS_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `gN:real^3->real^3^3`;
                  `y:real^3`; `v:real^3`] P3S_XI_PULLBACK_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `&1`; `y:real^3`; `v:real^3`]
           P3S_XI_G0_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`;
                    `sqrt(&2) * log(norm(y:real^3))`] P3S_LAM_RHO1) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC P3S_ALPHA THEN
    DISCH_THEN(MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))` o CONJUNCT1 o CONJUNCT2) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= p3s_phi c q A0 r0 (sqrt(&2) * log(norm(y:real^3))) /\
                  p3s_phi c q A0 r0 (sqrt(&2) * log(norm y)) <= &1`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`;
                    `sqrt(&2) * log(norm(y:real^3))`] P3S_PHI_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `--(&2 * p3s_f c q (A0 + &4))` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P3S_NEAR_ARITH THEN
    EXISTS_TAC `v dot (cylinder_flow (&0) y ** v)` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= A0 + &4 - p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`] P3S_LAM_A0) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`&2`; `sqrt(&2) * log(norm(y:real^3))`]
                                  (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))) THEN
                         MP_TAC(SPEC `&2` (CONJUNCT1(CONJUNCT2 th)))) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                `dl:real`; `h:real`; `gN:real^3->real^3^3`; `p3s_xi g0 A0 e (y:real^3)`]
               P3S_GS_FAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`; `&1 + &4 * e`; `y:real^3`;
                `v:real^3`] P3S_XI_G0_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `e:real`] P3S_LAM_A0) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `sqrt(&2) * log(norm(y:real^3))` o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2) THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `&2`;
                `A0 + &4 - p3s_lam (A0 + &4) e (sqrt(&2) * log(norm(y:real^3)))`]
               P3S_PHI_SLACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC P3S_FAR_ARITH THEN
  MAP_EVERY EXISTS_TAC [`&1 + &4 * e`; `exp(--(&2 * p3s_f c q (&2)))`;
                        `v dot (cylinder_flow (&0) y ** v)`] THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The choice of e (slope slack paid by phi) and the collapse               *)
(* clauses (f), (g), (h) of P3_THM_13_2_STATEMENT for xi = p3s_xi g0 A0 e   *)
(* and gS = p3s_gs g0 A0 c q r0 dl h gN.                                    *)
(* ------------------------------------------------------------------------- *)

let P3S_XI_E_CHOICE = prove
 (`!c q. &0 < c /\ &0 < q
         ==> ?e. &0 < e /\ e <= &1 / &4 /\
                 (&1 + &4 * e) pow 2 * exp(--(&2 * p3s_f c q (&2))) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3s_f c q (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_POS; REAL_ARITH `&0 < &2`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ABBREV_TAC `F2 = p3s_f c q (&2)` THEN
  EXISTS_TAC `min (&1 / &4) (F2 / &4)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &4 * min (&1 / &4) (F2 / &4) <= exp F2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + F2` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &4 * min (&1 / &4) (F2 / &4)) pow 2 <= exp F2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp F2 pow 2 * exp(--(&2 * F2)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_NEG_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp F2 pow 2 * exp(--(&2 * F2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P3S_XI_CLAUSES = prove
 (`!g0 A0 c q r0 dl h (gN:real^3->real^3^3) e.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\
     &0 < dl /\ dl < &1 /\ &0 < h /\ &0 < e /\ e <= &1 / &4 /\
     (&1 + &4 * e) pow 2 * exp(--(&2 * p3s_f c q (&2))) <= &1 /\
     riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
     rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% gN y)
     ==> smooth_map_on (rfs_neck_dom dl) (p3s_xi g0 A0 e) /\
         (!y. y IN rfs_neck_dom dl
              ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (p3s_xi g0 A0 e y) /\
                  (sqrt(&2) * log(norm y) <= &0
                   ==> p3_std_nc g0 A0 (p3s_xi g0 A0 e y) = y) /\
                  (&0 <= sqrt(&2) * log(norm y)
                   ==> &0 <= A0 + &4 - p3_std_dist g0 (p3s_xi g0 A0 e y)) /\
                  (A0 + &4 <= sqrt(&2) * log(norm y) ==> p3s_xi g0 A0 e y = vec 0)) /\
         (!y v. y IN rfs_neck_dom dl
                ==> (jacobian (p3s_xi g0 A0 e) (at y) ** v) dot
                    (p3s_gs g0 A0 c q r0 dl h gN (p3s_xi g0 A0 e y) **
                     (jacobian (p3s_xi g0 A0 e) (at y) ** v)) <=
                    v dot (gN y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (gN:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[P3S_NECK_DOM_OPEN]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_XI_SMOOTH_NECK THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P3S_XI_RANGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_XI_GS_BOUND THEN ASM_REWRITE_TAC[]]);;

