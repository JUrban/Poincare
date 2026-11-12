(* ========================================================================= *)
(* Unit pc_p2b_flatknc (Part 2B, MT Lemma 9.65, last step of Claim 9.66):    *)
(* P2B_REQ_FLAT_KNC proves the statement P2B_REQ_FLAT_KNC_STATEMENT of       *)
(* pc_p2b_flatreq: a complete flat Riemannian 3-manifold with                *)
(* Vol B(p,r) >= kappa r^3 for all p and r > 0 has                           *)
(* Vol B(p,r) = 4/3 pi r^3.                                                  *)
(*                                                                           *)
(* Route.  On a flat manifold mfd_rm_norm = 0, so every K > 0 bounds the     *)
(* curvature and the explicit Cheeger-Gromov-Taylor counting CMPT_INJ        *)
(* (pc_cmp_cgt) applies at every scale: for a given radius I take N with     *)
(* 256 <= N kappa, b = 64 N^2 I, r = 16 b and K = 1 / (256 b^2); then        *)
(* exp_p is injective on the tangent ball of radius I, and the CGT endgame   *)
(* (GEOS_INJECTIVE_PARAM and the conjugate radius) gives mfd_inj_ball p I    *)
(* for every I > 0.  The Gunther bound (K = 0) and Bishop (pc_cmp_bg) give   *)
(* 4/3 pi r^3 <= v <= 4/3 pi r^3 for the volume v of B(p,r) supplied         *)
(* by the hypothesis.  MT pp. 226-227 use the deck group of the universal    *)
(* cover instead; the CGT counting is the same argument done locally.  The   *)
(* hypothesis connected_space top of the statement is not used, and          *)
(* everything is pointwise in p.  Non-vacuity: FLT_EUCLID_SANITY (Euclidean  *)
(* R^3 with kappa = 4/3 pi).                                                 *)
(* ========================================================================= *)

needs "src/pc_cmp_cgt.ml";;
needs "src/pc_cmp_gunther.ml";;
needs "src/pc_p2b_flatreq.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Flatness facts.  In real^3 there are planes (basis 1 and basis 2 are not  *)
(* collinear with 0), so at a flat point the curvature norm mfd_rm_norm, the *)
(* sup of the absolute sectional curvatures over all planes, is 0, and every *)
(* K >= 0 bounds it on every ball.                                           *)
(* ========================================================================= *)

let FLT_NONCOLLINEAR = prove
 (`~collinear {vec 0:real^3,basis 1,basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  X_GEN_TAC `c:real` THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$2`) THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let FLT_RM_NORM_FLAT = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (y:A).
        (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g y u v = &0)
        ==> mfd_rm_norm atlas g y = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  SUBGOAL_THEN
   `{abs(mfd_sectional atlas (g:A->real^3^3) y u v) | u,v | ~collinear {vec 0,u,v}} =
    {&0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `z:real` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[REAL_ABS_0];
      DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN
      ASM_SIMP_TAC[FLT_NONCOLLINEAR; REAL_ABS_0]];
    REWRITE_TAC[SUP_SING]]);;

let FLT_FLAT_RM_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x r K.
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g y u v = &0) /\ &0 <= K
        ==> !y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x r` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `y:A`]
    FLT_RM_NORM_FLAT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Model-volume bounds and the counting inequality.  For K >= 0: sinh-type   *)
(* lower bound u <= cmp_sn (--K) u, hence |B(0,b)| <= V_{-K}(b); for K r^2   *)
(* <= 1 the bound cmp_sn (--K) t ^2 <= 2 t^2 gives V_{-K}(r) <= 2 |B(0,r)|   *)
(* in dimension 3.  With b > 0, r = 16 b, K = 1 / (256 b^2) and 256 <= N     *)
(* kappa this yields the counting hypothesis of CMPT_INJ for v0 = kappa r^3  *)
(* (FLT_COUNT).                                                              *)
(* ========================================================================= *)

(* FLT_CS_NEG_LOWER and FLT_SN_NEG_LOWER: copied from pc_p2b_capfix        *)
(* (P2BF_CS_NEG_BOUNDS and P2BF_SN_NEG_BOUNDS, first halves) to avoid the  *)
(* load closure of that unit.                                              *)

let FLT_CS_NEG_LOWER = prove
 (`!K u. &0 <= K /\ &0 <= u ==> &1 <= cmp_cs (--K) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; CMP_CS_FLAT; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  SUBGOAL_THEN `&0 <= sqrt K * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `x = sqrt K * u` THEN
  SUBGOAL_THEN `&0 < exp x /\ exp(--x) = inv(exp x) /\ &1 <= exp x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_NEG] THEN
    MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `a = exp x` THEN
  SUBGOAL_THEN `a + inv a - &2 = (a - &1) pow 2 / a` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (a - &1) pow 2 / a` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let FLT_SN_NEG_LOWER = prove
 (`!K u. &0 <= K /\ &0 <= u ==> u <= cmp_sn (--K) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\v. cmp_sn (--K) v - v`; `\v. cmp_cs (--K) v - &1`;
                 `{v:real | &0 <= v}`; `&0`; `u:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[CMP_SN_ZERO; REAL_SUB_REFL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `v:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      X_GEN_TAC `v:real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`K:real`; `v:real`] FLT_CS_NEG_LOWER) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let FLT_VMODEL_LOWER = prove
 (`!K b. &0 <= K /\ &0 <= b
         ==> measure(ball(vec 0:real^N,b)) <= cmp_vmodel (:N) (--K) b`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CMP_VMODEL_FLAT] THEN
  REWRITE_TAC[cmp_vmodel; CMP_SN_FLAT] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[ETA_AX; CMPV_SN_CONTINUOUS_ON];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN BETA_TAC THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[FLT_SN_NEG_LOWER]]);;

let FLT_VMODEL_UPPER = prove
 (`!K r. &0 <= K /\ &0 < r /\ K * r pow 2 <= &1
         ==> cmp_vmodel (:3) (--K) r <= &2 * measure(ball(vec 0:real^3,r))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CMP_VMODEL_FLAT; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[cmp_vmodel; CMP_SN_FLAT; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,r]) (\t. cmp_sn (--K) t pow 2) <=
    &2 * real_integral (real_interval[&0,r]) (\t. t pow 2)`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\t:real. t pow 2`; `&2`; `real_interval[&0,r]`]
      REAL_INTEGRAL_LMUL)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[ETA_AX; CMPV_SN_CONTINUOUS_ON];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN BETA_TAC THEN
      STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
       [ASM_REWRITE_TAC[CMP_SN_ZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      MATCH_MP_TAC CMP_SN_UPPER_NEG_TWO THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * r pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&3 * measure(ball(vec 0:real^3,&1))`;
                 `real_integral (real_interval[&0,r]) (\t. cmp_sn (--K) t pow 2)`;
                 `&2 * real_integral (real_interval[&0,r]) (\t. t pow 2)`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POS; MEASURE_POS_LE; MEASURABLE_BALL];
    REAL_ARITH_TAC]);;

let FLT_SQRT2_CUBE = prove
 (`sqrt(&2) pow 3 <= &3`,
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ sqrt(&2) pow 2 = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) pow 3 = &2 * sqrt(&2)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let FLT_COUNT_ALG = prove
 (`!s M2 X Y Vr Vb n k r3 p.
        &0 <= s /\ s <= &3 /\ M2 = &8 * X /\ &0 < X /\ &0 <= Vr /\
        Vr <= &2 * Y /\ Y = &4 / &3 * p * r3 /\ p < &4 /\ &0 < r3 /\
        &256 <= n * k /\ X <= Vb
        ==> s * M2 * Vr < n * (k * r3) * Vb`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s * M2 * Vr <= &3 * M2 * (&2 * Y)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * M2 * (&2 * Y) = (&64 * p) * (X * r3)` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X * r3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&64 * p) * (X * r3) < &256 * (X * r3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&256 * (X * r3) <= (n * k) * (X * r3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n * k * r3) * X <= (n * k * r3) * Vb` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (n * k) * r3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let FLT_COUNT = prove
 (`!kappa N b.
        &0 < kappa /\ &256 <= &N * kappa /\ &0 < b
        ==> sqrt(&2) pow dimindex(:3) * measure(ball(vec 0:real^3,&2 * b)) *
            cmp_vmodel (:3) (--inv(&256 * b pow 2)) (&16 * b) <
            &N * (kappa * (&16 * b) pow 3) * cmp_vmodel (:3) (--inv(&256 * b pow 2)) b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIMINDEX_3] THEN
  ABBREV_TAC `K = inv(&256 * b pow 2)` THEN ABBREV_TAC `r = &16 * b` THEN
  SUBGOAL_THEN `&0 < K /\ K * r pow 2 = &1 /\ &0 < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "r"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `r:real`] FLT_VMODEL_UPPER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`K:real`; `b:real`] (INST_TYPE [`:3`,`:N`] FLT_VMODEL_LOWER)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`K:real`; `r:real`] (INST_TYPE [`:3`,`:N`] FLT_VMODEL_LOWER)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `measure(ball(vec 0:real^3,b)) = &4 / &3 * pi * b pow 3 /\
    measure(ball(vec 0:real^3,r)) = &4 / &3 * pi * r pow 3 /\
    measure(ball(vec 0:real^3,&2 * b)) = &4 / &3 * pi * (&2 * b) pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC VOLUME_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b pow 3 /\ &0 < r pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC PI2_BOUNDS THEN MP_TAC PI_POS THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &4 / &3 * pi * b pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 / &3 * pi * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC FLT_COUNT_ALG THEN
  MAP_EVERY EXISTS_TAC [`&4 / &3 * pi * b pow 3`; `&4 / &3 * pi * r pow 3`; `pi`] THEN
  ASM_REWRITE_TAC[FLT_SQRT2_CUBE] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN CONV_TAC REAL_RING);;


(* ========================================================================= *)
(* Injectivity at every scale.  For a given radius i0 > 0 choose N with 256  *)
(* < N kappa, b = 64 N^2 i0, r = 16 b, K = 1 / (256 b^2) and v0 = kappa      *)
(* r^3: every hypothesis of CMPT_INJ holds (FLT_COUNT for the counting), so  *)
(* exp_x o E is injective on ball(0,i0) (FLT_PSI_INJ).  The endgame of       *)
(* CMPT_CGT_GEN (GEOS_INJECTIVE_PARAM, the conjugate radius                  *)
(* CMP_CONJUGATE_RADIUS with K' = (pi / (2 i0))^2, sec = 0 <= K') then       *)
(* gives mfd_inj_ball x i0 (FLT_INJ_BALL).  Only the volume growth at x is   *)
(* used.                                                                     *)
(* ========================================================================= *)

let FLT_PSI_INJ = prove
 (`!top atlas (g:A->real^3^3) (x:A) (E:real^3^3) kappa i0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g y u v = &0) /\
        x IN topspace top /\ mfd_orthonormal_frame g x E /\ &0 < kappa /\
        (!r. &0 < r
             ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
                     kappa * r pow 3 <= v) /\
        &0 < i0
        ==> !w1 w2. norm w1 < i0 /\ norm w2 < i0 /\
                    cmp_psi (top,atlas) g x E w1 = cmp_psi (top,atlas) g x E w2
                    ==> w1 = w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `kappa:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num` o SPEC `&256`) THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; ARITH_RULE `n < 1 <=> n = 0`] THEN DISCH_TAC THEN
    UNDISCH_TAC `&256 < &N * kappa` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b = &64 * &N pow 2 * i0` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&16 * b`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&256 * b pow 2) /\ &256 * inv(&256 * b pow 2) * b pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top (top closure_of mfd_ball (top,atlas) (g:A->real^3^3) x (&16 * b))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN mfd_ball (top,atlas) (g:A->real^3^3) x (&16 * b)
        ==> mfd_rm_norm atlas g y <= inv(&256 * b pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLT_FLAT_RM_BALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`kappa:real`; `N:num`; `b:real`] FLT_COUNT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MATCH_MP_TAC CMPT_INJ THEN
  MAP_EVERY EXISTS_TAC [`inv(&256 * b pow 2)`; `&16 * b`; `kappa * (&16 * b) pow 3`;
                        `v:real`; `b:real`; `N:num`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let FLT_INJ_BALL = prove
 (`!top atlas (g:A->real^3^3) (x:A) kappa.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g y u v = &0) /\
        x IN topspace top /\ &0 < kappa /\
        (!r. &0 < r
             ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
                     kappa * r pow 3 <= v)
        ==> !i0. &0 < i0 ==> mfd_inj_ball (top,atlas) g x i0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i0:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^3^3`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `E:real^3^3`; `kappa:real`; `i0:real`]
    FLT_PSI_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `K' = (pi / (&2 * i0)) pow 2` THEN
  SUBGOAL_THEN `&0 < K' /\ pi / sqrt K' = &2 * i0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < pi / (&2 * i0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "K'" THEN ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE] THEN
    MP_TAC PI_POS THEN UNDISCH_TAC `&0 < i0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^3^3) x (&2 * i0) SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPQ_COMPACT_DOM THEN ASM_SIMP_TAC[CMPZ_COMPLETE_CLOSURE_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^3^3) x i0 SUBSET mfd_tball g x (&2 * i0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^3^3) x i0 SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[mfd_inj_ball] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN ASM_REWRITE_TAC[GEOI_TBALL_OPEN] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^3^3) x` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^3^3) x` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`v1:real^3`; `v2:real^3`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
    SUBGOAL_THEN `!u:real^3. (E:real^3^3) ** (matrix_inv E ** u) = u` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:real^3. norm(matrix_inv(E:real^3^3) ** u) = mfd_tnorm (g:A->real^3^3) x u`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real^3` THEN
      MP_TAC(ISPECL [`g:A->real^3^3`; `x:A`; `E:real^3^3`; `matrix_inv(E:real^3^3) ** u`]
        CMPP_TNORM_FRAME) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `matrix_inv(E:real^3^3) ** v1 = matrix_inv E ** v2` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `i0:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "cmp_psi" with Failure _ -> false))
          (concl th))) THEN
      ASM_REWRITE_TAC[cmp_psi];
      DISCH_THEN(MP_TAC o AP_TERM `\u:real^3. (E:real^3^3) ** u`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_CONJUGATE_RADIUS) THEN
  REWRITE_TAC[CMP_CONJUGATE_RADIUS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`; `x:A`; `K':real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:A`; `e1:real^3`; `e2:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x (&2 * i0)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_sectional atlas (g:A->real^3^3) y e1 e2 = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`v1:real^3`; `h:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v1:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&2 * i0`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                             with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]);;


(* ========================================================================= *)
(* The ball volume and the main theorem.  With the injectivity radius        *)
(* infinite, the Gunther bound CMPU_GUNTHER_MAIN at K = 0 gives |B(0,r)| <=  *)
(* v, Bishop (CMP_T3_BISHOP_GROMOV_P2B with r1 = r2 = r) gives v <= 4/3 pi   *)
(* r^3, and |B(0,r)| = 4/3 pi r^3 (VOLUME_BALL); so the volume certificate   *)
(* of the hypothesis is the Euclidean value.                                 *)
(* ========================================================================= *)

let FLT_BALL_VOLUME = prove
 (`!top atlas (g:A->real^3^3) (p:A) kappa r v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g y u v = &0) /\
        p IN topspace top /\ &0 < kappa /\
        (!r. &0 < r
             ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r) v /\
                     kappa * r pow 3 <= v) /\
        &0 < r /\ mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r) v
        ==> v = &4 / &3 * pi * r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= v /\ v <= a ==> v = a`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `cmp_vmodel (:3) (&0) r <= v` MP_TAC THENL
     [MATCH_MP_TAC CMPU_GUNTHER_MAIN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `p:A`] THEN
      ASM_REWRITE_TAC[SQRT_0; REAL_MUL_LZERO; PI_POS_LE; REAL_LE_REFL] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `p:A`; `kappa:real`] FLT_INJ_BALL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`y:A`; `e1:real^3`; `e2:real^3`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
         [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) p r` THEN
          REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                                   with Failure _ -> false)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[CMP_VMODEL_FLAT; REAL_LT_IMP_LE; VOLUME_BALL]];
    MP_TAC(ISPEC `(:A)` CMP_T3_BISHOP_GROMOV_P2B) THEN
    REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                               `g:A->real^3^3`; `p:A`; `r:real`; `r:real`;
                               `v:real`; `v:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MAP_EVERY X_GEN_TAC [`y:A`; `e1:real^3`; `e2:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]]]);;

(* The main theorem: the statement of pc_p2b_flatreq. *)

let P2B_REQ_FLAT_KNC = prove
 (`!w:B->bool. P2B_REQ_FLAT_KNC_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_FLAT_KNC_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `kappa:real`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`p:B`; `r:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?v. mfd_has_volume (top,atlas) (g:B->real^3^3) (mfd_ball (top,atlas) g p r) v /\
        kappa * r pow 3 <= v`
  (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `v = &4 / &3 * pi * r pow 3` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] FLT_BALL_VOLUME) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `p:B`; `kappa:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Non-vacuity.  Euclidean R^3 (topology euclidean, the identity atlas       *)
(* open_set_atlas (:real^3), metric mat 1) satisfies every hypothesis of     *)
(* P2B_REQ_FLAT_KNC_STATEMENT with kappa = 4/3 pi: it is Hausdorff and       *)
(* connected, the Riemannian distance is the Euclidean one                   *)
(* (MFD_DIST_EUCLIDEAN), so closed balls are compact and the balls are       *)
(* Euclidean balls of measure 4/3 pi r^3 (MFD_HAS_VOLUME_EUCLIDEAN), and the *)
(* Riemann tensor of a constant metric vanishes (LRIEMANN_FLAT).             *)
(* ========================================================================= *)

let FLT_EUCLID_BALL = prove
 (`!(x:real^3) r.
        mfd_ball (euclidean,open_set_atlas (:real^3)) (\x. mat 1) x r = ball(x,r) /\
        mfd_cball (euclidean,open_set_atlas (:real^3)) (\x. mat 1) x r = cball(x,r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(:real^3)` MFD_DIST_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_ball; mfd_cball; EXTENSION; IN_ELIM_THM; IN_BALL; IN_CBALL]);;

let FLT_EUCLID_SECTIONAL = prove
 (`!(x:real^3) u v. mfd_sectional (open_set_atlas (:real^3)) (\x. mat 1) x u v = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_sectional; GEOL_EUCLID_FACTS; SND] THEN
  SUBGOAL_THEN
   `metric_local (open_set_atlas (:real^3)) ((:real^3),(\x:real^3. x)) (\x. mat 1) =
    (\y. mat 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GEOL_EUCLID_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[lsectional; LRIEMANN_FLAT; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO;
              real_div; REAL_MUL_LZERO]);;

let FLT_EUCLID_COMPLETE = prove
 (`mfd_complete (euclidean,open_set_atlas (:real^3)) (\x:real^3. mat 1)`,
  REWRITE_TAC[mfd_complete; FLT_EUCLID_BALL; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL]);;

let FLT_EUCLID_CONNECTED = prove
 (`connected_space (euclidean:(real^3)topology)`,
  REWRITE_TAC[GSYM CONNECTED_IN_TOPSPACE; TOPSPACE_EUCLIDEAN; CONNECTED_IN_EUCLIDEAN;
              CONNECTED_UNIV]);;

let FLT_EUCLID_VOLUME = prove
 (`!(p:real^3) r.
        &0 <= r
        ==> mfd_has_volume (euclidean,open_set_atlas (:real^3)) (\x. mat 1)
              (mfd_ball (euclidean,open_set_atlas (:real^3)) (\x. mat 1) p r)
              (&4 / &3 * pi * r pow 3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FLT_EUCLID_BALL] THEN
  MP_TAC(ISPECL [`(:real^3)`; `ball(p:real^3,r)`; `&4 / &3 * pi * r pow 3`]
    MFD_HAS_VOLUME_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL; VOLUME_BALL]);;

(* The hypotheses of P2B_REQ_FLAT_KNC_STATEMENT are satisfiable on a       *)
(* nonempty space, so the main theorem is not vacuous.                     *)

let FLT_EUCLID_SANITY = prove
 (`?top atlas (g:real^3->real^3^3) kappa.
        ~(topspace top = {}) /\
        hausdorff_space top /\ connected_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &0) /\
        &0 < kappa /\
        (!p r. p IN topspace top /\ &0 < r
               ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r) v /\
                       kappa * r pow 3 <= v)`,
  MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `(\x. mat 1):real^3->real^3^3`; `&4 / &3 * pi`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; UNIV_NOT_EMPTY; GEOL_EUCLID_FACTS;
              FLT_EUCLID_COMPLETE; FLT_EUCLID_SECTIONAL; FLT_EUCLID_CONNECTED] THEN
  CONJ_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN EXISTS_TAC `&4 / &3 * pi * r pow 3` THEN
    ASM_SIMP_TAC[FLT_EUCLID_VOLUME; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

