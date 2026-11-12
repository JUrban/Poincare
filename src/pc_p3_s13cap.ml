(* ========================================================================= *)
(* Unit pc_p3_s13cap (Part 3 proofs; MT Ch 13, section 13.3.2):            *)
(* positive curvature of the surgery metric on the cap s1 >= 2, where      *)
(* gS = h^2 (1 - dl) phi(s1) g0 is rotationally symmetric.  The model:      *)
(* for g0 at x (not the tip) with d = p3_std_dist g0 and w the warping      *)
(* function, |dd| = 1, Hess d = (w'/w)(g0 - dd dd), and on g0-orthonormal  *)
(* pairs K = K_tan (1 - sg) + K_rad sg with sg = dd(u)^2 + dd(v)^2.  Hence *)
(* for F = Fr(s1),                                                          *)
(*   e^{-2F} Khat = (1 - sg)(K_tan - 2 F' W - F'^2) + sg (K_rad + F'' - F'W) *)
(* with W = w'/w.  The conformal exponent is cfr = -(1/2) log phi.  Both   *)
(* brackets are positive: on [2, A0 + 4 - r0) where cfr = f because         *)
(* f'' > f' W once q > 2 L + L^2 / w(r0/2) (L = A0 + 4; this q depends on  *)
(* g0, repairing MT 13.3.2, which applies Cor 13.12 for near-product        *)
(* metrics to the cap) and K_tan >= kappa > 0 with f' <= c q / 4 small; on  *)
(* the blend [L - r0, L - r0/2] where K_tan = K_rad = 1/4 (round region)    *)
(* and |cfr'|, |cfr''| <= B c; near the tip gS is a constant multiple of    *)
(* the round g0.  Headline P3S_CAP_GS (positivity of mfd_sectional of gS   *)
(* where s1 > 2, for r0 fixed, all q >= Q0 and c <= cm(q)).                 *)
(*                                                                           *)
(* Contents: the Hessian of d; the sigma form and the cap identity; W        *)
(* bounds, K_tan, K_rad; cfr and its derivative bounds; positivity on the    *)
(* three regions and the headline.                                           *)
(* ========================================================================= *)

needs "src/pc_p3_s13plane.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The differential, gradient and Hessian of the distance d                 *)
(* from the tip for g0, away from the tip.                                  *)
(* ------------------------------------------------------------------------- *)

let P3S_G0_FIELD_PUNCT = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> metric_field ((:real^3) DELETE vec 0) g0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[P3S_OPEN_PUNCT; SUBSET_UNIV] THEN
  MATCH_MP_TAC P3S_STD_METRIC_FIELD THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_D_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on ((:real^3) DELETE vec 0) (\z. lift(p3_std_dist g0 z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP P3S_ROT_DIST_SMOOTH th)]));;

let P3S_G0_CDF_D = prove
 (`!g0 A0 (x:real^3) a.
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_cdf (p3_std_dist g0) x a =
         sqrt(p3s_rad_a g0 (norm x)) * (a dot x) / norm x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cdf] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_DIST_HAS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP]);;

let P3S_G0_CGRAD_D = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_cgrad g0 (p3_std_dist g0) x =
         (inv(sqrt(p3s_rad_a g0 (norm x))) * inv(norm x)) % x /\
         p3s_cdf (p3_std_dist g0) x (p3s_cgrad g0 (p3_std_dist g0) x) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3s_cgrad g0 (p3_std_dist g0) x =
                (inv(sqrt(p3s_rad_a g0 (norm x))) * inv(norm x)) % (x:real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_CGRAD_UNIQUE THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_G0_FIELD_PUNCT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV] THEN
      MATCH_MP_TAC P3S_D_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `w:real^3`;
                    `(inv(sqrt(p3s_rad_a g0 (norm x))) * inv(norm x)) % (x:real^3)`]
                   P3S_ROT_BIL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `w:real^3`]
                   P3S_G0_CDF_D) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2] THEN
      UNDISCH_TAC `sqrt (p3s_rad_a g0 (norm(x:real^3))) pow 2 = p3s_rad_a g0 (norm x)` THEN
      UNDISCH_TAC `&0 < sqrt (p3s_rad_a g0 (norm(x:real^3)))` THEN
      UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                `(inv(sqrt(p3s_rad_a g0 (norm x))) * inv(norm x)) % (x:real^3)`]
               P3S_G0_CDF_D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DOT_LMUL; GSYM NORM_POW_2] THEN
  UNDISCH_TAC `&0 < sqrt (p3s_rad_a g0 (norm(x:real^3)))` THEN
  UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let P3S_Q_A_DERIV = prove
 (`!g0 A0 t. p3_std_initial g0 A0 /\ &0 < t
             ==> ((\t. sqrt(p3s_rad_a g0 t) * inv t) has_real_derivative
                  (real_derivative (p3s_rad_a g0) t / (&2 * sqrt(p3s_rad_a g0 t))) / t -
                  sqrt(p3s_rad_a g0 t) / t pow 2) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL P3S_AB_DERIVS)))
    `((\t. sqrt(p3s_rad_a (g0:real^3->real^3^3) t) * inv t) has_real_derivative f')
     (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(sqrt(p3s_rad_a g0 t) = &0)` THEN
  UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

let P3S_G0_CD2F_D = prove
 (`!g0 A0 (x:real^3) a b.
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_cd2f (p3_std_dist g0) x a b =
         (sqrt(p3s_rad_a g0 (norm x)) * inv(norm x)) * (b dot a) +
         (((real_derivative (p3s_rad_a g0) (norm x) /
            (&2 * sqrt(p3s_rad_a g0 (norm x)))) / norm x -
           sqrt(p3s_rad_a g0 (norm x)) / norm x pow 2) / norm x * (x dot a)) *
         (b dot x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cd2f] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `Q = \t. sqrt(p3s_rad_a g0 t) * inv t` THEN
  ABBREV_TAC `Q1 = (real_derivative (p3s_rad_a g0) (norm(x:real^3)) /
                    (&2 * sqrt(p3s_rad_a g0 (norm x)))) / norm x -
                   sqrt(p3s_rad_a g0 (norm x)) / norm x pow 2` THEN
  SUBGOAL_THEN `(Q has_real_derivative Q1) (atreal (norm(x:real^3)))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "Q1"] THEN MATCH_MP_TAC P3S_Q_A_DERIV THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0)
               ==> frechet_derivative (\x. lift(p3_std_dist g0 x)) (at z) b =
                   drop(lift((Q:real->real)(norm z))) % lift(b dot z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_DIST_HAS_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[LIFT_DROP; GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. frechet_derivative (\x. lift(p3_std_dist g0 x)) (at z) b) has_derivative
     (\h. (Q:real->real)(norm(x:real^3)) % lift(b dot h) +
          ((Q1 / norm x) * (x dot h)) % lift(b dot x))) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z:real^3. drop(lift((Q:real->real)(norm z))) % lift(b dot z)` THEN
    EXISTS_TAC `norm(x:real^3)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `dist(z:real^3,x) < norm x` THEN ASM_REWRITE_TAC[DIST_0] THEN
      NORM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`\z:real^3. (Q:real->real)(norm z)`; `\h:real^3. (Q1 / norm(x:real^3)) * (x dot h)`;
                   `\z:real^3. lift(b dot z)`; `\h:real^3. lift(b dot h)`; `x:real^3`]
                  HAS_DERIVATIVE_MUL_AT) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
      MP_TAC(ISPECL [`Q:real->real`; `Q1:real`; `x:real^3`] P3S_RADIAL_DERIV) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  EXPAND_TAC "Q" THEN REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let P3S_G0_HESS_D = prove
 (`!g0 A0 (x:real^3) a b.
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_chess g0 (p3_std_dist g0) x a b =
         (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))) *
         p3s_rad_b g0 (norm x) * ((a dot b) - (a dot x) * (b dot x) / norm x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_chess] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `a:real^3`; `b:real^3`]
         P3S_G0_CD2F_D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                `christoffel g0 x (a:real^3) b`] P3S_G0_CDF_D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `a:real^3`; `b:real^3`]
         P3S_G0_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[P3S_RS_M1_EQ; P3S_RS_M2_EQ; P3S_RS_M3_EQ; P3S_RS_F1_EQ] THEN
  REWRITE_TAC[DOT_LADD; DOT_LMUL; GSYM NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN
  MAP_EVERY ABBREV_TAC
   [`r = norm(x:real^3)`; `aa = p3s_rad_a g0 r`; `bb = p3s_rad_b g0 r`;
    `da = real_derivative (p3s_rad_a g0) r`; `db = real_derivative (p3s_rad_b g0) r`;
    `sa = sqrt aa`; `sb = sqrt bb`] THEN
  UNDISCH_TAC `sa pow 2 = aa` THEN UNDISCH_TAC `sb pow 2 = bb` THEN
  UNDISCH_TAC `&0 < sa` THEN UNDISCH_TAC `&0 < sb` THEN UNDISCH_TAC `&0 < r` THEN
  UNDISCH_TAC `&0 < aa` THEN UNDISCH_TAC `&0 < bb` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The curvature of g0 on orthonormal pairs in the sg form, and              *)
(* the conformal curvature of e^{-2F} g0 for F = Fr(A0 + 4 - d), as an      *)
(* exact identity (no perturbation).                                         *)
(* ------------------------------------------------------------------------- *)

let P3S_G0_SEC_ON = prove
 (`!g0 A0 (x:real^3) u v.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\
     u dot (g0 x ** u) = &1 /\ v dot (g0 x ** v) = &1 /\ u dot (g0 x ** v) = &0
     ==> lsectional g0 x u v =
         p3s_rs_ktan g0 (norm x) *
           (&1 - (p3s_cdf (p3_std_dist g0) x u pow 2 + p3s_cdf (p3_std_dist g0) x v pow 2)) +
         p3s_rs_krad g0 (norm x) *
           (p3s_cdf (p3_std_dist g0) x u pow 2 + p3s_cdf (p3_std_dist g0) x v pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
         P3S_G0_SECTIONAL) THEN
  ASM_REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`] P3S_G0_CDF_D) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`] P3S_G0_CDF_D) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `u:real^3`]
         P3S_ROT_BIL) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`; `v:real^3`]
         P3S_ROT_BIL) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
         P3S_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`r = norm(x:real^3)`; `aa = p3s_rad_a g0 r`; `bb = p3s_rad_b g0 r`;
    `sa = sqrt aa`; `kt = p3s_rs_ktan g0 r`; `kr = p3s_rs_krad g0 r`;
    `pu = (u:real^3) dot x`; `pv = (v:real^3) dot x`; `nu = (u:real^3) dot u`;
    `nv = (v:real^3) dot v`; `m = (u:real^3) dot v`] THEN
  REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  UNDISCH_TAC `sa pow 2 = aa` THEN UNDISCH_TAC `&0 < r` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  CONV_TAC REAL_FIELD);;

let P3S_FR_SHIFT = prove
 (`!(Fr:real->real) Fr1 Fr2 A0 t0.
     (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (A0 + &4 - t0))
     ==> (!t. ((\t. Fr(A0 + &4 - t)) has_real_derivative --(Fr1(A0 + &4 - t))) (atreal t)) /\
         ((\t. --(Fr1(A0 + &4 - t))) has_real_derivative Fr2) (atreal t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. ((\t. A0 + &4 - t) has_real_derivative --(&1)) (atreal t)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV `((\t. A0 + &4 - t) has_real_derivative f') (atreal t)`)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\t. A0 + &4 - t`; `Fr:real->real`; `--(&1)`;
                   `(Fr1:real->real)(A0 + &4 - t)`; `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\t. A0 + &4 - t`; `\u. --((Fr1:real->real) u)`; `--(&1)`;
                   `--(Fr2:real)`; `t0:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ANTS_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]]);;

let P3S_CAP_KHAT = prove
 (`!g0 A0 (Fr:real->real) Fr1 Fr2 (x:real^3) u v.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\
     smooth_map_on (:real^1) (lift o Fr o drop) /\
     (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (A0 + &4 - p3_std_dist g0 x)) /\
     ~collinear {vec 0,u,v}
     ==> ?sg. &0 <= sg /\ sg <= &1 /\
              exp(--(&2 * Fr(A0 + &4 - p3_std_dist g0 x))) *
              lsectional (\z. exp(--(&2 * Fr(A0 + &4 - p3_std_dist g0 z))) %% g0 z) x u v =
              (&1 - sg) *
              (p3s_rs_ktan g0 (norm x) -
               &2 * Fr1(A0 + &4 - p3_std_dist g0 x) *
               (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))) -
               Fr1(A0 + &4 - p3_std_dist g0 x) pow 2) +
              sg *
              (p3s_rs_krad g0 (norm x) + Fr2 -
               Fr1(A0 + &4 - p3_std_dist g0 x) *
               (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^3) DELETE vec 0) /\ (x:real^3) IN (:real^3) DELETE vec 0 /\
                metric_field ((:real^3) DELETE vec 0) g0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV] THEN
    MATCH_MP_TAC P3S_G0_FIELD_PUNCT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Fr:real->real`; `Fr1:real->real`; `Fr2:real`; `A0:real`;
                `p3_std_dist g0 (x:real^3)`] P3S_FR_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "S2")) THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0)
                  (\z. lift((Fr:real->real)(A0 + &4 - p3_std_dist g0 z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_S1_COMP_SMOOTH THEN ASM_REWRITE_TAC[P3S_OPEN_PUNCT; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0) (\z. lift(p3_std_dist g0 z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_D_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0)
                  (\z. exp(--(&2 * (Fr:real->real)(A0 + &4 - p3_std_dist g0 z))) %% g0 z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `g0:real^3->real^3^3`;
                   `\z. (Fr:real->real)(A0 + &4 - p3_std_dist g0 z)`] P3S_CONF_FIELD) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `g0:real^3->real^3^3`; `x:real^3`; `u:real^3`;
                 `v:real^3`] P3S_PLANE_ONB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `c:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "INV")))))))))) THEN
  MAP_EVERY ABBREV_TAC [`u' = c1 % (u:real^3)`; `v' = c2 % ((v:real^3) - c % u)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `c1 % (u:real^3) = u'`;
                              ASSUME `c2 % ((v:real^3) - c % u) = v'`]) THEN
  USE_THEN "INV" (fun th -> MP_TAC(SPEC
    `\z. exp(--(&2 * (Fr:real->real)(A0 + &4 - p3_std_dist g0 z))) %% g0 z` th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REMOVE_THEN "INV" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `g0:real^3->real^3^3`;
                 `\z. (Fr:real->real)(A0 + &4 - p3_std_dist g0 z)`; `x:real^3`;
                 `u':real^3`; `v':real^3`] P3S_CONF_SECT_PL) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`g0 (x:real^3):real^3^3`;
                 `\a b. p3s_chess g0 (\z. (Fr:real->real)(A0 + &4 - p3_std_dist g0 z)) x a b +
                        p3s_cdf (\z. Fr(A0 + &4 - p3_std_dist g0 z)) x a *
                        p3s_cdf (\z. Fr(A0 + &4 - p3_std_dist g0 z)) x b`;
                 `u':real^3`; `v':real^3`] P3S_PL_ON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN BETA_TAC THEN
  (* Hessian, differential and gradient norm of F = Fr(A0 + 4 - d) *)
  SUBGOAL_THEN
   `!a b. p3s_chess g0 (\z. (Fr:real->real)(A0 + &4 - p3_std_dist g0 z)) x a b =
          Fr2 * p3s_cdf (p3_std_dist g0) x a * p3s_cdf (p3_std_dist g0) x b +
          --(Fr1(A0 + &4 - p3_std_dist g0 x)) * p3s_chess g0 (p3_std_dist g0) x a b`
  (LABEL_TAC "HF") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real)`; `g0:real^3->real^3^3`;
                   `p3_std_dist g0`; `\t. (Fr:real->real)(A0 + &4 - t)`;
                   `\t. --((Fr1:real->real)(A0 + &4 - t))`; `Fr2:real`; `x:real^3`;
                   `a:real^3`; `b:real^3`] P3S_CHESS_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN
    USE_THEN "S1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "S2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. p3s_cdf (\z. (Fr:real->real)(A0 + &4 - p3_std_dist g0 z)) x a =
        --(Fr1(A0 + &4 - p3_std_dist g0 x)) * p3s_cdf (p3_std_dist g0) x a`
  (LABEL_TAC "DF") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `p3_std_dist g0`;
                   `\t. (Fr:real->real)(A0 + &4 - t)`;
                   `--((Fr1:real->real)(A0 + &4 - p3_std_dist g0 x))`; `x:real^3`;
                   `a:real^3`] P3S_CDF_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "S1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `g0:real^3->real^3^3`; `p3_std_dist g0`;
                 `\t. (Fr:real->real)(A0 + &4 - t)`;
                 `--((Fr1:real->real)(A0 + &4 - p3_std_dist g0 x))`; `x:real^3`]
                P3S_GRADSQ_COMPOSE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_G0_CGRAD_D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  USE_THEN "HF" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e:real^3. e dot (g0 x ** e) = &1
               ==> p3s_chess g0 (p3_std_dist g0) x e e =
                   (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))) *
                   (&1 - p3s_cdf (p3_std_dist g0) x e pow 2)`
  (LABEL_TAC "HE") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `e:real^3`; `e:real^3`]
           P3S_G0_HESS_D) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `e:real^3`] P3S_G0_CDF_D) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `e:real^3`; `e:real^3`]
           P3S_ROT_BIL) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`r = norm(x:real^3)`; `aa = p3s_rad_a g0 r`; `bb = p3s_rad_b g0 r`;
      `sa = sqrt aa`; `ff = p3s_rs_f1 g0 r`; `sb = sqrt bb`; `pe = (e:real^3) dot x`;
      `ne = (e:real^3) dot e`] THEN
    UNDISCH_TAC `sa pow 2 = aa` THEN UNDISCH_TAC `&0 < r` THEN
    UNDISCH_TAC `&0 < sb` THEN UNDISCH_TAC `sb pow 2 = bb` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "HE" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u':real^3) dot ((g0:real^3->real^3^3) x ** u') = &1`);
                                       MATCH_MP th (ASSUME `(v':real^3) dot ((g0:real^3->real^3^3) x ** v') = &1`)]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u':real^3`; `v':real^3`]
         P3S_G0_SEC_ON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC `p3s_cdf (p3_std_dist g0) x u' pow 2 + p3s_cdf (p3_std_dist g0) x v' pow 2` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_G0_CGRAD_D) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC P3S_BESSEL2 THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC (LAND_CONV) [REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_EXP_NEG_MUL2; REAL_MUL_LID] THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* The model coefficients.  W = w'(d)/w(d) in [0, 1/w(e)] for               *)
(* d >= e; K_tan >= kappa > 0 for d >= e; K_rad >= 0; K_tan = K_rad = 1/4 in *)
(* the round region near the tip.                                           *)
(* ------------------------------------------------------------------------- *)

let P3S_W_EQ = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x))) =
         real_derivative (p3s_warp g0) (p3_std_dist g0 x) / p3s_warp g0 (p3_std_dist g0 x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_WARP_RHO) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rho g0 (norm(x:real^3))`]
         P3S_WARP_RD1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_RHO_POS THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RINV_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P3S_W_BOUNDS = prove
 (`!g0 A0 e (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < e /\ e <= p3_std_dist g0 x
     ==> &0 <= p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x))) /\
         p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x))) <=
         inv(p3s_warp g0 e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_W_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_WARP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `dd = p3_std_dist g0 (x:real^3)` THEN
  SUBGOAL_THEN `&0 < p3s_warp g0 e /\ p3s_warp g0 e <= p3s_warp g0 dd /\
                &0 <= real_derivative (p3s_warp g0) dd /\
                real_derivative (p3s_warp g0) dd <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC P3S_WARP_INCR THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3s_warp g0 dd` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_MUL_LINV
    (MATCH_MP REAL_LT_IMP_NZ (ASSUME `&0 < p3s_warp g0 e`)))] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let P3S_KTAN_RAD_EQ = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> p3s_rs_ktan g0 (norm x) = p3s_sec_tan g0 (p3_std_dist g0 x) /\
         p3s_rs_krad g0 (norm x) = p3s_sec_rad g0 (p3_std_dist g0 x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THENL
   [MATCH_MP_TAC P3S_SEC_TAN_RHO; MATCH_MP_TAC P3S_SEC_RAD_RHO] THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[NORM_POS_LT]);;

let P3S_ROUND_KK = prove
 (`!g0 A0 rt (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ p3_std_dist g0 x < rt /\
     (!x u v. p3_std_dist g0 x < rt /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v = &1 / &4)
     ==> p3s_rs_ktan g0 (norm x) = &1 / &4 /\ p3s_rs_krad g0 (norm x) = &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (norm(x:real^3) % basis 1:real^3) = p3_std_dist g0 x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                   `norm(x:real^3) % basis 1:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_ABS_NORM; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3s_sec_tan g0 (p3s_rad_rho g0 (norm(x:real^3))) = &1 / &4 /\
                p3s_sec_rad g0 (p3s_rad_rho g0 (norm(x:real^3))) = &1 / &4`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`]
             P3S_SEC_TANG_PLANE);
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`]
             P3S_SEC_RADIAL_PLANE)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[P3S_NONCOLL_BASIS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_SEC_TAN_RHO) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_SEC_RAD_RHO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The conformal exponent of the cap, cfr = -(1/2) log phi, so               *)
(* that phi = e^{-2 cfr}.  It is smooth; below A0 + 4 - r0 it equals f, so   *)
(* its derivatives are f' = (q/s^2) f and f'' = (q^2/s^4 - 2q/s^3) f; on the *)
(* blend [A0 + 4 - r0, A0 + 4 - r0/2] its first two derivatives are O(c).    *)
(* ------------------------------------------------------------------------- *)

let p3s_cfr = new_definition
 `p3s_cfr c q A0 r0 (s:real) = --(log(p3s_phi c q A0 r0 s)) / &2`;;

let P3S_PHI_POS = prove
 (`!c q A0 r0 s. &0 <= c /\ &0 < q /\ &0 < r0 ==> &0 < p3s_phi c q A0 r0 s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `exp(--(&2 * p3s_f c q (A0 + &4)))` THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s:real`] P3S_PHI_BOUNDS) THEN
  ASM_SIMP_TAC[]);;

let P3S_CFR_EXP = prove
 (`!c q A0 r0 s. &0 <= c /\ &0 < q /\ &0 < r0
                 ==> exp(--(&2 * p3s_cfr c q A0 r0 s)) = p3s_phi c q A0 r0 s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cfr] THEN
  REWRITE_TAC[REAL_ARITH `--(&2 * --x / &2) = x`] THEN
  MATCH_MP_TAC EXP_LOG THEN MATCH_MP_TAC P3S_PHI_POS THEN ASM_REWRITE_TAC[]);;

let P3S_CFR_SMOOTH = prove
 (`!c q A0 r0. &0 <= c /\ &0 < q /\ &0 < r0
               ==> smooth_map_on (:real^1) (lift o p3s_cfr c q A0 r0 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_cfr c q A0 r0 = (\s. --(&1 / &2) * log(p3s_phi c q A0 r0 s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3s_cfr] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o p3s_phi c q A0 r0 o drop`] SMOOTH_MAP_ON_LIFT_LOG) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_PHI_SMOOTH; o_THM; LIFT_DROP; P3S_PHI_POS] THEN
  REWRITE_TAC[o_DEF]);;

let P3S_CFR_DERIVS = prove
 (`!c q A0 r0. &0 <= c /\ &0 < q /\ &0 < r0
     ==> (!t. (p3s_cfr c q A0 r0 has_real_derivative
               real_derivative (p3s_cfr c q A0 r0) t) (atreal t)) /\
         (!t. (real_derivative (p3s_cfr c q A0 r0) has_real_derivative
               real_derivative (real_derivative (p3s_cfr c q A0 r0)) t) (atreal t)) /\
         smooth_map_on (:real^1) (lift o real_derivative (p3s_cfr c q A0 r0) o drop)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_CFR_SMOOTH) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_cfr c q A0 r0`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_cfr c q A0 r0)`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let P3S_CFR_LOW = prove
 (`!c q A0 r0 s. &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < s /\ s < A0 + &4 - r0
     ==> real_derivative (p3s_cfr c q A0 r0) s = (q / s pow 2) * p3s_f c q s /\
         real_derivative (real_derivative (p3s_cfr c q A0 r0)) s =
         (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t < A0 + &4 - r0 ==> p3s_cfr c q A0 r0 t = p3s_f c q t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cfr] THEN
    MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `t:real`] P3S_PHI_LOW) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t /\ t < A0 + &4 - r0
                    ==> real_derivative (p3s_cfr c q A0 r0) t = (q / t pow 2) * p3s_f c q t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`p3s_f c q`; `min t (A0 + &4 - r0 - t)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_F_DERIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\u. (q / u pow 2) * p3s_f c q u`; `min s (A0 + &4 - r0 - s)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3S_F_DERIV2 THEN ASM_REWRITE_TAC[]]);;

let P3S_BETA_DERIVS = prove
 (`!A0 r0. &0 < r0
     ==> (!t. (p3s_beta A0 r0 has_real_derivative real_derivative (p3s_beta A0 r0) t)
              (atreal t)) /\
         (!t. (real_derivative (p3s_beta A0 r0) has_real_derivative
               real_derivative (real_derivative (p3s_beta A0 r0)) t) (atreal t)) /\
         smooth_map_on (:real^1) (lift o real_derivative (p3s_beta A0 r0) o drop) /\
         smooth_map_on (:real^1)
           (lift o real_derivative (real_derivative (p3s_beta A0 r0)) o drop)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_beta A0 r0`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_beta A0 r0)`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let P3S_PHI_D1 = prove
 (`!c q A0 r0 t. &0 < q /\ &0 < r0 /\ &0 < t
     ==> (p3s_phi c q A0 r0 has_real_derivative
          real_derivative (p3s_beta A0 r0) t *
          (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
          p3s_beta A0 r0 t * (exp(--(&2 * p3s_f c q t)) *
                              --(&2 * ((q / t pow 2) * p3s_f c q t)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA_DERIVS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p3s_phi c q A0 r0 =
                (\t. p3s_beta A0 r0 t * exp(--(&2 * p3s_f c q t)) +
                     (&1 - p3s_beta A0 r0 t) * exp(--(&2 * p3s_f c q (A0 + &4))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_phi]; ALL_TAC] THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [ASSUME `!t. (p3s_beta A0 r0 has_real_derivative real_derivative (p3s_beta A0 r0) t)
                 (atreal t)`;
     GEN `s:real` (MP (SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`c:real`; `q:real`] P3S_F_DERIV))) (ASSUME `&0 < q`))]
    `((\t. p3s_beta A0 r0 t * exp(--(&2 * p3s_f c q t)) +
           (&1 - p3s_beta A0 r0 t) * exp(--(&2 * p3s_f c q (A0 + &4))))
      has_real_derivative f') (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P3S_PHI_D2 = prove
 (`!c q A0 r0 t. &0 < q /\ &0 < r0 /\ &0 < t
     ==> ((\t. real_derivative (p3s_beta A0 r0) t *
               (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
               p3s_beta A0 r0 t * (exp(--(&2 * p3s_f c q t)) *
                                   --(&2 * ((q / t pow 2) * p3s_f c q t))))
          has_real_derivative
          real_derivative (real_derivative (p3s_beta A0 r0)) t *
          (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
          &2 * real_derivative (p3s_beta A0 r0) t *
          (exp(--(&2 * p3s_f c q t)) * --(&2 * ((q / t pow 2) * p3s_f c q t))) +
          p3s_beta A0 r0 t * exp(--(&2 * p3s_f c q t)) *
          (&4 * ((q / t pow 2) * p3s_f c q t) pow 2 -
           &2 * ((q pow 2 / t pow 4 - &2 * q / t pow 3) * p3s_f c q t))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA_DERIVS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(t pow 2 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [ASSUME `!t. (p3s_beta A0 r0 has_real_derivative real_derivative (p3s_beta A0 r0) t)
                 (atreal t)`;
     ASSUME `!t. (real_derivative (p3s_beta A0 r0) has_real_derivative
                  real_derivative (real_derivative (p3s_beta A0 r0)) t) (atreal t)`;
     GEN `s:real` (MP (SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`c:real`; `q:real`] P3S_F_DERIV))) (ASSUME `&0 < q`))]
    `((\t. real_derivative (p3s_beta A0 r0) t *
           (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
           p3s_beta A0 r0 t * (exp(--(&2 * p3s_f c q t)) *
                               --(&2 * ((q / t pow 2) * p3s_f c q t))))
      has_real_derivative f') (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

let p3s_phi1 = new_definition
 `p3s_phi1 c q A0 r0 (t:real) =
    real_derivative (p3s_beta A0 r0) t *
    (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
    p3s_beta A0 r0 t * (exp(--(&2 * p3s_f c q t)) * --(&2 * ((q / t pow 2) * p3s_f c q t)))`;;

let p3s_phi2 = new_definition
 `p3s_phi2 c q A0 r0 (t:real) =
    real_derivative (real_derivative (p3s_beta A0 r0)) t *
    (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
    &2 * real_derivative (p3s_beta A0 r0) t *
    (exp(--(&2 * p3s_f c q t)) * --(&2 * ((q / t pow 2) * p3s_f c q t))) +
    p3s_beta A0 r0 t * exp(--(&2 * p3s_f c q t)) *
    (&4 * ((q / t pow 2) * p3s_f c q t) pow 2 -
     &2 * ((q pow 2 / t pow 4 - &2 * q / t pow 3) * p3s_f c q t))`;;

let P3S_PHI_HD1 = prove
 (`!c q A0 r0 t. &0 < q /\ &0 < r0 /\ &0 < t
     ==> (p3s_phi c q A0 r0 has_real_derivative p3s_phi1 c q A0 r0 t) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_phi1] THEN
  MATCH_MP_TAC P3S_PHI_D1 THEN ASM_REWRITE_TAC[]);;

let P3S_PHI_HD2 = prove
 (`!c q A0 r0 t. &0 < q /\ &0 < r0 /\ &0 < t
     ==> (p3s_phi1 c q A0 r0 has_real_derivative p3s_phi2 c q A0 r0 t) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3s_phi1 c q A0 r0 =
    (\t. real_derivative (p3s_beta A0 r0) t *
         (exp(--(&2 * p3s_f c q t)) - exp(--(&2 * p3s_f c q (A0 + &4)))) +
         p3s_beta A0 r0 t * (exp(--(&2 * p3s_f c q t)) *
                             --(&2 * ((q / t pow 2) * p3s_f c q t))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_phi1]; ALL_TAC] THEN
  REWRITE_TAC[p3s_phi2] THEN MATCH_MP_TAC P3S_PHI_D2 THEN ASM_REWRITE_TAC[]);;

let P3S_CFR_D1 = prove
 (`!c q A0 r0 t. &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < t
     ==> (p3s_cfr c q A0 r0 has_real_derivative
          --(p3s_phi1 c q A0 r0 t / p3s_phi c q A0 r0 t) / &2) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_cfr c q A0 r0 = (\s. --(log(p3s_phi c q A0 r0 s)) / &2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_cfr]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `t:real`] P3S_PHI_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [GEN `t:real` (MP (MP (SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_PHI_HD1)))
       (ASSUME `&0 < q`)) (ASSUME `&0 < r0`))]
    `((\s. --(log(p3s_phi c q A0 r0 s)) / &2) has_real_derivative f') (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < p3s_phi c q A0 r0 t` THEN CONV_TAC REAL_FIELD);;

let P3S_CFR_D1_EQ = prove
 (`!c q A0 r0 t. &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < t
     ==> real_derivative (p3s_cfr c q A0 r0) t =
         --(p3s_phi1 c q A0 r0 t / p3s_phi c q A0 r0 t) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC P3S_CFR_D1 THEN ASM_REWRITE_TAC[]);;

let P3S_CFR_D2 = prove
 (`!c q A0 r0 t. &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < t
     ==> real_derivative (real_derivative (p3s_cfr c q A0 r0)) t =
         --((p3s_phi2 c q A0 r0 t * p3s_phi c q A0 r0 t - p3s_phi1 c q A0 r0 t pow 2) /
            p3s_phi c q A0 r0 t pow 2) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\s. --(p3s_phi1 c q A0 r0 s / p3s_phi c q A0 r0 s) / &2`;
                        `t:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_CFR_D1_EQ THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `t:real`] P3S_PHI_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p3s_phi c q A0 r0 t = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [GEN `t:real` (MP (MP (SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_PHI_HD1)))
       (ASSUME `&0 < q`)) (ASSUME `&0 < r0`));
     GEN `t:real` (MP (MP (SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_PHI_HD2)))
       (ASSUME `&0 < q`)) (ASSUME `&0 < r0`))]
    `((\s. --(p3s_phi1 c q A0 r0 s / p3s_phi c q A0 r0 s) / &2) has_real_derivative f')
     (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < p3s_phi c q A0 r0 t` THEN CONV_TAC REAL_FIELD);;

let P3S_RCONT_BOUNDED = prove
 (`!(g:real->real) a b.
     g real_continuous_on real_interval[a,b]
     ==> ?B. &0 <= B /\ !t. a <= t /\ t <= b ==> abs(g t) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `real_interval[a,b]`] REAL_COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let P3S_BETA_DBOUND = prove
 (`!A0 r0 a b. &0 < r0
     ==> ?B. &0 <= B /\
             !t. a <= t /\ t <= b
                 ==> abs(real_derivative (p3s_beta A0 r0) t) <= B /\
                     abs(real_derivative (real_derivative (p3s_beta A0 r0)) t) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA_DERIVS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`real_derivative (p3s_beta A0 r0)`; `a:real`; `b:real`]
         P3S_RCONT_BOUNDED) THEN
  ASM_SIMP_TAC[P2C_S1_CONTINUOUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H1"))) THEN
  MP_TAC(ISPECL [`real_derivative (real_derivative (p3s_beta A0 r0))`; `a:real`; `b:real`]
         P3S_RCONT_BOUNDED) THEN
  ASM_SIMP_TAC[P2C_S1_CONTINUOUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H2"))) THEN
  EXISTS_TAC `B1 + B2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REMOVE_THEN "H1" (MP_TAC o SPEC `t:real`) THEN
  REMOVE_THEN "H2" (MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3S_QUOT_BOUNDS = prove
 (`!p1 p2 ph M1 M2.
     &1 / &2 <= ph /\ abs p1 <= M1 /\ abs p2 <= M2
     ==> abs(--(p1 / ph) / &2) <= M1 /\
         abs(--((p2 * ph - p1 pow 2) / ph pow 2) / &2) <= M2 + &2 * M1 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ph` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv ph /\ inv ph <= &2 /\ ph * inv ph = &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_POW_INV] THEN
  ABBREV_TAC `u = inv ph` THEN
  SUBGOAL_THEN `(p2 * ph - p1 pow 2) * u pow 2 = p2 * u - p1 pow 2 * u pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `ph * u = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M1 /\ &0 <= M2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `p1:real` REAL_ABS_POS) THEN MP_TAC(SPEC `p2:real` REAL_ABS_POS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs p1 * u <= M1 * &2 /\ abs p2 * u <= M2 * &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(abs p1 * u) * (abs p1 * u) <= (M1 * &2) * (M1 * &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(p1 * u) = abs p1 * u /\ abs(p2 * u) = abs p2 * u /\
                p1 pow 2 * u pow 2 = (abs p1 * u) * (abs p1 * u)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MP_TAC(SPEC `p1:real` REAL_POW2_ABS) THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (abs p1 * u) * (abs p1 * u)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_PHI12_ARITH = prove
 (`!b b1 b2 E EH g1 g2 B Q R c.
     &0 <= b /\ b <= &1 /\ abs b1 <= B /\ abs b2 <= B /\
     &0 <= E /\ E <= &1 /\ abs(E - EH) <= &2 * c /\
     &0 <= g1 /\ g1 <= Q * c /\ abs g2 <= R * c /\ &0 <= c /\ c <= &1 /\
     &0 <= B /\ &0 <= Q /\ &0 <= R
     ==> abs(b1 * (E - EH) + b * (E * --(&2 * g1))) <= (&2 * B + &2 * Q) * c /\
         abs(b2 * (E - EH) + &2 * b1 * (E * --(&2 * g1)) +
             b * E * (&4 * g1 pow 2 - &2 * g2))
         <= (&2 * B + &4 * B * Q + &4 * Q pow 2 + &2 * R) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(b1 * (E - EH)) <= B * (&2 * c) /\ abs(b2 * (E - EH)) <= B * (&2 * c)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b * E /\ b * E <= &1 * &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b * E) * g1 /\ (b * E) * g1 <= (&1 * &1) * (Q * c)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E * g1 /\ E * g1 <= &1 * (Q * c)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(b1 * (E * g1)) <= B * (&1 * (Q * c))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; GSYM REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `g1 pow 2 <= Q pow 2 * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Q * c) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b * E) * g1 pow 2 /\ (b * E) * g1 pow 2 <= (&1 * &1) * (Q pow 2 * c)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((b * E) * g2) <= (&1 * &1) * (R * c)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; GSYM REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_INV_POW3_LE = prove
 (`!s. &3 <= s ==> inv(s pow 2) <= inv(&9) /\ inv(s pow 3) <= inv(&27) /\
                   inv(s pow 4) <= inv(&81)`,
  REPEAT STRIP_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THENL
   [MP_TAC(SPECL [`2`; `&3`; `s:real`] REAL_POW_LE2);
    MP_TAC(SPECL [`3`; `&3`; `s:real`] REAL_POW_LE2);
    MP_TAC(SPECL [`4`; `&3`; `s:real`] REAL_POW_LE2)] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let P3S_F_BOUNDS3 = prove
 (`!c q s. &0 <= c /\ &0 < q /\ &3 <= s
     ==> &0 <= (q / s pow 2) * p3s_f c q s /\
         (q / s pow 2) * p3s_f c q s <= (q / &9) * c /\
         abs((q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s) <=
         (q pow 2 / &81 + &2 * q / &27) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p3s_f c q s /\ p3s_f c q s <= c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_NONNEG; P3S_F_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s:real` P3S_INV_POW3_LE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv(s pow 2) /\ &0 <= inv(s pow 3) /\ &0 <= inv(s pow 4)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q / s pow 2 /\ q / s pow 2 <= q / &9` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(q pow 2 / s pow 4 - &2 * q / s pow 3) <= q pow 2 / &81 + &2 * q / &27`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= q pow 2 * inv(s pow 4) /\
                  q pow 2 * inv(s pow 4) <= q pow 2 * inv(&81) /\
                  &0 <= q * inv(s pow 3) /\ q * inv(s pow 3) <= q * inv(&27)`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_LE_LMUL];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]]);;

let P3S_E_BOUNDS = prove
 (`!c q s. &0 <= c /\ &0 < q
     ==> &1 - &2 * c <= exp(--(&2 * p3s_f c q s)) /\ exp(--(&2 * p3s_f c q s)) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_F_NONNEG) THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_F_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPEC `--(&2 * p3s_f c q s)` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC]);;

let P3S_CFR_BLEND = prove
 (`!q A0 r0. &0 < q /\ &0 < r0 /\ r0 <= &1 /\ &0 < A0
     ==> ?B. &0 <= B /\
             !c s. &0 <= c /\ c <= &1 / &4 /\
                   A0 + &4 - r0 <= s /\ s <= A0 + &4 - r0 / &2
                   ==> abs(real_derivative (p3s_cfr c q A0 r0) s) <= B * c /\
                       abs(real_derivative (real_derivative (p3s_cfr c q A0 r0)) s)
                       <= B * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`; `A0 + &4 - r0`; `A0 + &4 - r0 / &2`]
         P3S_BETA_DBOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BB"))) THEN
  ABBREV_TAC `P1 = &2 * Bb + &2 * (q / &9)` THEN
  ABBREV_TAC `P2 = &2 * Bb + &4 * Bb * (q / &9) + &4 * (q / &9) pow 2 +
                   &2 * (q pow 2 / &81 + &2 * q / &27)` THEN
  SUBGOAL_THEN `&0 <= q / &9 /\ &0 <= q pow 2 / &81 + &2 * q / &27` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= q pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P1 /\ &0 <= P2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN
    SUBGOAL_THEN `&0 <= Bb * (q / &9) /\ &0 <= (q / &9) pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `P1 + P2 + &2 * P1 pow 2` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= P1 pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 <= s /\ &0 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "BB" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_F_BOUNDS3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_E_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0 + &4`] P3S_E_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= p3s_phi c q A0 r0 s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s:real`] P3S_PHI_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(exp(--(&2 * p3s_f c q s)) - exp(--(&2 * p3s_f c q (A0 + &4)))) <= &2 * c`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(p3s_phi1 c q A0 r0 s) <= P1 * c /\ abs(p3s_phi2 c q A0 r0 s) <= P2 * c`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN REWRITE_TAC[p3s_phi1; p3s_phi2] THEN
    MATCH_MP_TAC P3S_PHI12_ARITH THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s:real`] P3S_CFR_D1_EQ) THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s:real`] P3S_CFR_D2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(SPECL [`p3s_phi1 c q A0 r0 s`; `p3s_phi2 c q A0 r0 s`; `p3s_phi c q A0 r0 s`;
                `P1 * c`; `P2 * c`] P3S_QUOT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= P1 * c /\ &0 <= P2 * c /\ &0 <= P1 pow 2 * c /\
                (P1 * c) pow 2 <= P1 pow 2 * c`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Positivity of the curvature of the cap metric                            *)
(* phi(s1) g0 on s1 >= 2 (MT Sec 13.3.2 with the repaired argument): from   *)
(* the cap identity both brackets K_tan - 2 F' W - F'^2 and                  *)
(* K_rad + F'' - F' W are positive, on [2, A0 + 4 - r0) because             *)
(* f'' > f' W for q large and f' is small for c small, on the blend         *)
(* because K = 1/4 there and |F'|, |F''| <= B c; near the tip the metric is  *)
(* a constant multiple of the round g0.                                     *)
(* ------------------------------------------------------------------------- *)

let P3S_CONVEX_POS = prove
 (`!e K sg a b. e * K = (&1 - sg) * a + sg * b
                ==> &0 < e /\ &0 <= sg /\ sg <= &1 /\ &0 < a /\ &0 < b ==> &0 < K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - sg) * a /\ &0 <= sg * b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - sg) * a + sg * b` ASSUME_TAC THENL
   [ASM_CASES_TAC `sg = &0` THENL
     [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID];
      SUBGOAL_THEN `&0 < sg * b` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e * K <= &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM REAL_MUL_RNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P3S_CAP_KHAT_POS = prove
 (`!g0 A0 (Fr:real->real) Fr1 Fr2 (x:real^3) u v.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\
     smooth_map_on (:real^1) (lift o Fr o drop) /\
     (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (A0 + &4 - p3_std_dist g0 x)) /\
     ~collinear {vec 0,u,v} /\
     &0 < p3s_rs_ktan g0 (norm x) -
          &2 * Fr1(A0 + &4 - p3_std_dist g0 x) *
          (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))) -
          Fr1(A0 + &4 - p3_std_dist g0 x) pow 2 /\
     &0 < p3s_rs_krad g0 (norm x) + Fr2 -
          Fr1(A0 + &4 - p3_std_dist g0 x) *
          (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x))))
     ==> &0 < lsectional (\z. exp(--(&2 * Fr(A0 + &4 - p3_std_dist g0 z))) %% g0 z) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `Fr:real->real`; `Fr1:real->real`;
                `Fr2:real`; `x:real^3`; `u:real^3`; `v:real^3`] P3S_CAP_KHAT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o MATCH_MP P3S_CONVEX_POS)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; REWRITE_TAC[]]);;

let P3S_CAP_CFR_POS = prove
 (`!g0 A0 c q r0 (x:real^3) u v.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\
     ~(x = vec 0) /\ ~collinear {vec 0,u,v} /\
     &0 < p3s_rs_ktan g0 (norm x) -
          &2 * real_derivative (p3s_cfr c q A0 r0) (A0 + &4 - p3_std_dist g0 x) *
          (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x)))) -
          real_derivative (p3s_cfr c q A0 r0) (A0 + &4 - p3_std_dist g0 x) pow 2 /\
     &0 < p3s_rs_krad g0 (norm x) +
          real_derivative (real_derivative (p3s_cfr c q A0 r0))
            (A0 + &4 - p3_std_dist g0 x) -
          real_derivative (p3s_cfr c q A0 r0) (A0 + &4 - p3_std_dist g0 x) *
          (p3s_rs_f1 g0 (norm x) / (norm x * sqrt(p3s_rad_b g0 (norm x))))
     ==> &0 < lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z)
                         x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_CFR_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_cfr c q A0 r0`;
                `real_derivative (p3s_cfr c q A0 r0)`;
                `real_derivative (real_derivative (p3s_cfr c q A0 r0))
                   (A0 + &4 - p3_std_dist g0 (x:real^3))`;
                `x:real^3`; `u:real^3`; `v:real^3`] P3S_CAP_KHAT_POS) THEN
  ASM_SIMP_TAC[P3S_CFR_SMOOTH; P3S_CFR_EXP]);;
let P3S_R1_F2 = prove
 (`!c q s L Wm.
     &0 < c /\ &0 < q /\ &0 < s /\ s <= L /\ &0 <= Wm /\ &2 * L + Wm * L pow 2 < q
     ==> ((q / s pow 2) * p3s_f c q s) * Wm <
         (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3s_f c q s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_POS] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Wm * s pow 2 <= Wm * L pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (q / s pow 4) * (q - &2 * s - Wm * s pow 2) * p3s_f c q s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s -
    ((q / s pow 2) * p3s_f c q s) * Wm =
    (q / s pow 4) * (q - &2 * s - Wm * s pow 2) * p3s_f c q s`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;

let P3S_R1_ARITH = prove
 (`!K Kr W Wm F1 F2 X kmin.
     kmin <= K /\ &0 <= Kr /\ &0 <= W /\ W <= Wm /\ &0 <= F1 /\ F1 <= X /\ X <= &1 /\
     X * (&2 * Wm + &1) <= kmin / &2 /\ &0 < kmin /\ F1 * Wm < F2
     ==> &0 < K - &2 * F1 * W - F1 pow 2 /\ &0 < Kr + F2 - F1 * W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `F1 * W <= X * Wm /\ F1 * W <= F1 * Wm` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `F1 pow 2 <= X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `X * X` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_R2_ARITH = prove
 (`!K Kr W Wm F1 F2 Y.
     K = &1 / &4 /\ Kr = &1 / &4 /\ &0 <= W /\ W <= Wm /\
     abs F1 <= Y /\ abs F2 <= Y /\ Y * (&2 * Wm + &1) <= &1 / &8
     ==> &0 < K - &2 * F1 * W - F1 pow 2 /\ &0 < Kr + F2 - F1 * W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
   [MP_TAC(SPEC `F1:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Y * Wm` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Y <= &1 / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(F1 * W) <= Y * Wm` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_ARITH `&0 <= x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `F1 pow 2 <= Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Y * Y` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;
let P3S_Q_S2_LE = prove
 (`!q s. &0 < q /\ &2 <= s ==> &0 <= q / s pow 2 /\ q / s pow 2 <= q / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ &4 <= s pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`2`; `&2`; `s:real`] REAL_POW_LE2) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let P3S_CAP_REG1 = prove
 (`!g0 A0 r0 kmin q c (x:real^3) u v.
     p3_std_initial g0 A0 /\ &0 < r0 /\ &0 < kmin /\
     (!s. r0 / &2 <= s ==> kmin <= p3s_sec_tan g0 s) /\
     &2 * (A0 + &4) + inv(p3s_warp g0 (r0 / &2)) * (A0 + &4) pow 2 < q /\
     &0 < c /\ (q / &4) * c <= &1 /\
     ((q / &4) * c) * (&2 * inv(p3s_warp g0 (r0 / &2)) + &1) <= kmin / &2 /\
     &2 <= A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < A0 + &4 - r0 /\
     ~collinear {vec 0,u,v}
     ==> &0 < lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z)
                         x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < p3s_warp g0 (r0 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_WARP_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(p3s_warp g0 (r0 / &2))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= inv(p3s_warp g0 (r0 / &2)) * (A0 + &4) pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`;
                `A0 + &4 - p3_std_dist g0 (x:real^3)`] P3S_CFR_LOW) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_KTAN_RAD_EQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `kmin <= p3s_sec_tan g0 (p3_std_dist g0 (x:real^3)) /\
                &0 <= p3s_sec_rad g0 (p3_std_dist g0 x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_KRAD_NONNEG THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0 / &2`; `x:real^3`] P3S_W_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`q:real`; `A0 + &4 - p3_std_dist g0 (x:real^3)`] P3S_Q_S2_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p3s_f c q (A0 + &4 - p3_std_dist g0 (x:real^3)) /\
                p3s_f c q (A0 + &4 - p3_std_dist g0 x) <= c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_NONNEG; P3S_F_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (q / (A0 + &4 - p3_std_dist g0 (x:real^3)) pow 2) *
          p3s_f c q (A0 + &4 - p3_std_dist g0 x) /\
    (q / (A0 + &4 - p3_std_dist g0 (x:real^3)) pow 2) *
    p3s_f c q (A0 + &4 - p3_std_dist g0 x) <= (q / &4) * c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0 + &4 - p3_std_dist g0 (x:real^3)`; `A0 + &4`;
                `inv(p3s_warp g0 (r0 / &2))`] P3S_R1_F2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_DIST_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC P3S_CAP_CFR_POS THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC P3S_R1_ARITH THEN
  MAP_EVERY EXISTS_TAC [`inv(p3s_warp g0 (r0 / &2))`; `(q / &4) * c`; `kmin:real`] THEN
  ASM_REWRITE_TAC[]);;
let P3S_CAP_REG2 = prove
 (`!g0 A0 rt r0 q B c (x:real^3) u v.
     p3_std_initial g0 A0 /\
     (!x u v. p3_std_dist g0 x < rt /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v = &1 / &4) /\
     &0 < r0 /\ r0 < rt /\ &0 < q /\
     (!c s. &0 <= c /\ c <= &1 / &4 /\ A0 + &4 - r0 <= s /\ s <= A0 + &4 - r0 / &2
            ==> abs(real_derivative (p3s_cfr c q A0 r0) s) <= B * c /\
                abs(real_derivative (real_derivative (p3s_cfr c q A0 r0)) s) <= B * c) /\
     &0 <= c /\ c <= &1 / &4 /\
     (B * c) * (&2 * inv(p3s_warp g0 (r0 / &2)) + &1) <= &1 / &8 /\
     A0 + &4 - r0 <= A0 + &4 - p3_std_dist g0 x /\
     A0 + &4 - p3_std_dist g0 x <= A0 + &4 - r0 / &2 /\
     ~collinear {vec 0,u,v}
     ==> &0 < lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z)
                         x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `rt:real`; `x:real^3`] P3S_ROUND_KK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0 / &2`; `x:real^3`] P3S_W_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `A0 + &4 - p3_std_dist g0 (x:real^3)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3S_CAP_CFR_POS THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3S_R2_ARITH THEN
  MAP_EVERY EXISTS_TAC [`inv(p3s_warp g0 (r0 / &2))`; `B * c`] THEN
  ASM_REWRITE_TAC[]);;

let P3S_CAP_TIP = prove
 (`!g0 A0 rt r0 c q (x:real^3) u v.
     p3_std_initial g0 A0 /\
     (!x u v. p3_std_dist g0 x < rt /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v = &1 / &4) /\
     &0 < r0 /\ r0 < rt /\
     A0 + &4 - r0 / &2 < A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
     ==> &0 < lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z)
                         x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `pL = exp(--(&2 * p3s_f c q (A0 + &4)))` THEN
  SUBGOAL_THEN `&0 < pL` ASSUME_TAC THENL
   [EXPAND_TAC "pL" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z) x u v =
    lsectional (\z:real^3. pL %% g0 z) x u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    EXISTS_TAC `{z:real^3 | A0 + &4 - r0 / &2 < A0 + &4 - p3_std_dist g0 z}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "pL" THEN
      MATCH_MP_TAC P3S_PHI_HIGH THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `pL:real`; `x:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN MATCH_MP_TAC P3S_STD_METRIC_FIELD THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SECTIONAL] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
let P3S_CAP_POS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> ?r0. &0 < r0 /\ r0 <= &1 /\
              ?Q0. &0 < Q0 /\
                   !q. Q0 <= q
                       ==> ?cm. &0 < cm /\
                                !c (x:real^3) u v.
                                  &0 < c /\ c <= cm /\
                                  &2 <= A0 + &4 - p3_std_dist g0 x /\
                                  ~collinear {vec 0,u,v}
                                  ==> &0 < lsectional
                                             (\z. p3s_phi c q A0 r0
                                                    (A0 + &4 - p3_std_dist g0 z) %% g0 z)
                                             x u v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              REWRITE_RULE[p3_std_initial]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r0. &0 < r0 /\ r0 <= &1 /\ r0 < rt` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (rt / &2)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0 / &2`] P3S_ROT_SEC_TAN_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `kmin:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `&0 < p3s_warp g0 (r0 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_WARP_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(p3s_warp g0 (r0 / &2)) /\
                &0 <= inv(p3s_warp g0 (r0 / &2)) * (A0 + &4) pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  EXISTS_TAC `&2 * (A0 + &4) + inv(p3s_warp g0 (r0 / &2)) * (A0 + &4) pow 2 + &1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `q:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < q /\
                &2 * (A0 + &4) + inv(p3s_warp g0 (r0 / &2)) * (A0 + &4) pow 2 < q`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`q:real`; `A0:real`; `r0:real`] P3S_CFR_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Wm = inv(p3s_warp g0 (r0 / &2))` THEN
  SUBGOAL_THEN `&0 < (q / &4) * (&2 * Wm + &1) /\ &0 < (B + &1) * (&2 * Wm + &1) /\
                &0 < q / &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &4) (min (inv(q / &4))
                (min ((kmin / &2) / ((q / &4) * (&2 * Wm + &1)))
                     ((&1 / &8) / ((B + &1) * (&2 * Wm + &1)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q / &4) * c <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(q / &4) * inv(q / &4)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((q / &4) * c) * (&2 * Wm + &1) <= kmin / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `c <= (kmin / &2) / ((q / &4) * (&2 * Wm + &1))` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(B * c) * (&2 * Wm + &1) <= &1 / &8` ASSUME_TAC THENL
   [UNDISCH_TAC `c <= (&1 / &8) / ((B + &1) * (&2 * Wm + &1))` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= c * (&2 * Wm + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 (x:real^3) < A0 + &4 - r0` THENL
   [MATCH_MP_TAC P3S_CAP_REG1 THEN EXISTS_TAC `kmin:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 (x:real^3) <= A0 + &4 - r0 / &2` THENL
   [MATCH_MP_TAC P3S_CAP_REG2 THEN
    MAP_EVERY EXISTS_TAC [`rt:real`; `B:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3S_CAP_TIP THEN EXISTS_TAC `rt:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;
let P3S_OPEN_MFD_SECTIONAL = prove
 (`!U (g:real^N->real^N^N) x u v.
     open U /\ x IN U
     ==> mfd_sectional (open_set_atlas U) g x u v = lsectional g x u v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_sectional; RFB_OPEN_SET_CHART_AT; SND] THEN
  MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

let P3S_CAP_GS_POS = prove
 (`!g0 A0 c q r0 dl h gN (x:real^3) u v.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\ r0 <= &1 /\
     &0 < dl /\ dl < &1 / &4 /\ &0 < h /\ metric_field (rfs_neck_dom dl) gN /\
     &2 < A0 + &4 - p3_std_dist g0 x /\
     &0 < lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z) x u v
     ==> &0 < mfd_sectional
                (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                (p3s_gs g0 A0 c q r0 dl h gN) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < inv dl` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z} /\
                open {z:real^3 | &2 < A0 + &4 - p3_std_dist g0 z}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z}`;
                 `p3s_gs g0 A0 c q r0 dl h gN`; `x:real^3`; `u:real^3`; `v:real^3`]
         P3S_OPEN_MFD_SECTIONAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                `dl:real`; `h:real`; `gN:real^3->real^3^3`] P3S_GS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2 * (&1 - dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k = inv(h pow 2 * (&1 - dl))` THEN
  SUBGOAL_THEN `&0 < k /\ k * (h pow 2 * (&1 - dl)) = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z}`;
                 `p3s_gs g0 A0 c q r0 dl h gN`; `k:real`; `x:real^3`; `u:real^3`;
                 `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `lsectional (\z. k %% p3s_gs g0 A0 c q r0 dl h gN z) x u v =
    lsectional (\z. p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 z) %% g0 z) x u v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    EXISTS_TAC `{z:real^3 | &2 < A0 + &4 - p3_std_dist g0 z}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                  `dl:real`; `h:real`; `gN:real^3->real^3^3`; `z:real^3`] P3S_GS_FAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `k * (h pow 2 * (&1 - dl)) = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lsectional (p3s_gs g0 A0 c q r0 dl h gN) x u v / k` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]);;
let P3S_CAP_GS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> ?r0. &0 < r0 /\ r0 <= &1 /\
              ?Q0. &0 < Q0 /\
                   !q. Q0 <= q
                       ==> ?cm. &0 < cm /\
                                !c dl h gN (x:real^3) u v.
                                  &0 < c /\ c <= cm /\ &0 < dl /\ dl < &1 / &4 /\
                                  &0 < h /\ metric_field (rfs_neck_dom dl) gN /\
                                  &2 < A0 + &4 - p3_std_dist g0 x /\
                                  ~collinear {vec 0,u,v}
                                  ==> &0 < mfd_sectional
                                             (open_set_atlas
                                                {z | --(inv dl) <
                                                     A0 + &4 - p3_std_dist g0 z})
                                             (p3s_gs g0 A0 c q r0 dl h gN) x u v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_CAP_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `Q0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q")))))) THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `Q0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:real` THEN DISCH_TAC THEN
  REMOVE_THEN "Q" (MP_TAC o SPEC `q:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  EXISTS_TAC `cm:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "C" (MP_TAC o SPECL [`c:real`; `x:real^3`; `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC P3S_CAP_GS_POS THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

