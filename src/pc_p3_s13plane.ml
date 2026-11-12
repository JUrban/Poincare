(* ========================================================================= *)
(* Unit pc_p3_s13plane (Part 3 proofs; MT Ch 13, sections 13.2             *)
(* and 13.3): the plane calculus for the curvature of the surgery metric.   *)
(* Reduction of a plane to an orthonormal pair, the conformal formula of    *)
(* pc_p3_s13conf on orthonormal pairs, chain rules for the differential and *)
(* the Hessian of F o phi, the cylinder model in the neck coordinates       *)
(* (s = sqrt 2 log|y| has unit gradient and zero Hessian, K = (1 - sigma)/2 *)
(* with sigma = ds(u)^2 + ds(v)^2), and linear perturbation bounds for      *)
(* C^2-close metrics in a frame.                                            *)
(* ========================================================================= *)

needs "src/pc_p3_s13col.ml";;
needs "src/pc_p3_s13conf.ml";;
needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Every plane has a G-orthonormal basis spanning it, and the               *)
(* sectional curvature of every metric field is the same on the new basis  *)
(* (shear and scaling invariance).  The conformal formula on G-orthonormal  *)
(* pairs:  Khat = e^{2F} (K + Hess F(u,u) + Hess F(v,v) + dF(u)^2 +          *)
(* dF(v)^2 - |dF|^2).                                                        *)
(* ------------------------------------------------------------------------- *)

let P3S_PLANE_ONB = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?c1 c2 c. ~(c1 = &0) /\ ~(c2 = &0) /\
                   (c1 % u) dot (G y ** (c1 % u)) = &1 /\
                   (c2 % (v - c % u)) dot (G y ** (c2 % (v - c % u))) = &1 /\
                   (c1 % u) dot (G y ** (c2 % (v - c % u))) = &0 /\
                   ~collinear {vec 0,c1 % u,c2 % (v - c % u)} /\
                   (!H. metric_field U H
                        ==> lsectional H y (c1 % u) (c2 % (v - c % u)) =
                            lsectional H y u v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  ABBREV_TAC `nu = (u:real^N) dot ((G:real^N->real^N^N) y ** u)` THEN
  SUBGOAL_THEN `&0 < nu` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = ((u:real^N) dot ((G:real^N->real^N^N) y ** v)) / nu` THEN
  ABBREV_TAC `w = (v:real^N) - c0 % u` THEN
  SUBGOAL_THEN `~(w:real^N = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nw = (w:real^N) dot ((G:real^N->real^N^N) y ** w)` THEN
  SUBGOAL_THEN `&0 < nw` ASSUME_TAC THENL
   [EXPAND_TAC "nw" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) dot ((G:real^N->real^N^N) y ** w) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB;
                DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c0" THEN
    UNDISCH_TAC `&0 < nu` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt nu /\ &0 < sqrt nw /\ sqrt nu pow 2 = nu /\ sqrt nw pow 2 = nw`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(sqrt nu)`; `inv(sqrt nw)`; `c0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(sqrt nu) * inv(sqrt nu) * nu = &1 /\
                inv(sqrt nw) * inv(sqrt nw) * nw = &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `sqrt nu pow 2 = nu` THEN UNDISCH_TAC `&0 < sqrt nu`;
      UNDISCH_TAC `sqrt nw pow 2 = nw` THEN UNDISCH_TAC `&0 < sqrt nw`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** w) = &0` THEN
    SUBGOAL_THEN `(w:real^N) = (sqrt nw * c * inv(sqrt nu)) % u` SUBST1_TAC THENL
     [MP_TAC(AP_TERM `(%) (sqrt nw):real^N->real^N` (ASSUME
        `inv(sqrt nw) % (w:real^N) = c % inv(sqrt nu) % u`)) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `sqrt nw * inv(sqrt nw) = &1` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `inv(sqrt nw) % (w:real^N) = c % inv(sqrt nu) % u` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_INV_EQ_0];
    X_GEN_TAC `H:real^N->real^N^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`; `inv(sqrt nu)`;
                   `inv(sqrt nw)`; `u:real^N`; `w:real^N`] P3S_LSECT_HOMOG) THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "w" THEN MATCH_MP_TAC LSECTIONAL_SHEAR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P3S_CONF_SECT_ON = prove
 (`!U (G:real^N->real^N^N) cf y u v.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> lsectional (\z. exp(--(&2 * cf z)) %% G z) y u v =
         exp(&2 * cf y) *
         (lsectional G y u v + p3s_chess G cf y u u + p3s_chess G cf y v v +
          p3s_cdf cf y u pow 2 + p3s_cdf cf y v pow 2 -
          p3s_cdf cf y (p3s_cgrad G cf y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `u:real^N`; `v:real^N`] P3S_CONF_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_MUL_RID; REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chain rules for Fr o phi (Fr a real function, phi a smooth                 *)
(* real function on an open set): d(Fr o phi) = Fr'(phi) d phi,               *)
(* Hess(Fr o phi) = Fr''(phi) d phi (x) d phi + Fr'(phi) Hess phi, and         *)
(* |d(Fr o phi)|^2 = Fr'(phi)^2 |d phi|^2.                                    *)
(* ------------------------------------------------------------------------- *)

let P3S_CDF_COMPOSE = prove
 (`!U (phi:real^N->real) (Fr:real->real) Fr1 y a.
     open U /\ y IN U /\ smooth_map_on U (\z. lift(phi z)) /\
     (Fr has_real_derivative Fr1) (atreal (phi y))
     ==> p3s_cdf (\z. Fr(phi z)) y a = Fr1 * p3s_cdf phi y a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cdf] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real`; `y:real^N`] P3S_CF_HAS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Fr:real->real`; `Fr1:real`; `\z:real^N. lift(phi z)`;
                 `\h:real^N. lift(p3s_cdf phi y h)`; `y:real^N`]
                LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP; p3s_cdf]);;

let P3S_CD2F_COMPOSE = prove
 (`!U V (phi:real^N->real) (Fr:real->real) Fr1 Fr2 y a b.
     open U /\ y IN U /\ smooth_map_on U (\z. lift(phi z)) /\
     real_open V /\ (!z. z IN U ==> phi z IN V) /\
     (!t. t IN V ==> (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (phi y))
     ==> p3s_cd2f (\z. Fr(phi z)) y a b =
         Fr2 * p3s_cdf phi y a * p3s_cdf phi y b + Fr1(phi y) * p3s_cd2f phi y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cd2f] THEN
  SUBGOAL_THEN
   `!z. z IN U
        ==> frechet_derivative (\x. lift(Fr((phi:real^N->real) x))) (at z) b =
            Fr1(phi z) % frechet_derivative (\x. lift(phi x)) (at z) b`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real`; `Fr:real->real`;
                   `(Fr1:real->real) (phi(z:real^N))`; `z:real^N`; `b:real^N`]
                  P3S_CDF_COMPOSE) THEN
    ASM_SIMP_TAC[p3s_cdf] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
    ALL_TAC] THEN
  ABBREV_TAC `Db = \z:real^N. frechet_derivative (\x. lift((phi:real^N->real) x)) (at z) b` THEN
  SUBGOAL_THEN `((Db:real^N->real^1) has_derivative frechet_derivative Db (at y)) (at y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Db" THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\z:real^N. frechet_derivative (\x. lift((phi:real^N->real) x)) (at z) b`]
                  SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. frechet_derivative (\x. lift(Fr((phi:real^N->real) x))) (at z) b) has_derivative
     (\h. Fr1(phi y) % frechet_derivative (Db:real^N->real^1) (at y) h +
          (Fr2 * p3s_cdf phi y h) % Db y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. (Fr1:real->real)((phi:real^N->real) z) % (Db:real^N->real^1) z` THEN
    MP_TAC(ISPEC `U:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "Db" THEN BETA_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `Fr:real->real`)) (concl th) && is_forall (concl th))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z:real^N. (Fr1:real->real)((phi:real^N->real) z)`;
                   `\h:real^N. Fr2 * p3s_cdf (phi:real^N->real) y h`;
                   `Db:real^N->real^1`; `frechet_derivative (Db:real^N->real^1) (at y)`;
                   `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_DEF] THEN BETA_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`Fr1:real->real`; `Fr2:real`; `\z:real^N. lift(phi z)`;
                   `\h:real^N. lift(p3s_cdf phi y h)`; `y:real^N`]
                  LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_CF_HAS_DERIV THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  SUBGOAL_THEN `(Db:real^N->real^1) y = lift(p3s_cdf phi y b)` SUBST1_TAC THENL
   [EXPAND_TAC "Db" THEN REWRITE_TAC[p3s_cdf; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let P3S_CHESS_COMPOSE = prove
 (`!U V (G:real^N->real^N^N) (phi:real^N->real) (Fr:real->real) Fr1 Fr2 y a b.
     open U /\ y IN U /\ smooth_map_on U (\z. lift(phi z)) /\
     real_open V /\ (!z. z IN U ==> phi z IN V) /\
     (!t. t IN V ==> (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (phi y))
     ==> p3s_chess G (\z. Fr(phi z)) y a b =
         Fr2 * p3s_cdf phi y a * p3s_cdf phi y b + Fr1(phi y) * p3s_chess G phi y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_chess] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real->bool`; `phi:real^N->real`; `Fr:real->real`;
                 `Fr1:real->real`; `Fr2:real`; `y:real^N`; `a:real^N`; `b:real^N`]
                P3S_CD2F_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real`; `Fr:real->real`;
                 `(Fr1:real->real)(phi(y:real^N))`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y a b`] P3S_CDF_COMPOSE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_GRADSQ_COMPOSE = prove
 (`!U (G:real^N->real^N^N) (phi:real^N->real) (Fr:real->real) Fr1 y.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(phi z)) /\
     (Fr has_real_derivative Fr1) (atreal (phi y)) /\
     (\z. lift(Fr(phi z))) differentiable at y
     ==> p3s_cdf (\z. Fr(phi z)) y (p3s_cgrad G (\z. Fr(phi z)) y) =
         Fr1 pow 2 * p3s_cdf phi y (p3s_cgrad G phi y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((phi:real^N->real) z)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g1 = p3s_cgrad (G:real^N->real^N^N) (\z. (Fr:real->real)((phi:real^N->real) z)) y` THEN
  ABBREV_TAC `g2 = p3s_cgrad (G:real^N->real^N^N) (phi:real^N->real) y` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real`; `Fr:real->real`; `Fr1:real`;
                 `y:real^N`; `g1:real^N`] P3S_CDF_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `phi:real^N->real`; `y:real^N`;
                 `g1:real^N`] P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `g1:real^N`;
                 `g2:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z. (Fr:real->real)((phi:real^N->real) z)`;
                 `y:real^N`; `g2:real^N`] P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real`; `Fr:real->real`; `Fr1:real`;
                 `y:real^N`; `g2:real^N`] P3S_CDF_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cylinder model in the neck coordinates.  With                        *)
(* q(z) = z.z and s = (sqrt 2 / 2) log q (= sqrt 2 log|z| off the origin),  *)
(* for the metric cyl0 = cylinder_flow 0 = 2|y|^-2 delta: ds has unit norm, *)
(* Hess s = 0, and on cyl0-orthonormal pairs K = (1 - ds(u)^2 - ds(v)^2)/2; *)
(* R = 1; and the curvature tensor of cyl0 is bounded in every frame.       *)
(* ------------------------------------------------------------------------- *)

let p3s_sy = new_definition
 `p3s_sy (z:real^3) = sqrt(&2) / &2 * log(z dot z)`;;

let P3S_SY_EQ = prove
 (`!y:real^3. ~(y = vec 0) ==> p3s_sy y = sqrt(&2) * log(norm y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_sy; GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC);;

let P3S_Q_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s (\z:real^3. lift(z dot z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\z:real^3. z`; `\z:real^3. z`] SMOOTH_MAP_ON_DOT_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let P3S_Q_CDF = prove
 (`!(y:real^3) a. p3s_cdf (\z. z dot z) y a = &2 * (y dot a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3s_cdf] THEN
  MP_TAC(ISPEC `y:real^3` HAS_DERIVATIVE_SQNORM_AT) THEN
  REWRITE_TAC[NORM_POW_2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP]);;

let P3S_Q_CD2F = prove
 (`!(y:real^3) a b. p3s_cd2f (\z. z dot z) y a b = &2 * (a dot b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3s_cd2f] THEN
  SUBGOAL_THEN `(\z:real^3. frechet_derivative (\x. lift(x dot x)) (at z) b) =
                (\z. lift(&2 * (z dot b)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MP_TAC(ISPEC `z:real^3` HAS_DERIVATIVE_SQNORM_AT) THEN
    REWRITE_TAC[NORM_POW_2] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[LIFT_CMUL; DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\z:real^3. lift(&2 * (z dot b))) has_derivative
                 (\z. lift(&2 * (z dot b)))) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP]);;

let P3S_CYL0_CHRISTOFFEL = prove
 (`!y u v:real^3.
     ~(y = vec 0)
     ==> christoffel (cylinder_flow (&0)) y u v =
         (--(&1) / norm y pow 2) % ((y dot u) % v + (y dot v) % u - (u dot v) % y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CYL_FLOW_CHRISTOFFEL THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3S_Q_CHESS = prove
 (`!(y:real^3) a b.
     ~(y = vec 0)
     ==> p3s_chess (cylinder_flow (&0)) (\z. z dot z) y a b =
         &4 * (y dot a) * (y dot b) / (y dot y)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[p3s_chess; P3S_Q_CD2F; P3S_Q_CDF; P3S_CYL0_CHRISTOFFEL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB; NORM_POW_2] THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let P3S_SY_FR = prove
 (`!t. &0 < t
       ==> ((\t. sqrt(&2) / &2 * log t) has_real_derivative
            (sqrt(&2) / &2 * inv t)) (atreal t) /\
           ((\t. sqrt(&2) / &2 * inv t) has_real_derivative
            (sqrt(&2) / &2 * --inv(t pow 2))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG; HAS_REAL_DERIVATIVE_INV_BASIC; REAL_LT_IMP_NZ]);;

let P3S_SY_SMOOTH = prove
 (`smooth_map_on ((:real^3) DELETE vec 0) (\z. lift(p3s_sy z))`,
  REWRITE_TAC[p3s_sy; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  REWRITE_TAC[P3S_OPEN_PUNCT] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\z:real^3. lift(z dot z)`]
         SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; LIFT_DROP; IN_DELETE; IN_UNIV] THEN
  SIMP_TAC[P3S_Q_SMOOTH; P3S_OPEN_PUNCT; DOT_POS_LT]);;

let P3S_SY_CDF = prove
 (`!(y:real^3) a. ~(y = vec 0)
                  ==> p3s_cdf p3s_sy y a = sqrt(&2) * (y dot a) / (y dot y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_sy = (\z:real^3. (\t. sqrt(&2) / &2 * log t) ((\z. z dot z) z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_sy]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\z:real^3. z dot z`;
                 `\t. sqrt(&2) / &2 * log t`; `sqrt(&2) / &2 * inv((y:real^3) dot y)`;
                 `y:real^3`; `a:real^3`] P3S_CDF_COMPOSE) THEN
  BETA_TAC THEN ASM_SIMP_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV; P3S_Q_SMOOTH; P3S_SY_FR] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[P3S_Q_CDF] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN CONV_TAC REAL_FIELD);;

let P3S_SY_CHESS = prove
 (`!(y:real^3) a b. ~(y = vec 0)
                    ==> p3s_chess (cylinder_flow (&0)) p3s_sy y a b = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_sy = (\z:real^3. (\t. sqrt(&2) / &2 * log t) ((\z. z dot z) z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_sy]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `{t:real | &0 < t}`;
                 `cylinder_flow (&0)`; `\z:real^3. z dot z`;
                 `\t. sqrt(&2) / &2 * log t`; `\t. sqrt(&2) / &2 * inv t`;
                 `sqrt(&2) / &2 * --inv(((y:real^3) dot y) pow 2)`;
                 `y:real^3`; `a:real^3`; `b:real^3`] P3S_CHESS_COMPOSE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[P3S_Q_SMOOTH; P3S_OPEN_PUNCT; DOT_POS_LT; P3S_SY_FR] THEN
    REWRITE_TAC[GSYM real_gt; REAL_OPEN_HALFSPACE_GT];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[P3S_Q_CDF; P3S_Q_CHESS] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN CONV_TAC REAL_FIELD);;

let P3S_CGRAD_UNIQUE = prove
 (`!U (G:real^N->real^N^N) cf y g.
     metric_field U G /\ y IN U /\ (\z. lift(cf z)) differentiable at y /\
     (!w. w dot (G y ** g) = p3s_cdf cf y w)
     ==> p3s_cgrad G cf y = g`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `p3s_cgrad (G:real^N->real^N^N) cf y - g`] LRG_METRIC_POS) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `p3s_cgrad (G:real^N->real^N^N) cf y - g`] P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_ON_NONCOLL = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> ~collinear {vec 0,u,v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** u) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `(v:real^N) dot ((G:real^N->real^N^N) y ** v) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** v) = &0` THEN
    UNDISCH_TAC `(v:real^N) dot ((G:real^N->real^N^N) y ** v) = &1` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL; REAL_MUL_RID] THEN
    DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC `c * c = &1` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P3S_SY_GRADSQ = prove
 (`!y:real^3. ~(y = vec 0)
              ==> p3s_cdf p3s_sy y (p3s_cgrad (cylinder_flow (&0)) p3s_sy y) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_cgrad (cylinder_flow (&0)) p3s_sy y = (sqrt(&2) / &2) % (y:real^3)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P3S_CGRAD_UNIQUE THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; IN_DELETE; IN_UNIV] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[P3S_OPEN_PUNCT; P3S_SY_SMOOTH; IN_DELETE; IN_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN ASM_SIMP_TAC[P3S_SY_CDF] THEN
    REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL;
                NORM_POW_2] THEN
    REWRITE_TAC[DOT_SYM] THEN UNDISCH_TAC `&0 < (y:real^3) dot y` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_CDF; DOT_RMUL] THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN CONV_TAC REAL_FIELD);;

let P3S_CYL0_SECT_ON = prove
 (`!y u v:real^3.
     ~(y = vec 0) /\
     u dot (cylinder_flow (&0) y ** u) = &1 /\ v dot (cylinder_flow (&0) y ** v) = &1 /\
     u dot (cylinder_flow (&0) y ** v) = &0
     ==> lsectional (cylinder_flow (&0)) y u v =
         (&1 - (p3s_cdf p3s_sy y u pow 2 + p3s_cdf p3s_sy y v pow 2)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`y:real^3`; `u:real^3`; `v:real^3`] LSECTIONAL_CYLINDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`; `y:real^3`] THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; IN_DELETE; IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_CDF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID;
                              DOT_RMUL]) THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_CYL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) dot u = norm(y:real^3) pow 2 / &2 /\
                (v:real^3) dot v = norm(y:real^3) pow 2 / &2 /\ (u:real^3) dot v = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `&2 / norm(y:real^3) pow 2`)) (concl th)))) THEN
    UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN
  UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN CONV_TAC REAL_FIELD);;

let P3S_CYL0_SCALAR = prove
 (`!y:real^3. ~(y = vec 0) ==> lscalar (cylinder_flow (&0)) y = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&0`; `y:real^3`] RFB_CYL_SCALAR) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let P3S_CYL0_FRAME_RM = prove
 (`?K. &0 <= K /\
       !(y:real^3) (M:real^3^3).
         ~(y = vec 0) /\ cylinder_flow (&0) y = transp M ** M
         ==> !u v w. norm(M ** lriemann (cylinder_flow (&0)) y u v w) <=
                     K * norm(M ** u) * norm(M ** v) * norm(M ** w)`,
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  EXISTS_TAC `abs K0` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (cylinder_flow (&0))` ASSUME_TAC THENL
   [SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_RM0_BOUND THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_UNIV; REAL_ABS_POS] THEN GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                 `lrm4 (cylinder_flow (&0))`; `y:real^3`; `M:real^3^3`; `u:num->real^3`;
                 `K0 pow 2`] LRG_FRAME_BOUND_DELTA) THEN
  ASM_REWRITE_TAC[PRODUCT_4; POW_2_SQRT_ABS; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Linear perturbation bounds in a frame M of G0 (G0 = M^T M)               *)
(* when lck_dist2 2 G0 G y <= D^2: the metric difference and its covariant *)
(* derivative are bounded by D, the Christoffel difference by 2 D           *)
(* (D <= 1/10), and the squared norm of a differential changes by a factor  *)
(* in [1/(1 + D), 1/(1 - D)].                                               *)
(* ------------------------------------------------------------------------- *)

let P3S_PERT_METRIC = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) D.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= D /\ lck_dist2 2 G0 G y <= D pow 2
     ==> !a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
               D * norm(M ** a) * norm(M ** b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                 `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                 `D pow 2`] LRG_FRAME_BOUND_DELTA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lck_dist2 2 (G0:real^N->real^N^N) G y` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
    ASM_SIMP_TAC[PRODUCT_2; lmetric2; ARITH; POW_2_SQRT]]);;

let P3S_PERT_NABLA = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) D.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= D /\ lck_dist2 2 G0 G y <= D pow 2
     ==> !u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
             D * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 2 (G0:real^N->real^N^N)
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                 `y:real^N`; `M:real^N^N`; `u:num->real^N`; `D pow 2`]
                LRG_FRAME_BOUND_DELTA) THEN
  ASM_SIMP_TAC[PRODUCT_3; POW_2_SQRT] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lck_dist2 2 (G0:real^N->real^N^N) G y` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
  REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

let P3S_FRAME_DOT_LE = prove
 (`!(A:real^N^N) (M:real^N^N) a b.
     A = transp M ** M ==> abs(a dot (A ** b)) <= norm(M ** a) * norm(M ** b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LRG_FRAME_DOT th)]) THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;

let P3S_FRAME_SQ = prove
 (`!(A:real^N^N) (M:real^N^N) a.
     A = transp M ** M ==> a dot (A ** a) = norm(M ** a) pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LRG_FRAME_DOT th)]) THEN
  REWRITE_TAC[NORM_POW_2]);;

let P3S_PERT_CHRIST = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) D.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= D /\ D <= &1 / &10 /\ lck_dist2 2 G0 G y <= D pow 2
     ==> !a b. norm(M ** (christoffel G y a b - christoffel G0 y a b)) <=
               &2 * D * norm(M ** a) * norm(M ** b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `x = christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `D:real`] P3S_PERT_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `x:real^N`]) THEN
  MP_TAC(ISPECL [`(G0:real^N->real^N^N) y`; `M:real^N^N`; `x:real^N`] P3S_FRAME_SQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(LABEL_TAC "MD") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `D:real`] P3S_PERT_NABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "NB") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `\m. if m = 1 then (a:real^N) else if m = 2 then b else x`]
                LRG_CHRISTOFFEL_DIFF_K) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(LABEL_TAC "CD") THEN
  SUBGOAL_THEN `abs((x:real^N) dot ((G:real^N->real^N^N) y ** x)) <=
                &3 / &2 * D * norm((M:real^N^N) ** a) * norm(M ** b) * norm(M ** x)`
  (LABEL_TAC "XB") THENL
   [USE_THEN "CD" SUBST1_TAC THEN
    USE_THEN "NB" (fun th ->
      MP_TAC(SPEC `\m. if (swap(1,2) o swap(2,3)) m = 1 then (a:real^N)
                       else if (swap(1,2) o swap(2,3)) m = 2 then b else x` th) THEN
      MP_TAC(SPEC `\m. if swap(2,3) m = 1 then (a:real^N)
                       else if swap(2,3) m = 2 then b else x` th) THEN
      MP_TAC(SPEC `\m. if m = 1 then (a:real^N) else if m = 2 then b else x` th)) THEN
    REWRITE_TAC[o_THM; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "CD" (K ALL_TAC) THEN
  ABBREV_TAC `nx = norm((M:real^N^N) ** x)` THEN
  ABBREV_TAC `p = norm((M:real^N^N) ** a) * norm(M ** b)` THEN
  SUBGOAL_THEN `&0 <= nx /\ &0 <= p` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["nx"; "p"] THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - D) * nx pow 2 <= &3 / &2 * D * p * nx` ASSUME_TAC THENL
   [REMOVE_THEN "XB" MP_TAC THEN REMOVE_THEN "MD" MP_TAC THEN
    EXPAND_TAC "p" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `nx = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < nx` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - D) * nx <= &3 / &2 * D * p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `nx:real` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(&1 - D) * nx pow 2 <= &3 / &2 * D * p * nx` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D * p <= &1 / &10 * p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `D * nx <= &1 / &10 * nx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_PERT_GRAD = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) D cf.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= D /\ D < &1 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <= D * norm(M ** a) * norm(M ** b)) /\
     (\z. lift(cf z)) differentiable at y
     ==> p3s_cdf cf y (p3s_cgrad G cf y) <=
         p3s_cdf cf y (p3s_cgrad G0 cf y) / (&1 - D) /\
         p3s_cdf cf y (p3s_cgrad G0 cf y) / (&1 + D) <=
         p3s_cdf cf y (p3s_cgrad G cf y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PM") ASSUME_TAC))))))) THEN
  ABBREV_TAC `g = p3s_cgrad (G:real^N->real^N^N) cf y` THEN
  ABBREV_TAC `g0 = p3s_cgrad (G0:real^N->real^N^N) cf y` THEN
  SUBGOAL_THEN `!w. w dot ((G:real^N->real^N^N) y ** g) = p3s_cdf cf y w /\
                    w dot ((G0:real^N->real^N^N) y ** g0) = p3s_cdf cf y w`
  (LABEL_TAC "GD") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["g"; "g0"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P3S_CGRAD_DOT THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real^N^N` (ASSUME_TAC o CONJUNCT2)) THEN
  SUBGOAL_THEN `p3s_cdf cf y (g:real^N) = norm((M1:real^N^N) ** g) pow 2` ASSUME_TAC THENL
   [USE_THEN "GD" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(SPEC `g:real^N` th))]) THEN
    MATCH_MP_TAC P3S_FRAME_SQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3s_cdf cf y (g0:real^N) = norm((M:real^N^N) ** g0) pow 2` ASSUME_TAC THENL
   [USE_THEN "GD" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(SPEC `g0:real^N` th))]) THEN
    MATCH_MP_TAC P3S_FRAME_SQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(p3s_cdf cf y (g:real^N)) <= norm((M:real^N^N) ** g0) * norm(M ** g)`
  ASSUME_TAC THENL
   [USE_THEN "GD" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(SPEC `g:real^N` th))]) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `g:real^N`;
                   `g0:real^N`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P3S_FRAME_DOT_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(p3s_cdf cf y (g0:real^N)) <= norm((M1:real^N^N) ** g0) * norm(M1 ** g)`
  ASSUME_TAC THENL
   [USE_THEN "GD" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(SPEC `g0:real^N` th))]) THEN
    MATCH_MP_TAC P3S_FRAME_DOT_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:real^N) dot ((G:real^N->real^N^N) y ** g) = norm((M1:real^N^N) ** g) pow 2 /\
    (g0:real^N) dot ((G:real^N->real^N^N) y ** g0) = norm((M1:real^N^N) ** g0) pow 2 /\
    (g:real^N) dot ((G0:real^N->real^N^N) y ** g) = norm((M:real^N^N) ** g) pow 2 /\
    (g0:real^N) dot ((G0:real^N->real^N^N) y ** g0) = norm((M:real^N^N) ** g0) pow 2`
  (LABEL_TAC "SQ") THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC P3S_FRAME_SQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(norm((M1:real^N^N) ** g) pow 2 - norm((M:real^N^N) ** g) pow 2) <=
    D * norm(M ** g) * norm(M ** g) /\
    abs(norm((M1:real^N^N) ** g0) pow 2 - norm((M:real^N^N) ** g0) pow 2) <=
    D * norm(M ** g0) * norm(M ** g0)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "PM" (fun th -> MP_TAC(SPECL [`g:real^N`; `g:real^N`] th) THEN
                             MP_TAC(SPECL [`g0:real^N`; `g0:real^N`] th)) THEN
    USE_THEN "SQ" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = norm((M1:real^N^N) ** g)`; `a0 = norm((M:real^N^N) ** g)`;
    `b1 = norm((M1:real^N^N) ** g0)`; `b0 = norm((M:real^N^N) ** g0)`] THEN
  SUBGOAL_THEN `&0 <= a1 /\ &0 <= a0 /\ &0 <= b1 /\ &0 <= b0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a1"; "a0"; "b1"; "b0"] THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `abs(p3s_cdf cf y (g:real^N)) <= b0 * a0` THEN
  UNDISCH_TAC `abs(p3s_cdf cf y (g0:real^N)) <= b1 * a1` THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 - D /\ &0 < &1 + D` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(&1 - D) * a0 pow 2 <= a1 pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(a1 pow 2 - a0 pow 2) <= D * a0 * a0` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a1 pow 2) pow 2 <= b0 pow 2 * a0 pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      UNDISCH_TAC `abs(a1 pow 2) <= b0 * a0` THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LE_MUL; REAL_ARITH `&0 <= x ==> abs x = x`];
      ALL_TAC] THEN
    ASM_CASES_TAC `a1 pow 2 = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < a1 pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `a1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `a1 pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - D) * (b0 pow 2 * a0 pow 2)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(a1 pow 2 * (&1 - D)) * a1 pow 2 = (&1 - D) * (a1 pow 2) pow 2`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `(&1 - D) * (b0 pow 2 * a0 pow 2) = b0 pow 2 * ((&1 - D) * a0 pow 2)`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    SUBGOAL_THEN `b1 pow 2 <= (&1 + D) * b0 pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(b1 pow 2 - b0 pow 2) <= D * b0 * b0` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(b0 pow 2) pow 2 <= b1 pow 2 * a1 pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      UNDISCH_TAC `abs(b0 pow 2) <= b1 * a1` THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LE_MUL; REAL_ARITH `&0 <= x ==> abs x = x`];
      ALL_TAC] THEN
    ASM_CASES_TAC `b0 pow 2 = &0` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b0 pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `b0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `b0 pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b1 pow 2 * a1 pow 2` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `(a1 pow 2 * (&1 + D)) * b0 pow 2 = ((&1 + D) * b0 pow 2) * a1 pow 2`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

(* ------------------------------------------------------------------------- *)
(* The plane functional pl_A(beta)(u,v), the trace of a                     *)
(* symmetric bilinear form over the plane of u, v in the inner product A:   *)
(*   (beta(u,u) A(v,v) + beta(v,v) A(u,u) - 2 beta(u,v) A(u,v)) / Gram.      *)
(* It is invariant under shear and scaling of the basis, equals              *)
(* beta(u,u) + beta(v,v) on A-orthonormal pairs, and moves by at most        *)
(* 7 B D when A is D-close to A0 and beta is bounded by B (A0-frame norms).  *)
(* The conformal formula in this form.                                       *)
(* ------------------------------------------------------------------------- *)

let p3s_pl = new_definition
 `p3s_pl (A:real^N^N) (beta:real^N->real^N->real) (u:real^N) (v:real^N) =
    (beta u u * (v dot (A ** v)) + beta v v * (u dot (A ** u)) -
     &2 * beta u v * (u dot (A ** v))) /
    ((u dot (A ** u)) * (v dot (A ** v)) - (u dot (A ** v)) pow 2)`;;

let P3S_PL_ON = prove
 (`!(A:real^N^N) beta u v.
     u dot (A ** u) = &1 /\ v dot (A ** v) = &1 /\ u dot (A ** v) = &0
     ==> p3s_pl A beta u v = beta u u + beta v v`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p3s_pl] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1] THEN REAL_ARITH_TAC);;

let P3S_PL_SCALE = prove
 (`!(A:real^N^N) (beta:real^N->real^N->real) u v c d.
     ~(c = &0) /\ ~(d = &0) /\
     (!r a b. beta (r % a) b = r * beta a b) /\ (!r a b. beta a (r % b) = r * beta a b)
     ==> p3s_pl A beta (c % u) (d % v) = p3s_pl A beta u v`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[p3s_pl; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_CASES_TAC `(u dot ((A:real^N^N) ** u)) * (v dot (A ** v)) - (u dot (A ** v)) pow 2 = &0`
  THENL
   [SUBGOAL_THEN
     `(c * c * (u dot ((A:real^N^N) ** u))) * (d * d * (v dot (A ** v))) -
      (c * d * (u dot (A ** v))) pow 2 = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(u dot ((A:real^N^N) ** u)) * (v dot (A ** v)) -
                   (u dot (A ** v)) pow 2 = &0` THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((c * d) pow 2 = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_ENTIRE; ARITH_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `~((u dot ((A:real^N^N) ** u)) * (v dot (A ** v)) -
                 (u dot (A ** v)) pow 2 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let P3S_PL_SHEAR = prove
 (`!(A:real^N^N) (beta:real^N->real^N->real) u v c.
     transp A = A /\
     (!a b. beta a b = beta b a) /\
     (!a b w. beta a (b - w) = beta a b - beta a w) /\
     (!r a b. beta a (r % b) = r * beta a b)
     ==> p3s_pl A beta u (v - c % u) = p3s_pl A beta u v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b w r. (beta:real^N->real^N->real) (a - b) w = beta a w - beta b w /\
                          beta (r % a) b = r * beta a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN ONCE_REWRITE_TAC[ASSUME
      `!a b. (beta:real^N->real^N->real) a b = beta b a`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^N. a dot ((A:real^N^N) ** b) = b dot (A ** a)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ASM_REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3s_pl; MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                  DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(v:real^N) dot ((A:real^N^N) ** u) = u dot (A ** v) /\
                (beta:real^N->real^N->real) v u = beta u v`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`p = (u:real^N) dot ((A:real^N^N) ** u)`; `r = (v:real^N) dot ((A:real^N^N) ** v)`;
    `m = (u:real^N) dot ((A:real^N^N) ** v)`;
    `bp = (beta:real^N->real^N->real) u u`; `br = (beta:real^N->real^N->real) v v`;
    `bm = (beta:real^N->real^N->real) u v`] THEN
  SUBGOAL_THEN `p * (r - c * m - c * (m - c * p)) - (m - c * p) pow 2 = p * r - m pow 2`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let P3S_GRAM_POS = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> &0 < (u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`; `v:real^N`]
         P3S_PLANE_ONB) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL;
              DOT_LSUB; DOT_RSUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`; `u:real^N`]
         LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`p = (u:real^N) dot ((G:real^N->real^N^N) y ** u)`;
    `r = (v:real^N) dot ((G:real^N->real^N^N) y ** v)`;
    `m = (u:real^N) dot ((G:real^N->real^N^N) y ** v)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `c:real`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `m = c * p` ASSUME_TAC THENL
   [UNDISCH_TAC `c1 * c2 * (m - c * p) = &0` THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p * r - m pow 2 = inv((c1 * c2) pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `c1 * c1 * p = &1` THEN
    UNDISCH_TAC `c2 * (c2 * (r - c * m) - c * c2 * (m - c * p)) = &1` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(c1 = &0)` THEN UNDISCH_TAC `~(c2 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_POW_2; REAL_LT_SQUARE; REAL_ENTIRE] THEN
  ASM_REWRITE_TAC[]);;

let P3S_CD2F_LIN = prove
 (`!U (cf:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> (!a1 a2 b. p3s_cd2f cf y (a1 - a2) b = p3s_cd2f cf y a1 b - p3s_cd2f cf y a2 b) /\
         (!r a b. p3s_cd2f cf y (r % a) b = r * p3s_cd2f cf y a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b. linear(frechet_derivative
                     (\z. frechet_derivative (\x. lift((cf:real^N->real) x)) (at z) b)
                     (at y))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  REWRITE_TAC[p3s_cd2f] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N`) THEN
  SIMP_TAC[LINEAR_SUB; LINEAR_CMUL; DROP_SUB; DROP_CMUL]);;

let P3S_CHESS_BILIN = prove
 (`!U (G:real^N->real^N^N) cf y.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> (!a b. p3s_chess G cf y a b = p3s_chess G cf y b a) /\
         (!a b w. p3s_chess G cf y (a - b) w =
                  p3s_chess G cf y a w - p3s_chess G cf y b w) /\
         (!r a b. p3s_chess G cf y (r % a) b = r * p3s_chess G cf y a b) /\
         (!a b w. p3s_chess G cf y a (b - w) =
                  p3s_chess G cf y a b - p3s_chess G cf y a w) /\
         (!r a b. p3s_chess G cf y a (r % b) = r * p3s_chess G cf y a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P3S_CD2F_LIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D2S") (LABEL_TAC "D2M")) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P3S_CDF_LIN3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "D1S") (LABEL_TAC "D1M"))) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CL" o CONJUNCT2) THEN
  SUBGOAL_THEN `!a b. p3s_chess (G:real^N->real^N^N) cf y a b = p3s_chess G cf y b a`
  (LABEL_TAC "SYM") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p3s_chess] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`; `a:real^N`;
                   `b:real^N`] P3S_CD2F_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                   `b:real^N`] CHRISTOFFEL_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b w. p3s_chess (G:real^N->real^N^N) cf y (a - b) w =
                        p3s_chess G cf y a w - p3s_chess G cf y b w`
  (LABEL_TAC "S1") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p3s_chess] THEN
    USE_THEN "CL" (fun th ->
      REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB (SPEC `w:real^N` th))]) THEN
    USE_THEN "D2S" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "D1S" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r a b. p3s_chess (G:real^N->real^N^N) cf y (r % a) b =
                        r * p3s_chess G cf y a b`
  (LABEL_TAC "M1") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p3s_chess] THEN
    USE_THEN "CL" (fun th ->
      REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL (SPEC `b:real^N` th))]) THEN
    USE_THEN "D2M" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "D1M" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "SYM" ACCEPT_TAC;
    USE_THEN "S1" ACCEPT_TAC;
    USE_THEN "M1" ACCEPT_TAC;
    REPEAT GEN_TAC THEN USE_THEN "SYM" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    USE_THEN "S1" MATCH_ACCEPT_TAC;
    REPEAT GEN_TAC THEN USE_THEN "SYM" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    USE_THEN "M1" MATCH_ACCEPT_TAC]);;

let P3S_CONF_SECT_PL = prove
 (`!U (G:real^N->real^N^N) cf y u v.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U /\
     ~collinear {vec 0,u,v}
     ==> lsectional (\z. exp(--(&2 * cf z)) %% G z) y u v =
         exp(&2 * cf y) *
         (lsectional G y u v +
          p3s_pl (G y) (\a b. p3s_chess G cf y a b + p3s_cdf cf y a * p3s_cdf cf y b) u v -
          p3s_cdf cf y (p3s_cgrad G cf y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `u:real^N`; `v:real^N`] P3S_CONF_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC P3S_GRAM_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p3s_pl] THEN BETA_TAC THEN REAL_ARITH_TAC);;

let P3S_PL_BASIS = prove
 (`!(A:real^N^N) (beta:real^N->real^N->real) u v c1 c2 c.
     transp A = A /\ ~(c1 = &0) /\ ~(c2 = &0) /\
     (!a b. beta a b = beta b a) /\
     (!a b w. beta a (b - w) = beta a b - beta a w) /\
     (!r a b. beta a (r % b) = r * beta a b)
     ==> p3s_pl A beta (c1 % u) (c2 % (v - c % u)) = p3s_pl A beta u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `beta:real^N->real^N->real`; `u:real^N`;
                 `v - c % u:real^N`; `c1:real`; `c2:real`] P3S_PL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [ASSUME `!a b. (beta:real^N->real^N->real) a b = beta b a`] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P3S_PL_SHEAR THEN ASM_REWRITE_TAC[]);;

let P3S_PL_ARITH = prove
 (`!buu bvv buv e1 e2 e3 B D.
     &0 <= D /\ D <= &1 / &10 /\ abs e1 <= D /\ abs e2 <= D /\ abs e3 <= D /\
     abs buu <= B /\ abs bvv <= B /\ abs buv <= B
     ==> abs((buu * (&1 + e2) + bvv * (&1 + e1) - &2 * buv * e3) /
             ((&1 + e1) * (&1 + e2) - e3 pow 2) - (buu + bvv)) <= &7 * B * D`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Gm = (&1 + e1) * (&1 + e2) - e3 pow 2` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MP_TAC(SPEC `buu:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e3 pow 2 <= D * D /\ (&1 - D) * (&1 - D) <= (&1 + e1) * (&1 + e2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * D <= &1 / &10 * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &5 <= Gm` ASSUME_TAC THENL
   [EXPAND_TAC "Gm" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(e1 * (&1 + e2)) <= D * (&11 / &10) /\
                abs(e2 * (&1 + e1)) <= D * (&11 / &10)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X1 = --(e1 * (&1 + e2)) + e3 pow 2` THEN
  ABBREV_TAC `X2 = --(e2 * (&1 + e1)) + e3 pow 2` THEN
  SUBGOAL_THEN `abs X1 <= &6 / &5 * D /\ abs X2 <= &6 / &5 * D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X1"; "X2"] THEN
    MP_TAC(SPEC `e3:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(buu * X1) <= B * (&6 / &5 * D) /\ abs(bvv * X2) <= B * (&6 / &5 * D) /\
                abs(buv * e3) <= B * D` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(buu * (&1 + e2) + bvv * (&1 + e1) - &2 * buv * e3) / Gm - (buu + bvv) =
    (buu * X1 + bvv * X2 - &2 * (buv * e3)) / Gm`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X1"; "X2"; "Gm"] THEN
    SUBGOAL_THEN `~((&1 + e1) * (&1 + e2) - e3 pow 2 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Gm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&22 / &5 * B * D` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&7 * B * D) * &4 / &5 <= (&7 * B * D) * Gm` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P3S_PL_PERT = prove
 (`!(A:real^N^N) A0 (M:real^N^N) (beta:real^N->real^N->real) u v B D.
     A0 = transp M ** M /\ &0 <= D /\ D <= &1 / &10 /\
     (!a b. abs(a dot (A ** b) - a dot (A0 ** b)) <= D * norm(M ** a) * norm(M ** b)) /\
     (!a b. abs(beta a b) <= B * norm(M ** a) * norm(M ** b)) /\
     u dot (A0 ** u) = &1 /\ v dot (A0 ** v) = &1 /\ u dot (A0 ** v) = &0
     ==> abs(p3s_pl A beta u v - (beta u u + beta v v)) <= &7 * B * D`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PA")
    (CONJUNCTS_THEN2 (LABEL_TAC "PB") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `norm((M:real^N^N) ** u) = &1 /\ norm((M:real^N^N) ** v) = &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A0:real^N^N`; `M:real^N^N`; `u:real^N`] P3S_FRAME_SQ) THEN
    MP_TAC(ISPECL [`A0:real^N^N`; `M:real^N^N`; `v:real^N`] P3S_FRAME_SQ) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[REAL_POW_EQ_1] THEN
    SIMP_TAC[REAL_ABS_NORM; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[p3s_pl] THEN
  MP_TAC(ISPECL [`(beta:real^N->real^N->real) u u`; `(beta:real^N->real^N->real) v v`;
                 `(beta:real^N->real^N->real) u v`;
                 `u dot ((A:real^N^N) ** u) - &1`; `v dot ((A:real^N^N) ** v) - &1`;
                 `u dot ((A:real^N^N) ** v)`; `B:real`; `D:real`] P3S_PL_ARITH) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "PB" (fun th -> MP_TAC(SPECL [`u:real^N`; `u:real^N`] th) THEN
                           MP_TAC(SPECL [`v:real^N`; `v:real^N`] th) THEN
                           MP_TAC(SPECL [`u:real^N`; `v:real^N`] th)) THEN
  USE_THEN "PA" (fun th -> MP_TAC(SPECL [`u:real^N`; `u:real^N`] th) THEN
                           MP_TAC(SPECL [`v:real^N`; `v:real^N`] th) THEN
                           MP_TAC(SPECL [`u:real^N`; `v:real^N`] th)) THEN
  REWRITE_TAC[ASSUME `norm((M:real^N^N) ** u) = &1`; ASSUME `norm((M:real^N^N) ** v) = &1`;
              ASSUME `u dot ((A0:real^N^N) ** u) = &1`;
              ASSUME `v dot ((A0:real^N^N) ** v) = &1`;
              ASSUME `u dot ((A0:real^N^N) ** v) = &0`; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let P3S_CDF_FRAME_BOUND = prove
 (`!U (G:real^N->real^N^N) cf y (M:real^N^N) a.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\
     (\z. lift(cf z)) differentiable at y
     ==> abs(p3s_cdf cf y a) <= sqrt(p3s_cdf cf y (p3s_cgrad G cf y)) * norm(M ** a)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = p3s_cgrad (G:real^N->real^N^N) cf y` THEN
  SUBGOAL_THEN `!w. w dot ((G:real^N->real^N^N) y ** g) = p3s_cdf cf y w` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3s_cdf cf y (g:real^N) = norm((M:real^N^N) ** g) pow 2` SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(SPEC `g:real^N` th)]) THEN
    MATCH_MP_TAC P3S_FRAME_SQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_NORM] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(SPEC `a:real^N` th)]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `g:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P3S_FRAME_DOT_LE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The conformal curvature estimate on the neck.  For a metric              *)
(* Ht that is D-close to cyl0 in C^2 at y (D <= 1/10) and F = Fr o s,       *)
(* every plane P = span(u,v) has a number sg in [0,1] (sg = |ds|_P|^2 in   *)
(* cyl0) with |K_Ht(P) - (1 - sg)/2| <= K D and                             *)
(*   e^{-2F} Khat(P) >= K_Ht(P) + Fr'' sg - Fr'^2 (1 - sg) - D E,           *)
(*   E = 6|Fr'| + 7|Fr''| + 9 Fr'^2,                                        *)
(* where Khat is the curvature of e^{-2F} Ht (MT Lemma 13.9 / Cor 13.10).   *)
(* ------------------------------------------------------------------------- *)

let P3S_BESSEL2 = prove
 (`!U (G:real^N->real^N^N) cf y u v.
     metric_field U G /\ y IN U /\ (\z. lift(cf z)) differentiable at y /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> p3s_cdf cf y u pow 2 + p3s_cdf cf y v pow 2 <=
         p3s_cdf cf y (p3s_cgrad G cf y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = p3s_cgrad (G:real^N->real^N^N) cf y` THEN
  SUBGOAL_THEN `!w. w dot ((G:real^N->real^N^N) y ** g) = p3s_cdf cf y w`
  (LABEL_TAC "GD") THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (ASSUME_TAC o CONJUNCT2)) THEN
  SUBGOAL_THEN `!a b. a dot ((G:real^N->real^N^N) y ** b) = ((M:real^N^N) ** a) dot (M ** b)`
  (LABEL_TAC "FD") THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "GD" (fun th -> REWRITE_TAC[GSYM(SPEC `u:real^N` th); GSYM(SPEC `v:real^N` th);
                                       GSYM(SPEC `g:real^N` th)]) THEN
  REMOVE_THEN "GD" (K ALL_TAC) THEN
  USE_THEN "FD" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  MAP_EVERY ABBREV_TAC [`x = (M:real^N^N) ** g`; `e1 = (M:real^N^N) ** u`;
                        `e2 = (M:real^N^N) ** v`] THEN
  MP_TAC(ISPEC `x - (e1 dot x) % e1 - (e2 dot x) % (e2:real^N)` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[DOT_SYM]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let P3S_SY_SMOOTH_ON = prove
 (`!U. U SUBSET (:real^3) DELETE vec 0 ==> smooth_map_on U (\z. lift(p3s_sy z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[P3S_SY_SMOOTH]);;

let P3S_CHESS_SY_G = prove
 (`!U (G:real^3->real^3^3) y a b.
     metric_field U G /\ U SUBSET (:real^3) DELETE vec 0 /\ y IN U
     ==> p3s_chess G p3s_sy y a b =
         --(p3s_cdf p3s_sy y (christoffel G y a b - christoffel (cylinder_flow (&0)) y a b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `p3s_sy`; `y:real^3`] P3S_CDF_LIN3) THEN
  ASM_REWRITE_TAC[P3S_OPEN_PUNCT; P3S_SY_SMOOTH; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
  MP_TAC(SPECL [`y:real^3`; `a:real^3`; `b:real^3`] P3S_SY_CHESS) THEN
  ASM_REWRITE_TAC[p3s_chess] THEN REAL_ARITH_TAC);;

let P3S_CHESS_F_G = prove
 (`!U (G:real^3->real^3^3) (Fr:real->real) Fr1 Fr2 y a b.
     metric_field U G /\ U SUBSET (:real^3) DELETE vec 0 /\ y IN U /\
     (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
     (Fr1 has_real_derivative Fr2) (atreal (p3s_sy y))
     ==> p3s_chess G (\z. Fr(p3s_sy z)) y a b =
         Fr2 * p3s_cdf p3s_sy y a * p3s_cdf p3s_sy y b -
         Fr1(p3s_sy y) *
         p3s_cdf p3s_sy y (christoffel G y a b - christoffel (cylinder_flow (&0)) y a b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(:real)`; `G:real^3->real^3^3`; `p3s_sy`;
                 `Fr:real->real`; `Fr1:real->real`; `Fr2:real`; `y:real^3`; `a:real^3`;
                 `b:real^3`] P3S_CHESS_COMPOSE) THEN
  ASM_SIMP_TAC[P3S_SY_SMOOTH_ON; REAL_OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`;
                 `b:real^3`] P3S_CHESS_SY_G) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_CDF_F = prove
 (`!U (Fr:real->real) Fr1 y a.
     open U /\ U SUBSET (:real^3) DELETE vec 0 /\ y IN U /\
     (!t. (Fr has_real_derivative Fr1 t) (atreal t))
     ==> p3s_cdf (\z. Fr(p3s_sy z)) y a = Fr1(p3s_sy y) * p3s_cdf p3s_sy y a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_CDF_COMPOSE THEN
  EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[P3S_SY_SMOOTH_ON]);;

let P3S_KHAT_ARITH = prove
 (`!K0 pl gsq Fr2 f1 du dv gu gv D Bb.
     Bb = abs Fr2 + f1 pow 2 + &2 * D * abs f1 /\
     abs(pl - ((Fr2 * du * du - f1 * gu + (f1 * du) * f1 * du) +
               Fr2 * dv * dv - f1 * gv + (f1 * dv) * f1 * dv)) <= &7 * Bb * D /\
     abs(f1 * gu) <= abs f1 * &2 * D /\ abs(f1 * gv) <= abs f1 * &2 * D /\
     D * &14 * D * abs f1 <= D * &2 * abs f1 /\
     gsq <= f1 pow 2 * (&1 + &2 * D)
     ==> K0 + Fr2 * (du pow 2 + dv pow 2) - f1 pow 2 * (&1 - (du pow 2 + dv pow 2)) -
         D * (&6 * abs f1 + &7 * abs Fr2 + &9 * f1 pow 2) <= K0 + pl - gsq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_NECK_KHAT = prove
 (`?K. &0 <= K /\
       !U (Ht:real^3->real^3^3) (Fr:real->real) Fr1 Fr2 y u v D.
         open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Ht /\ y IN U /\
         &0 <= D /\ D <= &1 / &10 /\ lck_dist2 2 (cylinder_flow (&0)) Ht y <= D pow 2 /\
         smooth_map_on (:real^1) (lift o Fr o drop) /\
         (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
         (Fr1 has_real_derivative Fr2) (atreal (p3s_sy y)) /\
         ~collinear {vec 0,u,v}
         ==> ?sg. &0 <= sg /\ sg <= &1 /\
                  abs(lsectional Ht y u v - (&1 - sg) / &2) <= K * D /\
                  lsectional Ht y u v + Fr2 * sg - Fr1(p3s_sy y) pow 2 * (&1 - sg) -
                  D * (&6 * abs(Fr1(p3s_sy y)) + &7 * abs Fr2 + &9 * Fr1(p3s_sy y) pow 2)
                  <= exp(--(&2 * Fr(p3s_sy y))) *
                     lsectional (\z. exp(--(&2 * Fr(p3s_sy z))) %% Ht z) y u v`,
  X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RMK")) P3S_CYL0_FRAME_RM THEN
  EXISTS_TAC `&8 * (&1 + K)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = p3s_sy y` THEN ABBREV_TAC `f1 = (Fr1:real->real) s0` THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((Fr:real->real)(p3s_sy z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(p3s_sy z)) differentiable at (y:real^3) /\
                (\z. lift((Fr:real->real)(p3s_sy z))) differentiable at y` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[P3S_SY_SMOOTH_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `y:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `y:real^3`; `u:real^3`;
                 `v:real^3`] P3S_PLANE_ONB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `c:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "INV")))))))))) THEN
  MAP_EVERY ABBREV_TAC [`u' = c1 % (u:real^3)`; `v' = c2 % ((v:real^3) - c % u)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `c1 % (u:real^3) = u'`;
                              ASSUME `c2 % ((v:real^3) - c % u) = v'`]) THEN
  SUBGOAL_THEN `&0 <= p3s_cdf p3s_sy y u' pow 2 + p3s_cdf p3s_sy y v' pow 2 /\
                p3s_cdf p3s_sy y u' pow 2 + p3s_cdf p3s_sy y v' pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    MP_TAC(SPEC `y:real^3` P3S_SY_GRADSQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC P3S_BESSEL2 THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lsectional (cylinder_flow (&0)) y u' v' =
                (&1 - (p3s_cdf p3s_sy y u' pow 2 + p3s_cdf p3s_sy y v' pow 2)) / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_CYL0_SECT_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sg = p3s_cdf p3s_sy y u' pow 2 + p3s_cdf p3s_sy y v' pow 2` THEN
  EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (cylinder_flow (&0)) (Ht:real^3->real^3^3) y) <= D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(D pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(lsectional (Ht:real^3->real^3^3) y u' v' - (&1 - sg) / &2) <=
                &8 * (&1 + K) * D` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `Ht:real^3->real^3^3`;
                   `y:real^3`; `M:real^3^3`; `K:real`] APX_SECTIONAL_STABILITY_LIP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "RMK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o SPECL [`u':real^3`; `v':real^3`])] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (\z. exp(--(&2 * (Fr:real->real)(p3s_sy z))) %%
                                     (Ht:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_CONF_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (Ht:real^3->real^3^3) y u' v' = lsectional Ht y u v /\
    lsectional (\z. exp(--(&2 * (Fr:real->real)(p3s_sy z))) %% Ht z) y u' v' =
    lsectional (\z. exp(--(&2 * Fr(p3s_sy z))) %% Ht z) y u v`
  (fun th -> SUBST1_TAC(SYM(CONJUNCT1 th)) THEN SUBST1_TAC(SYM(CONJUNCT2 th))) THENL
   [CONJ_TAC THEN USE_THEN "INV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "INV" (K ALL_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &8 * (&1 + K) * D ==> x <= (&8 * (&1 + K)) * D`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `Ht:real^3->real^3^3`; `\z. (Fr:real->real)(p3s_sy z)`;
                 `y:real^3`; `u':real^3`; `v':real^3`] P3S_CONF_SECT_PL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL2; REAL_MUL_LID] THEN
  (* the differential and the Hessian of F = Fr o s in Ht *)
  SUBGOAL_THEN `!a:real^3. p3s_cdf (\z. (Fr:real->real)(p3s_sy z)) y a =
                           f1 * p3s_cdf p3s_sy y a` (LABEL_TAC "DF") THENL
   [GEN_TAC THEN EXPAND_TAC "f1" THEN EXPAND_TAC "s0" THEN MATCH_MP_TAC P3S_CDF_F THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^3. p3s_chess (Ht:real^3->real^3^3) (\z. (Fr:real->real)(p3s_sy z)) y a b =
                 Fr2 * p3s_cdf p3s_sy y a * p3s_cdf p3s_sy y b -
                 f1 * p3s_cdf p3s_sy y (christoffel Ht y a b -
                                        christoffel (cylinder_flow (&0)) y a b)`
  (LABEL_TAC "HF") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "f1" THEN EXPAND_TAC "s0" THEN
    MATCH_MP_TAC P3S_CHESS_F_G THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^3. abs(p3s_cdf p3s_sy y a) <= norm((M:real^3^3) ** a)`
  (LABEL_TAC "DS") THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `p3s_sy`;
                               `y:real^3`; `M:real^3^3`; `a:real^3`] P3S_CDF_FRAME_BOUND) THEN
    ASM_SIMP_TAC[P3S_SY_GRADSQ; SQRT_1; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `Ht:real^3->real^3^3`; `y:real^3`;
                 `M:real^3^3`; `D:real`] P3S_PERT_CHRIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "CH")] THEN
  SUBGOAL_THEN
   `!a b:real^3. abs(p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y a b -
                                      christoffel (cylinder_flow (&0)) y a b)) <=
                 &2 * D * norm((M:real^3^3) ** a) * norm(M ** b)`
  (LABEL_TAC "DCH") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((M:real^3^3) ** (christoffel (Ht:real^3->real^3^3) y a b -
                                     christoffel (cylinder_flow (&0)) y a b))` THEN
    USE_THEN "DS" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "CH" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB];
    ALL_TAC] THEN
  ABBREV_TAC `Bb = abs Fr2 + f1 pow 2 + &2 * D * abs f1` THEN
  SUBGOAL_THEN
   `!a b:real^3. abs(p3s_chess (Ht:real^3->real^3^3) (\z. (Fr:real->real)(p3s_sy z)) y a b +
                     p3s_cdf (\z. Fr(p3s_sy z)) y a * p3s_cdf (\z. Fr(p3s_sy z)) y b) <=
                 Bb * norm((M:real^3^3) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "HF" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "DS" (fun th -> MP_TAC(SPEC `a:real^3` th) THEN MP_TAC(SPEC `b:real^3` th)) THEN
    USE_THEN "DCH" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    MAP_EVERY ABBREV_TAC [`na = norm((M:real^3^3) ** a)`; `nb = norm((M:real^3^3) ** b)`;
                          `da = p3s_cdf p3s_sy y (a:real^3)`;
                          `db = p3s_cdf p3s_sy y (b:real^3)`] THEN
    ABBREV_TAC `dg = p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y a b -
                                       christoffel (cylinder_flow (&0)) y a b)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(da * db) <= na * nb` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    EXPAND_TAC "Bb" THEN
    SUBGOAL_THEN `abs(Fr2 * da * db) <= abs Fr2 * na * nb /\
                  abs(f1 * dg) <= abs f1 * (&2 * D * na * nb) /\
                  abs((f1 * da) * (f1 * db)) <= f1 pow 2 * na * nb`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN ASM_REWRITE_TAC[GSYM REAL_ABS_MUL];
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[REAL_ABS_POS];
        SUBGOAL_THEN `(f1 * da) * (f1 * db) = f1 pow 2 * (da * db)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW2_ABS; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2; GSYM REAL_ABS_MUL]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Ht:real^3->real^3^3) y`; `cylinder_flow (&0) y`; `M:real^3^3`;
                 `\a b. p3s_chess (Ht:real^3->real^3^3) (\z. (Fr:real->real)(p3s_sy z)) y a b +
                        p3s_cdf (\z. Fr(p3s_sy z)) y a * p3s_cdf (\z. Fr(p3s_sy z)) y b`;
                 `u':real^3`; `v':real^3`; `Bb:real`; `D:real`] P3S_PL_PERT) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC P3S_PERT_METRIC THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  BETA_TAC THEN
  USE_THEN "HF" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "PL") THEN
  SUBGOAL_THEN `norm((M:real^3^3) ** u') = &1 /\ norm((M:real^3^3) ** v') = &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cylinder_flow (&0) y`; `M:real^3^3`; `u':real^3`] P3S_FRAME_SQ) THEN
    MP_TAC(ISPECL [`cylinder_flow (&0) y`; `M:real^3^3`; `v':real^3`] P3S_FRAME_SQ) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[REAL_POW_EQ_1] THEN
    SIMP_TAC[REAL_ABS_NORM; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y u' u' -
                          christoffel (cylinder_flow (&0)) y u' u')) <= &2 * D /\
    abs(p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y v' v' -
                          christoffel (cylinder_flow (&0)) y v' v')) <= &2 * D`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "DCH" (fun th -> MP_TAC(SPECL [`u':real^3`; `u':real^3`] th) THEN
                              MP_TAC(SPECL [`v':real^3`; `v':real^3`] th)) THEN
    REWRITE_TAC[ASSUME `norm((M:real^3^3) ** u') = &1`;
                ASSUME `norm((M:real^3^3) ** v') = &1`; REAL_MUL_RID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f1 * p3s_cdf p3s_sy y (p3s_cgrad (Ht:real^3->real^3^3) (\z. (Fr:real->real)(p3s_sy z)) y)
    <= f1 pow 2 * (&1 + &2 * D)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `Ht:real^3->real^3^3`; `p3s_sy`; `Fr:real->real`;
                   `f1:real`; `y:real^3`] P3S_GRADSQ_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P3S_SY_SMOOTH_ON] THEN EXPAND_TAC "f1" THEN EXPAND_TAC "s0" THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `Ht:real^3->real^3^3`; `y:real^3`;
                   `M:real^3^3`; `D:real`; `p3s_sy`] P3S_PERT_GRAD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC P3S_PERT_METRIC THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3S_SY_GRADSQ] THEN
    ABBREV_TAC `gq = p3s_cdf p3s_sy y (p3s_cgrad (Ht:real^3->real^3^3) p3s_sy y)` THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / (&1 - D)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 - D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `D * D <= &1 / &10 * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `du = p3s_cdf p3s_sy y (u':real^3)` THEN
  ABBREV_TAC `dv = p3s_cdf p3s_sy y (v':real^3)` THEN
  ABBREV_TAC `gu = p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y u' u' -
                                     christoffel (cylinder_flow (&0)) y u' u')` THEN
  ABBREV_TAC `gv = p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y v' v' -
                                     christoffel (cylinder_flow (&0)) y v' v')` THEN
  SUBGOAL_THEN `abs(f1 * gu) <= abs f1 * (&2 * D) /\ abs(f1 * gv) <= abs f1 * (&2 * D)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * (&14 * D * abs f1) <= D * (&2 * abs f1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `D * abs f1 <= &1 / &10 * abs f1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    MP_TAC(SPEC `f1:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sg = du pow 2 + dv pow 2` SUBST1_TAC THENL
   [EXPAND_TAC "sg" THEN MAP_EVERY EXPAND_TAC ["du"; "dv"] THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3S_KHAT_ARITH THEN
  MAP_EVERY EXISTS_TAC [`gu:real`; `gv:real`; `Bb:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `Bb:real`)));;
let P3S_RHAT_ARITH = prove
 (`!R Fr2 f1 d1 d2 d3 c1 c2 c3 gq D.
     &0 <= D /\ D <= &1 / &10 /\ &0 <= Fr2 /\
     d1 pow 2 + d2 pow 2 + d3 pow 2 = gq /\
     &1 / (&1 + D) <= gq /\ gq <= &1 / (&1 - D) /\
     abs c1 <= &2 * D * (&10 / &9) /\ abs c2 <= &2 * D * (&10 / &9) /\
     abs c3 <= &2 * D * (&10 / &9)
     ==> R + &3 * Fr2 - &28 * D * abs f1 - &3 * f1 pow 2 <=
         R + &4 * ((Fr2 * d1 * d1 - f1 * c1) + (Fr2 * d2 * d2 - f1 * c2) +
                   (Fr2 * d3 * d3 - f1 * c3)) -
         &2 * (f1 pow 2 * gq)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&10 / &11 <= gq /\ gq <= &10 / &9` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / (&1 + D)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &1 + D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / (&1 - D)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &1 - D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Fr2 * &10 / &11 <= Fr2 * gq /\ f1 pow 2 * gq <= f1 pow 2 * &10 / &9`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(f1 * c1) <= abs f1 * (&2 * D * (&10 / &9)) /\
                abs(f1 * c2) <= abs f1 * (&2 * D * (&10 / &9)) /\
                abs(f1 * c3) <= abs f1 * (&2 * D * (&10 / &9))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs f1 * D /\ &0 <= f1 pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `Fr2 * d1 * d1 + Fr2 * d2 * d2 + Fr2 * d3 * d3 = Fr2 * gq` ASSUME_TAC THENL
   [UNDISCH_TAC `d1 pow 2 + d2 pow 2 + d3 pow 2 = gq` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_NECK_RHAT = prove
 (`?P. &0 <= P /\
       !U (Ht:real^3->real^3^3) (Fr:real->real) Fr1 Fr2 y D.
         open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Ht /\ y IN U /\
         &0 <= D /\ D <= &1 / &10 /\ lck_dist2 2 (cylinder_flow (&0)) Ht y <= D pow 2 /\
         smooth_map_on (:real^1) (lift o Fr o drop) /\
         (!t. (Fr has_real_derivative Fr1 t) (atreal t)) /\
         (Fr1 has_real_derivative Fr2) (atreal (p3s_sy y)) /\ &0 <= Fr2
         ==> abs(lscalar Ht y - &1) <= P * D /\
             lscalar Ht y + &3 * Fr2 - &28 * D * abs(Fr1(p3s_sy y)) -
             &3 * Fr1(p3s_sy y) pow 2
             <= exp(--(&2 * Fr(p3s_sy y))) *
                lscalar (\z. exp(--(&2 * Fr(p3s_sy z))) %% Ht z) y`,
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  EXISTS_TAC `&8 * &3 pow 2 * (&1 + abs K0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (cylinder_flow (&0)) (Ht:real^3->real^3^3) y) <= D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(D pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`K0:real`; `U:real^3->bool`; `cylinder_flow (&0)`;
                   `Ht:real^3->real^3^3`; `y:real^3`] APX_SCALAR_STABILITY_LIP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3S_CYL0_SCALAR; DIMINDEX_3] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
            [TRY(MP_TAC(SPEC `K0:real` REAL_ABS_POS)) THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = p3s_sy y` THEN ABBREV_TAC `f1 = (Fr1:real->real) s0` THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((Fr:real->real)(p3s_sy z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(p3s_sy z)) differentiable at (y:real^3) /\
                (\z. lift((Fr:real->real)(p3s_sy z))) differentiable at y` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[P3S_SY_SMOOTH_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `y:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `Ht:real^3->real^3^3`; `y:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `Ht:real^3->real^3^3`; `\z. (Fr:real->real)(p3s_sy z)`;
                 `y:real^3`; `M1:real^3^3`] P3S_CONF_SCALAR3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_EXP_NEG_MUL2; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `!a b:real^3. p3s_chess (Ht:real^3->real^3^3) (\z. (Fr:real->real)(p3s_sy z)) y a b =
                 Fr2 * p3s_cdf p3s_sy y a * p3s_cdf p3s_sy y b -
                 f1 * p3s_cdf p3s_sy y (christoffel Ht y a b -
                                        christoffel (cylinder_flow (&0)) y a b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "f1" THEN EXPAND_TAC "s0" THEN
    MATCH_MP_TAC P3S_CHESS_F_G THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `Ht:real^3->real^3^3`; `p3s_sy`; `Fr:real->real`;
                 `f1:real`; `y:real^3`] P3S_GRADSQ_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P3S_SY_SMOOTH_ON] THEN EXPAND_TAC "f1" THEN EXPAND_TAC "s0" THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `!a b. abs(a dot ((Ht:real^3->real^3^3) y ** b) -
                          a dot (cylinder_flow (&0) y ** b)) <=
                      D * norm((M:real^3^3) ** a) * norm(M ** b)` (LABEL_TAC "MB") THENL
   [MATCH_MP_TAC P3S_PERT_METRIC THEN EXISTS_TAC `U:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `Ht:real^3->real^3^3`; `y:real^3`;
                 `M:real^3^3`; `D:real`; `p3s_sy`] P3S_PERT_GRAD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_GRADSQ] THEN STRIP_TAC THEN
  ABBREV_TAC `g = p3s_cgrad (Ht:real^3->real^3^3) p3s_sy y` THEN
  ABBREV_TAC `gq = p3s_cdf p3s_sy y (g:real^3)` THEN
  SUBGOAL_THEN `!w:real^3. p3s_cdf p3s_sy y w = w dot ((Ht:real^3->real^3^3) y ** g)`
  (LABEL_TAC "GD") THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = matrix_inv(M1:real^3^3) ** basis 1` THEN
  ABBREV_TAC `e2 = matrix_inv(M1:real^3^3) ** basis 2` THEN
  ABBREV_TAC `e3 = matrix_inv(M1:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN `p3s_cdf p3s_sy y (e1:real^3) pow 2 + p3s_cdf p3s_sy y e2 pow 2 +
                p3s_cdf p3s_sy y e3 pow 2 = gq` ASSUME_TAC THENL
   [USE_THEN "GD" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "gq" THEN
    USE_THEN "GD" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`(Ht:real^3->real^3^3) y`; `M1:real^3^3`; `g:real^3`]
           P3S_FRAME_PARSEVAL3) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ASSUME `matrix_inv(M1:real^3^3) ** basis 1 = e1`;
                ASSUME `matrix_inv(M1:real^3^3) ** basis 2 = e2`;
                ASSUME `matrix_inv(M1:real^3^3) ** basis 3 = e3`] THEN
    SUBGOAL_THEN `!a:real^3. a dot ((Ht:real^3->real^3^3) y ** g) = g dot (Ht y ** a)`
    (LABEL_TAC "SY") THENL
     [GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN EXISTS_TAC `U:real^3->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "SY" (fun th -> REWRITE_TAC[SPEC `e1:real^3` th; SPEC `e2:real^3` th;
                                         SPEC `e3:real^3` th]);
    ALL_TAC] THEN
  REMOVE_THEN "GD" (K ALL_TAC) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3
                    ==> norm((M:real^3^3) ** (matrix_inv (M1:real^3^3) ** basis i)) pow 2 <= &10 / &9`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(Ht:real^3->real^3^3) y`; `M1:real^3^3`; `i:num`; `i:num`]
           P2B_FRAME_ORTHO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3]; REWRITE_TAC[]] THEN DISCH_TAC THEN
    USE_THEN "MB" (MP_TAC o SPECL [`matrix_inv(M1:real^3^3) ** basis i`;
                                   `matrix_inv(M1:real^3^3) ** basis i`]) THEN
    MP_TAC(ISPECL [`cylinder_flow (&0) y`; `M:real^3^3`;
                   `matrix_inv(M1:real^3^3) ** basis i`] P3S_FRAME_SQ) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `nn = norm((M:real^3^3) ** (matrix_inv (M1:real^3^3) ** basis i))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - D) * nn pow 2 <= &1` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(&1 - nn pow 2) <= D * nn * nn` THEN REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / (&1 - D)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `Ht:real^3->real^3^3`; `y:real^3`;
                 `M:real^3^3`; `D:real`] P3S_PERT_CHRIST) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC);
                  DISCH_THEN(LABEL_TAC "CH")] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> abs(p3s_cdf p3s_sy y (christoffel (Ht:real^3->real^3^3) y
                  (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i) -
                christoffel (cylinder_flow (&0)) y
                  (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i))) <=
            &2 * D * (&10 / &9)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((M:real^3^3) ** (christoffel (Ht:real^3->real^3^3) y
                  (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i) -
                christoffel (cylinder_flow (&0)) y
                  (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i)))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `p3s_sy`; `y:real^3`;
                     `M:real^3^3`;
                     `christoffel (Ht:real^3->real^3^3) y
                        (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i) -
                      christoffel (cylinder_flow (&0)) y
                        (matrix_inv (M1:real^3^3) ** basis i) (matrix_inv (M1:real^3^3) ** basis i)`]
                    P3S_CDF_FRAME_BOUND) THEN
      ASM_SIMP_TAC[P3S_SY_GRADSQ; SQRT_1; REAL_MUL_LID];
      ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPECL [`matrix_inv(M1:real^3^3) ** basis i`;
                                   `matrix_inv(M1:real^3^3) ** basis i`]) THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3S_RHAT_ARITH THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY EXPAND_TAC ["e1"; "e2"; "e3"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

