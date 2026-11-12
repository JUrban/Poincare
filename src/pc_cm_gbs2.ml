(* ========================================================================= *)
(* Unit pc_cm_gbs2: the Gauss-Bonnet bridge CM_GB_SPHERE_AREA_STATEMENT of   *)
(* pc_cm_gbs2req, used in the proof of MT Prop 9.46 (pc_p2b_p946h).  A piece *)
(* S of a surface, open and the image of the standard S^2 under a            *)
(* diffeomorphism psi, with Gauss curvature K = R/2 at most k0, has area a   *)
(* with 4 pi <= k0 a.  Route: embed S in real^5 (CM_EMB_EXISTS) with an      *)
(* ambient metric Q, put the pulled back metric on S^2 in the format of      *)
(* CM_D7_UNIFORMIZATION and take its conformal reparametrization h; then the *)
(* planar map psi o h o stereo2_n_inv is conformal with factor mu, the       *)
(* curvature is K = --(Laplacian of log mu) / (2 mu), the area is the        *)
(* integral of mu (GRGA_AREA_FORMULA), and CML_GB_INEQ gives 4 pi <= int k0  *)
(* mu = k0 a.                                                                *)
(* ========================================================================= *)

needs "src/pc_cm_lemma122.ml";;
needs "src/pc_grg_area.ml";;
needs "src/pc_cm_gbs2req.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The curvature of a conformal metric on an open set of the                *)
(* plane.                                                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The curvature of a conformal metric mu |dz|^2 on an open set of the       *)
(* plane: with P the gradient of log mu, the Christoffel symbols are         *)
(* (P.a) b + (P.b) a - (a.b) P over 2, and the scalar curvature is           *)
(* --(Laplacian of log mu) / mu.                                            *)
(* ------------------------------------------------------------------------- *)

let gbs2_lgrad = new_definition
 `gbs2_lgrad (mu:real^2->real) (z:real^2) =
    vector[cml_d 1 (\x. log(mu x)) z; cml_d 2 (\x. log(mu x)) z]:real^2`;;

let GBS2_LGRAD_COMPONENT = prove
 (`!mu z. gbs2_lgrad mu z$1 = cml_d 1 (\x. log(mu x)) z /\
          gbs2_lgrad mu z$2 = cml_d 2 (\x. log(mu x)) z`,
  REWRITE_TAC[gbs2_lgrad; VECTOR_2]);;

let GBS2_DMU = prove
 (`!s (mu:real^2->real) z h.
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x) /\ z IN s
     ==> drop(frechet_derivative (\x. lift(mu x)) (at z) h) =
         mu z * (gbs2_lgrad mu z dot h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((mu:real^2->real) x)) differentiable (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [CML_BASIS_EXPAND2] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN
  REWRITE_TAC[GSYM partial_derivative] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[FUN_EQ_THM] cml_d)] THEN
  SUBGOAL_THEN `!i. cml_d i (mu:real^2->real) z = mu z * cml_d i (\x. log(mu x)) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `mu:real^2->real`; `z:real^2`; `i:num`] CML_D_LOG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~((mu:real^2->real) z = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_SIMP_TAC[]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_2; GBS2_LGRAD_COMPONENT] THEN REAL_ARITH_TAC);;

let GBS2_CONF_METRIC = prove
 (`!s (mu:real^2->real).
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x)
     ==> metric_field s (\z. mu z %% mat 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^2^2->real^(2,2)finite_prod) o (\z:real^2. mu z %% mat 1) =
      (\z. drop((\z:real^2. lift(mu z)) z) % vectorize(mat 1:real^2^2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[DOT_POS_LT]]);;

let GBS2_CONF_MDERIV = prove
 (`!s (mu:real^2->real) z a.
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x) /\ z IN s
     ==> mderiv (\z. mu z %% mat 1) z a = (mu z * (gbs2_lgrad mu z dot a)) %% mat 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN
   `(vectorize:real^2^2->real^(2,2)finite_prod) o (\z:real^2. mu z %% mat 1) =
    (\x. mu x % vectorize(mat 1:real^2^2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift((mu:real^2->real) x)) has_derivative
                 frechet_derivative (\x. lift(mu x)) (at z)) (at z)` MP_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN MATCH_MP_TAC CML_SM_DIFF THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `vectorize(mat 1:real^2^2)` o MATCH_MP HAS_DERIVATIVE_VMUL_DROP) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `mu:real^2->real`; `z:real^2`; `a:real^2`] GBS2_DMU) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let GBS2_CONF_CHRISTOFFEL = prove
 (`!s (mu:real^2->real) z a b.
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x) /\ z IN s
     ==> christoffel (\z. mu z %% mat 1) z a b =
         inv(&2) % ((gbs2_lgrad mu z dot a) % b + (gbs2_lgrad mu z dot b) % a -
                    (a dot b) % gbs2_lgrad mu z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `(\z. mu z %% mat 1):real^2->real^2^2`; `z:real^2`] THEN
  ASM_SIMP_TAC[GBS2_CONF_METRIC] THEN X_GEN_TAC `w:real^2` THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `(\z. mu z %% mat 1):real^2->real^2^2`;
                 `z:real^2`; `a:real^2`; `b:real^2`; `w:real^2`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_SIMP_TAC[GBS2_CONF_METRIC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `mu:real^2->real`; `z:real^2`] GBS2_CONF_MDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB] THEN REWRITE_TAC[DOT_SYM] THEN
  CONV_TAC REAL_RING);;

(* The derivative of the Christoffel field, for a differentiable P. *)

let GBS2_CONF_DCHRISTOFFEL = prove
 (`!(G:real^2->real^2^2) s (P:real^2->real^2) y a b u.
     open s /\ y IN s /\
     (!z a b. z IN s
              ==> christoffel G z a b =
                  inv(&2) % ((P z dot a) % b + (P z dot b) % a - (a dot b) % P z)) /\
     P differentiable (at y)
     ==> frechet_derivative (\z. christoffel G z a b) (at y) u =
         inv(&2) % ((frechet_derivative P (at y) u dot a) % b +
                    (frechet_derivative P (at y) u dot b) % a -
                    (a dot b) % frechet_derivative P (at y) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. christoffel (G:real^2->real^2^2) z a b) (at y) =
    frechet_derivative
      ((\p:real^2. inv(&2) % ((p dot a) % b + (p dot b) % a - (a dot b) % p)) o P) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear (\p:real^2. inv(&2) % ((p dot a) % b + (p dot b) % a - (a dot b) % p))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LRG_LINEAR_RADIAL_L];
    ALL_TAC] THEN
  SUBGOAL_THEN `((P:real^2->real^2) has_derivative frechet_derivative P (at y)) (at y)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`P:real^2->real^2`;
    `\p:real^2. inv(&2) % ((p dot a) % b + (p dot b) % a - (a dot b) % p)`;
    `frechet_derivative (P:real^2->real^2) (at y)`;
    `\p:real^2. inv(&2) % ((p dot a) % b + (p dot b) % a - (a dot b) % p)`;
    `y:real^2`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[o_THM]);;

let GBS2_LGRAD_SMOOTH = prove
 (`!s (mu:real^2->real).
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x)
     ==> smooth_map_on s (gbs2_lgrad mu)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `gbs2_lgrad (mu:real^2->real) =
    (\z. drop(lift(cml_d 1 (\x. log(mu x)) z)) % basis 1 +
         drop(lift(cml_d 2 (\x. log(mu x)) z)) % basis 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP] THEN GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [CML_BASIS_EXPAND2] THEN
    REWRITE_TAC[GBS2_LGRAD_COMPONENT];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN MATCH_MP_TAC CML_D_SMOOTH THEN
  ASM_SIMP_TAC[CML_SM_LOG]);;

let GBS2_DLGRAD_COMPONENT = prove
 (`!s (mu:real^2->real) y.
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x) /\ y IN s
     ==> (frechet_derivative (gbs2_lgrad mu) (at y) (basis 1))$1 =
         cml_d 1 (cml_d 1 (\x. log(mu x))) y /\
         (frechet_derivative (gbs2_lgrad mu) (at y) (basis 2))$2 =
         cml_d 2 (cml_d 2 (\x. log(mu x))) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `gbs2_lgrad (mu:real^2->real) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[GBS2_LGRAD_SMOOTH];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`gbs2_lgrad (mu:real^2->real)`; `y:real^2`; `basis 1:real^2`; `1`]
                  CML_FRECHET_COMPONENT);
    MP_TAC(ISPECL [`gbs2_lgrad (mu:real^2->real)`; `y:real^2`; `basis 2:real^2`; `2`]
                  CML_FRECHET_COMPONENT)] THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GBS2_LGRAD_COMPONENT] THEN REWRITE_TAC[cml_d; partial_derivative]);;

let GBS2_CONF_SCALAR = prove
 (`!s (mu:real^2->real) y.
     open s /\ smooth_map_on s (\x. lift(mu x)) /\ (!x. x IN s ==> &0 < mu x) /\ y IN s
     ==> lscalar (\z. mu z %% mat 1) y = --(cml_lap (\x. log(mu x)) y) / mu y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `gbs2_lgrad (mu:real^2->real) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[GBS2_LGRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z a b. z IN s
            ==> christoffel (\z. (mu:real^2->real) z %% mat 1) z a b =
                inv(&2) % ((gbs2_lgrad mu z dot a) % b + (gbs2_lgrad mu z dot b) % a -
                           (a dot b) % gbs2_lgrad mu z)`
  (LABEL_TAC "chr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GBS2_CONF_CHRISTOFFEL THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b u. frechet_derivative (\z. christoffel (\z. (mu:real^2->real) z %% mat 1) z a b)
                               (at y) u =
            inv(&2) % ((frechet_derivative (gbs2_lgrad mu) (at y) u dot a) % b +
                       (frechet_derivative (gbs2_lgrad mu) (at y) u dot b) % a -
                       (a dot b) % frechet_derivative (gbs2_lgrad mu) (at y) u)`
  (LABEL_TAC "dchr") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC GBS2_CONF_DCHRISTOFFEL THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `mu:real^2->real`; `y:real^2`] GBS2_DLGRAD_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dd1") (LABEL_TAC "dd2")) THEN
  SUBGOAL_THEN `~((mu:real^2->real) y = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lscalar; lricci; lriemann; DIMINDEX_2; SUM_2] THEN
  USE_THEN "dchr" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "chr" (fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[MATRIX_INV_CMUL; MATRIX_INV_I; MATRIX_CMUL_COMPONENT] THEN
  SIMP_TAC[MAT_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[cml_lap] THEN
  USE_THEN "dd1" (fun th1 -> USE_THEN "dd2" (fun th2 -> REWRITE_TAC[GSYM th1; GSYM th2])) THEN
  ABBREV_TAC `DP = frechet_derivative (gbs2_lgrad (mu:real^2->real)) (at y)` THEN
  ABBREV_TAC `P = gbs2_lgrad (mu:real^2->real) y` THEN
  REWRITE_TAC[DOT_2; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  UNDISCH_TAC `~((mu:real^2->real) y = &0)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Radial extensions of smooth maps on the standard sphere.                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Maps from the standard S^2 into real^K that are smooth in the charts of  *)
(* sphere2_atlas have smooth radial extensions on real^3 minus 0.           *)
(* ------------------------------------------------------------------------- *)

let GBS2_REFL3_NORM = prove
 (`!x:real^3. norm(bel_refl3 x) = norm x`,
  GEN_TAC THEN REWRITE_TAC[vector_norm; BEL_REFL3_DOT]);;

let GBS2_REFL3_CMUL = prove
 (`!c x:real^3. bel_refl3(c % x) = c % bel_refl3 x`,
  MESON_TAC[BEL_REFL3_LINEAR; LINEAR_CMUL]);;

let GBS2_STEREO_S_NORMALIZED_SMOOTH = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0) /\ --(&1) < (inv(norm x) % x)$3}
                 (\x. stereo2_s(inv(norm x) % x))`,
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\x:real^3. stereo2_n(inv(norm x) % x)) o bel_refl3` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[GBS2_REFL3_NORM; GSYM GBS2_REFL3_CMUL] THEN
    ABBREV_TAC `w = inv(norm x) % x:real^3` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; stereo2_n; stereo2_s] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; ARITH; BEL_REFL3_COMPONENTS] THEN
    REWRITE_TAC[REAL_ARITH `&1 - --x = &1 + x`];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
  REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; SMT_STEREO_NORMALIZED_SMOOTH] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    REWRITE_TAC[GSYM NORM_EQ_0; GBS2_REFL3_NORM] THEN
    REWRITE_TAC[GSYM GBS2_REFL3_CMUL] THEN
    ASM_REWRITE_TAC[NORM_EQ_0; BEL_REFL3_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM I_O_ID] THEN REWRITE_TAC[I_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[BEL_REFL3_LINEAR; SMOOTH_MAP_ON_ID; SMT_OPEN_NORMALIZED_HALFSPACES]]);;

let GBS2_STEREO2_IMAGES = prove
 (`IMAGE stereo2_n (sphere(vec 0:real^3,&1) DELETE basis 3) = (:real^2) /\
   IMAGE stereo2_s (sphere(vec 0:real^3,&1) DELETE --(basis 3)) = (:real^2)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN CONJ_TAC THEN X_GEN_TAC `y:real^2` THENL
   [EXISTS_TAC `stereo2_n_inv y` THEN
    REWRITE_TAC[STEX_STEREO2_N_RIGHT; STEX_STEREO2_N_INV_IN];
    EXISTS_TAC `stereo2_s_inv y` THEN
    REWRITE_TAC[STEX_STEREO2_S_RIGHT; STEX_STEREO2_S_INV_IN]]);;

let GBS2_REXT_SMOOTH = prove
 (`!u:real^3->real^K.
     mfd_smooth_on sphere2_atlas (sphere(vec 0,&1)) u
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. u(inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) ((u:real^3->real^K) o stereo2_n_inv) /\
                smooth_map_on (:real^2) (u o stereo2_s_inv)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_smooth_on]) THEN
    REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `(sphere(vec 0:real^3,&1) DELETE basis 3,stereo2_n)` th) THEN
      MP_TAC(SPEC `(sphere(vec 0:real^3,&1) DELETE --(basis 3),stereo2_s)` th)) THEN
    REWRITE_TAC[FST; SND; STEX_SPHERE2_CHART_INV] THEN
    REWRITE_TAC[SET_RULE `!s a:real^3. (s DELETE a) INTER s = s DELETE a`; GBS2_STEREO2_IMAGES] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_NONZERO] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(inv(norm z) % z:real^3) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `(inv(norm z) % z:real^3)$3 < &1` THENL
   [EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
    ASM_REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `((u:real^3->real^K) o stereo2_n_inv) o (\x:real^3. stereo2_n(inv(norm x) % x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN
      REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN CONJ_TAC THENL
       [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
        DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
        SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMT_OPEN_NORMALIZED_HALFSPACES;
                      SMT_STEREO_NORMALIZED_SMOOTH]];
    EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ --(&1) < (inv(norm x) % x)$3}` THEN
    ASM_REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] COMPONENT_LE_NORM) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `((u:real^3->real^K) o stereo2_s_inv) o (\x:real^3. stereo2_s(inv(norm x) % x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN
      REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN CONJ_TAC THENL
       [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
        DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
        SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMT_OPEN_NORMALIZED_HALFSPACES;
                      GBS2_STEREO_S_NORMALIZED_SMOOTH]]]);;

(* ========================================================================= *)
(* The sphere piece and its embedding into real^5.                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The sphere piece S: elementary facts from the diffeomorphism, and an     *)
(* embedding of S into real^5 with an ambient metric Q whose pullback is g  *)
(* (CM_EMB_EXISTS on the compact surface S with the restricted atlas).      *)
(* ------------------------------------------------------------------------- *)

let GBS2_SPHERE_FACTS = prove
 (`!top atlas S (psi:real^3->A) psi'.
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top (atlas:((A->bool)#(A->real^2))->bool)
                S psi psi'
     ==> open_in top S /\ S SUBSET topspace top /\
         IMAGE psi (sphere(vec 0,&1)) = S /\ compact_in top S /\
         (!y. y IN sphere(vec 0,&1) ==> psi y IN S /\ psi'(psi y) = y) /\
         (!x. x IN S ==> psi' x IN sphere(vec 0,&1) /\ psi(psi' x) = x) /\
         continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) psi /\
         mfd_smooth_map sphere2_atlas atlas (sphere(vec 0,&1)) psi /\
         mfd_smooth_map atlas sphere2_atlas S psi'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; INTER_IDEMPOT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top INTER (S:A->bool) = S` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->A) (sphere(vec 0,&1)) = S` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE; SUBSET_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM SET_TAC[]);;

let GBS2_EMBED = prove
 (`!top atlas (g:A->real^2^2) S (psi:real^3->A) psi'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi'
     ==> ?(f:A->real^5) (Q:real^5->real^5^5) lam.
           smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
           (!z. transp(Q z) = Q z) /\ &0 < lam /\
           (!z v. lam * norm v pow 2 <= v dot (Q z ** v)) /\
           continuous_map (subtopology top S,euclidean) f /\
           (!U phi. (U,phi) IN atlas
                    ==> ?h. smooth_map_on (IMAGE phi (U INTER S)) h /\
                            (!x. x IN U INTER S ==> h(phi x) = f x) /\
                            (!y v. y IN IMAGE phi (U INTER S) /\
                                   frechet_derivative h (at y) v = vec 0
                                   ==> v = vec 0)) /\
           (!U phi. (U,phi) IN atlas
                    ==> !x. x IN U INTER S
                            ==> metric_local atlas (U,phi) g (phi x) =
                                transp(matrix(frechet_derivative
                                   (f o chart_inv (U INTER S,phi)) (at (phi x)))) **
                                Q(f x) **
                                matrix(frechet_derivative
                                   (f o chart_inv (U INTER S,phi)) (at (phi x))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "psiS") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(psi:real^3->A)(basis 3) IN S` ASSUME_TAC THENL
   [USE_THEN "psiS" (MP_TAC o SPEC `basis 3:real^3`) THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (S:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^2))->bool) S`;
                 `restrict_metric (atlas:((A->bool)#(A->real^2))->bool) S g`]
                (INST_TYPE [`:5`,`:K`] CM_EMB_EXISTS)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT;
                 RIEMANNIAN_METRIC_RESTRICT; COMPACT_SPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[DIMINDEX_2; DIMINDEX_CONV `dimindex(:5)`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    TRY(CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(psi:real^3->A)(basis 3)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(S:A->bool) SUBSET topspace top` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^5` (X_CHOOSE_THEN `Q:real^5->real^5^5`
    (X_CHOOSE_THEN `d:real` MP_TAC))) THEN
  REWRITE_TAC[cm_emb; mfd_embedding; cm_target] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`f:A->real^5`; `Q:real^5->real^5^5`; `lam:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^2`] THEN DISCH_TAC THEN
    UNDISCH_TAC `smooth_immersion_into (restrict_atlas (atlas:((A->bool)#(A->real^2))->bool) S)
                                       (f:A->real^5)` THEN
    REWRITE_TAC[smooth_immersion_into] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^2`] THEN DISCH_TAC THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `phi:A->real^2`; `S:A->bool`; `g:A->real^2^2`; `x:A`]
                  METRIC_LOCAL_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(U INTER S:A->bool,phi:A->real^2)`; `(phi:A->real^2) x`] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "metric_local"
                                                with Failure _ -> false)) (concl th) &&
                       is_forall (concl th))) THEN
    REWRITE_TAC[IN_RESTRICT_ATLAS; FST; SND] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`subtopology top (S:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^2))->bool) S`;
                   `U INTER S:A->bool`; `phi:A->real^2`] CHART_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_RESTRICT_ATLAS] THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]]);;

(* ========================================================================= *)
(* The embedded sphere F = f o psi o (normalization).                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The embedded sphere F = f o psi o (normalization): smooth on real^3     *)
(* minus 0, homogeneous of degree 0, and an immersion on tangent planes.    *)
(* ------------------------------------------------------------------------- *)

let GBS2_FPSI_SMOOTH = prove
 (`!top atlas S (psi:real^3->A) psi' (f:A->real^5).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     continuous_map (subtopology top S,euclidean) f /\
     (!U phi. (U,phi) IN atlas
              ==> ?h. smooth_map_on (IMAGE phi (U INTER S)) h /\
                      (!x. x IN U INTER S ==> h(phi x) = f x))
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. f(psi(inv(norm z) % z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_smooth_on (atlas:((A->bool)#(A->real^2))->bool) S (f:A->real^5)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_smooth_on; FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^2`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^2`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on"
                                 with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^5` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `h:real^2->real^5` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `phi:A->real^2`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (:real^5))
                                     (open_set_atlas (:real^5))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
                        (sphere(vec 0,&1))` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                            (sphere(vec 0,&1)),top) (psi:real^3->A)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology top S,subtopology euclidean (:real^5))
                               (f:A->real^5)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (atlas:((A->bool)#(A->real^2))->bool)
                               (open_set_atlas (:real^5)) S (f:A->real^5)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->A) (sphere(vec 0,&1)) SUBSET S` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
    `top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
    `subtopology euclidean (:real^5)`; `open_set_atlas (:real^5)`;
    `sphere(vec 0:real^3,&1)`; `S:A->bool`; `psi:real^3->A`; `f:A->real^5`]
   MFD_SMOOTH_MAP_COMPOSE) THEN
  ASM_REWRITE_TAC[SPHERE2_ATLAS] THEN REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `(f:A->real^5) o (psi:real^3->A)` GBS2_REXT_SMOOTH) THEN
  ASM_REWRITE_TAC[o_THM]);;

(* ========================================================================= *)
(* The pulled back metric on S^2 and its uniformization.                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The pulled back metric on S^2 in the format of CM_D7_UNIFORMIZATION:     *)
(* G(y) = DF(y)^T Q(Fe y) DF(y) for a smooth map Fe of real^3 minus 0 into    *)
(* real^5, homogeneous of degree 0 and an immersion on tangent planes, and  *)
(* an ambient metric Q; then the conformal reparametrization h of S^2.      *)
(* ------------------------------------------------------------------------- *)

let gbs2_G = new_definition
 `gbs2_G (Fe:real^3->real^5) (Q:real^5->real^5^5) (y:real^3) =
    transp(jacobian Fe (at y)) ** Q(Fe y) ** jacobian Fe (at y)`;;

let GBS2_JAC_BASIS = prove
 (`!(Fe:real^3->real^K) y i.
     Fe differentiable (at y) /\ 1 <= i /\ i <= 3
     ==> jacobian Fe (at y) ** basis i = partial_derivative i Fe y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian; partial_derivative] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE]);;

let GBS2_G_ENTRY = prove
 (`!(Fe:real^3->real^5) Q y i j.
     Fe differentiable (at y) /\ 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> gbs2_G Fe Q y$i$j =
         partial_derivative i Fe y dot (Q(Fe y) ** partial_derivative j Fe y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gbs2_G] THEN
  MP_TAC(ISPECL [`jacobian (Fe:real^3->real^5) (at y)`; `(Q:real^5->real^5^5)((Fe:real^3->real^5) y)`;
                 `i:num`; `j:num`] CMT_GRAM_ENTRY) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GBS2_JAC_BASIS]);;

let GBS2_GRAM_ENTRY_SMOOTH = prove
 (`!s (Fe:real^N->real^5) (Q:real^5->real^5^5) i j.
     open s /\ smooth_map_on s Fe /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q)
     ==> smooth_map_on s
           (\z. lift(partial_derivative i Fe z dot (Q(Fe z) ** partial_derivative j Fe z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `\(m:real^(5,5)finite_prod) (v:real^5). (matrify m:real^5^5) ** v`;
                 `(vectorize:real^5^5->real^(5,5)finite_prod) o Q o (Fe:real^N->real^5)`;
                 `partial_derivative j (Fe:real^N->real^5)`]
                SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_SIMP_TAC[LRG_BILINEAR_MATRIFY_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  REWRITE_TAC[o_THM; MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^5)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]);;

let GBS2_G_SMOOTH = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) i j.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     (!t z. &0 < t /\ ~(z = vec 0) ==> Fe(t % z) = Fe z) /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                       (\z. lift(gbs2_G Fe Q (inv(norm z) % z)$i$j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z:real^3. lift(norm z pow 2 *
                (partial_derivative i (Fe:real^3->real^5) z dot
                 ((Q:real^5->real^5^5)(Fe z) ** partial_derivative j Fe z)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < inv(norm(z:real^3))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ; NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(inv(norm z) % z:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `!w:real^3. ~(w = vec 0) ==> (Fe:real^3->real^5) differentiable (at w)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GBS2_G_ENTRY] THEN
    SUBGOAL_THEN
     `!k. partial_derivative k (Fe:real^3->real^5) (inv(norm z) % z) =
          norm z % partial_derivative k Fe z`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`Fe:real^3->real^5`; `z:real^3`; `inv(norm(z:real^3))`; `k:num`]
                    CML_HOMOG_PD) THEN
      ASM_SIMP_TAC[REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[DOT_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CML_SM_MUL THEN REWRITE_TAC[OPEN_NONZERO] THEN
    ASM_SIMP_TAC[CML_SM_NORM2; OPEN_NONZERO] THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC GBS2_GRAM_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[OPEN_NONZERO]]);;

let GBS2_JAC_EXPAND = prove
 (`!(Fe:real^3->real^K) y v.
     Fe differentiable (at y)
     ==> jacobian Fe (at y) ** v = vsum(1..3) (\i. v$i % partial_derivative i Fe y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DIMINDEX_3;
               partial_derivative]);;

let GBS2_IMMERSION_UNIFORM = prove
 (`!(Fe:real^3->real^5).
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     (!y v. y IN sphere(vec 0,&1) /\ v dot y = &0 /\ jacobian Fe (at y) ** v = vec 0
            ==> v = vec 0)
     ==> ?m. &0 < m /\
             !y v. y IN sphere(vec 0,&1) /\ v dot y = &0
                   ==> m * norm v <= norm(jacobian Fe (at y) ** v)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = (sphere(vec 0:real^3,&1) PCROSS sphere(vec 0:real^3,&1)) INTER
                  {x:real^(3,3)finite_sum | sndcart x dot fstcart x = &0}` THEN
  SUBGOAL_THEN `compact(K:real^(3,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE] THEN
    SUBGOAL_THEN `{x:real^(3,3)finite_sum | sndcart x dot fstcart x = &0} =
                  {x | lift(sndcart x dot fstcart x) IN {vec 0}}` SUBST1_TAC THENL
     [REWRITE_TAC[IN_SING; GSYM LIFT_NUM; LIFT_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN REWRITE_TAC[CLOSED_SING] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
    SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^(3,3)finite_sum.
                  x IN K <=> fstcart x IN sphere(vec 0,&1) /\ sndcart x IN sphere(vec 0,&1) /\
                             sndcart x dot fstcart x = &0` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "K" THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_ELIM_THM; CONJ_ASSOC;
                FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> (Fe:real^3->real^5) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> ~(y = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^(3,3)finite_sum.
                   norm(jacobian (Fe:real^3->real^5) (at (fstcart x)) ** sndcart x)`;
                 `K:real^(3,3)finite_sum->bool`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `pastecart (basis 1:real^3) (basis 2:real^3)` THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SPHERE_0] THEN
      SIMP_TAC[NORM_BASIS; DOT_BASIS_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x:real^(3,3)finite_sum.
                  vsum(1..3) (\i. sndcart x$i % partial_derivative i (Fe:real^3->real^5)
                                                   (fstcart x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^(3,3)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GBS2_JAC_EXPAND THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^(3,3)finite_sum. partial_derivative i (Fe:real^3->real^5) (fstcart x)) =
                  partial_derivative i Fe o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
      ASM_REWRITE_TAC[OPEN_NONZERO];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x0:real^(3,3)finite_sum` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm(jacobian (Fe:real^3->real^5) (at (fstcart x0)) ** sndcart x0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_POS_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`fstcart(x0:real^(3,3)finite_sum)`;
                                  `sndcart(x0:real^(3,3)finite_sum)`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "jacobian" with Failure _ -> false))
            (concl th) &&
        can (find_term (fun t -> t = `vec 0:real^3`)) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; NORM_POS_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^3) (inv(norm v) % v:real^3)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "IN" with Failure _ -> false))
          (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "real_le" with Failure _ -> false))
          (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_SPHERE_0] THEN
  SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; DOT_LMUL] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REWRITE_TAC[real_div] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let GBS2_UNIFORMIZE = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) lam.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     (!t z. &0 < t /\ ~(z = vec 0) ==> Fe(t % z) = Fe z) /\
     (!y v. y IN sphere(vec 0,&1) /\ v dot y = &0 /\ jacobian Fe (at y) ** v = vec 0
            ==> v = vec 0) /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\ &0 < lam /\ (!z v. lam * norm v pow 2 <= v dot (Q z ** v))
     ==> ?h:real^3->real^3.
           (!y. y IN sphere(vec 0,&1) ==> h y IN sphere(vec 0,&1)) /\
           (!x. x IN sphere(vec 0,&1) ==> ?!y. y IN sphere(vec 0,&1) /\ h y = x) /\
           smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h(inv(norm z) % z)) /\
           (!y. y IN sphere(vec 0,&1)
                ==> ?l. &0 < l /\
                        !v w. v dot y = &0 /\ w dot y = &0
                              ==> (jacobian (\z. h(inv(norm z) % z)) (at y) ** v) dot
                                  (gbs2_G Fe Q (h y) **
                                   (jacobian (\z. h(inv(norm z) % z)) (at y) ** w)) =
                                  l * (v dot w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `Fe:real^3->real^5` GBS2_IMMERSION_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC CM_D7_UNIFORMIZATION THEN REWRITE_TAC[CM_D7_UNIFORMIZATION_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `\t:real. gbs2_G (Fe:real^3->real^5) Q`) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC GBS2_G_SMOOTH THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `(\x:real^(3,1)finite_sum.
           iterated_partial l (\z. lift(gbs2_G (Fe:real^3->real^5) Q (inv(norm z) % z)$i$j))
                            (fstcart x)) =
        iterated_partial l (\z. lift(gbs2_G Fe Q (inv(norm z) % z)$i$j)) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
        REWRITE_TAC[OPEN_NONZERO] THEN MATCH_MP_TAC GBS2_G_SMOOTH THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[gbs2_G; MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
      ASM_REWRITE_TAC[MATRIX_MUL_ASSOC];
      EXISTS_TAC `lam * m pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[gbs2_G; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * norm(jacobian (Fe:real^3->real^5) (at y) ** v) pow 2` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real^3->real^3` (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POS] THEN STRIP_TAC THEN
  EXISTS_TAC `(h:real->real^3->real^3) (&0)` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Sphere charts through the normalization; F is an immersion               *)
(* on tangent planes.                                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Sphere charts through the normalization; the chart representative of psi *)
(* through the normalization is smooth and injective on tangent vectors, so *)
(* F = f o psi o (normalization) is an immersion on tangent planes.         *)
(* ------------------------------------------------------------------------- *)

let GBS2_NORMALIZED_POLES = prove
 (`!z:real^3.
     ~(z = vec 0)
     ==> (inv(norm z) % z IN sphere(vec 0,&1) DELETE basis 3 <=>
          (inv(norm z) % z)$3 < &1) /\
         (inv(norm z) % z IN sphere(vec 0,&1) DELETE --(basis 3) <=>
          --(&1) < (inv(norm z) % z)$3)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
  SUBGOAL_THEN `norm(inv(norm z) % z:real^3) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
  MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] COMPONENT_LE_NORM) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH; REAL_ABS_BOUNDS] THEN
  DISCH_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REAL_ARITH_TAC);;

let GBS2_NORMALIZED_DOMAINS = prove
 (`{z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN sphere(vec 0,&1) DELETE basis 3} =
   {z | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1} /\
   {z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN sphere(vec 0,&1) DELETE --(basis 3)} =
   {z | ~(z = vec 0) /\ --(&1) < (inv(norm z) % z)$3}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[GBS2_NORMALIZED_POLES]);;

let GBS2_SPHERE_CHART_FACTS = prove
 (`!c. c IN sphere2_atlas
       ==> open {z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN FST c} /\
           smooth_map_on {z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN FST c}
                         (\z. SND c (inv(norm z) % z)) /\
           FST c SUBSET sphere(vec 0,&1) /\
           (!x. x IN FST c ==> chart_inv c (SND c x) = x) /\
           (!w. chart_inv c w IN FST c) /\
           smooth_map_on (:real^2) (chart_inv c)`,
  REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND; STEX_SPHERE2_CHART_INV; GBS2_NORMALIZED_DOMAINS;
                                 DELETE_SUBSET; SMT_OPEN_NORMALIZED_HALFSPACES] THEN
  REWRITE_TAC[SMT_STEREO_NORMALIZED_SMOOTH; GBS2_STEREO_S_NORMALIZED_SMOOTH;
              STEX_STEREO2_N_LEFT; STEX_STEREO2_S_LEFT; STEX_STEREO2_N_INV_IN;
              STEX_STEREO2_S_INV_IN; STEX_STEREO2_N_INV_SMOOTH] THEN
  REWRITE_TAC[CML_XS_PROPS]);;

let GBS2_NORMALIZE_TANGENT = prove
 (`!y v:real^3. norm y = &1 /\ v dot y = &0
                ==> frechet_derivative (\z. inv(norm z) % z) (at y) v = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BEL_NORMALIZE_HAS_DERIVATIVE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO;
                  VECTOR_SUB_RZERO]);;

let GBS2_STEREO_TANGENT = prove
 (`!c y v. c IN sphere2_atlas /\ y IN FST c /\ v dot y = &0 /\
           frechet_derivative (\z. SND c (inv(norm z) % z)) (at y) v = vec 0
           ==> v = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GBS2_SPHERE_CHART_FACTS) THEN
  SUBGOAL_THEN `norm(y:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm y) % y:real^3 = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  ABBREV_TAC `Ts = {z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN FST (c:(real^3->bool)#(real^3->real^2))}` THEN
  SUBGOAL_THEN `(y:real^3) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z:real^3. inv(norm z) % z) (at y) =
    frechet_derivative (chart_inv (c:(real^3->bool)#(real^3->real^2)) o (\z. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `Ts:real^3->bool` THEN
    ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)) differentiable (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Ts:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ts" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(chart_inv (c:(real^3->bool)#(real^3->real^2))) differentiable
                (at ((\z:real^3. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)`; `chart_inv (c:(real^3->bool)#(real^3->real^2))`;
                 `frechet_derivative (\z:real^3. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)) (at y)`;
                 `frechet_derivative (chart_inv (c:(real^3->bool)#(real^3->real^2)))
                    (at ((\z:real^3. SND (c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)) y))`;
                 `y:real^3`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN
  ASM_SIMP_TAC[GBS2_NORMALIZE_TANGENT; o_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (chart_inv (c:(real^3->bool)#(real^3->real^2)))
                                          (at (SND c (y:real^3)))` LINEAR_0) THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let GBS2_SPHERE2_COVER = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> ?c. c IN sphere2_atlas /\ y IN FST c`,
  REPEAT STRIP_TAC THEN
  MP_TAC SPHERE2_ATLAS THEN REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `st:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(U:real^3->bool,st:real^3->real^2)` THEN ASM_REWRITE_TAC[FST]);;

let GBS2_PSI_CHART = prove
 (`!top atlas S (psi:real^3->A) psi' U phi y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     (U,phi) IN atlas /\ y IN sphere(vec 0,&1) /\ psi y IN U
     ==> ?W. open W /\ y IN W /\
             (!z. z IN W ==> ~(z = vec 0) /\ psi(inv(norm z) % z) IN U) /\
             smooth_map_on W (\z. phi(psi(inv(norm z) % z))) /\
             (!v. v dot y = &0 /\
                  frechet_derivative (\z. phi(psi(inv(norm z) % z))) (at y) v = vec 0
                  ==> v = vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE2_COVER) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)#(real^3->real^2)` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GBS2_SPHERE_CHART_FACTS) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                 `sphere(vec 0:real^3,&1)`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `FST(c:(real^3->bool)#(real^3->real^2))`;
                 `SND(c:(real^3->bool)#(real^3->real^2))`; `U:A->bool`; `phi:A->real^2`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[SPHERE2_ATLAS; PAIR] THEN
  ABBREV_TAC `D1 = IMAGE (SND(c:(real^3->bool)#(real^3->real^2)))
                         {x | x IN FST c INTER sphere(vec 0,&1) /\ (psi:real^3->A) x IN U}` THEN
  ABBREV_TAC `H = (phi:A->real^2) o (psi:real^3->A) o chart_inv(c:(real^3->bool)#(real^3->real^2))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `open (D1:real^2->bool) /\ smooth_map_on D1 (H:real^2->real^2)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Ts = {z:real^3 | ~(z = vec 0) /\ inv(norm z) % z IN FST(c:(real^3->bool)#(real^3->real^2))}` THEN
  ABBREV_TAC `N = \z:real^3. SND(c:(real^3->bool)#(real^3->real^2)) (inv(norm z) % z)` THEN
  EXISTS_TAC `{z:real^3 | z IN Ts /\ (N:real^3->real^2) z IN D1}` THEN
  SUBGOAL_THEN `!z:real^3. z IN Ts ==> ~(z = vec 0) /\ inv(norm z) % z IN FST(c:(real^3->bool)#(real^3->real^2)) /\
                            inv(norm z) % z IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN Ts /\ (N:real^3->real^2) z IN D1
               ==> (psi:real^3->A)(inv(norm z) % z) IN U /\
                   (phi:A->real^2)(psi(inv(norm z) % z)) = (H:real^2->real^2)(N z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      can (find_term (fun t -> t = `Ts:real^3->bool`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(N:real^3->real^2) z IN D1` THEN EXPAND_TAC "N" THEN EXPAND_TAC "D1" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^3 = inv(norm z) % z` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | z IN Ts /\ (N:real^3->real^2) z IN D1}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm y) % y:real^3 = y` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:real^3->real^2) y IN D1` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN EXPAND_TAC "D1" THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `(H:real^2->real^2) o (N:real^3->real^2)` THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `D1:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Ts:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(N:real^3->real^2) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Ts:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^2->real^2) differentiable (at ((N:real^3->real^2) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D1:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (phi:A->real^2)((psi:real^3->A)(inv(norm z) % z))) (at y) =
    frechet_derivative ((H:real^2->real^2) o (N:real^3->real^2)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `{z:real^3 | z IN Ts /\ (N:real^3->real^2) z IN D1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:real^3->real^2`; `H:real^2->real^2`;
                 `frechet_derivative (N:real^3->real^2) (at y)`;
                 `frechet_derivative (H:real^2->real^2) (at ((N:real^3->real^2) y))`;
                 `y:real^3`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])) THEN
  SUBGOAL_THEN
   `frechet_derivative (H:real^2->real^2) (at ((N:real^3->real^2) y))
      (frechet_derivative N (at y) v) = vec 0`
  (LABEL_TAC "zero") THENL
   [UNDISCH_TAC `frechet_derivative (\z. (phi:A->real^2)((psi:real^3->A)(inv(norm z) % z)))
                   (at y) v = vec 0` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(N:real^3->real^2) y` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] LRG_DIFFEO_DERIV) o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "diffeomorphism_on"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lin")
    (CONJUNCTS_THEN2 (LABEL_TAC "inv") ASSUME_TAC))))) THEN
  MATCH_MP_TAC GBS2_STEREO_TANGENT THEN
  MAP_EVERY EXISTS_TAC [`c:(real^3->bool)#(real^3->real^2)`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "inv" (MP_TAC o SPEC `frechet_derivative (N:real^3->real^2) (at y) v`) THEN
  USE_THEN "zero" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "inv" (MP_TAC o SPEC `vec 0:real^2`) THEN
  USE_THEN "lin" (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]));;

let GBS2_CHART_RESTRICT_OPEN = prove
 (`!top atlas S (U:A->bool) (phi:A->real^2).
     smooth_manifold_atlas top atlas /\ open_in top S /\ (U,phi) IN atlas
     ==> open (IMAGE phi (U INTER S))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`]
                SMOOTH_MANIFOLD_ATLAS_RESTRICT) THEN
  ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o SPECL [`U INTER S:A->bool`; `phi:A->real^2`] o CONJUNCT1) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  ANTS_TAC THENL [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let GBS2_FE_TANGENT = prove
 (`!top atlas S (psi:real^3->A) psi' (f:A->real^5).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. f(psi(inv(norm z) % z))) /\
     (!U phi. (U,phi) IN atlas
              ==> ?h. smooth_map_on (IMAGE phi (U INTER S)) h /\
                      (!x. x IN U INTER S ==> h(phi x) = f x) /\
                      (!y v. y IN IMAGE phi (U INTER S) /\
                             frechet_derivative h (at y) v = vec 0 ==> v = vec 0))
     ==> !y v. y IN sphere(vec 0,&1) /\ v dot y = &0 /\
               jacobian (\z. f(psi(inv(norm z) % z))) (at y) ** v = vec 0
               ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GBS2_SPHERE_FACTS) THEN
  SUBGOAL_THEN `(psi:real^3->A) y IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?U phi. (U,phi:A->real^2) IN (atlas:((A->bool)#(A->real^2))->bool) /\
                         (psi:real^3->A) y IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool)` THEN
    REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPEC `(psi:real^3->A) y` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^2`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^5` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `U:A->bool`; `phi:A->real^2`; `y:real^3`]
                GBS2_PSI_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = \z:real^3. (phi:A->real^2)((psi:real^3->A)(inv(norm z) % z))` THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^2) (U INTER S))` ASSUME_TAC THENL
   [MATCH_MP_TAC GBS2_CHART_RESTRICT_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^3->real^2) y IN IMAGE (phi:A->real^2) (U INTER S)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(psi:real^3->A) y` THEN
    UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
    ASM_SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN W ==> (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) z =
                          ((h:real^2->real^5) o (P:real^3->real^2)) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm z) % z IN sphere(vec 0:real^3,&1)` MP_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^3->real^2) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2->real^5) differentiable (at ((P:real^3->real^2) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^2) (U INTER S)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) differentiable (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `jacobian (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) (at y) ** v =
               vec 0` THEN
  REWRITE_TAC[jacobian] THEN ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) (at y) =
    frechet_derivative ((h:real^2->real^5) o (P:real^3->real^2)) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^3->real^2`; `h:real^2->real^5`;
                 `frechet_derivative (P:real^3->real^2) (at y)`;
                 `frechet_derivative (h:real^2->real^5) (at ((P:real^3->real^2) y))`;
                 `y:real^3`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (P:real^3->real^2) (at y) v = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      exists (fun t -> fst(dest_var t) = "h") (frees(concl th)) &&
      can (find_term (fun t -> try fst(dest_const t) = "frechet_derivative"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `(P:real^3->real^2) y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    exists (fun t -> fst(dest_var t) = "P") (frees(concl th)) &&
    can (find_term (fun t -> try fst(dest_const t) = "dot" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The planar conformal factors.                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The planar maps w |-> F(h(X w)) for X = stereo2_n_inv, stereo2_s_inv:    *)
(* conformal for the ambient metric Q with factor gbs2_mu, smooth and       *)
(* positive, and the north and south factors related by the inversion.     *)
(* ------------------------------------------------------------------------- *)

let gbs2_mu = new_definition
 `gbs2_mu (Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3) (X:real^2->real^3)
          (w:real^2) =
    partial_derivative 1 (\w. Fe(h(X w))) w dot
    (Q(Fe(h(X w))) ** partial_derivative 1 (\w. Fe(h(X w))) w)`;;

let GBS2_E_COMPOSE = prove
 (`!(Fe:real^3->real^5) (h:real^3->real^3) (X:real^2->real^3).
     (!w. X w IN sphere(vec 0,&1))
     ==> (\w. Fe(h(X w))) = Fe o (\z. h(inv(norm z) % z)) o X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `w:real^2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2`) THEN
  SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

let GBS2_E_SMOOTH = prove
 (`!(Fe:real^3->real^5) (h:real^3->real^3) (X:real^2->real^3).
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h(inv(norm z) % z)) /\
     (!y. y IN sphere(vec 0,&1) ==> h y IN sphere(vec 0,&1)) /\
     smooth_map_on (:real^2) X /\ (!w. X w IN sphere(vec 0,&1))
     ==> smooth_map_on (:real^2) (\w. Fe(h(X w)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GBS2_E_COMPOSE] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_SPHERE_0; NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  ASM_REWRITE_TAC[OPEN_NONZERO] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(norm z) % z IN sphere(vec 0:real^3,&1)` MP_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
    is_forall(concl th) && is_imp(snd(strip_forall(concl th)))))) THEN
  MESON_TAC[IN_SPHERE_0; NORM_0; REAL_ARITH `~(&0 = &1)`]);;

let GBS2_CHAIN3 = prove
 (`!(f:real^N->real^P) (g:real^M->real^N) (k:real^L->real^M) x.
     k differentiable (at x) /\ g differentiable (at (k x)) /\ f differentiable (at (g(k x)))
     ==> frechet_derivative (f o g o k) (at x) =
         frechet_derivative f (at (g(k x))) o frechet_derivative g (at (k x)) o
         frechet_derivative k (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[o_THM] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let GBS2_E_PD = prove
 (`!(Fe:real^3->real^5) (h:real^3->real^3) (X:real^2->real^3) w i.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h(inv(norm z) % z)) /\
     (!y. y IN sphere(vec 0,&1) ==> h y IN sphere(vec 0,&1)) /\
     smooth_map_on (:real^2) X /\ (!w. X w IN sphere(vec 0,&1))
     ==> partial_derivative i (\w. Fe(h(X w))) w =
         jacobian Fe (at (h(X w))) **
         (jacobian (\z. h(inv(norm z) % z)) (at (X w)) ** partial_derivative i X w)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GBS2_E_COMPOSE] THEN
  REWRITE_TAC[partial_derivative; jacobian] THEN
  SUBGOAL_THEN `norm((X:real^2->real^3) w) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~((X:real^2->real^3) w = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((h:real^3->real^3)((X:real^2->real^3) w)) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^3->real^3)((X:real^2->real^3) w) = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `\z. (h:real^3->real^3)(inv(norm z) % z)`;
                 `X:real^2->real^3`; `w:real^2`] GBS2_CHAIN3) THEN
  ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. (h:real^3->real^3)(inv(norm z) % z))
                                          (at ((X:real^2->real^3) w))) /\
                linear(frechet_derivative (Fe:real^3->real^5)
                                          (at ((h:real^3->real^3)((X:real^2->real^3) w))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let gbs2_conformal = new_definition
 `gbs2_conformal (Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3) <=>
    (!y. y IN sphere(vec 0,&1) ==> h y IN sphere(vec 0,&1)) /\
    (!x. x IN sphere(vec 0,&1) ==> ?!y. y IN sphere(vec 0,&1) /\ h y = x) /\
    smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h(inv(norm z) % z)) /\
    (!y. y IN sphere(vec 0,&1)
         ==> ?l. &0 < l /\
                 !v w. v dot y = &0 /\ w dot y = &0
                       ==> (jacobian (\z. h(inv(norm z) % z)) (at y) ** v) dot
                           (gbs2_G Fe Q (h y) **
                            (jacobian (\z. h(inv(norm z) % z)) (at y) ** w)) =
                           l * (v dot w))`;;

let GBS2_E_GRAM = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3) (X:real^2->real^3) w.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\ gbs2_conformal Fe Q h /\
     smooth_map_on (:real^2) X /\ (!w. X w IN sphere(vec 0,&1)) /\
     (!w i. X w dot partial_derivative i X w = &0)
     ==> ?l. &0 < l /\
             !i j. partial_derivative i (\w. Fe(h(X w))) w dot
                   (Q(Fe(h(X w))) ** partial_derivative j (\w. Fe(h(X w))) w) =
                   l * (partial_derivative i X w dot partial_derivative j X w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gbs2_conformal] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(X:real^2->real^3) w` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "gbs2_G" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `h:real^3->real^3`; `X:real^2->real^3`; `w:real^2`]
                GBS2_E_PD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`partial_derivative i (X:real^2->real^3) w`;
                                `partial_derivative j (X:real^2->real^3) w`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "gbs2_G" with Failure _ -> false))
          (concl th))) THEN
  ANTS_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gbs2_G; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  SIMP_TAC[]);;

let GBS2_STEREO_INV_FACTS = prove
 (`!X. X = stereo2_n_inv \/ X = stereo2_s_inv
       ==> smooth_map_on (:real^2) X /\ (!w. X w IN sphere(vec 0:real^3,&1)) /\
           (!w. X differentiable at w) /\
           (!w i. X w dot partial_derivative i X w = &0) /\
           (!w a b. frechet_derivative X (at w) a dot frechet_derivative X (at w) b =
                    cml_rho w * (a dot b))`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CML_XN_PROPS; CML_XS_PROPS; IN_SPHERE_0; partial_derivative; BEL_P_FRECHET;
              BEL_P_TANG; BEL_Q_TANG; BEL_P_CONF; BEL_Q_CONF; cml_rho]);;

let GBS2_MU_FACTS = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3) X.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal Fe Q h /\ (X = stereo2_n_inv \/ X = stereo2_s_inv)
     ==> smooth_map_on (:real^2) (\w. Fe(h(X w))) /\
         (!w. &0 < gbs2_mu Fe Q h X w) /\
         (!w a b. frechet_derivative (\w. Fe(h(X w))) (at w) a dot
                  (Q(Fe(h(X w))) ** frechet_derivative (\w. Fe(h(X w))) (at w) b) =
                  gbs2_mu Fe Q h X w * (a dot b)) /\
         smooth_map_on (:real^2) (\w. lift(gbs2_mu Fe Q h X w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o MATCH_MP GBS2_STEREO_INV_FACTS)))) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GBS2_E_SMOOTH THEN
    UNDISCH_TAC `gbs2_conformal (Fe:real^3->real^5) Q h` THEN
    REWRITE_TAC[gbs2_conformal] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. ?l. &0 < l /\
            !i j. partial_derivative i (\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w))) w dot
                  ((Q:real^5->real^5^5)(Fe(h(X w))) ** partial_derivative j (\w. Fe(h(X w))) w) =
                  l * (cml_rho w * ((basis i:real^2) dot basis j))`
  (LABEL_TAC "gram") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`Fe:real^3->real^5`; `Q:real^5->real^5^5`; `h:real^3->real^3`;
                   `X:real^2->real^3`; `w:real^2`] GBS2_E_GRAM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[partial_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
            ==> partial_derivative i (\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w))) w dot
                ((Q:real^5->real^5^5)(Fe(h(X w))) ** partial_derivative j (\w. Fe(h(X w))) w) =
                gbs2_mu Fe Q h X w * ((basis i:real^2) dot basis j)`
  (LABEL_TAC "entries") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "gram" (X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC o
                                            SPEC `w:real^2`) THEN
    ASM_REWRITE_TAC[gbs2_mu] THEN
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "gram" (X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC o
                                   SPEC `w:real^2`) THEN
    ASM_REWRITE_TAC[gbs2_mu] THEN SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[CML_RHO_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:real^2`; `a:real^2`; `b:real^2`] THEN
    SUBGOAL_THEN `(\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w))) differentiable at w`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CML_FRECHET_BASIS2] THEN
    REWRITE_TAC[DOT_LADD; DOT_LMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_RADD; DOT_RMUL] THEN
    USE_THEN "entries" (fun th -> SIMP_TAC[th; ARITH]) THEN
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH; DOT_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[gbs2_mu] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w))`;
                 `Q:real^5->real^5^5`; `1`; `1`] GBS2_GRAM_ENTRY_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV]);;

let GBS2_MU_REL = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3) w.
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal Fe Q h /\ ~(w = vec 0)
     ==> gbs2_mu Fe Q h stereo2_n_inv w =
         gbs2_mu Fe Q h stereo2_s_inv (cml_inv w) / norm w pow 4`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `Q:real^5->real^5^5`; `h:real^3->real^3`;
                 `stereo2_s_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\w. (Fe:real^3->real^5)((h:real^3->real^3)(stereo2_s_inv w))) differentiable
                (at (cml_inv w))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_FRECHET) THEN
  SUBGOAL_THEN
   `frechet_derivative (\w. (Fe:real^3->real^5)((h:real^3->real^3)(stereo2_n_inv w))) (at w) =
    frechet_derivative ((\w. Fe(h(stereo2_s_inv w))) o cml_inv) (at w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM; o_THM] THEN
    SIMP_TAC[CML_XN_XS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cml_inv`; `\w. (Fe:real^3->real^5)((h:real^3->real^3)(stereo2_s_inv w))`;
                 `bel_dT w`;
                 `frechet_derivative (\w. (Fe:real^3->real^5)((h:real^3->real^3)
                                             (stereo2_s_inv w))) (at (cml_inv w))`;
                 `w:real^2`] DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "bel_dT" with Failure _ -> false))
            (concl th) && is_eq(concl th))) THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])) THEN
  REWRITE_TAC[gbs2_mu; partial_derivative] THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_SIMP_TAC[CML_XN_XS] THEN
  ASM_REWRITE_TAC[CML_DT_DOT] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[real_div; REAL_MUL_RID; REAL_POW_INV] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Local charts of the planar parametrization.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Local charts of the planar parametrization w |-> psi(h(X w)): near each  *)
(* w, its representative in the preferred chart at psi(h(X w)) is smooth    *)
(* and pulls the metric back to gbs2_mu times the Euclidean metric.         *)
(* ------------------------------------------------------------------------- *)

let GBS2_LOCAL_CHART = prove
 (`!top atlas (g:A->real^2^2) S (psi:real^3->A) psi' (f:A->real^5) Q h X.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     (!U phi. (U,phi) IN atlas
              ==> ?hc. smooth_map_on (IMAGE phi (U INTER S)) hc /\
                       (!x. x IN U INTER S ==> hc(phi x) = f x)) /\
     (!U phi. (U,phi) IN atlas
              ==> !x. x IN U INTER S
                      ==> metric_local atlas (U,phi) g (phi x) =
                          transp(matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) **
                          Q(f x) **
                          matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. f(psi(inv(norm z) % z))) /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal (\z. f(psi(inv(norm z) % z))) Q h /\
     (X = stereo2_n_inv \/ X = stereo2_s_inv)
     ==> !w. ?t. open t /\ w IN t /\
                 (!w'. w' IN t ==> psi(h(X w')) IN FST(chart_at atlas (psi(h(X w))))) /\
                 smooth_map_on t (\w'. SND(chart_at atlas (psi(h(X w)))) (psi(h(X w')))) /\
                 (!w' a b.
                    w' IN t
                    ==> frechet_derivative
                          (\w'. SND(chart_at atlas (psi(h(X w)))) (psi(h(X w')))) (at w') a
                        dot
                        (metric_local atlas (chart_at atlas (psi(h(X w)))) g
                           (SND(chart_at atlas (psi(h(X w)))) (psi(h(X w')))) **
                         frechet_derivative
                          (\w'. SND(chart_at atlas (psi(h(X w)))) (psi(h(X w')))) (at w') b) =
                        gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h X w' * (a dot b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN X_GEN_TAC `w:real^2` THEN
  ABBREV_TAC `Fe = \z:real^3. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_STEREO_INV_FACTS) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `Q:real^5->real^5^5`; `h:real^3->real^3`;
                 `X:real^2->real^3`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `gbs2_conformal (Fe:real^3->real^5) Q h` THEN
  REWRITE_TAC[gbs2_conformal] THEN STRIP_TAC THEN
  (* the point and its chart *)
  ABBREV_TAC `y = (h:real^3->real^3)((X:real^2->real^3) w)` THEN
  SUBGOAL_THEN `(y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->A) y IN topspace top /\ psi y IN S` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(psi:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^2))->bool) ((psi:real^3->A) y)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(FST c,SND c) IN (atlas:((A->bool)#(A->real^2))->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `FST(c:(A->bool)#(A->real^2))`;
                 `SND(c:(A->bool)#(A->real^2))`; `y:real^3`] GBS2_PSI_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w':real^2. norm((X:real^2->real^3) w') = &1 /\ norm((h:real^3->real^3)(X w')) = &1`
  ASSUME_TAC THENL [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\w':real^2. (h:real^3->real^3)((X:real^2->real^3) w'))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\z. (h:real^3->real^3)(inv(norm z) % z)) o (X:real^2->real^3)` THEN
    ASM_REWRITE_TAC[o_THM; REAL_INV_1; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  EXISTS_TAC `{w':real^2 | w' IN (:real^2) /\ (h:real^3->real^3)((X:real^2->real^3) w') IN W}` THEN
  ABBREV_TAC `t = {w':real^2 | w' IN (:real^2) /\ (h:real^3->real^3)((X:real^2->real^3) w') IN W}` THEN
  SUBGOAL_THEN `open (t:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w':real^2. w' IN t
       ==> (h:real^3->real^3)((X:real^2->real^3) w') IN W /\
           (psi:real^3->A)(h(X w')) IN FST(c:(A->bool)#(A->real^2)) /\ psi(h(X w')) IN S`
  (LABEL_TAC "tprops") THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `w':real^2` THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^3->real^3)((X:real^2->real^3) w')` o check (fun th ->
      is_forall(concl th) && exists (fun v -> fst(dest_var v) = "W") (frees(concl th)))) THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h:real^3->real^3)((X:real^2->real^3) w') IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (psi:real^3->A) (sphere(vec 0,&1)) = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on t (\w':real^2. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w'))))` ASSUME_TAC THENL
  [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\z. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)(inv(norm z) % z))) o
              (\w':real^2. (h:real^3->real^3)((X:real^2->real^3) w'))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[o_THM; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN USE_THEN "tprops" (fun th -> MESON_TAC[th]);
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    EXPAND_TAC "t" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV];
    USE_THEN "tprops" (fun th -> MESON_TAC[th]);
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`w':real^2`; `a:real^2`; `b:real^2`] THEN DISCH_TAC THEN
    USE_THEN "tprops" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(w':real^2) IN t`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`FST(c:(A->bool)#(A->real^2))`; `SND(c:(A->bool)#(A->real^2))`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
          (concl th) &&
      exists (fun v -> fst(dest_var v) = "S") (frees(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `hc:real^2->real^5` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w'))` o
    C MATCH_MP (ASSUME `(FST c,SND c) IN (atlas:((A->bool)#(A->real^2))->bool)`) o
    SPECL [`FST(c:(A->bool)#(A->real^2))`; `SND(c:(A->bool)#(A->real^2))`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "metric_local" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER; PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c INTER S))` ASSUME_TAC THENL
   [MATCH_MP_TAC GBS2_CHART_RESTRICT_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    SUBGOAL_THEN
   `frechet_derivative ((f:A->real^5) o chart_inv (FST(c:(A->bool)#(A->real^2)) INTER S,SND c))
                       (at (SND c ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w'))))) =
    frechet_derivative (hc:real^2->real^5) (at (SND c (psi(h(X w')))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c INTER S)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x'':A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology top (S:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^2))->bool) S`;
                   `FST(c:(A->bool)#(A->real^2)) INTER S`; `SND(c:(A->bool)#(A->real^2))`]
                  CHART_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_RESTRICT_ATLAS] THEN
      EXISTS_TAC `FST(c:(A->bool)#(A->real^2))` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x'':A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    SUBGOAL_THEN `(\w':real^2. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))) differentiable (at w')` ASSUME_TAC THENL
  [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(hc:real^2->real^5) differentiable (at (SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))))` ASSUME_TAC THENL
  [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
   EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c INTER S)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (\w. (Fe:real^3->real^5)((h:real^3->real^3)((X:real^2->real^3) w))) (at w') =
   frechet_derivative ((hc:real^2->real^5) o (\w':real^2. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)(h(X w'))))) (at w')` ASSUME_TAC THENL
  [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `t:real^2->bool` THEN
   ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `w'':real^2` THEN DISCH_TAC THEN
   USE_THEN "tprops" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(w'':real^2) IN t`)) THEN
   EXPAND_TAC "Fe" THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
   CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\w':real^2. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))`;
                 `hc:real^2->real^5`;
                 `frechet_derivative (\w':real^2. SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))) (at w')`;
                 `frechet_derivative (hc:real^2->real^5) (at (SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))))`;
                 `w':real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w':real^2`; `a:real^2`; `b:real^2`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "gbs2_mu" with Failure _ -> false)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "frechet_derivative" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "Fe" THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    SUBGOAL_THEN `linear(frechet_derivative (hc:real^2->real^5) (at (SND(c:(A->bool)#(A->real^2)) ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w'))))))` ASSUME_TAC THENL
  [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS]]);;

(* ========================================================================= *)
(* The Gauss curvature in the planar coordinates.                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The Gauss curvature in the planar coordinates: K = R/2 with              *)
(* R(psi(h(X w))) = --(Laplacian of log mu)(w) / mu(w).                      *)
(* ------------------------------------------------------------------------- *)

let GBS2_GRAM_CMUL = prove
 (`!(J:real^2^2) (G:real^2^2) m.
     (!a b. (J ** a) dot (G ** (J ** b)) = m * (a dot b))
     ==> transp J ** G ** J = m %% mat 1`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MATRIX_CMUL_COMPONENT; MAT_COMPONENT; ARITH] THEN
  SIMP_TAC[CMT_GRAM_ENTRY; DIMINDEX_2; ARITH] THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let GBS2_CURV = prove
 (`!top atlas (g:A->real^2^2) S (psi:real^3->A) psi' (f:A->real^5) Q h X w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     (!U phi. (U,phi) IN atlas
              ==> ?hc. smooth_map_on (IMAGE phi (U INTER S)) hc /\
                       (!x. x IN U INTER S ==> hc(phi x) = f x)) /\
     (!U phi. (U,phi) IN atlas
              ==> !x. x IN U INTER S
                      ==> metric_local atlas (U,phi) g (phi x) =
                          transp(matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) **
                          Q(f x) **
                          matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. f(psi(inv(norm z) % z))) /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal (\z. f(psi(inv(norm z) % z))) Q h /\
     (X = stereo2_n_inv \/ X = stereo2_s_inv)
     ==> mfd_scalar atlas g (psi(h(X w))) =
         --(cml_lap (\x. log(gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h X x)) w) /
         gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h X w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`;
                 `Q:real^5->real^5^5`; `h:real^3->real^3`; `X:real^2->real^3`]
                GBS2_LOCAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^2`) THEN
  ABBREV_TAC `mu = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h X` THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^2))->bool)
                           ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w)))` THEN
  ABBREV_TAC `Fc = \w':real^2. SND(c:(A->bool)#(A->real^2))
                                 ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `X:real^2->real^3`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN t ==> (Fc:real^2->real^2) differentiable (at z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN t
        ==> mpullback (Fc:real^2->real^2) (metric_local atlas c (g:A->real^2^2)) z =
            (mu:real^2->real) z %% mat 1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN MATCH_MP_TAC GBS2_GRAM_CMUL THEN
    SUBGOAL_THEN `linear(frechet_derivative (Fc:real^2->real^2) (at z))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN
    UNDISCH_TAC `(\w':real^2. SND(c:(A->bool)#(A->real^2))
                   ((psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w')))) = Fc` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th] THEN RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fc:real^2->real^2) (at w))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(det(matrix(frechet_derivative (Fc:real^2->real^2) (at w))) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `matrix(frechet_derivative (Fc:real^2->real^2) (at w)) ** a = vec 0` THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^2`; `a:real^2`; `a:real^2`] o check (fun th ->
      is_forall(concl th) && exists (fun v -> fst(dest_var v) = "Fc") (frees(concl th)) &&
      can (find_term (fun t -> try fst(dest_const t) = "metric_local" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN
    SUBGOAL_THEN `&0 < (mu:real^2->real) w * ((a:real^2) dot a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fc:real^2->real^2`; `t:real^2->bool`; `w:real^2`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^2->bool` (X_CHOOSE_THEN `u:real^2->bool`
    (X_CHOOSE_THEN `Gi:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w)) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false)) (concl th))) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `gbs2_conformal (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h` THEN
    REWRITE_TAC[gbs2_conformal] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_STEREO_INV_FACTS o check (fun th -> is_disj(concl th))) THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^2)) IN atlas` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `(psi:real^3->A)((h:real^3->real^3)((X:real^2->real^3) w))`] CHART_AT) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field u (metric_local atlas (c:(A->bool)#(A->real^2)) (g:A->real^2^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `diffeomorphism_on t' u (Fc:real^2->real^2) Gi` THEN
    REWRITE_TAC[diffeomorphism_on] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    EXPAND_TAC "Fc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "FST" with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "IN" with Failure _ -> false)) (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "metric_local" with Failure _ -> false)) (concl th)))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->bool`; `t':real^2->bool`; `Fc:real^2->real^2`; `Gi:real^2->real^2`;
                 `metric_local atlas (c:(A->bool)#(A->real^2)) (g:A->real^2^2)`; `w:real^2`]
                LSCALAR_PULLBACK) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lscalar (mpullback (Fc:real^2->real^2) (metric_local atlas c (g:A->real^2^2))) w =
                lscalar (\z. (mu:real^2->real) z %% mat 1) w` SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `t':real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `mu:real^2->real`; `w:real^2`] GBS2_CONF_SCALAR) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "Fc" THEN EXPAND_TAC "c" THEN REWRITE_TAC[mfd_scalar]);;

(* ------------------------------------------------------------------------- *)
(* Integrability of the conformal factor: mu = (mu / rho) rho with mu / rho *)
(* bounded (on the unit disc directly, outside it through the inversion and *)
(* the south factor), and cml_rho integrable.                               *)
(* ------------------------------------------------------------------------- *)

let GBS2_MU_INTEGRABLE = prove
 (`!(Fe:real^3->real^5) (Q:real^5->real^5^5) (h:real^3->real^3).
     smooth_map_on {z:real^3 | ~(z = vec 0)} Fe /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal Fe Q h
     ==> (\w. lift(gbs2_mu Fe Q h stereo2_n_inv w)) absolutely_integrable_on (:real^2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `Q:real^5->real^5^5`; `h:real^3->real^3`;
                 `stereo2_n_inv`] GBS2_MU_FACTS) THEN
  MP_TAC(ISPECL [`Fe:real^3->real^5`; `Q:real^5->real^5^5`; `h:real^3->real^3`;
                 `stereo2_s_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mu = gbs2_mu (Fe:real^3->real^5) Q h stereo2_n_inv` THEN
  ABBREV_TAC `mu' = gbs2_mu (Fe:real^3->real^5) Q h stereo2_s_inv` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^2. ~(w = vec 0) ==> (mu:real^2->real) w = mu'(cml_inv w) / norm w pow 4`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["mu"; "mu'"] THEN
    MATCH_MP_TAC GBS2_MU_REL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift((mu:real^2->real) w / cml_rho w)) continuous_on (:real^2) /\
    (\w. lift((mu':real^2->real) w / cml_rho w)) continuous_on (:real^2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC CML_SM_DIV THEN
    ASM_SIMP_TAC[OPEN_UNIV; CML_RHO_SMOOTH; CML_RHO_POS; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\w. (mu:real^2->real) w / cml_rho w` CML_CONT_BOUNDED_CBALL) THEN
  MP_TAC(ISPEC `\w. (mu':real^2->real) w / cml_rho w` CML_CONT_BOUNDED_CBALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "M2")) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (LABEL_TAC "M1")) THEN
  SUBGOAL_THEN `!w:real^2. (mu:real^2->real) w <= max M1 M2 * cml_rho w` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN
    SUBGOAL_THEN `(mu:real^2->real) w / cml_rho w <= max M1 M2` MP_TAC THENL
     [ASM_CASES_TAC `(w:real^2) IN cball(vec 0,&1)` THENL
       [USE_THEN "M1" (MP_TAC o C MATCH_MP (ASSUME `(w:real^2) IN cball(vec 0,&1)`)) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(w:real^2 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((w:real^2) IN cball(vec 0,&1))` THEN
        ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(mu:real^2->real) w / cml_rho w = mu'(cml_inv w) / cml_rho(cml_inv w)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[] THEN
        MP_TAC(SPEC `w:real^2` CML_RHO_REL) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `&0 < norm(w:real^2) pow 4 /\ &0 < cml_rho(cml_inv w)` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT; CML_RHO_POS]; ALL_TAC] THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      USE_THEN "M2" (MP_TAC o SPEC `cml_inv w`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_CBALL_0; cml_inv; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
        UNDISCH_TAC `~((w:real^2) IN cball(vec 0,&1))` THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_POW_2; REAL_INV_MUL; REAL_FIELD
          `&0 < x ==> (inv x * inv x) * x = inv x`] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[] THEN REAL_ARITH_TAC];
      SIMP_TAC[REAL_LE_LDIV_EQ; CML_RHO_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\w:real^2. lift(max M1 M2 * cml_rho w)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN REWRITE_TAC[CML_RHO_INTEGRABLE];
    REWRITE_TAC[IN_UNIV; NORM_LIFT; LIFT_DROP] THEN X_GEN_TAC `w:real^2` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "real_max" with Failure _ -> false))
          (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "real_lt" with Failure _ -> false))
          (concl th) &&
      exists (fun v -> fst(dest_var v) = "mu") (frees(concl th)))) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The area of the surface: the Riemannian density of the chart            *)
(* representative of w |-> psi(h(stereo2_n_inv w)) is gbs2_mu, a point has *)
(* volume 0, and the planar parametrization covers S but one point.         *)
(* ------------------------------------------------------------------------- *)

let GBS2_DENSITY = prove
 (`!(J:real^2^2) (G:real^2^2) m.
     transp J ** G ** J = m %% mat 1 /\ &0 <= m
     ==> abs(det J) * sqrt(det G) = m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `det(J:real^2^2) pow 2 * det(G:real^2^2) = m pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `det:real^2^2->real`) THEN
    REWRITE_TAC[DET_MUL; DET_TRANSP; DET_CMUL; DET_I; DIMINDEX_2] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS; GSYM SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT]);;

let GBS2_VOLUME_SING = prove
 (`!top atlas (g:A->real^N^N) p.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ p IN topspace top
     ==> mfd_has_volume (top,atlas) g {p} (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) p`; `{p:A}`; `&0`]
                MFD_HAS_VOLUME_CHART) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[NEGLIGIBLE_SING; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE;
           ABSOLUTELY_INTEGRABLE_ON_NEGLIGIBLE; INTEGRAL_ON_NEGLIGIBLE; DROP_VEC]);;

let GBS2_AREA = prove
 (`!top atlas (g:A->real^2^2) S (psi:real^3->A) psi' (f:A->real^5) Q h a.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
     (!U phi. (U,phi) IN atlas
              ==> ?hc. smooth_map_on (IMAGE phi (U INTER S)) hc /\
                       (!x. x IN U INTER S ==> hc(phi x) = f x)) /\
     (!U phi. (U,phi) IN atlas
              ==> !x. x IN U INTER S
                      ==> metric_local atlas (U,phi) g (phi x) =
                          transp(matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) **
                          Q(f x) **
                          matrix(frechet_derivative
                             (f o chart_inv (U INTER S,phi)) (at (phi x)))) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. f(psi(inv(norm z) % z))) /\
     smooth_map_on (:real^5) ((vectorize:real^5^5->real^(5,5)finite_prod) o Q) /\
     gbs2_conformal (\z. f(psi(inv(norm z) % z))) Q h /\
     mfd_has_volume (top,atlas) g S a
     ==> a = drop(integral (:real^2)
                  (\w. lift(gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h stereo2_n_inv w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`;
                 `Q:real^5->real^5^5`; `h:real^3->real^3`; `stereo2_n_inv`]
                GBS2_LOCAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "lc") THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`] GBS2_MU_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `stereo2_n_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `stereo2_n_inv` GBS2_STEREO_INV_FACTS) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false))
        (concl th))) THEN
  STRIP_TAC THEN
  UNDISCH_TAC `gbs2_conformal (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h` THEN
  REWRITE_TAC[gbs2_conformal] THEN STRIP_TAC THEN
  ABBREV_TAC `mu = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                           stereo2_n_inv` THEN
  SUBGOAL_THEN `!w:real^2. norm(stereo2_n_inv w) = &1 /\
                           norm((h:real^3->real^3)(stereo2_n_inv w)) = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* smoothness and continuity of the planar parametrization *)
  SUBGOAL_THEN `smooth_map_on (:real^2) (\w:real^2. (h:real^3->real^3)(stereo2_n_inv w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\z. (h:real^3->real^3)(inv(norm z) % z)) o stereo2_n_inv` THEN
    ASM_REWRITE_TAC[o_THM; REAL_INV_1; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (:real^2),top)
                  (\w. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))) =
                  psi o (\w. h(stereo2_n_inv w))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* injectivity of psi o h on the sphere *)
  SUBGOAL_THEN `!y1 y2. y1 IN sphere(vec 0:real^3,&1) /\ y2 IN sphere(vec 0,&1) /\
                        (psi:real^3->A)((h:real^3->real^3) y1) = psi(h y2)
                        ==> y1 = y2`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) y1 IN sphere(vec 0,&1) /\ h y2 IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3) y1 = h y2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `psi':A->real^3`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?!y. y IN sphere(vec 0:real^3,&1) /\ (h:real^3->real^3) y = h y1`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the parametrization covers S but the image of the pole *)
  SUBGOAL_THEN `!y. y IN sphere(vec 0:real^3,&1) ==> (psi:real^3->A)((h:real^3->real^3) y) IN S`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\w. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))) (:real^2) UNION
                {psi(h(basis 3))} = S` (LABEL_TAC "cover") THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_SING] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THENL [STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?y. y IN sphere(vec 0:real^3,&1) /\ (psi:real^3->A) y = x` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `(psi':A->real^3) x` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?!y0. y0 IN sphere(vec 0:real^3,&1) /\ (h:real^3->real^3) y0 = y` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    ASM_CASES_TAC `y0:real^3 = basis 3` THENL
     [DISJ2_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ1_TAC THEN EXISTS_TAC `stereo2_n y0` THEN
    SUBGOAL_THEN `stereo2_n_inv(stereo2_n y0) = y0` SUBST1_TAC THENL
     [MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (\w. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w)))
                                (:real^2))
                         {psi(h(basis 3))}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `!s (a:A). DISJOINT s {a} <=> ~(a IN s)`; IN_IMAGE; IN_UNIV;
                NOT_EXISTS_THM] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `basis 3 = stereo2_n_inv w` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `w:real^2` STEX_STEREO2_N_INV_IN) THEN REWRITE_TAC[IN_DELETE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\w. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))) (:real^2)
                SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cover" (SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->A)((h:real^3->real^3)(basis 3)) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `S:A->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* derivatives and density of the chart representatives *)
  SUBGOAL_THEN
   `!Z:real^2. ((\W. SND(chart_at (atlas:((A->bool)#(A->real^2))->bool)
                          ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv Z))))
                       (psi(h(stereo2_n_inv W)))) has_derivative
                frechet_derivative (\W. SND(chart_at atlas (psi(h(stereo2_n_inv Z))))
                                         (psi(h(stereo2_n_inv W)))) (at Z))
               (at Z within (:real^2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^2` THEN USE_THEN "lc" (MP_TAC o SPEC `Z:real^2`) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z:real^2.
      abs(det(matrix(frechet_derivative
         (\W. SND(chart_at (atlas:((A->bool)#(A->real^2))->bool)
                   ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv Z))))
                 (psi(h(stereo2_n_inv W)))) (at Z)))) *
      mfd_density atlas (chart_at atlas (psi(h(stereo2_n_inv Z)))) (g:A->real^2^2)
        (SND(chart_at atlas (psi(h(stereo2_n_inv Z)))) (psi(h(stereo2_n_inv Z)))) =
      (mu:real^2->real) Z`
  (LABEL_TAC "dens") THENL
   [X_GEN_TAC `Z:real^2` THEN USE_THEN "lc" (MP_TAC o SPEC `Z:real^2`) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[mfd_density] THEN MATCH_MP_TAC GBS2_DENSITY THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
    MATCH_MP_TAC GBS2_GRAM_CMUL THEN
    SUBGOAL_THEN
     `linear(frechet_derivative
        (\W. SND(chart_at (atlas:((A->bool)#(A->real^2))->bool)
                  ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv Z))))
                (psi(h(stereo2_n_inv W)))) (at Z))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z:real^2. lift((mu:real^2->real) Z)) integrable_on (:real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the area formula *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `\w:real^2. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))`;
                 `\Z:real^2. frechet_derivative
                     (\W:real^2. SND(chart_at (atlas:((A->bool)#(A->real^2))->bool)
                                    ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv Z))))
                                 (psi(h(stereo2_n_inv W)))) (at Z)`;
                 `(:real^2)`] GRGA_AREA_FORMULA) THEN
  REWRITE_TAC[] THEN USE_THEN "dens" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2))) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`Z:real^2`; `Z':real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `stereo2_n_inv Z = stereo2_n_inv Z'` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `stereo2_n`) THEN REWRITE_TAC[STEX_STEREO2_N_RIGHT];
    DISCH_THEN SUBST_ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                       `g:A->real^2^2`; `S:A->bool`] MFD_HAS_VOLUME_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "cover" (SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_SIMP_TAC[GBS2_VOLUME_SING]);;

(* ------------------------------------------------------------------------- *)
(* The headline: Gauss-Bonnet area bound for a Riemannian 2-sphere,         *)
(* 4 pi <= k0 * area when the scalar curvature is at most 2 k0.             *)
(* ------------------------------------------------------------------------- *)

let GBS2_GB_SPHERE_AREA = prove
 (`!u:A->bool. CM_GB_SPHERE_AREA_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[CM_GB_SPHERE_AREA_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                       `g:A->real^2^2`; `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`;
                       `k0:real`; `a:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`] GBS2_EMBED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^5` (X_CHOOSE_THEN `Q:real^5->real^5^5`
    (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!U phi. (U,phi) IN (atlas:((A->bool)#(A->real^2))->bool)
                        ==> ?hc. smooth_map_on (IMAGE phi (U INTER S)) hc /\
                                 (!x. x IN U INTER S ==> hc(phi x) = (f:A->real^5) x)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MESON_TAC[check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "frechet_derivative"
                               with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "metric_local"
                                   with Failure _ -> false)) (concl th))) th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`] GBS2_FPSI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`] GBS2_FE_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* homogeneity of the radial extension *)
  SUBGOAL_THEN `!t z. &0 < t /\ ~(z = vec 0)
                      ==> (f:A->real^5)((psi:real^3->A)(inv(norm(t % z)) % (t % z))) =
                          f(psi(inv(norm z) % z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `inv(norm(t % z)) % (t % z) = inv(norm(z:real^3)) % z`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* uniformization *)
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `lam:real`] GBS2_UNIFORMIZE) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `gbs2_conformal (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h`
  ASSUME_TAC THENL [REWRITE_TAC[gbs2_conformal] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the area *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`;
                 `Q:real^5->real^5^5`; `h:real^3->real^3`; `a:real`] GBS2_AREA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* the planar factors *)
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `stereo2_n_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `stereo2_s_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`] GBS2_MU_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w:real^2. ~(w = vec 0)
               ==> gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                           stereo2_n_inv w =
                   gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h stereo2_s_inv (cml_inv w) /
                   norm w pow 4`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GBS2_MU_REL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. mfd_scalar atlas (g:A->real^2^2) ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))) =
        --(cml_lap (\x. log(gbs2_mu (\z. (f:A->real^5)(psi(inv(norm z) % z))) Q h
                                    stereo2_n_inv x)) w) /
        gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h stereo2_n_inv w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GBS2_CURV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:A->bool`; `psi':A->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w)) IN S`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false))
          (concl th))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `stereo2_n_inv` GBS2_STEREO_INV_FACTS) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `mu = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                           stereo2_n_inv` THEN
  ABBREV_TAC `mu' = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                            stereo2_s_inv` THEN
  (* the curvature bound and the integrability of k0 mu *)
  SUBGOAL_THEN `!z:real^2. --(cml_lap (\x. log((mu:real^2->real) x)) z) / &2 <= k0 * mu z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^2^2)
                    ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv z))) <= &2 * k0`
    MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_scalar" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (mu:real^2->real) z` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. lift(k0 * (mu:real^2->real) z)) absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the planar Gauss-Bonnet inequality *)
  MP_TAC(ISPECL [`mu:real^2->real`; `mu':real^2->real`; `\z:real^2. k0 * (mu:real^2->real) z`]
                CML_GB_INEQ) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> &4 * pi <= x ==> &4 * pi <= y`) THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_CMUL]);;

