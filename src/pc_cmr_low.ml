(* ========================================================================= *)
(* Unit pc_cmr_low (a unit of the replacement chain of pc_cm_replacement):   *)
(* the pre-step Contr.  Slices of a sweepout of energy at most E1 are        *)
(* deformed to constant maps, slices of energy at least E2 are kept,         *)
(* energies do not increase, by a homotopy of sweepouts.                     *)
(*                                                                           *)
(* The reflected chart and the C^0 estimate for the                          *)
(* replacement on the big cap IMAGE (cm_capmap (mat 1)) (ball(vec 0,R)),    *)
(* the complement of a small cap around the north pole basis 3 (CMW_V_CLOSE *)
(* of pc_cmw_pos for W^{1,2} maps instead of C^1 sweepouts).                *)
(* ========================================================================= *)

needs "src/pc_cmr_nonharm.ml";;

prioritize_real();;
type_invention_error := true;;

(* The chart of the reflection z3 |-> --z3: its cap map is stereo2_s_inv.   *)

let CMR_QS_FACTS = prove
 (`orthogonal_matrix (matrix bel_refl3) /\
   (!x. cm_capmap (matrix bel_refl3) x = stereo2_s_inv x)`,
  CONJ_TAC THENL
   [MATCH_MP_TAC ORTHOGONAL_MATRIX_MATRIX THEN
    REWRITE_TAC[orthogonal_transformation; BEL_REFL3_LINEAR; BEL_REFL3_DOT];
    SIMP_TAC[cm_capmap; MATRIX_WORKS; BEL_REFL3_LINEAR; BEL_Q_FORM]]);;

(* Chart energies are at most twice the S^2 energy.                         *)

let CMR_CHART_GDIR_LE_SEN = prove
 (`!S (G:real^K->real^K^K) Lam (u:real^3->real^K) (Q:real^3^3) D.
     CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\ open D
     ==> wan_gdir D G (\y. u(cm_capmap Q y)) <= &2 * cm_sen G u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`;
                 `D:real^2->bool`] CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`]
                CMR_SEN_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`IMAGE (cm_capmap Q) (D:real^2->bool)`;
                             `IMAGE (cm_capmap Q) (:real^2)`] o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMR_CAPMAP_CONE; OPEN_UNIV] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  UNDISCH_TAC `cm_sen G (u:real^3->real^K) = cmr_sen_on G u (IMAGE (cm_capmap Q) (:real^2))` THEN
  UNDISCH_TAC
   `cmr_sen_on G (u:real^3->real^K) (IMAGE (cm_capmap Q) D) =
    wan_gdir D G (\y. u(cm_capmap Q y)) / &2` THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The C^0 estimate for the replacement on the big cap.                     *)

let CMR_BIGCAP_C0 = prove
 (`!S (G:real^K->real^K^K) d e Lam eta.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     CMR_GCOND G Lam /\ &0 < eta
     ==> ?delta. &0 < delta /\
           !R (u:real^3->real^K).
             &1 <= R /\ cm_smap S u /\ cm_sen G u <= delta /\
             (!y. y IN sphere(vec 0,&1) /\ norm(y - basis 3) <= &2 / R
                  ==> norm(u y - u(basis 3)) <= delta)
             ==> !y. y IN sphere(vec 0,&1)
                     ==> norm(cmr_rep1 S G (mat 1) (vec 0) R u y - u(basis 3)) < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `eta:real`]
                CMW_C0EST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_TARGET_ELLIPTIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `min (delta0 / &2) (min (lam * delta0 / &4) (min (e / &4) (eta / &2)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (delta0 / &2) (min (lam * delta0 / &4) (min (e / &4) (eta / &2)))` THEN
  SUBGOAL_THEN
   `delta <= delta0 / &2 /\ delta <= lam * delta0 / &4 /\ delta <= e / &4 /\ delta <= eta / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`R:real`; `u:real^3->real^K`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "osc")))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(CONJUNCT1 CMR_QS_FACTS) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3->real^K)(basis 3) IN S` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  ABBREV_TAC `f = \x. (u:real^3->real^K)(cm_capmap (mat 1) x)` THEN
  (* the data on the big disc and its minimizer *)
  SUBGOAL_THEN `cm_cmap S (ball(vec 0:real^2,R)) (f:real^2->real^K) /\
                wan_gdir (ball(vec 0:real^2,R)) G f <= e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * cm_sen G (u:real^3->real^K)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CMR_CHART_GDIR_LE_SEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `Lam:real`] THEN
    ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `vec 0:real^2`; `R:real`;
                 `f:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w = cmr_minw S G (vec 0:real^2) R (f:real^2->real^K)` THEN
  (* the rescaled minimizer on the unit disc *)
  SUBGOAL_THEN
   `cm_minimizer S G (ball(vec 0:real^2,&1)) (\x. (w:real^2->real^K)(R % x + vec 0)) /\
    cm_cmap S (ball(vec 0:real^2,&1)) (\x. (w:real^2->real^K)(R % x + vec 0))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^2`; `R:real`] CMR_AFF_UNIT_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMR_AFF_MINIMIZER THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC CMR_AFF_CMAP THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  (* the reflected data *)
  ABBREV_TAC `g = cmr_dat (matrix bel_refl3) (vec 0:real^2) (inv R) (u:real^3->real^K)` THEN
  SUBGOAL_THEN `&0 < inv R` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `matrix bel_refl3`;
                 `vec 0:real^2`; `inv R`; `u:real^3->real^K`] CMR_DAT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_gdir (ball(vec 0:real^2,inv R)) G
      (\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x)) <= &2 * delta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * cm_sen G (u:real^3->real^K)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CMR_CHART_GDIR_LE_SEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `Lam:real`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(vec 0:real^2,&1)) (g:real^2->real^K) <= delta0` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `wan_w12 (ball(vec 0:real^2,inv R))
        (\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `matrix bel_refl3`;
                     `vec 0:real^2`; `inv R`] CMR_CHART_CMAP) THEN
      ASM_SIMP_TAC[cm_cmap];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(vec 0:real^2,inv R)`;
                   `\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x)`; `inv R`;
                   `vec 0:real^2`] CMR_AFF_DIR) THEN
    ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE] THEN
    REWRITE_TAC[GSYM cmr_dat] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^2,inv R)`; `G:real^K->real^K^K`;
                   `\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x)`; `lam:real`;
                   `Lam2:real`] HMD_GDIR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN
     `lam * wan_dir (ball(vec 0:real^2,inv R))
              (\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x)) <= lam * delta0`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `wan_gdir (ball(vec 0:real^2,inv R)) G
                    (\x. (u:real^3->real^K)(cm_capmap (matrix bel_refl3) x))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * delta` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= lam * delta0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `delta <= lam * delta0 / &4` THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. g x = (u:real^3->real^K)(stereo2_s_inv(inv R % x))` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[cmr_dat; VECTOR_ADD_RID; CMR_QS_FACTS];
    ALL_TAC] THEN
  (* CMW_C0EST for the reflected data and the rescaled minimizer *)
  USE_THEN "c0" (MP_TAC o SPECL
   [`g:real^2->real^K`; `\x. (w:real^2->real^K)(R % x + vec 0)`;
    `(u:real^3->real^K)(basis 3)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta:real` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      USE_THEN "osc" MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[BEL_P_CHART]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * norm(inv R % x:real^2)` THEN
      REWRITE_TAC[CMW_STEREO_S_NEAR_N; NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`; real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN
      SUBGOAL_THEN `(w:real^2->real^K)(R % x) = f(R % x)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `sphere(vec 0:real^2,R)`)) (concl th))) THEN
        REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[CMW_STEREO_CIRCLE]];
    DISCH_TAC] THEN
  (* the replaced map *)
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[cmr_rep1] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cmr_chart (mat 1) (cm_capmap (mat 1) x) = x:real^2` SUBST1_TAC THENL
     [MP_TAC(ISPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
      REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x IN ball(vec 0:real^2,R)` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^2->real^K) x = (\x. w(R % x + vec 0)) (inv R % x)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`R:real`; `x:real^2`] CMW_SCALE_IN_BALL) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `delta:real` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  USE_THEN "osc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMW_NORTH_CAP THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `y:real^3 = basis 3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((y:real^3) IN IMAGE (cm_capmap (mat 1)) (ball(vec 0,R)))` THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `stereo2_n(y:real^3)` THEN
  ASM_REWRITE_TAC[IN_BALL_0] THEN
  MP_TAC(ISPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ID; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[cmr_chart; TRANSP_MAT; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* The contraction toward a point of S.  Affine images of                    *)
(* W^{1,2} maps; the global retraction P of CMW_RETRACTION (named           *)
(* cmr_retr); its jacobian is that of closest_point S near S; the pointwise *)
(* bound for the G-energy density of P((1 - s) w + s q) (CMR_PROJ_QUAD):     *)
(* no tangency of the derivative of w is needed, by the G-orthogonality of  *)
(* tangent and normal spaces in cm_target.                                   *)
(* ========================================================================= *)

(* Affine images of W^{1,2} maps (WAN_CHAIN_W12 with an affine map).        *)

let CMR_AFFINE_DERIV = prove
 (`!(a:real) (b:real^K) y.
     frechet_derivative (\y:real^K. a % y + b) (at y) = (\h. a % h)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN `(\h:real^K. a % h) = (\h. a % h + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID]);;

let CMR_AFFINE_W12 = prove
 (`!(s:real^N->bool) (f:real^N->real^K) a b.
     open s /\ bounded s /\ wan_w12 s f
     ==> wan_w12 s (\x. a % f x + b) /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd s i (\x. a % f x + b) (\x. a % wan_wd s i f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:N)`; `(:K)`; `(:K)`] WAN_CHAIN_W12) THEN
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `f:real^N->real^K`;
                             `\y:real^K. a % y + b`]) THEN
  ASM_REWRITE_TAC[CMR_AFFINE_DERIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN
      SIMP_TAC[OPEN_UNIV; CONTINUOUSLY_DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; CONTINUOUSLY_DIFFERENTIABLE_ID];
      EXISTS_TAC `abs a` THEN
      MP_TAC(ISPECL [`\h:real^K. a % h`; `abs a`] ONORM_LE_EQ) THEN
      SIMP_TAC[LINEAR_SCALING; NORM_MUL; REAL_LE_REFL]];
    REWRITE_TAC[]]);;

(* The global retraction of CMW_RETRACTION, named.                          *)

let cmr_retr = new_definition
 `cmr_retr (S:real^K->bool) d (P:real^K->real^K) <=>
    continuously_differentiable 1 (:real^K) P /\
    (?B. !y. norm(vectorize(jacobian P (at y))) <= B) /\
    (!e. &0 < e
         ==> ?r. &0 < r /\
                 !a b. norm(a - b) < r
                       ==> norm(vectorize(jacobian P (at a)) -
                                vectorize(jacobian P (at b))) < e) /\
    (!z. (?p. p IN S /\ dist(z,p) <= d / &2) ==> P z = closest_point S z)`;;

let CMR_RETR_EXISTS = prove
 (`!S (G:real^K->real^K^K) d. cm_target S G d ==> ?P. cmr_retr S d P`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_retr] THEN
  MATCH_MP_TAC CMW_RETRACTION THEN EXISTS_TAC `G:real^K->real^K^K` THEN
  ASM_REWRITE_TAC[]);;

(* Near S the retraction and closest_point S have the same jacobian.        *)

let CMR_RETR_JAC = prove
 (`!S (P:real^K->real^K) d w z.
     cmr_retr S d P /\ w IN S /\ dist(z,w) < d / &2
     ==> jacobian P (at z) = jacobian (closest_point S) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_retr] THEN STRIP_TAC THEN
  REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`P:real^K->real^K`; `d / &2 - dist(z:real^K,w)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z':real^K` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `w:real^K` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z':real^K`; `z:real^K`; `w:real^K`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MP_TAC(ISPECL [`0:num`; `(:real^K)`; `P:real^K->real^K`]
                  CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    REWRITE_TAC[GSYM ONE] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_UNIV; IN_UNIV]]);;
(* The facts of cm_target used for the contraction.                         *)

let CMR_TARGET_PROJ_FACTS = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> closed S /\ &0 < d /\
         (!z. z IN cm_tube S d ==> closest_point S z IN S) /\
         (!z. z IN S
              ==> transp(jacobian (closest_point S) (at z)) =
                  jacobian (closest_point S) (at z) /\
                  jacobian (closest_point S) (at z) ** jacobian (closest_point S) (at z) =
                  jacobian (closest_point S) (at z)) /\
         (!z u v. z IN S
                  ==> (jacobian (closest_point S) (at z) ** u) dot
                      (G z ** ((mat 1 - jacobian (closest_point S) (at z)) ** v)) = &0) /\
         (!z. transp(G z) = G z) /\
         (?lam. &0 < lam /\ !z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
         (?C0. &0 <= C0 /\
               !z. z IN cm_tube S d
                   ==> onorm(\v. jacobian (closest_point S) (at z) ** v -
                                 jacobian (closest_point S) (at (closest_point S z)) ** v)
                       <= C0 * dist(z,closest_point S z)) /\
         (?Lam1 C3. &0 <= Lam1 /\ &0 <= C3 /\
                    (!z xi. z IN S ==> norm(G z ** xi) <= Lam1 * norm xi) /\
                    (!y z xi. y IN S /\ z IN S
                              ==> norm((G y - G z) ** xi) <= C3 * norm(y - z) * norm xi))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_CONSTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lamh:real` (X_CHOOSE_THEN `Lam1:real` (X_CHOOSE_THEN `CJ:real`
    (X_CHOOSE_THEN `CG:real` (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `C3:real`
    (X_CHOOSE_THEN `C4:real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `lamh:real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`Lam1:real`; `C3:real`] THEN ASM_REWRITE_TAC[]]);;

(* The pointwise bound for the G-energy density after closest_point.        *)

let CMR_PROJ_QUAD = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?C. &0 <= C /\
             !w z a. w IN S /\ norm(z - w) < d / &2
                     ==> (jacobian (closest_point S) (at z) ** a) dot
                         (G(closest_point S z) ** (jacobian (closest_point S) (at z) ** a))
                         <= (&1 + C * norm(z - w)) * (a dot (G w ** a))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMR_TARGET_PROJ_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inS") (CONJUNCTS_THEN2 (LABEL_TAC "proj")
   (CONJUNCTS_THEN2 (LABEL_TAC "orth") (CONJUNCTS_THEN2 (LABEL_TAC "symG")
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ell")))
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0")))
    (X_CHOOSE_THEN `Lam1:real` (X_CHOOSE_THEN `C3:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "L1") (LABEL_TAC "C3")))))))))))))) THEN
  ABBREV_TAC `K0 = &2 * C3 + &2 * Lam1 * C0 + Lam1 * C0 pow 2 * d` THEN
  SUBGOAL_THEN `&0 <= K0` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= &2 * a + &2 * b + c`) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  EXISTS_TAC `K0 / lam` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^K`; `z:real^K`; `a:real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^K) IN cm_tube S d` ASSUME_TAC THENL
   [REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `w:real^K` THEN
    ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = closest_point S (z:real^K)` THEN
  SUBGOAL_THEN `(p:real^K) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN USE_THEN "inS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(z - p:real^K) <= norm(z - w)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC CLOSEST_POINT_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(p - w:real^K) <= &2 * norm(z - w)` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(z - p:real^K) <= norm(z - w)` THEN NORM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Jz = jacobian (closest_point S) (at (z:real^K))` THEN
  ABBREV_TAC `Jp = jacobian (closest_point S) (at (p:real^K))` THEN
  USE_THEN "proj" (MP_TAC o C MATCH_MP (ASSUME `(p:real^K) IN S`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = (Jp:real^K^K) ** (a:real^K)` THEN
  ABBREV_TAC `e = (Jz:real^K^K) ** (a:real^K) - c` THEN
  SUBGOAL_THEN `(Jz:real^K^K) ** (a:real^K) = c + e` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = norm(z - w:real^K)` THEN
  ABBREV_TAC `A = norm(a:real^K)` THEN
  ABBREV_TAC `E = norm(e:real^K)` THEN
  SUBGOAL_THEN `&0 <= D /\ &0 <= A /\ &0 <= E` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "A"; "E"] THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  (* the error of the jacobian *)
  SUBGOAL_THEN `E <= C0 * D * A` ASSUME_TAC THENL
   [USE_THEN "C0" (MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN cm_tube S d`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["E"; "e"; "c"] THEN
    SUBGOAL_THEN `(Jz:real^K^K) ** (a:real^K) - (Jp:real^K^K) ** a = (\v:real^K. Jz ** v - Jp ** v) a`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(\v:real^K. (Jz:real^K^K) ** v - (Jp:real^K^K) ** v) * A` THEN CONJ_TAC THENL
     [EXPAND_TAC "A" THEN
      MP_TAC(ISPEC `\v:real^K. (Jz:real^K^K) ** v - (Jp:real^K^K) ** v` ONORM) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LINEAR];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C0 * D) * A` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * dist(z:real^K,p)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[dist];
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the projection does not increase the G(p)-quadratic form *)
  SUBGOAL_THEN `c dot ((G:real^K->real^K^K) p ** c) <= a dot (G p ** a)` ASSUME_TAC THENL
   [ABBREV_TAC `n = (mat 1 - (Jp:real^K^K)) ** (a:real^K)` THEN
    SUBGOAL_THEN `a:real^K = c + n` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["c"; "n"] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c dot ((G:real^K->real^K^K) p ** n) = &0` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["c"; "n"] THEN
      REWRITE_TAC[SYM(ASSUME `jacobian (closest_point S) (at (p:real^K)) = Jp`)] THEN
      USE_THEN "orth" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `n dot ((G:real^K->real^K^K) p ** c) = &0` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN
      USE_THEN "symG" (fun th -> ONCE_REWRITE_TAC[GSYM(SPEC `p:real^K` th)]) THEN
      REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= n dot ((G:real^K->real^K^K) p ** n)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * norm(n:real^K) pow 2` THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the cross term and the quadratic error term *)
  SUBGOAL_THEN `abs(c dot ((G:real^K->real^K^K) p ** e)) <= Lam1 * C0 * D * A pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(c:real^K) * norm((G:real^K->real^K^K) p ** e)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * (Lam1 * E)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
       [EXPAND_TAC "A" THEN EXPAND_TAC "c" THEN MATCH_MP_TAC HMC_PROJ_NORM THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "E" THEN USE_THEN "L1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `A * Lam1 * E <= A * Lam1 * (C0 * D * A)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(e dot ((G:real^K->real^K^K) p ** e)) <= Lam1 * C0 pow 2 * d * D * A pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(e:real^K) * norm((G:real^K->real^K^K) p ** e)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E * (Lam1 * E)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
       [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_LE_REFL];
        EXPAND_TAC "E" THEN USE_THEN "L1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `E * E <= (C0 * D * A) * (C0 * D * A)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `D * D <= d * D` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Lam1 * (E * E) <= Lam1 * ((C0 * D * A) * (C0 * D * A))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(Lam1 * C0 pow 2 * A pow 2) * (D * D) <= (Lam1 * C0 pow 2 * A pow 2) * (d * D)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* G(p) against G(w) *)
  SUBGOAL_THEN `a dot ((G:real^K->real^K^K) p ** a) <= a dot (G w ** a) + &2 * C3 * D * A pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(a dot ((G:real^K->real^K^K) p ** a) - a dot (G w ** a)) <=
                  A * (C3 * norm(p - w:real^K) * A)` MP_TAC THENL
     [REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(a:real^K) * norm(((G:real^K->real^K^K) p - G w) ** a)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN EXPAND_TAC "A" THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      USE_THEN "C3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `A * (C3 * norm(p - w:real^K) * A) <= A * (C3 * (&2 * D) * A)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the expansion *)
  SUBGOAL_THEN
   `(c + e) dot ((G:real^K->real^K^K) p ** (c + e)) =
    c dot (G p ** c) + &2 * (c dot (G p ** e)) + e dot (G p ** e)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
    SUBGOAL_THEN `e dot ((G:real^K->real^K^K) p ** c) = c dot (G p ** e)` SUBST1_TAC THENL
     [MATCH_MP_TAC HMC_SYM_DOT THEN USE_THEN "symG" (fun th -> REWRITE_TAC[th]);
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the ellipticity *)
  SUBGOAL_THEN `lam * A pow 2 <= a dot ((G:real^K->real^K^K) w ** a)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN USE_THEN "ell" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `K0 * D * A pow 2 <= K0 / lam * D * (a dot ((G:real^K->real^K^K) w ** a))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `K0 * D * A pow 2 = (K0 * inv lam * D) * (lam * A pow 2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `K0 / lam * D * (a dot ((G:real^K->real^K^K) w ** a)) =
                  (K0 * inv lam * D) * (a dot (G w ** a))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `K0 * D * A pow 2 <= K0 / lam * D * (a dot ((G:real^K->real^K^K) w ** a))` THEN
  UNDISCH_TAC `a dot ((G:real^K->real^K^K) p ** a) <= a dot (G w ** a) + &2 * C3 * D * A pow 2` THEN
  UNDISCH_TAC `abs(e dot ((G:real^K->real^K^K) p ** e)) <= Lam1 * C0 pow 2 * d * D * A pow 2` THEN
  UNDISCH_TAC `abs(c dot ((G:real^K->real^K^K) p ** e)) <= Lam1 * C0 * D * A pow 2` THEN
  UNDISCH_TAC `c dot ((G:real^K->real^K^K) p ** c) <= a dot (G p ** a)` THEN
  EXPAND_TAC "K0" THEN REAL_ARITH_TAC);;
(* The numerical factor of the contraction is at most 1.                     *)

let CMR_CTR_FACTOR = prove
 (`!s C x. &0 <= s /\ s <= &1 /\ &0 <= C /\ &0 <= x /\ (s = &0 \/ C * x <= &1)
           ==> (&1 - s) pow 2 * (&1 + C * (s * x)) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - s) pow 2 * (&1 + s)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `C * (s * x) = s * (C * x)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= s ==> &1 + y <= &1 + s`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(&1 - s) pow 2 * (&1 + s) = &1 - s * (&1 + s - s pow 2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &1 - y <= &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s pow 2 <= s` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

(* The energy does not increase under w |-> P((1 - s) w + s q) when w stays *)
(* eta-close to q (or s = 0).                                               *)

let CMR_PROJ_SEN_LE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eta. &0 < eta /\ eta <= d / &4 /\
           !P Lam (w:real^3->real^K) q s.
              cmr_retr S d P /\ CMR_GCOND G Lam /\ cm_smap S w /\ q IN S /\
              &0 <= s /\ s <= &1 /\
              (&0 < s ==> !y. y IN sphere(vec 0,&1) ==> norm(w y - q) <= eta)
              ==> cm_smap S (\y. P((&1 - s) % w y + s % q)) /\
                  cm_sen G (\y. P((&1 - s) % w y + s % q)) <= cm_sen G w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMR_PROJ_QUAD) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "quad"))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `min (d / &4) (inv(C + &1))` THEN
  SUBGOAL_THEN `&0 < inv(C + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (d / &4) (inv(C + &1))` THEN
  SUBGOAL_THEN `eta <= d / &4 /\ eta <= inv(C + &1) /\ &0 < eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * eta <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * inv(C + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM real_div] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`;
               ASSUME `&0 <= C`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`P:real^K->real^K`; `Lam:real`; `w:real^3->real^K`; `q:real^K`;
                       `s:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmr_retr]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_smap]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CMR_GCOND]) THEN
  SUBGOAL_THEN `open wan_shell /\ bounded wan_shell` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]; ALL_TAC] THEN
  ABBREV_TAC `R = wan_rext (w:real^3->real^K)` THEN
  SUBGOAL_THEN `wan_w12 wan_shell (R:real^3->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_MESON_TAC[wan_s2_w12]; ALL_TAC] THEN
  (* the values of R on the shell *)
  SUBGOAL_THEN
   `!x:real^3. x IN wan_shell
               ==> (R:real^3->real^K) x IN S /\
                   (s = &0 \/ norm(q - R x) <= eta)`
  (LABEL_TAC "Rx") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(norm x) % (x:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0] THEN
      ASM_SIMP_TAC[CMT_SHELL_NONZERO];
      ALL_TAC] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[wan_rext] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the affine image and the chain rule *)
  ABBREV_TAC `U = \x:real^3. (&1 - s) % (R:real^3->real^K) x + s % q` THEN
  MP_TAC(ISPECL [`wan_shell`; `R:real^3->real^K`; `&1 - s`; `s % (q:real^K)`]
                CMR_AFFINE_W12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Uwpd")) THEN
  SUBGOAL_THEN `?B. !y. onorm(frechet_derivative (P:real^K->real^K) (at y)) <= B`
  ASSUME_TAC THENL
   [EXISTS_TAC `B:real` THEN X_GEN_TAC `y:real^K` THEN
    SUBGOAL_THEN `frechet_derivative (P:real^K->real^K) (at y) = (\v. jacobian P (at y) ** v)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; CMW_FD_JAC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (P:real^K->real^K) (at y)))` THEN
    ASM_REWRITE_TAC[ONORM_LE_NORM_VECTORIZE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:3)`; `(:K)`; `(:K)`] WAN_CHAIN_W12) THEN
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `U:real^3->real^K`; `P:real^K->real^K`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Vwpd")) THEN
  SUBGOAL_THEN
   `wan_rext (\y. (P:real^K->real^K)((&1 - s) % (w:real^3->real^K) y + s % q)) =
    (\x. P(U x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN EXPAND_TAC "R" THEN REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
  (* the points of the shell *)
  SUBGOAL_THEN
   `!x:real^3. x IN wan_shell
               ==> norm((U:real^3->real^K) x - R x) = s * norm(q - R x) /\
                   norm(U x - R x) < d / &2 /\
                   (P:real^K->real^K)(U x) = closest_point S (U x) /\
                   jacobian P (at (U x)) = jacobian (closest_point S) (at (U x))`
  (LABEL_TAC "Ux") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "Rx" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN wan_shell`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `norm((U:real^3->real^K) x - R x) = s * norm(q - R x)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN
      REWRITE_TAC[VECTOR_ARITH `((&1 - s) % r + s % q) - r:real^N = s % (q - r)`] THEN
      REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((U:real^3->real^K) x - R x) < d / &2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * eta` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `closest_point S:real^K->real^K`)) (concl th) &&
        can (find_term ((=) `d / &2`)) (concl th))) THEN
      EXISTS_TAC `(R:real^3->real^K) x` THEN ASM_REWRITE_TAC[dist] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CMR_RETR_JAC THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `(R:real^3->real^K) x`] THEN
      ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* cm_smap of the new map *)
  SUBGOAL_THEN `cm_smap S (\y. (P:real^K->real^K)((&1 - s) % (w:real^3->real^K) y + s % q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[cm_smap; wan_s2_w12] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\y. (P:real^K->real^K)((&1 - s) % (w:real^3->real^K) y + s % q)) =
        P o (\y. (&1 - s) % w y + s % q)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        EXISTS_TAC `1:num` THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN wan_shell /\ wan_rext (w:real^3->real^K) y = w y`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
        SIMP_TAC[wan_shell; IN_ELIM_THM; IN_SPHERE_0; wan_rext; REAL_INV_1;
                 VECTOR_MUL_LID] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(U:real^3->real^K) y = (&1 - s) % w y + s % q` ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN EXPAND_TAC "R" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "Ux" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN wan_shell`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[SYM(ASSUME `(U:real^3->real^K) y = (&1 - s) % w y + s % q`)] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the energy *)
  REWRITE_TAC[cm_sen] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &3 <= b / &3`) THEN
  REWRITE_TAC[wan_gdir; DIMINDEX_3] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`;
                 `\x:real^3. (P:real^K->real^K)((U:real^3->real^K) x)`;
                 `&0`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3]; DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`; `R:real^3->real^K`;
                 `&0`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3]; DISCH_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
  EXISTS_TAC
   `{x | x IN wan_shell /\
         ~(wan_wd wan_shell i (\x. (P:real^K->real^K)(U x)) x =
           frechet_derivative P (at (U x)) (wan_wd wan_shell i (U:real^3->real^K) x))} UNION
    {x | x IN wan_shell /\
         ~(wan_wd wan_shell i (U:real^3->real^K) x =
           (&1 - s) % wan_wd wan_shell i (R:real^3->real^K) x)}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THENL
     [USE_THEN "Vwpd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIMINDEX_3];
      USE_THEN "Uwpd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIMINDEX_3]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B")) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  USE_THEN "Rx" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN wan_shell`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "disj")) THEN
  USE_THEN "Ux" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN wan_shell`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "U1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "U3") (LABEL_TAC "U4")))) THEN
  USE_THEN "A" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "B" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `P:real^K->real^K` CMW_FD_JAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "U3" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "U4" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `a = wan_wd wan_shell i (R:real^3->real^K) x` THEN
  USE_THEN "quad" (MP_TAC o SPECL [`(R:real^3->real^K) x`; `(U:real^3->real^K) x`;
                                   `a:real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "U1" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real`; `C:real`; `norm(q - (R:real^3->real^K) x)`] CMR_CTR_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "disj" (DISJ_CASES_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * eta` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= a dot ((G:real^K->real^K^K)((R:real^3->real^K) x) ** a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `X = (jacobian (closest_point S) (at ((U:real^3->real^K) x)) ** a) dot
                  ((G:real^K->real^K^K)(closest_point S (U x)) **
                   (jacobian (closest_point S) (at (U x)) ** a))` THEN
  ABBREV_TAC `Ga = a dot ((G:real^K->real^K^K)((R:real^3->real^K) x) ** a)` THEN
  ABBREV_TAC `F0 = (&1 - s) pow 2 * (&1 + C * (s * norm(q - (R:real^3->real^K) x)))` THEN
  SUBGOAL_THEN
   `(&1 - s) pow 2 * X <=
    (&1 - s) pow 2 * ((&1 + C * (s * norm(q - (R:real^3->real^K) x))) * Ga)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `F0 * Ga <= &1 * Ga` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "F0" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The contraction family cmr_ctr P sf sigma a y t =                         *)
(*   P((1 - a sf(t)) sigma(y,t) + a sf(t) sigma(basis 3,t)),                *)
(* a in [0,1] the homotopy parameter: values in S, continuity, ends, a = 0, *)
(* the homotopy to a = 1, the slices (cm_smap, energy), and the W^{1,2}     *)
(* continuity in t (CMW_CHAIN_DIR_EST).                                     *)
(* ========================================================================= *)

let CMR_RETR_FACTS = prove
 (`!S (G:real^K->real^K^K) d (P:real^K->real^K).
     cm_target S G d /\ cmr_retr S d P
     ==> (!z. P continuous (at z)) /\
         (!w. w IN S ==> P w = w) /\
         (!w z. w IN S /\ norm(z - w) <= d / &2
                ==> P z = closest_point S z /\ P z IN S /\
                    norm(P z - w) <= &2 * norm(z - w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmr_retr]) THEN
  SUBGOAL_THEN `!w z. w IN S /\ norm(z - w) <= d / &2 ==> (P:real^K->real^K) z = closest_point S z`
  (LABEL_TAC "Pcp") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w:real^K` THEN
    ASM_REWRITE_TAC[dist];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MP_TAC(ISPECL [`0:num`; `(:real^K)`; `P:real^K->real^K`]
                  CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    REWRITE_TAC[GSYM ONE] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_UNIV; IN_UNIV];
    X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `closest_point S (w:real^K)` THEN CONJ_TAC THENL
     [USE_THEN "Pcp" MATCH_MP_TAC THEN EXISTS_TAC `w:real^K` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`w:real^K`; `z:real^K`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(P:real^K->real^K) z = closest_point S z` ASSUME_TAC THENL
     [USE_THEN "Pcp" MATCH_MP_TAC THEN EXISTS_TAC `w:real^K` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `dist(z:real^K,closest_point S z) <= dist(z,w)` MP_TAC THENL
     [MATCH_MP_TAC CLOSEST_POINT_LE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH]);;

let cmr_ctr = new_definition
 `cmr_ctr (P:real^K->real^K) (sf:real->real) (sigma:real^3->real->real^K) a (y:real^3) t =
    P((&1 - a * sf t) % sigma y t + (a * sf t) % sigma (basis 3) t)`;;

(* Values in S and closeness to the slice.                                  *)

let CMR_CTR_CLOSE = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K) eta a y t.
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\ eta <= d / &4 /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= sf t /\ sf t <= &1) /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\ &0 < sf t
            ==> norm(sigma y t - sigma (basis 3) t) <= eta) /\
     a IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
     ==> cmr_ctr P sf sigma a y t IN S /\
         norm(cmr_ctr P sf sigma a y t - sigma y t) <= &2 * (a * sf t) * eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sf") (CONJUNCTS_THEN2 (LABEL_TAC "cl")
    STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`]
                CMR_RETR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inS") ASSUME_TAC)) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  USE_THEN "sf" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a /\ a <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  ABBREV_TAC `w = (sigma:real^3->real->real^K) y t` THEN
  ABBREV_TAC `q = (sigma:real^3->real->real^K) (basis 3) t` THEN
  SUBGOAL_THEN `(w:real^K) IN S /\ (q:real^K) IN S` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w"; "q"] THEN CONJ_TAC THEN USE_THEN "inS" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * (sf:real->real) t /\ a * (sf:real->real) t <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(((&1 - a * (sf:real->real) t) % w + (a * (sf:real->real) t) % q) - w:real^K) <= (a * (sf:real->real) t) * eta`
  ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `((&1 - c) % w + c % q) - w:real^N = c % (q - w)`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
    ASM_CASES_TAC `&0 < (sf:real->real) t` THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN MAP_EVERY EXPAND_TAC ["w"; "q"] THEN
      USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sf(t:real) = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * (sf:real->real) t) * eta <= d / &2` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < (sf:real->real) t` THENL
     [SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((sigma:real^3->real->real^K) y t - sigma (basis 3) t)` THEN
        REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * eta` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `sf(t:real) = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_BASICS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPECL [`w:real^K`; `(&1 - a * (sf:real->real) t) % w + (a * (sf:real->real) t) % q:real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cmr_ctr] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(((&1 - a * (sf:real->real) t) % w + (a * (sf:real->real) t) % q) - w:real^K)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `norm(((&1 - a * (sf:real->real) t) % w + (a * (sf:real->real) t) % q) - w:real^K) <= (a * (sf:real->real) t) * eta` THEN
  REAL_ARITH_TAC);;

(* a = 0 gives the sweepout itself; the ends stay constant.                 *)

let CMR_CTR_ZERO = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K) y t.
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\
     y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
     ==> cmr_ctr P sf sigma (&0) y t = sigma y t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cmr_ctr; REAL_MUL_LZERO; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`]
                CMR_RETR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  ASM_SIMP_TAC[]);;

let CMR_CTR_ENDS = prove
 (`!S P sf (sigma:real^3->real->real^K) a y y'.
     cm_sweep S sigma /\ y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
     ==> cmr_ctr P sf sigma a y (&0) = cmr_ctr P sf sigma a y' (&0) /\
         cmr_ctr P sf sigma a y (&1) = cmr_ctr P sf sigma a y' (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  DISCH_THEN(ASSUME_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[cmr_ctr] THEN ASM_SIMP_TAC[]);;

(* sf = 1 gives the constant map at the north pole value.                   *)

let CMR_CTR_ONE = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K) y t.
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\
     t IN real_interval[&0,&1] /\ sf t = &1
     ==> cmr_ctr P sf sigma (&1) y t = sigma (basis 3) t`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[cmr_ctr; REAL_MUL_LID; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
                  VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`]
                CMR_RETR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]);;

(* Joint continuity of the contraction family.                              *)

let CMR_CTR_CONT = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K).
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\
     sf real_continuous_on real_interval[&0,&1]
     ==> continuous_map
           (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1]))),
            euclidean)
           (\(a,(y,t)). cmr_ctr P sf sigma a y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_PROD3_SEQ_CONT THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `y:real^3`; `t:real`; `an:num->real`; `yn:num->real^3`;
                       `tn:num->real`] THEN
  STRIP_TAC THEN REWRITE_TAC[cmr_ctr] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`]
                CMR_RETR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. (sigma:real^3->real->real^K) (yn n) (tn n)) --> sigma y t) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_SWEEP_SEQ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. (sigma:real^3->real->real^K) (basis 3) (tn n)) --> sigma (basis 3) t) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sigma:real^3->real->real^K`; `basis 3:real^3`; `t:real`;
                   `\n:num. basis 3:real^3`; `tn:num->real`] CMW_SWEEP_SEQ) THEN
    REWRITE_TAC[LIM_CONST] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. (sf:real->real)(tn n)) ---> sf t) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_REAL_CONT_SEQ THEN EXISTS_TAC `real_interval[&0,&1]` THEN
    ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. (an:num->real) n * (sf:real->real)(tn n)) ---> a * sf t) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM TENDSTO_REAL] THEN
  TRY(MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST]) THEN
  ASM_REWRITE_TAC[]);;

(* The homotopy from sigma to the contracted family.                        *)

let CMR_CTR_HOMOTOPIC = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K) eta.
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\ eta <= d / &4 /\
     sf real_continuous_on real_interval[&0,&1] /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= sf t /\ sf t <= &1) /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\ &0 < sf t
            ==> norm(sigma y t - sigma (basis 3) t) <= eta)
     ==> cm_shomotopic S sigma (cmr_ctr P sf sigma (&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_shomotopic] THEN
  EXISTS_TAC `\a:real. cmr_ctr (P:real^K->real^K) sf (sigma:real^3->real->real^K) a` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMR_CTR_CONT THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real`; `y:real^3`; `t:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`;
                   `sf:real->real`; `sigma:real^3->real->real^K`; `eta:real`; `a:real`;
                   `y:real^3`; `t:real`] CMR_CTR_CLOSE) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_CTR_ENDS THEN
    EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_CTR_ZERO THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* The slices of the contracted family (a = 1): maps of S^2 into S whose    *)
(* energy is at most that of the slice of sigma.                            *)

let CMR_CTR_SLICES = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eta. &0 < eta /\ eta <= d / &4 /\
           !P Lam sf (sigma:real^3->real->real^K) t.
              cmr_retr S d P /\ CMR_GCOND G Lam /\ cm_sweep S sigma /\
              t IN real_interval[&0,&1] /\ &0 <= sf t /\ sf t <= &1 /\
              (&0 < sf t
               ==> !y. y IN sphere(vec 0,&1)
                       ==> norm(sigma y t - sigma (basis 3) t) <= eta)
              ==> cm_smap S (\y. cmr_ctr P sf sigma (&1) y t) /\
                  cm_sen G (\y. cmr_ctr P sf sigma (&1) y t) <= cm_sen G (\y. sigma y t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMR_PROJ_SEN_LE) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`P:real^K->real^K`; `Lam:real`; `sf:real->real`;
                       `sigma:real^3->real->real^K`; `t:real`] THEN
  STRIP_TAC THEN REWRITE_TAC[cmr_ctr; REAL_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`P:real^K->real^K`; `Lam:real`; `\y:real^3. (sigma:real^3->real->real^K) y t`;
    `(sigma:real^3->real->real^K) (basis 3) t`; `(sf:real->real) t`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `cm_sweep S (sigma:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]]);;
(* Dirichlet energy of an affine image (any open bounded domain).           *)

let CMR_DIR_AFFINE = prove
 (`!(s:real^N->bool) (f:real^N->real^K) a b.
     open s /\ bounded s /\ wan_w12 s f
     ==> wan_w12 s (\x. a % f x + b) /\
         wan_dir s (\x. a % f x + b) = a pow 2 * wan_dir s f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^K`; `a:real`; `b:real^K`]
                CMR_AFFINE_W12) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^K`; `a:real`] WAN_DIR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. a % (f:real^N->real^K) x + b`;
                 `\i x. a % wan_wd s i (f:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. a % (f:real^N->real^K) x`;
                 `\i x. a % wan_wd s i (f:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* The change of the affine combination between two times.                  *)

let CMR_CTR_UDIR = prove
 (`!(R:real->real^3->real^K) (q:real->real^K) (sf:real->real) s t.
     wan_w12 wan_shell (R s) /\ wan_w12 wan_shell (R t)
     ==> wan_dir wan_shell (\z. ((&1 - sf s) % R s z + sf s % q s) -
                                ((&1 - sf t) % R t z + sf t % q t))
         <= &2 * (&1 - sf s) pow 2 * wan_dir wan_shell (\z. R s z - R t z) +
            &2 * (sf t - sf s) pow 2 * wan_dir wan_shell (R t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open wan_shell /\ bounded wan_shell` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. ((&1 - sf s) % (R:real->real^3->real^K) s z + sf s % q s) -
         ((&1 - sf t) % R t z + sf t % q t)) =
    (\z. (\z. (&1 - sf s) % (R s z - R t z)) z +
         (\z. (sf t - sf s) % R t z + (sf s % q s - sf t % q t)) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 wan_shell (\z. (R:real->real^3->real^K) s z - R t z)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_shell`; `\z. (R:real->real^3->real^K) s z - R t z`; `&1 - (sf:real->real) s`]
                WAN_DIR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_shell`; `(R:real->real^3->real^K) t`; `(sf:real->real) t - sf s`;
                 `sf s % (q:real->real^K) s - sf t % q t`] CMR_DIR_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * wan_dir wan_shell (\z. (&1 - sf s) % ((R:real->real^3->real^K) s z - R t z)) +
              &2 * wan_dir wan_shell (\z. (sf t - sf s) % R t z + (sf s % q s - sf t % q t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_DIR_ADD_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Uniform closeness of the affine combinations for nearby times.          *)

let CMR_CTR_UCLOSE = prove
 (`!S (sigma:real^3->real->real^K) sf t.
     cm_sweep S sigma /\ compact S /\ sf real_continuous_on real_interval[&0,&1] /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= sf t /\ sf t <= &1) /\
     t IN real_interval[&0,&1]
     ==> !r. &0 < r
             ==> ?dl. &0 < dl /\
                      !s z. s IN real_interval[&0,&1] /\ abs(s - t) < dl /\ z IN wan_shell
                            ==> norm(((&1 - sf s) % wan_rext (\y. sigma y s) z +
                                      sf s % sigma (basis 3) s) -
                                     ((&1 - sf t) % wan_rext (\y. sigma y t) z +
                                      sf t % sigma (basis 3) t)) < r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sfb") ASSUME_TAC)))) THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (sigma:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (CONJUNCTS_THEN2 (LABEL_TAC "inS") (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M"))) THEN
  USE_THEN "cont" (MP_TAC o MATCH_MP CMW_SWEEP_JOINT_UNIF) THEN
  DISCH_THEN(MP_TAC o SPEC `r / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ju"))) THEN
  UNDISCH_TAC `(sf:real->real) real_continuous_on real_interval[&0,&1]` THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r / (&4 * (M + &1))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sfc"))) THEN
  EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm z) % (z:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0] THEN
    ASM_SIMP_TAC[CMT_SHELL_NONZERO];
    ALL_TAC] THEN
  REWRITE_TAC[wan_rext] THEN
  ABBREV_TAC `y = inv(norm z) % (z:real^3)` THEN
  USE_THEN "sfc" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "ju" (MP_TAC o SPECL [`y:real^3`; `y:real^3`; `s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]; DISCH_TAC] THEN
  USE_THEN "ju" (MP_TAC o SPECL [`basis 3:real^3`; `basis 3:real^3`; `s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]; DISCH_TAC] THEN
  SUBGOAL_THEN `norm((sigma:real^3->real->real^K) y t) <= M /\ norm(sigma (basis 3) t) <= M`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "M" MATCH_MP_TAC THEN USE_THEN "inS" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "sfb" (MP_TAC o C MATCH_MP (ASSUME `s IN real_interval[&0,&1]`)) THEN
  STRIP_TAC THEN
  ABBREV_TAC `A = (sigma:real^3->real->real^K) y s - sigma y t` THEN
  ABBREV_TAC `C = (sigma:real^3->real->real^K) (basis 3) s - sigma (basis 3) t` THEN
  SUBGOAL_THEN
   `((&1 - sf s) % (sigma:real^3->real->real^K) y s + sf s % sigma (basis 3) s) -
    ((&1 - sf t) % sigma y t + sf t % sigma (basis 3) t) =
    (&1 - sf s) % A + sf s % C + (sf s - sf t) % (sigma (basis 3) t - sigma y t)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm((&1 - sf s) % (A:real^K)) + norm(sf s % (C:real^K)) +
              norm((sf s - sf t) % ((sigma:real^3->real->real^K) (basis 3) t - sigma y t))` THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC(NORM_ARITH
     `!a b c:real^N. norm(a + b + c) <= norm a + norm b + norm c`);
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `abs(&1 - sf s) <= &1 /\ abs((sf:real->real) s) <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(&1 - sf s) * norm(A:real^K) < r / &4 /\ abs((sf:real->real) s) * norm(C:real^K) < r / &4`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THENL
     [EXISTS_TAC `&1 * norm(A:real^K)`; EXISTS_TAC `&1 * norm(C:real^K)`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
       REWRITE_TAC[REAL_MUL_LID] THEN MAP_EVERY EXPAND_TAC ["A"; "C"] THEN
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((sf:real->real) s - sf t) * (M + &1) < r / &4` ASSUME_TAC THENL
   [UNDISCH_TAC `abs((sf:real->real) s - sf t) < r / (&4 * (M + &1))` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < M ==> &0 < &4 * (M + &1)`;
             ASSUME `&0 < M`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((sf:real->real) s - sf t) *
    norm((sigma:real^3->real->real^K) (basis 3) t - sigma y t) <=
    abs(sf s - sf t) * (&2 * (M + &1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^N) <= M /\ norm(b:real^N) <= M ==> norm(a - b) <= &2 * (M + &1)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
(* Two pieces of epsilon arithmetic.                                         *)

let CMR_EPS_ARITH1 = prove
 (`!B2 x ep. &0 <= B2 /\ &0 <= x /\ &0 < ep /\ x < ep / (&16 * (B2 + &1))
             ==> &4 * B2 * x <= ep / &4`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `x < ep / (&16 * (B2 + &1))` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= B2 ==> &0 < &16 * (B2 + &1)`] THEN
  SUBGOAL_THEN `&0 <= B2 * x` MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_EPS_ARITH2 = prove
 (`!B2 Dt y ep. &0 <= B2 /\ &0 <= Dt /\ &0 <= y /\ &0 < ep /\
                y <= ep / (&32 * (B2 + &1) * (Dt + &1))
                ==> &4 * B2 * y * Dt <= ep / &8`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `y <= ep / (&32 * (B2 + &1) * (Dt + &1))` THEN
  SUBGOAL_THEN `&0 < &32 * (B2 + &1) * (Dt + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= B2 * y /\ &0 <= y * Dt /\ &0 <= B2 * y * Dt` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The W^{1,2} continuity in t of the slices of the contracted family.      *)

let CMR_CTR_DIRCONT = prove
 (`!S (G:real^K->real^K^K) d P sf (sigma:real^3->real->real^K) t.
     cm_target S G d /\ cmr_retr S d P /\ cm_sweep S sigma /\
     sf real_continuous_on real_interval[&0,&1] /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= sf t /\ sf t <= &1) /\
     t IN real_interval[&0,&1]
     ==> ((\s. wan_dir wan_shell (\z. wan_rext (\y. cmr_ctr P sf sigma (&1) y s) z -
                                      wan_rext (\y. cmr_ctr P sf sigma (&1) y t) z))
          ---> &0) (atreal t within real_interval[&0,&1])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sfb") ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmr_retr]) THEN
  SUBGOAL_THEN `open wan_shell /\ bounded wan_shell` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(S:real^K->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (P:real^K->real^K) (at (vec 0))))` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `R = \s. wan_rext (\y. (sigma:real^3->real->real^K) y s)` THEN
  ABBREV_TAC `q = \s. (sigma:real^3->real->real^K) (basis 3) s` THEN
  ABBREV_TAC `U = \s z. (&1 - sf s) % (R:real->real^3->real^K) s z + sf s % (q:real->real^K) s` THEN
  SUBGOAL_THEN
   `!s. wan_rext (\y. cmr_ctr P sf sigma (&1) y s) =
        (\z. (P:real^K->real^K)((U:real->real^3->real^K) s z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["U"; "R"; "q"] THEN
    REWRITE_TAC[FUN_EQ_THM; wan_rext; cmr_ctr; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> wan_w12 wan_shell ((R:real->real^3->real^K) s)`
  (LABEL_TAC "Rw") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[GSYM wan_s2_w12] THEN
    UNDISCH_TAC `cm_sweep S (sigma:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_SIMP_TAC[cm_smap];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> wan_w12 wan_shell ((U:real->real^3->real^K) s)`
  (LABEL_TAC "Uw") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`wan_shell`; `(R:real->real^3->real^K) s`; `&1 - (sf:real->real) s`;
                   `(sf:real->real) s % (q:real->real^K) s`] CMR_AFFINE_W12) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[&0,&1]
        ==> wan_dir wan_shell (\z. (U:real->real^3->real^K) s z - U t z) <=
            &2 * wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z) +
            &2 * ((sf:real->real) t - sf s) pow 2 * wan_dir wan_shell (R t)`
  (LABEL_TAC "Ud") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&1 - sf s) pow 2 *
                wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z) +
                &2 * ((sf:real->real) t - sf s) pow 2 * wan_dir wan_shell (R t)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CMR_CTR_UDIR THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - (sf:real->real) s) pow 2 <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN
      USE_THEN "sfb" (MP_TAC o C MATCH_MP (ASSUME `s IN real_interval[&0,&1]`)) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 - (sf:real->real) s) pow 2 *
      wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z) <=
      &1 * wan_dir wan_shell (\z. R s z - R t z)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z)) ---> &0)
    (atreal t within real_interval[&0,&1])`
  MP_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `cm_sweep S (sigma:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  ABBREV_TAC `D = wan_dir wan_shell ((U:real->real^3->real^K) t)` THEN
  ABBREV_TAC `Dt = wan_dir wan_shell ((R:real->real^3->real^K) t)` THEN
  SUBGOAL_THEN `&0 <= D /\ &0 <= Dt` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "Dt"] THEN CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = min (&1) (ep / (&4 * (D + &1)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 /\ &2 * e pow 2 * D <= ep / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ep / (&4 * (D + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e /\ e <= &1 /\ e <= ep / (&4 * (D + &1))` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `e <= ep / (&4 * (D + &1))` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= D ==> &0 < &4 * (D + &1)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `e pow 2 * D <= e * D /\ &0 <= e * D` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the uniform continuity of the jacobian *)
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `vectorize:real^K^K->real^(K,K)finite_prod`)) (concl th) &&
    is_imp(snd(dest_forall(concl th))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Jc"))) THEN
  (* uniform closeness of U s and U t *)
  MP_TAC(ISPECL [`S:real^K->bool`; `sigma:real^3->real->real^K`; `sf:real->real`; `t:real`]
                CMR_CTR_UCLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rJ:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  (* dir(R s - R t) small *)
  FIRST_X_ASSUM(MP_TAC o SPEC `ep / (&16 * (B pow 2 + &1))` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `R:real->real^3->real^K`)) (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd"))) THEN
  (* sf close to sf t *)
  ABBREV_TAC `e2 = min (&1) (ep / (&32 * (B pow 2 + &1) * (Dt + &1)))` THEN
  SUBGOAL_THEN `&0 < e2 /\ e2 <= &1 /\ e2 <= ep / (&32 * (B pow 2 + &1) * (Dt + &1))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ep / (&32 * (B pow 2 + &1) * (Dt + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "e2" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(sf:real->real) real_continuous_on real_interval[&0,&1]` THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e2:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))) THEN
  EXISTS_TAC `min dl1 (min dl2 dl3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  (* the chain estimate *)
  MP_TAC(ISPECL [`wan_shell`; `(U:real->real^3->real^K) s`; `(U:real->real^3->real^K) t`;
                 `P:real^K->real^K`; `B:real`; `e:real`] CMW_CHAIN_DIR_EST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "Jc" MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["U"; "R"; "q"] THEN REWRITE_TAC[] THEN
    USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `&0 <= wan_dir wan_shell
           (\z. (P:real^K->real^K)((U:real->real^3->real^K) s z) - P(U t z))`
  ASSUME_TAC THENL [MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "Ud" (MP_TAC o C MATCH_MP (ASSUME `s IN real_interval[&0,&1]`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "rd" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  USE_THEN "sc" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  (* the arithmetic *)
  ABBREV_TAC `dR = wan_dir wan_shell (\z. (R:real->real^3->real^K) s z - R t z)` THEN
  ABBREV_TAC `dU = wan_dir wan_shell (\z. (U:real->real^3->real^K) s z - U t z)` THEN
  ABBREV_TAC `dP = wan_dir wan_shell
                    (\z. (P:real^K->real^K)((U:real->real^3->real^K) s z) - P(U t z))` THEN
  ABBREV_TAC `dl = ((sf:real->real) t - sf s) pow 2` THEN
  SUBGOAL_THEN `&0 <= dR /\ &0 <= dl /\ dl <= e2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "dR" THEN MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      ASM_SIMP_TAC[ETA_AX];
      EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_LE_POW_2];
      EXPAND_TAC "dl" THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((sf:real->real) t - sf s)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        UNDISCH_TAC `abs((sf:real->real) s - sf t) < e2` THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `abs((sf:real->real) s - sf t) < e2` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B pow 2`; `dR:real`; `ep:real`] CMR_EPS_ARITH1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`B pow 2`; `Dt:real`; `dl:real`; `ep:real`] CMR_EPS_ARITH2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&2 * B pow 2 * dU <= &2 * B pow 2 * (&2 * dR + &2 * dl * Dt)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `dP <= &2 * B pow 2 * dU + &2 * e pow 2 * D` THEN
  UNDISCH_TAC `&0 <= dP` THEN
  UNDISCH_TAC `&2 * e pow 2 * D <= ep / &2` THEN
  UNDISCH_TAC `&4 * B pow 2 * dR <= ep / &4` THEN
  UNDISCH_TAC `&4 * B pow 2 * dl * Dt <= ep / &8` THEN
  UNDISCH_TAC `&0 < ep` THEN
  REAL_ARITH_TAC);;

(* The contracted family is a sweepout, homotopic to sigma, with slice      *)
(* energies at most those of sigma.                                          *)

let CMR_CTR_SWEEP = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eta. &0 < eta /\ eta <= d / &4 /\
           !P Lam sf (sigma:real^3->real->real^K).
              cmr_retr S d P /\ CMR_GCOND G Lam /\ cm_sweep S sigma /\
              sf real_continuous_on real_interval[&0,&1] /\
              (!t. t IN real_interval[&0,&1] ==> &0 <= sf t /\ sf t <= &1) /\
              (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\ &0 < sf t
                     ==> norm(sigma y t - sigma (basis 3) t) <= eta)
              ==> cm_sweep S (cmr_ctr P sf sigma (&1)) /\
                  cm_shomotopic S sigma (cmr_ctr P sf sigma (&1)) /\
                  (!t. t IN real_interval[&0,&1]
                       ==> cm_sen G (\y. cmr_ctr P sf sigma (&1) y t) <=
                           cm_sen G (\y. sigma y t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMR_CTR_SLICES) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")))) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`P:real^K->real^K`; `Lam:real`; `sf:real->real`;
                       `sigma:real^3->real->real^K`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sfb") (LABEL_TAC "cl")))))) THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> cm_smap S (\y. cmr_ctr P sf (sigma:real^3->real->real^K) (&1) y t) /\
            cm_sen G (\y. cmr_ctr P sf sigma (&1) y t) <= cm_sen G (\y. sigma y t)`
  (LABEL_TAC "slt") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "sl" MATCH_MP_TAC THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sfb" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cm_sweep] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `cmr_ctr (P:real^K->real^K) sf (sigma:real^3->real->real^K)`
                   CMW_END_CONT) THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC CMR_CTR_CONT THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "slt" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
      SIMP_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMR_CTR_DIRCONT THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_CTR_ENDS THEN
      EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CMR_CTR_HOMOTOPIC THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `eta:real`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "slt" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The pre-step Contr.  lambda(t) = 1 at energy                              *)
(* <= E1, 0 at energy >= E2; stage 1 replaces on the big cap of radius      *)
(* min 1 (2 lambda) R0 (cmr_fam with one cap); stage 2 contracts with       *)
(* sf = max 0 (2 lambda - 1) toward the north pole value (cmr_ctr).          *)
(* ========================================================================= *)

(* The energy of the slices of a sweepout is continuous in t.               *)

let CMR_SEN_SWEEP_CONT = prove
 (`!S (G:real^K->real^K^K) d e Lam C (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmr_repest S G e C /\ &0 <= C /\
     CMR_GCOND G Lam /\ cm_sweep S sigma
     ==> (\t. cm_sen G (\y. sigma y t)) real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_on] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `C:real`; `sigma:real^3->real->real^K`; `t:real`; `ep / &2`]
                CMR_SWEEP_SEN_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The weight lambda and its properties.                                    *)

let CMR_LAMBDA_FACTS = prove
 (`!(f:real->real) E1 E2 t.
     E1 < E2
     ==> &0 <= min (&1) (max (&0) ((E2 - f t) / (E2 - E1))) /\
         min (&1) (max (&0) ((E2 - f t) / (E2 - E1))) <= &1 /\
         (f t <= E1 ==> min (&1) (max (&0) ((E2 - f t) / (E2 - E1))) = &1) /\
         (E2 <= f t ==> min (&1) (max (&0) ((E2 - f t) / (E2 - E1))) = &0) /\
         (&0 < min (&1) (max (&0) ((E2 - f t) / (E2 - E1))) ==> f t < E2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < E2 - E1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= (E2 - f(t:real)) / (E2 - E1)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `(E2 - f(t:real)) / (E2 - E1) <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (E2 - f(t:real)) / (E2 - E1)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC]]);;

let CMR_LAMBDA_CONT = prove
 (`!(f:real->real) E1 E2. f real_continuous_on real_interval[&0,&1]
             ==> (\t. min (&1) (max (&0) ((E2 - f t) / (E2 - E1))))
                 real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* The one-cap family of stage 1: the replacement on the big cap of radius  *)
(* min 1 (2 lambda(t)) R0.                                                  *)

let CMR_LOW_STAGE1 = prove
 (`!S (G:real^K->real^K^K) d e Lam lam R0 (gamma0:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     CMR_GCOND G Lam /\ cm_sweep S gamma0 /\ &1 <= R0 /\
     lam real_continuous_on real_interval[&0,&1] /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= lam t /\ lam t <= &1) /\
     (!t. t IN real_interval[&0,&1] /\ &0 < lam t
          ==> &2 * cm_sen G (\y. gamma0 y t) <= e)
     ==> cmr_famok S G e (\j. mat 1) (\j. vec 0)
           (\j t. if j = 1 then min (&1) (&2 * lam t) * R0 else &0) gamma0 /\
         !y t. cmr_fam S G 1 (\j. mat 1) (\j. vec 0)
                 (\j t. if j = 1 then min (&1) (&2 * lam t) * R0 else &0) gamma0 (&1) y t =
               cmr_rep1 S G (mat 1) (vec 0) (min (&1) (&2 * lam t) * R0)
                 (\y. gamma0 y t) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "lb") (LABEL_TAC "en")))))))))) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[cmr_fam; num_CONV `1`; cmr_repn] THEN
    REWRITE_TAC[GSYM ONE; REAL_MUL_LID]] THEN
  REWRITE_TAC[cmr_famok] THEN ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[] THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
        X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        USE_THEN "lb" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `m:num`] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[ARITH; GSYM ONE; cmr_repn] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < lam(t:real)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < s * min (&1) (&2 * (lam:real->real) t) * R0` THEN
      USE_THEN "lb" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
      UNDISCH_TAC `s IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `lam(t:real) = &0` THENL
       [UNDISCH_TAC `&0 < s * min (&1) (&2 * (lam:real->real) t) * R0` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * cm_sen G (\y. (gamma0:real^3->real->real^K) y t)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`;
                     `\y:real^3. (gamma0:real^3->real->real^K) y t`; `mat 1:real^3^3`;
                     `ball(vec 0:real^2,s * min (&1) (&2 * (lam:real->real) t) * R0)`]
                    CMR_CHART_GDIR_LE_SEN) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; OPEN_BALL] THEN
      UNDISCH_TAC `cm_sweep S (gamma0:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      USE_THEN "en" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[ARITH_RULE `SUC m = 1 <=> m = 0`; REAL_MUL_RZERO; REAL_LT_REFL]]);;

(* The pre-step Contr: slices of energy <= E1 become constant, slices of     *)
(* energy >= E2 are kept, energies do not increase, by a homotopy of        *)
(* sweepouts.  Ebar depends only on S, G and the replacement data.           *)

let CMR_LOW = prove
 (`!S (G:real^K->real^K^K) d e C Lam.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_repest S G e C /\ &0 <= C /\ CMR_GCOND G Lam
     ==> ?Ebar. &0 < Ebar /\
           !E1 E2 (gamma0:real^3->real->real^K).
              &0 < E1 /\ E1 < E2 /\ E2 <= Ebar /\ cm_sweep S gamma0
              ==> ?sigma. cm_sweep S sigma /\ cm_shomotopic S gamma0 sigma /\
                          (!t. t IN real_interval[&0,&1]
                               ==> cm_sen G (\y. sigma y t) <= cm_sen G (\y. gamma0 y t)) /\
                          (!t. t IN real_interval[&0,&1] /\ cm_sen G (\y. gamma0 y t) <= E1
                               ==> !y. y IN sphere(vec 0,&1)
                                       ==> sigma y t = sigma (basis 3) t) /\
                          (!t. t IN real_interval[&0,&1] /\ E2 <= cm_sen G (\y. gamma0 y t)
                               ==> !y. y IN sphere(vec 0,&1) ==> sigma y t = gamma0 y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMR_CTR_SWEEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctr")))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `eta:real`] CMR_BIGCAP_C0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  EXISTS_TAC `min (e / &4) delta` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`E1:real`; `E2:real`; `gamma0:real^3->real->real^K`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (gamma0:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g0S") (K ALL_TAC))) THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> cm_smap S (\y. (gamma0:real^3->real->real^K) y t)`
  (LABEL_TAC "g0m") THENL
   [UNDISCH_TAC `cm_sweep S (gamma0:real^3->real->real^K)` THEN SIMP_TAC[cm_sweep];
    ALL_TAC] THEN
  (* lambda and sf *)
  ABBREV_TAC `En = \t. cm_sen G (\y. (gamma0:real^3->real->real^K) y t)` THEN
  SUBGOAL_THEN `!t. (En:real->real) t = cm_sen G (\y. (gamma0:real^3->real->real^K) y t)`
  (LABEL_TAC "Ent") THENL [EXPAND_TAC "En" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(En:real->real) real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "En" THEN MATCH_MP_TAC CMR_SEN_SWEEP_CONT THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `e:real`; `Lam:real`; `C:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `lam = \t. min (&1) (max (&0) ((E2 - (En:real->real) t) / (E2 - E1)))` THEN
  SUBGOAL_THEN `(lam:real->real) real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MATCH_MP_TAC CMR_LAMBDA_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= (lam:real->real) t /\ lam t <= &1 /\
        ((En:real->real) t <= E1 ==> lam t = &1) /\ (E2 <= En t ==> lam t = &0) /\
        (&0 < lam t ==> En t < E2)`
  (LABEL_TAC "lf") THENL
   [GEN_TAC THEN EXPAND_TAC "lam" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_LAMBDA_FACTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sf = \t. max (&0) (&2 * (lam:real->real) t - &1)` THEN
  SUBGOAL_THEN `(sf:real->real) real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "sf" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= (sf:real->real) t /\ sf t <= &1 /\
        (&0 < sf t ==> &1 <= &2 * (lam:real->real) t) /\
        (lam t = &1 ==> sf t = &1) /\ (lam t = &0 ==> sf t = &0)`
  (LABEL_TAC "sff") THENL
   [GEN_TAC THEN EXPAND_TAC "sf" THEN REWRITE_TAC[] THEN
    USE_THEN "lf" (MP_TAC o SPEC `t:real`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* R0 from the uniform continuity of gamma0 *)
  MP_TAC(ISPEC `gamma0:real^3->real->real^K` CMW_SWEEP_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `delta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  ABBREV_TAC `R0 = max (&1) (&4 / rho)` THEN
  SUBGOAL_THEN `&1 <= R0 /\ &2 / R0 < rho` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= R0 /\ &4 / rho <= R0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "R0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&4 / rho <= R0` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_LDIV_EQ; REAL_ARITH `&1 <= R0 ==> &0 < R0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* stage 1 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `lam:real->real`; `R0:real`; `gamma0:real^3->real->real^K`]
                CMR_LOW_STAGE1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(En:real->real) t < E2` MP_TAC THENL
     [USE_THEN "lf" (MATCH_MP_TAC o el 4 o CONJUNCTS o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "Ent" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `E2 <= min (e / &4) delta` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1f")) THEN
  ABBREV_TAC
   `sigma1 = cmr_fam S G 1 (\j. mat 1) (\j. vec 0)
               (\j t. if j = 1 then min (&1) (&2 * (lam:real->real) t) * R0 else &0)
               (gamma0:real^3->real->real^K) (&1)` THEN
  SUBGOAL_THEN
   `cm_sweep S (sigma1:real^3->real->real^K) /\ cm_shomotopic S gamma0 sigma1 /\
    (!t. t IN real_interval[&0,&1]
         ==> cm_sen G (\y. sigma1 y t) <= cm_sen G (\y. gamma0 y t))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sigma1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMR_FAM_SWEEP THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMR_FAM_HOMOTOPIC THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMR_FAM_SEN_LE THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. (sigma1:real^3->real->real^K) y t =
          cmr_rep1 S G (mat 1) (vec 0) (min (&1) (&2 * (lam:real->real) t) * R0)
                   (\y. gamma0 y t) y`
  (LABEL_TAC "s1") THENL
   [USE_THEN "s1f" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  (* the north pole is never replaced *)
  SUBGOAL_THEN `!t. (sigma1:real^3->real->real^K) (basis 3) t =
                    (gamma0:real^3->real->real^K) (basis 3) t`
  (LABEL_TAC "s1n") THENL
   [GEN_TAC THEN USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[cmr_rep1; IN_IMAGE] THEN
    MP_TAC(ISPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
    REWRITE_TAC[ORTHOGONAL_MATRIX_ID; MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* closeness on the slices with sf > 0 *)
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\ &0 < (sf:real->real) t
          ==> norm((sigma1:real^3->real->real^K) y t - sigma1 (basis 3) t) <= eta`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= &2 * (lam:real->real) t` ASSUME_TAC THENL
     [USE_THEN "sff" (MATCH_MP_TAC o el 2 o CONJUNCTS o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `min (&1) (&2 * (lam:real->real) t) * R0 = R0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> min (&1) x = &1`; REAL_MUL_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `(En:real->real) t < E2` ASSUME_TAC THENL
     [USE_THEN "lf" (MATCH_MP_TAC o el 4 o CONJUNCTS o SPEC `t:real`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "s1n" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "c0" (MP_TAC o SPECL [`R0:real`; `\y:real^3. (gamma0:real^3->real->real^K) y t`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "Ent" (fun th -> REWRITE_TAC[GSYM th]) THEN
        UNDISCH_TAC `E2 <= min (e / &4) delta` THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* stage 2 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMR_RETR_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `P:real^K->real^K`) THEN
  USE_THEN "ctr" (MP_TAC o SPECL [`P:real^K->real^K`; `Lam:real`; `sf:real->real`;
                                  `sigma1:real^3->real->real^K`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "sff" (MP_TAC o SPEC `t:real`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `cmr_ctr (P:real^K->real^K) sf (sigma1:real^3->real->real^K) (&1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMW_SHOMOTOPIC_TRANS THEN
    EXISTS_TAC `sigma1:real^3->real->real^K` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm_sen G (\y. (sigma1:real^3->real->real^K) y t)` THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(lam:real->real) t = &1` ASSUME_TAC THENL
     [USE_THEN "lf" (MATCH_MP_TAC o el 2 o CONJUNCTS o SPEC `t:real`) THEN
      USE_THEN "Ent" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sf:real->real) t = &1` ASSUME_TAC THENL
     [USE_THEN "sff" (MATCH_MP_TAC o el 3 o CONJUNCTS o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`;
                   `sf:real->real`; `sigma1:real^3->real->real^K`] CMR_CTR_ONE) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`y:real^3`; `t:real`] th) THEN
                         MP_TAC(SPECL [`basis 3:real^3`; `t:real`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(lam:real->real) t = &0` ASSUME_TAC THENL
     [USE_THEN "lf" (MATCH_MP_TAC o el 3 o CONJUNCTS o SPEC `t:real`) THEN
      USE_THEN "Ent" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sf:real->real) t = &0` ASSUME_TAC THENL
     [USE_THEN "sff" (MATCH_MP_TAC o el 4 o CONJUNCTS o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[cmr_ctr] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO;
      VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ARITH `min (&1) (&0) * R0 = &0`] THEN
    SIMP_TAC[CMR_REP1_NONPOS; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `P:real^K->real^K`]
                  CMR_RETR_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    USE_THEN "g0S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

