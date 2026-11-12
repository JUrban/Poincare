(* ========================================================================= *)
(* Unit pc_geo_normal (geodesics layer): Gaussian normal coordinates         *)
(* (MFD_NORMAL_CHART).  The chart exp_x(E w) |-> w on the image of ball(0,r) *)
(* is compatible with the atlas (GEON_PARAM_CHART_INSERT), its local metric  *)
(* is the exp-pullback metric cmp_expmetric of pc_cmp_defs, which is the     *)
(* identity at 0 (CMPP_EXPMETRIC_ZERO) and satisfies G(w) w = w              *)
(* (CMPP_EXPMETRIC_GAUSS); the latter forces the Christoffel symbols to      *)
(* vanish at 0 (GEON_CHRISTOFFEL_ZERO).                                      *)
(* ========================================================================= *)

needs "src/pc_geo_inj.ml";;
needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Orthonormal frames and charts from parametrizations.                      *)
(* ========================================================================= *)

let GEON_FRAME_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) E.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ mfd_orthonormal_frame g x E
        ==> invertible E /\ !w. mfd_tnorm g x (E ** w) = norm w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_orthonormal_frame] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN DISCH_TAC THEN
    UNDISCH_TAC `transp (E:real^N^N) ** (g:A->real^N^N) x ** E = mat 1` THEN
    DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
    ASM_REWRITE_TAC[DET_MUL; DET_TRANSP; DET_I; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[mfd_tnorm; vector_norm] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID]]);;

(* The inverse of a parametrization, as a chart compatible with the atlas. *)

let GEON_PARAM_CHART_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^N->A) B.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas B Fm
        ==> (!w. w IN B ==> (@v. v IN B /\ Fm v = Fm w) = w) /\
            (!y. y IN IMAGE Fm B
                 ==> (@v. v IN B /\ Fm v = y) IN B /\
                     Fm(@v. v IN B /\ Fm v = y) = y) /\
            (!w. w IN B ==> chart_inv (IMAGE Fm B,(\y. @v. v IN B /\ Fm v = y)) w = Fm w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Fm:real^N->A`; `B:real^N->bool`] GEOJR_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. w IN B ==> (@v. v IN B /\ (Fm:real^N->A) v = Fm w) = w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_inv] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let GEON_PARAM_CHART_INSERT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^N->A) B.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas B Fm
        ==> smooth_manifold_atlas top
              ((IMAGE Fm B,(\y. @v. v IN B /\ Fm v = y)) INSERT atlas)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Fm:real^N->A`; `B:real^N->bool`] GEON_PARAM_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) B (Fm:real^N->A)` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^N`) THEN
  MP_TAC(ASSUME `mfd_diffeo euclidean (open_set_atlas (:real^N)) B top
                   (atlas:((A->bool)#(A->real^N))->bool) (IMAGE (Fm:real^N->A) B) Fm e'`) THEN
  REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM OPEN_IN]) THEN
  ABBREV_TAC `psi = \y:A. @v. v IN B /\ (Fm:real^N->A) v = y` THEN
  SUBGOAL_THEN `!y. y IN IMAGE (Fm:real^N->A) B ==> (psi:A->real^N) y = e' y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (subtopology euclidean B,
                                   subtopology top (IMAGE (Fm:real^N->A) B)) (Fm,e')` THEN
    REWRITE_TAC[homeomorphic_maps; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "psi" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN B ==> (psi:A->real^N) ((Fm:real^N->A) w) = w` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->real^N) (IMAGE (Fm:real^N->A) B) = B` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN EXPAND_TAC "psi" THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[smooth_manifold_atlas; IN_INSERT; PAIR_EQ] THEN
    MP_TAC(GEN_REWRITE_RULE I [smooth_manifold_atlas] th)) THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC) ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_EQ THEN EXISTS_TAC `e':A->real^N` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[];
        REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN EXISTS_TAC `Fm:real^N->A` THEN
        ONCE_REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM] THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `chi:A->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC) ASSUME_TAC)
   (DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC) ASSUME_TAC)) THENL
   [(* new, new *)
    EXISTS_TAC `\w:real^N. w` THEN REWRITE_TAC[SMOOTH_MAP_ON_ID];
    (* new, old *)
    EXISTS_TAC `(chi:A->real^N) o (Fm:real^N->A)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_map (open_set_atlas (:real^N))
                     (atlas:((A->bool)#(A->real^N))->bool) B (Fm:real^N->A)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`((:real^N),(\x:real^N. x))`; `(V:A->bool,chi:A->real^N)`]) THEN
      ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND] THEN
      MATCH_MP_TAC(MESON[SMOOTH_MAP_ON_EQ]
       `(s:real^N->bool) = t /\ (!x. x IN t ==> (f:real^N->real^N) x = h x)
        ==> smooth_map_on s f ==> smooth_map_on t h`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_UNIV] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]];
      REWRITE_TAC[IN_INTER; IN_IMAGE; o_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    (* old, new *)
    EXISTS_TAC `(e':A->real^N) o chart_inv (U:A->bool,phi:A->real^N)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                     (open_set_atlas (:real^N)) (IMAGE (Fm:real^N->A) B) e'` THEN
      REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`; `((:real^N),(\x:real^N. x))`]) THEN
      ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; IN_UNIV] THEN
      REWRITE_TAC[SET_RULE `{x:A | x IN s /\ T} = s`; SET_RULE `{x:A | x IN s} = s`;
                  o_DEF; ETA_AX];
      REWRITE_TAC[IN_INTER; o_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST; SND]];
    (* old, old *)
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The normal parametrization w -> exp_x(E w) of ball(0,r)                   *)
(* (GEON_NORMAL_PARAM), and Christoffel symbols of a metric field with       *)
(* G(z) z = z vanish at 0 (GEON_RADIAL_CHRISTOFFEL, GEON_CHRISTOFFEL_ZERO).  *)
(* ========================================================================= *)

let GEON_LINEAR_DIFFEO = prove
 (`!(E:real^N^N) (g:A->real^N^N) x r.
        invertible E /\ (!w. mfd_tnorm g x (E ** w) = norm w)
        ==> diffeomorphism_on (ball(vec 0,r)) (mfd_tball g x r)
                              (\w. E ** w) (\v. matrix_inv E ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!v:real^N. (E:real^N^N) ** (matrix_inv E ** v) = v) /\
                (!w:real^N. matrix_inv E ** (E ** w) = w)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. mfd_tnorm (g:A->real^N^N) x v = norm(matrix_inv (E:real^N^N) ** v)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `matrix_inv (E:real^N^N) ** v`
      (ASSUME `!w. mfd_tnorm (g:A->real^N^N) x ((E:real^N^N) ** w) = norm w`)) THEN
    REWRITE_TAC[ASSUME `!v:real^N. (E:real^N^N) ** (matrix_inv E ** v) = v`];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_BALL; GEOI_TBALL_OPEN] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; mfd_tball; IN_ELIM_THM; IN_BALL_0] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `matrix_inv (E:real^N^N) ** (v:real^N)` THEN ASM_MESON_TAC[]];
    X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(E:real^N^N) ** (w:real^N)` THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(\w:real^N. (E:real^N^N) ** w) = (\w. E ** w) o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_BALL; MATRIX_VECTOR_MUL_LINEAR; SMOOTH_MAP_ON_ID];
    SUBGOAL_THEN `(\v:real^N. matrix_inv (E:real^N^N) ** v) = (\v. matrix_inv E ** v) o (\x. x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; SMOOTH_MAP_ON_ID] THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `r:real`] GEOI_TBALL_OPEN) THEN
    REWRITE_TAC[mfd_tball]]);;

let GEON_NORMAL_PARAM = prove
 (`!top atlas (g:A->real^N^N) (x:A) E r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ mfd_inj_ball (top,atlas) g x r
        ==> mfd_param top atlas (ball(vec 0,r)) (\w. mfd_exp (top,atlas) g x (E ** w)) /\
            IMAGE (\w. mfd_exp (top,atlas) g x (E ** w)) (ball(vec 0,r)) =
            IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r) /\
            (!w. w IN ball(vec 0,r) <=> E ** w IN mfd_tball g x r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`] GEON_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`E:real^N^N`; `g:A->real^N^N`; `x:A`; `r:real`] GEON_LINEAR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!w. w IN ball(vec 0,r) <=> (E:real^N^N) ** w IN mfd_tball (g:A->real^N^N) x r`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0; mfd_tball; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)) (ball(vec 0,r)) =
    IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (\w:real^N. (E:real^N^N) ** w) (ball(vec 0,r)) =
                  mfd_tball (g:A->real^N^N) x r`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
     [ASM_MESON_TAC[diffeomorphism_on]; REWRITE_TAC[GSYM IMAGE_o; o_DEF]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_param] THEN
  UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
  REWRITE_TAC[mfd_inj_ball; mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `e':A->real^N`)) THEN
  EXISTS_TAC `(\v. matrix_inv (E:real^N^N) ** v) o (e':A->real^N)` THEN
  SUBGOAL_THEN `(\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)) =
                mfd_exp (top,atlas) g x o (\w. E ** w)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                        `mfd_tball (g:A->real^N^N) x r`] THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN]);;

(* Christoffel symbols of a metric field with the Gauss property. *)

let GEON_RADIAL_CHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> christoffel G y y y = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `!h. mderiv (G:real^N->real^N^N) y h ** y + G y ** h = h` ASSUME_TAC THENL
   [SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                  differentiable at (y:real^N)`
    MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N)) (at (y:real^N))`;
                   `\z:real^N. z`; `\h:real^N. h`; `y:real^N`] LRG_HAS_DERIVATIVE_MATVEC) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((\z:real^N. (G:real^N->real^N^N) z ** z) has_derivative (\h. h)) (at y)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\z:real^N. z`; `U:real^N->bool`] THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_ID];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `h:real^N` THEN
    MP_TAC(ISPECL [`\z:real^N. (G:real^N->real^N^N) z ** z`;
                   `\w. matrify(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                                    (G:real^N->real^N^N)) (at (y:real^N)) w) **
                        y + G y ** w`;
                   `\h:real^N. h`; `y:real^N`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN
    REWRITE_TAC[mderiv];
    ALL_TAC] THEN
  REWRITE_TAC[christoffel] THEN
  SUBGOAL_THEN
   `((lambda k. inv(&2) *
                ((mderiv (G:real^N->real^N^N) y y ** y)$k + (mderiv G y y ** y)$k -
                 y dot (mderiv G y (basis k) ** y))):real^N) = vec 0`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `mderiv (G:real^N->real^N^N) y y ** y = vec 0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mderiv (G:real^N->real^N^N) y (basis k) ** y = basis k - G y ** basis k`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `basis k:real^N`) THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DOT_RSUB; DOT_BASIS; GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
    SUBGOAL_THEN `transp((G:real^N->real^N^N) y) ** y = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[DOT_BASIS] THEN REAL_ARITH_TAC;
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

let GEON_CHRISTOFFEL_DIAG = prove
 (`!U (G:real^N->real^N^N) a.
        metric_field U G /\ vec 0 IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> christoffel G (vec 0) a a = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `christoffel (G:real^N->real^N^N) (vec 0)` BILINEAR_LZERO) THEN
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. christoffel (G:real^N->real^N^N) z a a) continuous at (vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rho. &0 < rho /\ ball(vec 0:real^N,rho) SUBSET U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(U:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t * norm(a:real^N) < rho
        ==> christoffel (G:real^N->real^N^N) (t % a) a a = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t % (a:real^N) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^N,rho) SUBSET U` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_BALL_0; NORM_MUL; REAL_ARITH `&0 < t ==> abs t = t`];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `t % a:real^N`]
      GEON_RADIAL_CHRISTOFFEL) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `t % a:real^N`]
      CHRISTOFFEL_BILINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LMUL th; MATCH_MP BILINEAR_RMUL th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_EQ_0] THEN
    ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  UNDISCH_TAC `(\z. christoffel (G:real^N->real^N^N) z a a) continuous at (vec 0)` THEN
  REWRITE_TAC[continuous_at; dist; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `norm(christoffel (G:real^N->real^N^N) (vec 0) a a)`) THEN
  REWRITE_TAC[NORM_POS_LT] THEN
  ASM_CASES_TAC `christoffel (G:real^N->real^N^N) (vec 0) a a = vec 0` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(a:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < min d rho / (&2 * norm(a:real^N)) /\
    min d rho / (&2 * norm(a:real^N)) * norm a < rho /\
    min d rho / (&2 * norm(a:real^N)) * norm a < d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MIN; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> m / (&2 * n) * n = m / &2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = min d rho / (&2 * norm(a:real^N))` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t % (a:real^N)`) THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < t ==> abs t = t`] THEN
  REWRITE_TAC[VECTOR_SUB_LZERO; NORM_NEG; REAL_LT_REFL]);;

let GEON_CHRISTOFFEL_ZERO = prove
 (`!U (G:real^N->real^N^N) u v.
        metric_field U G /\ vec 0 IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> christoffel G (vec 0) u v = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `u + v:real^N`]
    GEON_CHRISTOFFEL_DIAG) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `u:real^N`]
    GEON_CHRISTOFFEL_DIAG) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `v:real^N`]
    GEON_CHRISTOFFEL_DIAG) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `vec 0:real^N`; `v:real^N`;
                 `u:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `vec 0:real^N`]
    CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LADD th; MATCH_MP BILINEAR_RADD th]) THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The local metric of the normal chart is the exp-pullback                  *)
(* metric (GEON_NORMAL_METRIC_LOCAL), which is a metric field on the ball    *)
(* (GEON_EXPMETRIC_FIELD); MFD_NORMAL_CHART.                                  *)
(* ========================================================================= *)

let GEON_NORMAL_METRIC_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) E r w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ mfd_inj_ball (top,atlas) g x r /\
        w IN ball(vec 0,r)
        ==> metric_local atlas (mfd_normal_chart (top,atlas) g x E r) g w =
            cmp_expmetric (top,atlas) g x E w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `w:real^N` o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`;
                 `ball(vec 0:real^N,r)`] GEON_PARAM_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
    REWRITE_TAC[mfd_inj_ball] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[metric_local; cmp_expmetric; mfd_normal_chart] THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `z = mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)` THEN
  SUBGOAL_THEN
   `chart_jac (IMAGE (\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w))
                     (ball(vec 0,r)),
               (\y. @v. v IN ball(vec 0,r) /\ mfd_exp (top,atlas) g x (E ** v) = y))
              (chart_at atlas (z:A)) z =
    (\h. mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x)
           (E ** w) (E ** h))`
  (fun th -> REWRITE_TAC[th; cmp_dexp]) THEN
  REWRITE_TAC[chart_jac; chart_trans] THEN
  SUBGOAL_THEN
   `(@v. v IN ball(vec 0,r) /\
         mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** v) = (z:A)) = w`
  SUBST1_TAC THENL [EXPAND_TAC "z" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `frechet_derivative
                (\y. SND(chart_at atlas (z:A))
                       (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** y)))
                (at w)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
    EXISTS_TAC `ball(vec 0:real^N,r)` THEN ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`] CMPP_EXP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. (E:real^N^N) ** y`;
                 `\y. SND(chart_at atlas (z:A)) (mfd_exp (top,atlas) (g:A->real^N^N) x y)`;
                 `\y:real^N. (E:real^N^N) ** y`;
                 `mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) ((E:real^N^N) ** w)`;
                 `w:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[o_DEF]]);;

let GEON_EXPMETRIC_FIELD = prove
 (`!top atlas (g:A->real^N^N) (x:A) E r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ mfd_inj_ball (top,atlas) g x r
        ==> metric_field (ball(vec 0,r)) (cmp_expmetric (top,atlas) g x E)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`] GEON_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
  REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`; `mfd_tball (g:A->real^N^N) x r`]
    GEOJR_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ns" o last o CONJUNCTS) THEN
  SUBGOAL_THEN `!w. w IN ball(vec 0,r) ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[metric_field; OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{w | (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x}` THEN
    CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`] CMPP_EXPMETRIC_SMOOTH) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CMPP_EXPMETRIC_SYM] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[cmp_expmetric; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[CMPP_DEXP_APPLY] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`]
    GEOD_G_POS_DEF) THEN
  ASM_SIMP_TAC[CMPP_EXP_IN_TOPSPACE] THEN DISCH_THEN MATCH_MP_TAC THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(E:real^N^N) ** v = vec 0` MP_TAC THENL
   [USE_THEN "ns" MATCH_MP_TAC THEN
    EXISTS_TAC `(E:real^N^N) ** w` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\u:real^N. matrix_inv(E:real^N^N) ** u`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
               MATRIX_VECTOR_MUL_RZERO]);;

let MFD_NORMAL_CHART = prove
 (`!top atlas (g:A->real^N^N) (x:A) E.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E
        ==> ?r0. &0 < r0 /\
                 !r. &0 < r /\ r <= r0
                     ==> smooth_manifold_atlas top
                           (mfd_normal_chart (top,atlas) g x E r INSERT atlas) /\
                         FST(mfd_normal_chart (top,atlas) g x E r) =
                         mfd_ball (top,atlas) g x r /\
                         IMAGE (SND(mfd_normal_chart (top,atlas) g x E r))
                               (FST(mfd_normal_chart (top,atlas) g x E r)) =
                         ball(vec 0,r) /\
                         SND(mfd_normal_chart (top,atlas) g x E r) x = vec 0 /\
                         metric_local atlas (mfd_normal_chart (top,atlas) g x E r) g
                                      (vec 0) = mat 1 /\
                         (!u v. christoffel
                                  (metric_local atlas
                                     (mfd_normal_chart (top,atlas) g x E r) g)
                                  (vec 0) u v = vec 0) /\
                         (!y. y IN FST(mfd_normal_chart (top,atlas) g x E r)
                              ==> mfd_dist (top,atlas) g x y =
                                  norm(SND(mfd_normal_chart (top,atlas) g x E r) y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_LOCAL_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`] GEON_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN ball(vec 0,r)
        ==> (E:real^N^N) ** w IN mfd_tball (g:A->real^N^N) x r /\
            E ** w IN mfd_exp_dom (top,atlas) g x`
  (LABEL_TAC "dom") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** w IN mfd_tball (g:A->real^N^N) x r` ASSUME_TAC THENL
     [REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[IN_BALL_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
    REWRITE_TAC[mfd_inj_ball] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`;
                 `ball(vec 0:real^N,r)`] GEON_PARAM_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
  DISCH_THEN(LABEL_TAC "sel" o CONJUNCT1) THEN
  SUBGOAL_THEN `(vec 0:real^N) IN ball(vec 0,r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** vec 0) = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_normal_chart] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`;
                   `ball(vec 0:real^N,r)`] GEON_PARAM_CHART_INSERT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    REWRITE_TAC[mfd_normal_chart] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2)] THEN
    MATCH_MP_TAC MFD_EXP_BALL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_normal_chart; GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[mfd_normal_chart] THEN
    USE_THEN "sel" (MP_TAC o C MATCH_MP (ASSUME `(vec 0:real^N) IN ball(vec 0,r)`) o
                    SPEC `vec 0:real^N`) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`; `vec 0:real^N`]
      GEON_NORMAL_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CMPP_EXPMETRIC_ZERO THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `christoffel (cmp_expmetric (top,atlas) (g:A->real^N^N) x E) (vec 0) u v` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `ball(vec 0:real^N,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC GEON_NORMAL_METRIC_LOCAL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GEON_CHRISTOFFEL_ZERO THEN EXISTS_TAC `ball(vec 0:real^N,r)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GEON_EXPMETRIC_FIELD THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN ASM_SIMP_TAC[]]];
    REWRITE_TAC[mfd_normal_chart; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN
    DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `r:real`; `(E:real^N^N) ** w`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[IN_BALL_0]; SIMP_TAC[]]]);;

