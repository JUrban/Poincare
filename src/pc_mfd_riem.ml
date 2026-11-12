(* ========================================================================= *)
(* pc_mfd_riem: Riemannian metrics on manifolds and their curvature.  A      *)
(* metric is a matrix field g : A -> real^N^N in the coordinates of the      *)
(* preferred charts; metric_local atlas c g is its representative in the     *)
(* chart c.  Chart independence of curvature comes from the naturality       *)
(* theorems of the local theory pc_lrg.                                      *)
(* ========================================================================= *)

needs "src/pc_mfd_base.ml";;
needs "src/pc_lrg.ml";;

prioritize_real();;
type_invention_error := true;;

let CHART_JAC_LINEAR = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> linear(chart_jac (U,phi) (V,psi) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[has_derivative]);;

(* Representative in the chart c of a matrix field given in preferred      *)
(* coordinates.                                                              *)

let metric_local = new_definition
 `metric_local (atlas:((A->bool)#(A->real^N))->bool)
               (c:(A->bool)#(A->real^N)) (g:A->real^N^N) =
    \y. transp(matrix(chart_jac c (chart_at atlas (chart_inv c y))
                                  (chart_inv c y))) **
        g(chart_inv c y) **
        matrix(chart_jac c (chart_at atlas (chart_inv c y)) (chart_inv c y))`;;

let riemannian_metric = new_definition
 `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) <=>
    !c. c IN atlas
        ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c g)`;;

let METRIC_LOCAL_AT = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ x IN topspace top
        ==> metric_local atlas (chart_at atlas x) g
                         (SND(chart_at atlas x) x) = g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi x) = x`
  SUBST1_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `chart_jac (U:A->bool,phi:A->real^N) (U,phi) x = (\h. h)`
  SUBST1_TAC THENL [ASM_MESON_TAC[CHART_JAC_SELF]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* On an overlap, chart representatives are pullbacks of each other. *)

let METRIC_LOCAL_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> metric_local atlas (U,phi) g (phi x) =
            mpullback (chart_trans (U,phi) (V,psi))
                      (metric_local atlas (V,psi) g) (phi x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `chi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  REWRITE_TAC[metric_local; mpullback] THEN
  SUBGOAL_THEN
   `chart_inv (U:A->bool,phi:A->real^N) (phi x) = x /\
    chart_inv (V:A->bool,psi:A->real^N) (psi x) = x`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_MESON_TAC[CHART_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x) = psi x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[SND] (SPECL
    [`(U:A->bool,phi:A->real^N)`; `(V:A->bool,psi:A->real^N)`; `x:A`]
    chart_jac))] THEN
  SUBGOAL_THEN
   `matrix(chart_jac (U:A->bool,phi:A->real^N) (W,chi) x) =
    matrix(chart_jac (V,psi) (W,chi) x) ** matrix(chart_jac (U,phi) (V,psi) x)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                  `W:A->bool`; `chi:A->real^N`; `x:A`] CHART_JAC_CHAIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MATRIX_COMPOSE THEN
    CONJ_TAC THEN MATCH_MP_TAC CHART_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* Restricting a Riemannian metric to a chart overlap. *)

let RIEMANNIAN_METRIC_OVERLAP = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> metric_field (IMAGE phi (U INTER V)) (metric_local atlas (U,phi) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]]);;

(* Scalar curvature on the manifold, and its value in any chart. *)

let mfd_scalar = new_definition
 `mfd_scalar (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    lscalar (metric_local atlas (chart_at atlas x) g)
            (SND(chart_at atlas x) x)`;;

let LSCALAR_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> lscalar (metric_local atlas (U,phi) g) (phi x) =
            lscalar (metric_local atlas (V,psi) g) (psi x)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `lscalar (mpullback (chart_trans (U:A->bool,phi:A->real^N) (V,psi))
                       (metric_local atlas (V,psi) (g:A->real^N^N)))
            (phi x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC LSCALAR_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_SCALAR_CHART = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ x IN U
        ==> mfd_scalar atlas g x = lscalar (metric_local atlas (U,phi) g) (phi x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `chi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MATCH_MP_TAC LSCALAR_CHART_TRANS THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The curvature tensors of two chart representatives correspond under the *)
(* derivative of the transition map.                                         *)

let LRIEMANN_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x u v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> chart_jac (U,phi) (V,psi) x
              (lriemann (metric_local atlas (U,phi) g) (phi x) u v w) =
            lriemann (metric_local atlas (V,psi) g) (psi x)
              (chart_jac (U,phi) (V,psi) x u) (chart_jac (U,phi) (V,psi) x v)
              (chart_jac (U,phi) (V,psi) x w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lriemann (metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N))
             (phi x) u v w =
    lriemann (mpullback (chart_trans (U,phi) (V,psi))
                        (metric_local atlas (V,psi) g)) (phi x) u v w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRIEMANN_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `chart_jac (U:A->bool,phi:A->real^N) (V,psi) x =
    frechet_derivative (chart_trans (U,phi) (V,psi)) (at (phi x))`
  SUBST1_TAC THENL [REWRITE_TAC[chart_jac; SND]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRIEMANN_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let mfd_riemann = new_definition
 `mfd_riemann (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    lriemann (metric_local atlas (chart_at atlas x) g)
             (SND(chart_at atlas x) x)`;;

let mfd_ricci = new_definition
 `mfd_ricci (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    lricci (metric_local atlas (chart_at atlas x) g)
           (SND(chart_at atlas x) x)`;;

(* ------------------------------------------------------------------------- *)
(* Chart representatives at a point differ by congruence with the Jacobian, *)
(* and sectional curvature is chart independent.                             *)
(* ------------------------------------------------------------------------- *)

let METRIC_LOCAL_JAC = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> metric_local atlas (U,phi) g (phi x) =
            transp(matrix(chart_jac (U,phi) (V,psi) x)) **
            metric_local atlas (V,psi) g (psi x) **
            matrix(chart_jac (U,phi) (V,psi) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `g:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[mpullback] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[SND] (SPECL
    [`(U:A->bool,phi:A->real^N)`; `(V:A->bool,psi:A->real^N)`; `x:A`]
    chart_jac))] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let LSECTIONAL_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> lsectional (metric_local atlas (U,phi) g) (phi x) u v =
            lsectional (metric_local atlas (V,psi) g) (psi x)
              (chart_jac (U,phi) (V,psi) x u) (chart_jac (U,phi) (V,psi) x v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `g:A->real^N^N`; `x:A`; `u:real^N`; `v:real^N`; `v:real^N`]
               LRIEMANN_CHART_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Sectional curvature on the manifold, its minimum (MT's nu) and |Rm| as   *)
(* the largest absolute sectional curvature (the sectional normalization of *)
(* |Rm|).                                                                   *)

let mfd_sectional = new_definition
 `mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A)
                (u:real^N) (v:real^N) =
    lsectional (metric_local atlas (chart_at atlas x) g)
               (SND(chart_at atlas x) x) u v`;;

let mfd_sec_min = new_definition
 `mfd_sec_min (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    inf {mfd_sectional atlas g x u v | u,v | ~collinear {vec 0,u,v}}`;;

let mfd_rm_norm = new_definition
 `mfd_rm_norm (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    sup {abs(mfd_sectional atlas g x u v) | u,v | ~collinear {vec 0,u,v}}`;;

(* ------------------------------------------------------------------------- *)
(* Pointwise properties of a Riemannian metric, and constant rescaling.      *)
(* ------------------------------------------------------------------------- *)

let RIEMANNIAN_METRIC_POS = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> transp(g x) = g x /\ !v. ~(v = vec 0) ==> &0 < v dot (g x ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`) THEN
  ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let METRIC_LOCAL_CMUL = prove
 (`!atlas c (g:A->real^N^N) k.
        metric_local atlas c (\x. k %% g x) = (\y. k %% metric_local atlas c g y)`,
  REWRITE_TAC[metric_local; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let RIEMANNIAN_METRIC_CMUL = prove
 (`!atlas (g:A->real^N^N) k.
        &0 < k /\ riemannian_metric atlas g
        ==> riemannian_metric atlas (\x. k %% g x)`,
  REWRITE_TAC[riemannian_metric; METRIC_LOCAL_CMUL; metric_field] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\y. k %% metric_local atlas c (g:A->real^N^N) y) =
      (\y. k % (vectorize o metric_local atlas c g) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[TRANSP_MATRIX_CMUL] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

