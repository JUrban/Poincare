(* ========================================================================= *)
(* pc_grg_dist2: further distance results on top of pc_grg_dist: scaling    *)
(* of the metric (lengths and distances scale by sqrt k), C^1 curves pushed *)
(* forward under smooth maps on open sets, and the length results used by    *)
(* the Appendix layer: length comparison under a comparison of the metrics   *)
(* (MFD_LENGTH_METRIC_COMPARE), lengths for a metric field on an open set    *)
(* (MFD_LENGTH_OPEN_SET_ATLAS), and C^1 curves and lengths under a           *)
(* parametrization (MFD_PARAM_C1_CURVE_LIFT, MFD_PARAM_C1_CURVE_LENGTH).     *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Scaling the metric: lengths and distances scale by sqrt k.                *)
(* ------------------------------------------------------------------------- *)

let GRGD_SPEED_SCALE = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) a b k t.
        mfd_speed atlas (\x. k %% g x) gamma a b t =
        sqrt k * mfd_speed atlas g gamma a b t`,
  REWRITE_TAC[mfd_speed; MATRIX_VECTOR_LMUL; DOT_RMUL; SQRT_MUL]);;

let MFD_LENGTH_SCALE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ &0 <= k
        ==> mfd_length atlas (\x. k %% g x) gamma a b =
            sqrt k * mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[a,b])
      (\t. sqrt k * mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b t)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; GRGD_SPEED_SCALE];
    MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let GRGD_IN_LENGTHS_SCALE = prove
 (`!top atlas (g:A->real^N^N) k x y L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 <= k
        ==> (L IN {mfd_length atlas (\x. k %% g x) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = x /\ gamma(&1) = y} <=>
             ?L0. L0 IN {mfd_length atlas g gamma (&0) (&1) | gamma |
                         mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                         gamma(&0) = x /\ gamma(&1) = y} /\
                  L = sqrt k * L0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN
  SUBGOAL_THEN
   `!gamma:real->A. mfd_c1_curve (top,atlas) gamma (&0) (&1)
        ==> mfd_length atlas (\x. k %% (g:A->real^N^N) x) gamma (&0) (&1) =
            sqrt k * mfd_length atlas g gamma (&0) (&1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_LENGTH_SCALE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)` THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `gamma:real->A` THEN ASM_MESON_TAC[]]);;

let GRGD_INF_SCALE = prove
 (`!s t c. &0 < c /\ ~(s = {}) /\ (!x. x IN s ==> &0 <= x) /\
           (!y. y IN t <=> ?x. x IN s /\ y = c * x)
           ==> inf t = c * inf s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN t ==> &0 <= y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `inf t / c <= inf s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_INF_LE THEN MAP_EVERY EXISTS_TAC [`&0`; `x * c:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[REAL_MUL_SYM];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_INF_LE THEN MAP_EVERY EXISTS_TAC [`&0`; `z:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let MFD_DIST_SCALE = prove
 (`!top atlas (g:A->real^N^N) k x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        &0 < k /\ mfd_joinable (top,atlas) x y
        ==> mfd_dist (top,atlas) (\z. k %% g z) x y =
            sqrt k * mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC GRGD_INF_SCALE THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
    ASM_MESON_TAC[mfd_joinable];
    ASM_MESON_TAC[GRGD_LENGTHS_POS_LE];
    X_GEN_TAC `L:real` THEN MATCH_MP_TAC GRGD_IN_LENGTHS_SCALE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let MFD_BALL_SCALE = prove
 (`!top atlas (g:A->real^N^N) k x r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < k
        ==> mfd_ball (top,atlas) (\z. k %% g z) x r =
            mfd_ball (top,atlas) g x (r / sqrt k) /\
            mfd_cball (top,atlas) (\z. k %% g z) x r =
            mfd_cball (top,atlas) g x (r / sqrt k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN
  ASM_CASES_TAC
   `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y` THEN
  ASM_SIMP_TAC[MFD_DIST_SCALE; REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; SQRT_POS_LT] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let MFD_COMPLETE_SCALE = prove
 (`!top atlas (g:A->real^N^N) k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < k
        ==> (mfd_complete (top,atlas) (\z. k %% g z) <=>
             mfd_complete (top,atlas) g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_complete] THEN
  ASM_SIMP_TAC[MFD_BALL_SCALE] THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `r * sqrt k`]) THEN
    SUBGOAL_THEN `(r * sqrt k) / sqrt k = r` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `&0 < s ==> (r * s) / s = r`) THEN
      ASM_SIMP_TAC[SQRT_POS_LT];
      ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C^1 curves pushed forward under smooth maps defined on an open set W.     *)
(* ------------------------------------------------------------------------- *)

(* The Jacobian matrix of a smooth map is continuous. *)

let GRGD_JACOBIAN_CONTINUOUS = prove
 (`!s (h:real^N->real^M).
        open s /\ smooth_map_on s h
        ==> (vectorize o (\z. matrix(frechet_derivative h (at z))))
            continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM CONTINUOUS_ON_MATRIX_VECTORIZE] THEN
  X_GEN_TAC `v:real^N` THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z. frechet_derivative (h:real^N->real^M) (at z) v` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^M) (at z))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^M`]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[has_derivative];
      ASM_SIMP_TAC[MATRIX_WORKS]];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]]);;

(* A smooth map on W, in charts, is differentiable at chart images of points *)
(* of W.                                                                     *)

let GRGD_CHART_MAP_DIFF = prove
 (`!top atlas top' atlas' W (f:A->B) (c:(A->bool)#(A->real^N))
    (c':(B->bool)#(B->real^M)) x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        c IN atlas /\ c' IN atlas' /\ x IN FST c /\ x IN W /\ f x IN FST c'
        ==> ((SND c' o f o chart_inv c) has_derivative
             frechet_derivative (SND c' o f o chart_inv c) (at (SND c x)))
            (at (SND c x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (SND (c:(A->bool)#(A->real^N)))
      {y | y IN FST c INTER W /\ (f:A->B) y IN FST (c':(B->bool)#(B->real^M))}`;
    `SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
     chart_inv (c:(A->bool)#(A->real^N))`]
   SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]);;

(* Chain rule for the velocity of a pushed-forward curve in charts. *)

let GRGD_PUSH_VD = prove
 (`!top atlas top' atlas' W (f:A->B) (gamma:real->A) a b
    (c:(A->bool)#(A->real^N)) (c':(B->bool)#(B->real^M)) x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        mfd_c1_curve (top,atlas) gamma a b /\
        c IN atlas /\ c' IN atlas' /\ x IN interval[lift a,lift b] /\
        gamma(drop x) IN FST c /\ gamma(drop x) IN W /\
        f(gamma(drop x)) IN FST c'
        ==> ((\s. SND c' (f(gamma(drop s)))) has_vector_derivative
             frechet_derivative (SND c' o f o chart_inv c)
                                (at (SND c (gamma(drop x))))
               (vector_derivative (\s. SND c (gamma(drop s)))
                                  (at x within interval[lift a,lift b])))
            (at x within interval[lift a,lift b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:A. y IN FST (c:(A->bool)#(A->real^N)) ==> chart_inv c (SND c y) = y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `gamma:real->A`; `a:real`; `b:real`;
    `{y | y IN FST (c:(A->bool)#(A->real^N)) INTER W /\
          (f:A->B) y IN FST (c':(B->bool)#(B->real^M))}`;
    `drop x`] GRGD_CURVE_TIMES_BALL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GRGD_DROP_IN_REAL_INTERVAL] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `(SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
               chart_inv (c:(A->bool)#(A->real^N))) o
              (\s. SND c ((gamma:real->A)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    USE_THEN "D" (MP_TAC o SPEC `s:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN BETA_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `a:real`; `b:real`;
                     `c:(A->bool)#(A->real^N)`; `drop x`] GRGD_C1_CHART_HAS_VD) THEN
      ASM_SIMP_TAC[LIFT_DROP; GRGD_DROP_IN_REAL_INTERVAL];
      MATCH_MP_TAC GRGD_CHART_MAP_DIFF THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `W:A->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

(* velocity within the interval, and the velocity is continuous.            *)

let GRGD_C1_OPEN_IN_VD = prove
 (`!(q:real^1->real^N) S a b.
        a < b /\
        open_in (subtopology euclidean (interval[lift a,lift b])) S /\
        continuously_differentiable 1 S q
        ==> (!x. x IN S
                 ==> (q has_vector_derivative
                      vector_derivative q (at x within interval[lift a,lift b]))
                     (at x within interval[lift a,lift b])) /\
            (\x. vector_derivative q (at x within interval[lift a,lift b]))
            continuous_on S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:real^1->bool) SUBSET interval[lift a,lift b]` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUSLY_DIFFERENTIABLE_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> ((q:real^1->real^N) has_vector_derivative
             (f':real^1->real^1->real^N) x (vec 1))
            (at x within interval[lift a,lift b])`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGD_HAS_DERIVATIVE_VECTOR THEN REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`q:real^1->real^N`; `(f':real^1->real^1->real^N) x`;
                   `x:real^1`; `S:real^1->bool`; `interval[lift a,lift b]`]
                  HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> vector_derivative (q:real^1->real^N)
              (at x within interval[lift a,lift b]) =
            (f':real^1->real^1->real^N) x (vec 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (f':real^1->real^1->real^N) x (vec 1)` THEN
    ASM_SIMP_TAC[]]);;

(* C^1 along a curve is a local property (relatively open pieces). *)

let GRGD_C1_LOCAL = prove
 (`!(q:real^1->real^N) S a b.
        a < b /\
        open_in (subtopology euclidean (interval[lift a,lift b])) S /\
        (!x. x IN S
             ==> ?S'. open_in (subtopology euclidean (interval[lift a,lift b])) S' /\
                      x IN S' /\ S' SUBSET S /\ continuously_differentiable 1 S' q)
        ==> continuously_differentiable 1 S q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC"))) THEN
  SUBGOAL_THEN `(S:real^1->bool) SUBSET interval[lift a,lift b]` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  EXISTS_TAC
   `\x:real^1 h:real^1.
      drop h % vector_derivative (q:real^1->real^N)
                 (at x within interval[lift a,lift b])` THEN
  BETA_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    USE_THEN "LOC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^1) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `S':real^1->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`q:real^1->real^N`; `S':real^1->bool`; `a:real`; `b:real`]
                  GRGD_C1_OPEN_IN_VD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^1` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift a,lift b]` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `h:real^1` THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    USE_THEN "LOC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^1) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `S':real^1->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`q:real^1->real^N`; `S':real^1->bool`; `a:real`; `b:real`]
                  GRGD_C1_OPEN_IN_VD) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^1` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CONTINUOUS_WITHIN_OPEN_IN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `interval[lift a,lift b]` THEN ASM_REWRITE_TAC[]]);;

(* C^1 curves inside W are pushed forward to C^1 curves. *)

let GRGD_C1_CURVE_PUSH = prove
 (`!top atlas top' atlas' W (f:A->B) (gamma:real->A) a b.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
        (!t. t IN real_interval[a,b] ==> gamma t IN W)
        ==> mfd_c1_curve (top',atlas') (f o gamma) a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (interval[lift a,lift b]),top')
                   ((f:A->B) o (gamma:real->A) o drop)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_CURVE_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
      ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_c1_curve] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `c':(B->bool)#(B->real^M)` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC GRGD_C1_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `FST(c':(B->bool)#(B->real^M))` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[GRGD_ATLAS_CHART]; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(gamma:real->A)(drop x) IN topspace top /\ gamma(drop x) IN W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC
       [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`] THEN
      ASM_SIMP_TAC[GRGD_DROP_IN_REAL_INTERVAL];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[GRGD_DROP_IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c:(A->bool)#(A->real^N). c IN atlas /\ (gamma:real->A)(drop x) IN FST c`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC
   `{s | s IN interval[lift a,lift b] /\
         (gamma:real->A)(drop s) IN
         {y | y IN FST (c:(A->bool)#(A->real^N)) INTER W /\
              (f:A->B) y IN FST (c':(B->bool)#(B->real^M))}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_CURVE_TIMES_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  EXISTS_TAC
   `\s h. drop h %
          frechet_derivative (SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
                              chart_inv (c:(A->bool)#(A->real^N)))
            (at (SND c ((gamma:real->A)(drop s))))
            (vector_derivative (\s. SND c (gamma(drop s)))
               (at s within interval[lift a,lift b]))` THEN
  BETA_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift a,lift b]` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM has_vector_derivative] THEN MATCH_MP_TAC GRGD_PUSH_VD THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `W:A->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^1` THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\s. matrix(frechet_derivative
                 (SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
                  chart_inv (c:(A->bool)#(A->real^N)))
                 (at (SND c ((gamma:real->A)(drop s))))) **
        vector_derivative (\s. SND c (gamma(drop s)))
          (at s within interval[lift a,lift b])` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN
     `linear(frechet_derivative
               (SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
                chart_inv (c:(A->bool)#(A->real^N)))
               (at (SND c ((gamma:real->A)(drop s)))))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                     `W:A->bool`; `f:A->B`; `c:(A->bool)#(A->real^N)`;
                     `c':(B->bool)#(B->real^M)`; `(gamma:real->A)(drop s)`]
                    GRGD_CHART_MAP_DIFF) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[has_derivative];
      ASM_SIMP_TAC[MATRIX_WORKS]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize o
       (\s. matrix(frechet_derivative
               (SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
                chart_inv (c:(A->bool)#(A->real^N)))
               (at (SND c ((gamma:real->A)(drop s))))))) =
      (vectorize o
       (\z. matrix(frechet_derivative (SND c' o f o chart_inv c) (at z)))) o
      (\s. SND c (gamma(drop s)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC
       `{s | s IN interval[lift a,lift b] /\
             (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^N))}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        EXISTS_TAC `1` THEN ASM_MESON_TAC[mfd_c1_curve];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC
       `IMAGE (SND (c:(A->bool)#(A->real^N)))
          {y | y IN FST c INTER W /\
               (f:A->B) y IN FST (c':(B->bool)#(B->real^M))}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_JACOBIAN_CONTINUOUS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC
     `{s | s IN interval[lift a,lift b] /\
           (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CHART_VD_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]]]);;

(* Curves on a one-point interval. *)

let GRGD_C1_CURVE_POINT = prove
 (`!top atlas (gamma:real->A) a.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a a <=>
        gamma a IN topspace top`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC
     [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `a:real`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
    DISCH_TAC THEN REWRITE_TAC[mfd_c1_curve; REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `\t:real. (gamma:real->A) a` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                      REAL_INTERVAL_SING; IN_SING] THEN
      MESON_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
      EXISTS_TAC `\x:real^1 h:real^1. vec 0:real^N` THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC GRGD_HAS_DERIVATIVE_TRIVIAL THEN
      REWRITE_TAC[LINEAR_ZERO; TRIVIAL_LIMIT_WITHIN] THEN
      MATCH_MP_TAC LIMIT_POINT_FINITE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{lift a}` THEN
      REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING; INTERVAL_SING] THEN
      MESON_TAC[]]]);;

(* Maps agreeing on an open set have the same derivative there. *)

let GRGD_FRECHET_EQ_OPEN = prove
 (`!(f:real^M->real^N) g s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z) /\ f differentiable (at y)
        ==> (g has_derivative frechet_derivative f (at y)) (at y) /\
            frechet_derivative g (at y) = frechet_derivative f (at y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((g:real^M->real^N) has_derivative frechet_derivative f (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

(* Open subsets of real^N with the identity chart: the preferred chart and   *)
(* the speed.                                                                *)

let GRGD_OPEN_SET_CHART_AT = prove
 (`!s y:real^N. y IN s ==> chart_at (open_set_atlas s) y = (s,\x. x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_at; open_set_atlas; IN_SING] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `k:(real^N->bool)#(real^N->real^N)` THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST]);;

let GRGD_OPEN_SET_SPEED = prove
 (`!s (G:real^N->real^N^N) c a b t.
        mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\
        t IN real_interval[a,b]
        ==> mfd_speed (open_set_atlas s) G c a b t =
            sqrt(vector_derivative (\r. c(drop r))
                   (at (lift t) within interval[lift a,lift b]) dot
                 (G(c t) **
                  vector_derivative (\r. c(drop r))
                    (at (lift t) within interval[lift a,lift b])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `c:real->real^N`;
                   `a:real`; `b:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_speed; mfd_velocity; GRGD_OPEN_SET_CHART_AT; SND]);;

(* ------------------------------------------------------------------------- *)
(* Length results used by the Appendix layer.                                *)
(* ------------------------------------------------------------------------- *)

(* Length comparison under a pointwise comparison of the metrics. *)

let MFD_LENGTH_METRIC_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' c gamma a b.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\
     mfd_c1_curve (top,atlas) gamma a b /\ &0 <= c /\
     (!t v. a <= t /\ t <= b
            ==> v dot (g'(gamma t) ** v) <= c * (v dot (g(gamma t) ** v)))
     ==> mfd_length atlas g' gamma a b <= sqrt c * mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b real_integrable_on
    real_interval[a,b] /\
    mfd_speed atlas (g':A->real^N^N) gamma a b real_integrable_on
    real_interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; ETA_AX] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_speed; GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lengths for a metric field on an open set with the identity chart.       *)

let MFD_LENGTH_OPEN_SET_ATLAS = prove
 (`!s (G:real^N->real^N^N) c a b.
     open s /\ mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b
     ==> mfd_length (open_set_atlas s) G c a b =
         real_integral (real_interval[a,b])
           (\t. sqrt(vector_derivative (\r. c(drop r))
                       (at (lift t) within interval[lift a,lift b]) dot
                     (G(c t) **
                      vector_derivative (\r. c(drop r))
                        (at (lift t) within interval[lift a,lift b]))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC GRGD_OPEN_SET_SPEED THEN ASM_REWRITE_TAC[]);;

(* The facts about a parametrization e of an open set s used below. *)

let GRGD_PARAM_FACTS = prove
 (`!top atlas (s:real^N->bool) (e:real^N->A).
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e
        ==> ?e'. open s /\ open_in top (IMAGE e s) /\
                 IMAGE e s SUBSET topspace top /\
                 continuous_map (subtopology euclidean s,top) e /\
                 mfd_smooth_map (open_set_atlas s) atlas s e /\
                 continuous_map (subtopology top (IMAGE e s),
                                 subtopology euclidean s) e' /\
                 mfd_smooth_map atlas (open_set_atlas s) (IMAGE e s) e' /\
                 (!x. x IN s ==> e'(e x) = x) /\
                 (!y. y IN IMAGE e s ==> e(e' y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `e':A->real^N`)) THEN
  EXISTS_TAC `e':A->real^N` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphic_maps; GSYM OPEN_IN]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `mfd_smooth_map (open_set_atlas (:real^N))
                     (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC
     [`k:(real^N->bool)#(real^N->real^N)`; `k':(A->bool)#(A->real^N)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`((:real^N),\x:real^N. x)`; `k':(A->bool)#(A->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV; INTER_IDEMPOT] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND (k':(A->bool)#(A->real^N)) o (e:real^N->A) o
                chart_inv ((:real^N),\x:real^N. x)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    UNDISCH_TAC
     `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                     (open_set_atlas (:real^N)) (IMAGE (e:real^N->A) s)
                     (e':A->real^N)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC
     [`k:(A->bool)#(A->real^N)`; `k':(real^N->bool)#(real^N->real^N)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`k:(A->bool)#(A->real^N)`; `((:real^N),\x:real^N. x)`]) THEN
    ASM_REWRITE_TAC[FST; SND; IN_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    UNDISCH_TAC `IMAGE (e':A->real^N) (IMAGE e s) SUBSET s` THEN SET_TAC[]]);;

(* C^1 curves of the manifold inside IMAGE e s come from s. *)

let MFD_PARAM_C1_CURVE_LIFT = prove
 (`!top atlas s (e:real^N->A) gamma a b.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e s)
     ==> ?c. mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\
             (!t. a <= t /\ t <= b ==> c t IN s /\ gamma t = e(c t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(e':A->real^N) o (gamma:real->A)` THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t <= b
        ==> ((e':A->real^N) o (gamma:real->A)) t IN s /\
            gamma t = (e:real^N->A)((e' o gamma) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(gamma:real->A) t IN IMAGE (e:real^N->A) s` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[GRGD_C1_CURVE_POINT; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `IMAGE (e:real^N->A) s`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]]);;

(* Naturality of length under a parametrization. *)

let MFD_PARAM_C1_CURVE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) G c a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\
     (!y. y IN s
          ==> G y = mpullback (SND(chart_at atlas (e y)) o e)
                              (metric_local atlas (chart_at atlas (e y)) g) y) /\
     mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b
     ==> mfd_c1_curve (top,atlas) (e o c) a b /\
         mfd_length atlas g (e o c) a b = mfd_length (open_set_atlas s) G c a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "G") ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^N->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool,\x:real^N. x) IN open_set_atlas s` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (c:real->real^N) t IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `c:real->real^N`;
                   `a:real`; `b:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; GRGD_C1_CURVE_POINT; o_THM] THEN
    SUBGOAL_THEN `(c:real->real^N) b IN s` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
      UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET topspace top` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean s) (s:real^N->bool) /\
    continuous_map (subtopology (subtopology euclidean s) s,top) (e:real^N->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; OPEN_IN_SUBTOPOLOGY_REFL;
                    TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                 ((e:real^N->A) o (c:real->real^N)) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (s:real^N->bool)`;
                          `open_set_atlas (s:real^N->bool)`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN s` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->A)((c:real->real^N) t) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET topspace top` THEN
    UNDISCH_TAC `(c:real->real^N) t IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGD_OPEN_SET_SPEED] THEN
  USE_THEN "G"
   (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(c:real->real^N) t IN s`)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)((c:real->real^N) t)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool)
                     ((e:real^N->A)((c:real->real^N) t))`,
           `k:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(e:real^N->A) o (c:real->real^N)`;
                 `a:real`; `b:real`; `t:real`; `V:A->bool`; `psi:A->real^N`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `((psi:A->real^N) o (e:real^N->A) o chart_inv (s:real^N->bool,\x:real^N. x))
    differentiable (at ((c:real->real^N) t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC
     `frechet_derivative ((psi:A->real^N) o (e:real^N->A) o
                          chart_inv (s:real^N->bool,\x:real^N. x))
                         (at ((c:real->real^N) t))` THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^N))->bool`; `s:real^N->bool`;
                   `e:real^N->A`; `(s:real^N->bool,\x:real^N. x)`;
                   `(V:A->bool,psi:A->real^N)`; `(c:real->real^N) t`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(psi:A->real^N) o (e:real^N->A) o chart_inv (s:real^N->bool,\x:real^N. x)`;
    `(psi:A->real^N) o (e:real^N->A)`; `s:real^N->bool`;
    `(c:real->real^N) t`] GRGD_FRECHET_EQ_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (\r. (psi:A->real^N)((e:real^N->A)((c:real->real^N)(drop r))))
      (at (lift t) within interval[lift a,lift b]) =
    frechet_derivative (psi o e o chart_inv (s:real^N->bool,\x:real^N. x))
      (at (c t))
      (vector_derivative (\r. c(drop r))
         (at (lift t) within interval[lift a,lift b]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^N))->bool`; `s:real^N->bool`;
                   `e:real^N->A`; `c:real->real^N`; `a:real`; `b:real`;
                   `(s:real^N->bool,\x:real^N. x)`; `(V:A->bool,psi:A->real^N)`;
                   `lift t`] GRGD_PUSH_VD) THEN
    ASM_REWRITE_TAC[FST; SND; LIFT_DROP; GRGD_IN_INTERVAL_LIFT];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN
  ASM_MESON_TAC[has_derivative]);;

