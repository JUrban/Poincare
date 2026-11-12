(* ========================================================================= *)
(* Unit pc_s2ent_heat: an approximate Poisson equation on a closed surface  *)
(* of positive curvature by the heat flow (S2E_APPROX_POISSON), and         *)
(* Hamilton's inequality int (R - r)^2 <= int |grad R|^2 / R                *)
(* (S2E_HAMILTON_INEQ).  First, Cauchy-Schwarz inequalities for the metric  *)
(* inner products.                                                          *)
(* ========================================================================= *)

needs "src/pc_s2ent_calc.ml";;

prioritize_real();;
type_invention_error := true;;

let S2E_DISCRIMINANT = prove
 (`!A B C. &0 <= B /\ (!t. &0 <= A + &2 * t * C + t pow 2 * B) ==> C pow 2 <= A * B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `B = &0` THENL
   [ASM_CASES_TAC `C = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--(abs A + &1) / (&2 * C)`) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SUBGOAL_THEN `&2 * (--(abs A + &1) / (&2 * C)) * C = --(abs A + &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(C = &0)` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `--C / B`) THEN
    SUBGOAL_THEN `A + &2 * (--C / B) * C + (--C / B) pow 2 * B = A - C pow 2 / B`
    SUBST1_TAC THENL [UNDISCH_TAC `~(B = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ]]);;

(* Cauchy-Schwarz for a positive semidefinite symmetric matrix. *)

let S2E_PSD_CS = prove
 (`!(H:real^N^N) a b.
     transp H = H /\ (!v. &0 <= v dot (H ** v))
     ==> (a dot (H ** b)) pow 2 <= (a dot (H ** a)) * (b dot (H ** b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC S2E_DISCRIMINANT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a + t % b:real^N`) THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(b:real^N) dot ((H:real^N^N) ** a) = a dot (H ** b)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`H:real^N^N`; `b:real^N`; `a:real^N`] DOT_MATRIX_TRANSP_RMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_SYM];
    REAL_ARITH_TAC]);;

(* The inverse metric is symmetric and positive semidefinite. *)

let S2E_GINV_PSD = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> transp(matrix_inv(G y)) = matrix_inv(G y) /\
         !v. &0 <= v dot (matrix_inv(G y) ** v)`,
  REPEAT STRIP_TAC THENL
   [SIMP_TAC[CART_EQ; TRANSP_COMPONENT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                  LRG_METRIC_INV_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL; DOT_POS_LE]]);;

(* Cauchy-Schwarz for the inner product of gradients, locally and on a      *)
(* manifold.                                                                 *)

let S2E_LGINNER_CS = prove
 (`!U (G:real^N->real^N^N) a b y.
     metric_field U G /\ y IN U
     ==> (rfa_lginner G a b y) pow 2 <= rfa_lginner G a a y * rfa_lginner G b b y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[S2E_LGINNER_DOT] THEN
  MATCH_MP_TAC S2E_PSD_CS THEN MATCH_MP_TAC S2E_GINV_PSD THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let S2E_GINNER_CS = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> (s2e_ginner atlas g a b x) pow 2 <=
         s2e_ginner atlas g a a x * s2e_ginner atlas g b b x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner] THEN
  MATCH_MP_TAC S2E_LGINNER_CS THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* Cauchy-Schwarz for a directional derivative: (df(v))^2 <= |df|^2 |v|^2. *)

let S2E_D1_CS = prove
 (`!U (G:real^N->real^N^N) f y v.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> (rfa_d1 f y v) pow 2 <= rfa_lginner G f f y * (v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\ invertible(G y) /\
                !v. &0 <= v dot (G y ** v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
      X_GEN_TAC `w:real^N` THEN ASM_CASES_TAC `w:real^N = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  ABBREV_TAC `dF = (lambda k. rfa_d1 (f:real^N->real) y (basis k)):real^N` THEN
  SUBGOAL_THEN `rfa_d1 (f:real^N->real) y v = dF dot v` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`; `y:real^N`; `v:real^N`] S2E_D1_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dF" THEN
    REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[S2E_LGINNER_DOT] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `matrix_inv((G:real^N->real^N^N) y) ** dF`;
                 `v:real^N`] S2E_PSD_CS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(matrix_inv((G:real^N->real^N^N) y) ** dF) dot (G y ** v) = dF dot v /\
                (matrix_inv(G y) ** dF) dot (G y ** matrix_inv(G y) ** dF) =
                dF dot (matrix_inv(G y) ** dF)`
  (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_ACCEPT_TAC DOT_SYM] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Along a C^1 curve a smooth function changes by at most                    *)
(* sup |grad f| times the length; on a compact connected manifold the       *)
(* oscillation of f is at most a fixed multiple of sup |grad f|.            *)
(* ------------------------------------------------------------------------- *)

let S2E_CURVE_DERIV = prove
 (`!top atlas (f:A->real) (gamma:real->A) a b t.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     mfd_smooth atlas (\x. lift(f x)) /\
     mfd_c1_curve (top,atlas) gamma a b /\ t IN real_interval[a,b]
     ==> ((\s. f(gamma s)) has_real_derivative
          rfa_d1 (\y. f(chart_inv (chart_at atlas (gamma t)) y))
                 (SND(chart_at atlas (gamma t)) (gamma t))
                 (mfd_velocity atlas gamma a b t))
         (atreal t within real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_velocity] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND c) (FST c))
                  (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
                differentiable at (SND c ((gamma:real->A) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `c:(A->bool)#(A->real^N)`; `t:real`]
                GRGD_C1_CHART_HAS_VD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `FST(c:(A->bool)#(A->real^N))`; `t:real`]
                GRGD_CURVE_TIMES_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `(\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) o
              (\s. SND c ((gamma:real->A)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_d1; LIFT_DROP] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* d <= K sqrt q from d^2 <= K^2 q. *)

let S2E_SQRT_BOUND = prove
 (`!d K q. &0 <= K /\ &0 <= q /\ d pow 2 <= K pow 2 * q ==> d <= K * sqrt q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `K * sqrt q = sqrt(K pow 2 * q)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]);;

(* The change along a curve. *)

let S2E_CURVE_BOUND = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (gamma:real->A) a b K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(f x)) /\ mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
     &0 <= K /\ (!x. x IN topspace top ==> s2e_ginner atlas g f f x <= K pow 2)
     ==> f(gamma b) - f(gamma a) <= K * mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `a:real`; `b:real`] GRGD_SPEED_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_length] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP REAL_INTEGRAL_LMUL th)]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  EXISTS_TAC `\t. rfa_d1 (\y. (f:A->real)(chart_inv (chart_at atlas ((gamma:real->A) t)) y))
                         (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (gamma t)) (gamma t))
                         (mfd_velocity atlas gamma a b t)` THEN
  EXISTS_TAC `\t. K * mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b t` THEN
  EXISTS_TAC `real_interval[a,b]` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `\s. (f:A->real)((gamma:real->A) s)` REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC S2E_CURVE_DERIV THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_speed] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  ABBREV_TAC `V = mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b t` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c))
                  (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                  (SND c ((gamma:real->A) t)) = g(gamma t)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC S2E_SQRT_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `metric_field (IMAGE (SND c) (FST c))
                   (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)` o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN
    ASM_CASES_TAC `V:real^N = vec 0` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `rfa_lginner (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                (\y. (f:A->real)(chart_inv c y)) (\y. f(chart_inv c y)) (SND c ((gamma:real->A) t)) *
              (V dot (g(gamma t) ** V))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `(g:A->real^N^N)((gamma:real->A) t)`)) THEN
    MATCH_MP_TAC S2E_D1_CS THEN EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A) t` o check (fun th ->
      is_forall(concl th) && s2e_mentions "s2e_ginner" th)) THEN
    ASM_REWRITE_TAC[s2e_ginner];
    UNDISCH_TAC `metric_field (IMAGE (SND c) (FST c))
                   (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)` o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN
    ASM_CASES_TAC `V:real^N = vec 0` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE]]);;

(* A continuous real function on a compact space is bounded. *)

let S2E_COMPACT_BOUND = prove
 (`!(X:A topology) f.
     compact_space X /\ continuous_map (X,euclideanreal) f
     ==> ?B. &0 < B /\ !x. x IN topspace X ==> abs(f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `euclideanreal`; `f:A->real`; `topspace(X:A topology)`]
                IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; REAL_BOUNDED_POS] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN MESON_TAC[]);;

(* On a compact connected manifold the Riemannian distance is bounded, and *)
(* any two points are joined by a curve of length at most L.              *)

let S2E_SHORT_CURVES = prove
 (`!top atlas (g:A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ connected_space top
     ==> ?L. &0 <= L /\
             !x y. x IN topspace top /\ y IN topspace top
                   ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                               gamma(&0) = x /\ gamma(&1) = y /\
                               mfd_length atlas g gamma (&0) (&1) <= L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prod_topology (top:A topology) top`;
                 `\(x,y). mfd_dist (top,atlas) (g:A->real^N^N) (x:A) y`] S2E_COMPACT_BOUND) THEN
  ASM_SIMP_TAC[MFD_DIST_CONTINUOUS; COMPACT_SPACE_PROD_TOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y` MP_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_joinable] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y}`;
                 `mfd_dist (top,atlas) (g:A->real^N^N) (x:A) y + &1`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM mfd_dist] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GRGD_IN_LENGTHS] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `L0 < mfd_dist (top,atlas) (g:A->real^N^N) (x:A) y + &1` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The oscillation bound. *)

let S2E_OSC_BOUND = prove
 (`!top atlas (g:A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ connected_space top
     ==> ?L. &0 <= L /\
             !f K x y. mfd_smooth atlas (\x. lift(f x)) /\ &0 <= K /\
                       (!z. z IN topspace top ==> s2e_ginner atlas g f f z <= K pow 2) /\
                       x IN topspace top /\ y IN topspace top
                       ==> abs(f x - f y) <= L * K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                S2E_SHORT_CURVES) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u v:A. u IN topspace top /\ v IN topspace top ==> (f:A->real) v - f u <= L * K`
  (fun th -> MP_TAC(SPECL [`x:A`; `y:A`] th) THEN MP_TAC(SPECL [`y:A`; `x:A`] th)) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:A`; `v:A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->A)(&1) = v`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->A)(&0) = u`)) THEN
      MATCH_MP_TAC S2E_CURVE_BOUND THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Space-time calculus for chart functions.  For FF smooth on                *)
(* an open set O of space-time real^(1,N) and its time slices              *)
(* U s = drop o FF(s,.), the time derivative of the first and second space  *)
(* derivatives, of the local Laplacian and of the local inner product of   *)
(* gradients is the same quantity for the time derivative Ft of FF          *)
(* (LRG_TIME_SPACE_SWAP, LRG_SECOND_DERIVATIVE_SYM); the local inner       *)
(* product of slices is smooth in space-time.                               *)
(* ------------------------------------------------------------------------- *)

let S2E_ST_TIME_NBHD = prove
 (`!(O:real^(1,N)finite_sum->bool) t y.
     open O /\ pastecart (lift t) y IN O
     ==> ?d. &0 < d /\ !s. abs(s - t) < d ==> pastecart (lift s) y IN O`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ASM_REWRITE_TAC[PDE_ST_PASTECART_DIST]);;

(* First space derivatives of a slice. *)

let S2E_ST_SLICE_D1 = prove
 (`!O (FF:real^(1,N)finite_sum->real^1) s z h.
     open O /\ smooth_map_on O FF /\ pastecart s z IN O
     ==> rfa_d1 (\w. drop(FF(pastecart s w))) z h =
         drop(frechet_derivative FF (at (pastecart s z)) (pastecart (vec 0) h))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1; LIFT_DROP; ETA_AX] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_SLICE_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]);;

(* The time derivative of a first space derivative. *)

let S2E_ST_D1_DERIV = prove
 (`!O (FF:real^(1,N)finite_sum->real^1) t y v.
     open O /\ smooth_map_on O FF /\ pastecart (lift t) y IN O
     ==> ((\s. rfa_d1 (\z. drop(FF(pastecart (lift s) z))) y v) has_real_derivative
          rfa_d1 (\z. drop(frechet_derivative FF (at (pastecart (lift t) z))
                                              (pastecart (lift(&1)) (vec 0)))) y v)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfa_d1; LIFT_DROP; ETA_AX; HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  MATCH_MP_TAC LRG_TIME_SPACE_SWAP THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The time derivative of a second space derivative. *)

let S2E_ST_D2_DERIV = prove
 (`!O (FF:real^(1,N)finite_sum->real^1) t y a b.
     open O /\ smooth_map_on O FF /\ pastecart (lift t) y IN O
     ==> ((\s. rfa_d2 (\z. drop(FF(pastecart (lift s) z))) y a b) has_real_derivative
          rfa_d2 (\z. drop(frechet_derivative FF (at (pastecart (lift t) z))
                                              (pastecart (lift(&1)) (vec 0)))) y a b)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `F1 = \p. frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at p)
                                          (pastecart (vec 0) (b:real^N))` THEN
  ABBREV_TAC `Ft = \p. frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at p)
                                          (pastecart (lift(&1)) (vec 0:real^N))` THEN
  SUBGOAL_THEN `smooth_map_on O (F1:real^(1,N)finite_sum->real^1) /\
                smooth_map_on O (Ft:real^(1,N)finite_sum->real^1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["F1"; "Ft"] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  (* the slices of rfa_d2 are first derivatives of slices of F1 *)
  SUBGOAL_THEN
   `!s. pastecart (lift s) (y:real^N) IN O
        ==> rfa_d2 (\z. drop((FF:real^(1,N)finite_sum->real^1)(pastecart (lift s) z))) y a b =
            rfa_d1 (\z. drop((F1:real^(1,N)finite_sum->real^1)(pastecart (lift s) z))) y a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_D2_AS_D1] THEN
    MATCH_MP_TAC RFA_D1_LOCAL THEN
    EXISTS_TAC `{z:real^N | pastecart (lift s) z IN (O:real^(1,N)finite_sum->bool)}` THEN
    ASM_SIMP_TAC[PDE_ST_SLICE_OPEN; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "F1" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC S2E_ST_SLICE_D1 THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `t:real`; `y:real^N`] S2E_ST_TIME_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. rfa_d1 (\z. drop((F1:real^(1,N)finite_sum->real^1)(pastecart (lift s) z))) y a` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_d2 (\z. drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1)
                       (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0)))) y a b =
    rfa_d1 (\z. drop(frechet_derivative (F1:real^(1,N)finite_sum->real^1)
                       (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0)))) y a`
  SUBST1_TAC THENL
   [REWRITE_TAC[RFA_D2_AS_D1] THEN MATCH_MP_TAC RFA_D1_LOCAL THEN
    EXISTS_TAC `{z:real^N | pastecart (lift t) z IN (O:real^(1,N)finite_sum->bool)}` THEN
    ASM_SIMP_TAC[PDE_ST_SLICE_OPEN; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `Ft:real^(1,N)finite_sum->real^1`;
                   `lift t`; `z:real^N`; `b:real^N`] S2E_ST_SLICE_D1) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ft" THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "F1" THEN
    MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN
    EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC S2E_ST_D1_DERIV THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The time derivative of the local Laplacian of the slices (static metric). *)

let S2E_ST_LLAP_DERIV = prove
 (`!O (FF:real^(1,N)finite_sum->real^1) (G:real^N->real^N^N) t y.
     open O /\ smooth_map_on O FF /\ pastecart (lift t) y IN O
     ==> ((\s. llap G (\z. drop(FF(pastecart (lift s) z))) y) has_real_derivative
          llap G (\z. drop(frechet_derivative FF (at (pastecart (lift t) z))
                                              (pastecart (lift(&1)) (vec 0)))) y)
         (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LLAP_D2] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC S2E_ST_D2_DERIV THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC S2E_ST_D1_DERIV THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* A product rule in the form needed below. *)

let S2E_DERIV_CMULMUL = prove
 (`!a b a' b' at bt c t.
     (a has_real_derivative a') (atreal t) /\ (b has_real_derivative b') (atreal t) /\
     a t = at /\ b t = bt
     ==> ((\s. c * a s * b s) has_real_derivative c * (at * b' + a' * bt)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[]);;

(* The time derivative of the local inner product of gradients of slices. *)

let S2E_ST_LGINNER_DERIV = prove
 (`!O (FF:real^(1,N)finite_sum->real^1) PP (G:real^N->real^N^N) t y.
     open O /\ smooth_map_on O FF /\ smooth_map_on O PP /\ pastecart (lift t) y IN O
     ==> ((\s. rfa_lginner G (\z. drop(FF(pastecart (lift s) z)))
                             (\z. drop(PP(pastecart (lift s) z))) y) has_real_derivative
          rfa_lginner G (\z. drop(frechet_derivative FF (at (pastecart (lift t) z))
                                                    (pastecart (lift(&1)) (vec 0))))
                        (\z. drop(PP(pastecart (lift t) z))) y +
          rfa_lginner G (\z. drop(FF(pastecart (lift t) z)))
                        (\z. drop(frechet_derivative PP (at (pastecart (lift t) z))
                                                    (pastecart (lift(&1)) (vec 0)))) y)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b a' b'. rfa_lginner (G:real^N->real^N^N) a' b y + rfa_lginner G a b' y =
                sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                  matrix_inv(G y)$i$j *
                  (rfa_d1 a y (basis i) * rfa_d1 b' y (basis j) +
                   rfa_d1 a' y (basis i) * rfa_d1 b y (basis j))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[rfa_lginner; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[rfa_lginner] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC S2E_DERIV_CMULMUL THEN REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC S2E_ST_D1_DERIV THEN
  EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]);;

(* The local inner product of gradients of slices is smooth in space-time. *)

let S2E_ST_LGINNER_SMOOTH = prove
 (`!O W (FF:real^(1,N)finite_sum->real^1) PP (G:real^N->real^N^N).
     open O /\ metric_field W G /\ (!p. p IN O ==> sndcart p IN W) /\
     smooth_map_on O FF /\ smooth_map_on O PP
     ==> smooth_map_on O
           (\p. lift(rfa_lginner G (\z. drop(FF(pastecart (fstcart p) z)))
                                   (\z. drop(PP(pastecart (fstcart p) z))) (sndcart p)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(W:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\p. lift(sum(1..dimindex(:N)) (\i. drop(vsum(1..dimindex(:N)) (\j.
                 lift(matrix_inv((G:real^N->real^N^N)(sndcart p))$i$j *
                      drop(frechet_derivative FF (at p) (pastecart (vec 0) (basis i))) *
                      drop(frechet_derivative (PP:real^(1,N)finite_sum->real^1) (at p)
                                              (pastecart (vec 0) (basis j))))))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[rfa_lginner; DROP_VSUM; o_DEF; LIFT_DROP] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `pastecart (fstcart p) (sndcart p) IN (O:real^(1,N)finite_sum->bool)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
    MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `FF:real^(1,N)finite_sum->real^1`;
                   `fstcart(p:real^(1,N)finite_sum)`; `sndcart(p:real^(1,N)finite_sum)`;
                   `basis i:real^N`] S2E_ST_SLICE_D1) THEN
    MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `PP:real^(1,N)finite_sum->real^1`;
                   `fstcart(p:real^(1,N)finite_sum)`; `sndcart(p:real^(1,N)finite_sum)`;
                   `basis j:real^N`] S2E_ST_SLICE_D1) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `\p:real^(1,N)finite_sum. lift(matrix_inv((G:real^N->real^N^N)(sndcart p))$i$j)`;
                 `\p:real^(1,N)finite_sum.
                    lift(drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at p)
                                                 (pastecart (vec 0) (basis i))) *
                         drop(frechet_derivative (PP:real^(1,N)finite_sum->real^1) (at p)
                                                 (pastecart (vec 0) (basis j))))`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\p:real^(1,N)finite_sum. lift(matrix_inv((G:real^N->real^N^N)(sndcart p))$i$j)) =
                  (\z. lift(matrix_inv(G z)$i$j)) o (sndcart o (\p. p))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[RFA_GINV_ENTRY_SMOOTH] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]]);;

(* ------------------------------------------------------------------------- *)
(* Families of functions smooth in space-time up to time a                   *)
(* (pde_sfun_from).  Their slices are smooth; their time derivative         *)
(* rfu_tder (pc_rf_unique) is read off a chart extension; the time          *)
(* derivative of the Laplacian and of the inner product of gradients of the *)
(* slices (static metric) is computed through the derivative of the        *)
(* family; the inner product of two such families is again one; such a     *)
(* family is jointly continuous on [a,b) x M.                               *)
(* ------------------------------------------------------------------------- *)

let S2E_SFUN_EXT = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b (u:real->A->real) c.
     pde_sfun_from atlas a b u /\ c IN atlas
     ==> ?d FF. &0 < d /\
                smooth_map_on (interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                      ==> u t (chart_inv c y) = drop(FF(pastecart (lift t) y))`,
  REWRITE_TAC[pde_sfun_from] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let S2E_SFUN_SMOOTH = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (u:real->A->real) t.
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b u /\ a <= t /\ t < b
     ==> mfd_smooth atlas (\x. lift(u t x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. (FF:real^(1,N)finite_sum->real^1)(pastecart (lift t) y)` THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^1`; `a - d:real`; `b:real`;
                 `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`; `t:real`]
                RFA_SMOOTH_MAP_ON_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The time derivative rfu_tder in a chart. *)

let S2E_SFUN_TDER_CHART = prove
 (`!(u:real->A->real) (c:(A->bool)#(A->real^N)) a b d FF t y.
     &0 < d /\
     smooth_map_on (interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
     open(IMAGE (SND c) (FST c)) /\
     (!t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
            ==> u t (chart_inv c y) = drop(FF(pastecart (lift t) y))) /\
     a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
     ==> rfu_tder a u t (chart_inv c y) =
         drop(frechet_derivative FF (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\s. drop((FF:real^(1,N)finite_sum->real^1) (pastecart (lift s) y))`;
                        `b - t:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC GRGT_TIME_DERIVATIVE THEN
    EXISTS_TAC `interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* The time derivative of the Laplacian of the slices. *)

let S2E_SFUN_LAP_DERIV = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b (u:real->A->real) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     pde_sfun_from atlas a b u /\ a < t /\ t < b /\ x IN topspace top
     ==> ((\s. rfa_lap atlas g (u s) x) has_real_derivative
          rfa_lap atlas g (rfu_tder a u t) x) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_lap] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `W = IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) (x:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `O = interval(lift(a - d),lift b) PCROSS (W:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool) /\
                pastecart (lift t) (SND (c:(A->bool)#(A->real^N)) (x:A)) IN O`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llap (metric_local atlas c (g:A->real^N^N))
         (\y. rfu_tder a (u:real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y)) (SND c x) =
    llap (metric_local atlas c g)
         (\z. drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at (pastecart (lift t) z))
                                      (pastecart (lift(&1)) (vec 0)))) (SND c x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC S2E_SFUN_TDER_CHART THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                       (\z. drop((FF:real^(1,N)finite_sum->real^1)(pastecart (lift s) z))) (SND c x)` THEN
  EXISTS_TAC `min (t - a) (b - t):real` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC S2E_ST_LLAP_DERIV THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN ASM_REWRITE_TAC[]]);;

(* The time derivative of the inner product of gradients of the slices. *)

let S2E_SFUN_GINNER_DERIV = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b (u:real->A->real) v t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     pde_sfun_from atlas a b u /\ pde_sfun_from atlas a b v /\
     a < t /\ t < b /\ x IN topspace top
     ==> ((\s. s2e_ginner atlas g (u s) (v s) x) has_real_derivative
          s2e_ginner atlas g (rfu_tder a u t) (v t) x +
          s2e_ginner atlas g (u t) (rfu_tder a v t) x) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[s2e_ginner] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `v:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real` (X_CHOOSE_THEN `PP:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `W = IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) (x:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS (W:real^N->bool))
                  (FF:real^(1,N)finite_sum->real^1) /\
    smooth_map_on (interval(lift a,lift b) PCROSS W) (PP:real^(1,N)finite_sum->real^1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(a - d),lift b) PCROSS (W:real^N->bool)`;
      EXISTS_TAC `interval(lift(a - d'),lift b) PCROSS (W:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (W:real^N->bool)) /\
                pastecart (lift t) (SND (c:(A->bool)#(A->real^N)) (x:A)) IN
                interval(lift a,lift b) PCROSS W`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real->A->real hh:real^(1,N)finite_sum->real^1 dd.
      &0 < dd /\ smooth_map_on (interval(lift(a - dd),lift b) PCROSS W) hh /\
      (!t y. a <= t /\ t < b /\ y IN W ==> h t (chart_inv c y) = drop(hh(pastecart (lift t) y)))
      ==> (!s z. a <= s /\ s < b /\ z IN W
                 ==> h s (chart_inv (c:(A->bool)#(A->real^N)) z) = drop(hh(pastecart (lift s) z))) /\
          (!z. z IN W
               ==> rfu_tder a h t (chart_inv c z) =
                   drop(frechet_derivative hh (at (pastecart (lift t) z))
                                           (pastecart (lift(&1)) (vec 0))))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC S2E_SFUN_TDER_CHART THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `dd:real`] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W" THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`u:real->A->real`; `FF:real^(1,N)finite_sum->real^1`; `d:real`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real->A->real`; `PP:real^(1,N)finite_sum->real^1`; `d':real`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `rfa_lginner (metric_local atlas c (g:A->real^N^N))
      (\y. rfu_tder a (u:real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y))
      (\y. (v:real->A->real) t (chart_inv c y)) (SND c (x:A)) +
    rfa_lginner (metric_local atlas c g)
      (\y. u t (chart_inv c y)) (\y. rfu_tder a v t (chart_inv c y)) (SND c x) =
    rfa_lginner (metric_local atlas c g)
      (\z. drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at (pastecart (lift t) z))
                                   (pastecart (lift(&1)) (vec 0))))
      (\z. drop((PP:real^(1,N)finite_sum->real^1)(pastecart (lift t) z))) (SND c x) +
    rfa_lginner (metric_local atlas c g)
      (\z. drop(FF(pastecart (lift t) z)))
      (\z. drop(frechet_derivative PP (at (pastecart (lift t) z))
                                   (pastecart (lift(&1)) (vec 0)))) (SND c x)`
  SUBST1_TAC THENL
   [BINOP_TAC THEN MATCH_MP_TAC S2E_LGINNER_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. rfa_lginner (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (\z. drop((FF:real^(1,N)finite_sum->real^1)(pastecart (lift s) z)))
                    (\z. drop((PP:real^(1,N)finite_sum->real^1)(pastecart (lift s) z))) (SND c x)` THEN
  EXISTS_TAC `min (t - a) (b - t):real` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC S2E_LGINNER_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC S2E_ST_LGINNER_DERIV THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (W:real^N->bool)` THEN
    ASM_REWRITE_TAC[]]);;

(* The inner product of gradients of two families is again such a family. *)

let S2E_SFUN_GINNER = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b (u:real->A->real) v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     pde_sfun_from atlas a b u /\ pde_sfun_from atlas a b v
     ==> pde_sfun_from atlas a b (\t x. s2e_ginner atlas g (u t) (v t) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `v:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real` (X_CHOOSE_THEN `PP:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `W = IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  EXISTS_TAC `min d d':real` THEN
  EXISTS_TAC `\p. lift(rfa_lginner (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                     (\z. drop((FF:real^(1,N)finite_sum->real^1)(pastecart (fstcart p) z)))
                     (\z. drop((PP:real^(1,N)finite_sum->real^1)(pastecart (fstcart p) z)))
                     (sndcart p))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC S2E_ST_LGINNER_SMOOTH THEN EXISTS_TAC `W:real^N->bool` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
      EXPAND_TAC "W" THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - d),lift b) PCROSS (W:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - d'),lift b) PCROSS (W:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(u:real->A->real) t`; `(v:real->A->real) t`; `c:(A->bool)#(A->real^N)`;
                   `y:real^N`] S2E_GINNER_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC S2E_SFUN_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC S2E_LGINNER_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

(* Joint continuity on [a,b) x M, chart by chart and globally. *)

let S2E_SFUN_CHART_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (u:real->A->real) c.
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b u /\ c IN atlas
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                            (subtopology top (topspace top)))
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | a <= t /\ t < b})
                                               (subtopology top (topspace top))) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. u (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean
       {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
            sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)},
      euclideanreal)
     (\w. drop((FF:real^(1,N)finite_sum->real^1) w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\w. drop((FF:real^(1,N)finite_sum->real^1) w)) o
    (\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
                o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`t:real`; `SND (c:(A->bool)#(A->real^N)) (x:A)`]
      (ASSUME `!t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                     ==> (u:real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y) =
                         drop((FF:real^(1,N)finite_sum->real^1)(pastecart (lift t) y))`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (x:A)) = x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
               {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                    sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z))) =
    (\(x,y). pastecart x y) o (\z. lift(FST z),SND c (SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology) (euclidean:(real^N)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_LIFT; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                   `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                     `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                  IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP
                                 (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]]);;

let S2E_SFUN_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (u:real->A->real).
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b u
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. u (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A. (u:real->A->real) (FST z) (SND z)`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | a <= t /\ t < b})
                                   (subtopology top (topspace top))) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `subtopology (top:A topology) (topspace top)` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND; SUBTOPOLOGY_TOPSPACE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC S2E_SFUN_CHART_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_CROSS; IN_INTER;
                IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_ELIM_THM; IN_CROSS; IN_INTER; TOPSPACE_PROD_TOPOLOGY;
             TOPSPACE_SUBTOPOLOGY; FST; SND] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The scalar forced heat equation d/dt phi = Lap phi + psi,                 *)
(* phi(0) = 0, from the linear tensor system of the PDE layer               *)
(* (PDE_MLIN_HOLDS) with k = h = g, f = psi g, v(0) = 0: phi is the        *)
(* normalized trace (1/n) tr_g v (S2E_LTRHESS_TRACE).  First, traces under *)
(* congruence and in charts.                                                *)
(* ------------------------------------------------------------------------- *)

let S2E_SUMPROD_TRACE = prove
 (`!(A:real^N^N) B.
     sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * B$i$j)) =
     trace(A ** transp B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[TRANSP_COMPONENT]);;

let S2E_TRACE_CONGRUENCE = prove
 (`!(J:real^N^N) G V.
     invertible J /\ invertible G
     ==> trace(matrix_inv(transp J ** G ** J) ** transp(transp J ** V ** J)) =
         trace(matrix_inv G ** transp V)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `matrix_inv(transp J ** G ** J:real^N^N) =
                matrix_inv J ** matrix_inv G ** transp(matrix_inv J)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP;
                 MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^N^N. transp(matrix_inv(J:real^N^N)) ** transp J ** X = X`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT; MATRIX_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID]);;

let S2E_TRACE_SELF = prove
 (`!(G:real^N^N). invertible G /\ transp G = G
                  ==> trace(matrix_inv G ** transp G) = &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_INV; TRACE_I]);;

(* The trace tr_g h is the same in every chart. *)

let S2E_TRACE_CHART = prove
 (`!(top:A topology) atlas (g:A->real^N^N) h c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c)
     ==> trace(matrix_inv(metric_local atlas c g y) ** transp(metric_local atlas c h y)) =
         trace(matrix_inv(g(chart_inv c y)) ** transp(h(chart_inv c y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
                chart_inv c y IN topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y) /\
                invertible((g:A->real^N^N)(chart_inv c y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                     `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `chart_inv (c:(A->bool)#(A->real^N)) y`] METRIC_LOCAL_AT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`IMAGE (SND(chart_at atlas (chart_inv (c:(A->bool)#(A->real^N)) y)))
                            (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                          (chart_inv c y)))`;
                     `metric_local atlas (chart_at atlas (chart_inv (c:(A->bool)#(A->real^N)) y))
                                   (g:A->real^N^N)`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   (chart_inv (c:(A->bool)#(A->real^N)) y)) (chart_inv c y)`]
                    LRG_METRIC_INVERTIBLE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `invertible(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y)` THEN
  REWRITE_TAC[metric_local; INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2E_TRACE_CONGRUENCE THEN ASM_REWRITE_TAC[]);;

(* The trace in sum form, in a chart. *)

let S2E_TRACE_SUM_CHART = prove
 (`!(top:A topology) atlas (g:A->real^N^N) h c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c)
     ==> sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
           matrix_inv(g(chart_inv c y))$i$j * (h(chart_inv c y))$i$j)) =
         sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
           matrix_inv(metric_local atlas c g y)$i$j * (metric_local atlas c h y)$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[S2E_SUMPROD_TRACE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC S2E_TRACE_CHART THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* Slices of a family of tensor fields smooth up to time a. *)

let S2E_TFAM_SLICE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (v:real->A->real^N^N) t.
     smooth_manifold_atlas top atlas /\ pde_tfam_from atlas a b v /\ a <= t /\ t < b
     ==> mfd_tensor2_smooth atlas (v t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tensor2_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tfam_from (atlas:((A->bool)#(A->real^N))->bool) a b (v:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)(pastecart (lift t) y)` THEN
  ASM_SIMP_TAC[o_THM] THEN
  MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^(N,N)finite_prod`; `a - e:real`; `b:real`;
                 `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`; `t:real`]
                RFA_SMOOTH_MAP_ON_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The trace of a smooth tensor field is a smooth function. *)

let S2E_TRACE_SMOOTH = prove
 (`!(top:A topology) atlas (g:A->real^N^N) V.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_tensor2_smooth atlas V
     ==> mfd_smooth atlas (\x. lift(sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                                     matrix_inv(g x)$i$j * (V x)$i$j))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c))
                  (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. lift(sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                   matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y)$i$j *
                   (metric_local atlas c (V:A->real^N^N) y)$i$j)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC S2E_TRACE_SUM_CHART THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                 `\y:real^N. lift(matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N))
                                                (g:A->real^N^N) y)$i$j)`;
                 `\y:real^N. lift((metric_local atlas (c:(A->bool)#(A->real^N))
                                                (V:A->real^N^N) y)$i$j)`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_ML_G_ENTRY_SMOOTH THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  UNDISCH_TAC `mfd_tensor2_smooth (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N^N)` THEN
  REWRITE_TAC[mfd_tensor2_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The manifold Laplacian commutes with constant factors. *)

let S2E_LAP_CMUL = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f k x.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\ x IN topspace top
     ==> rfa_lap atlas g (\x. k * f x) x = k * rfa_lap atlas g f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_lap] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_LLAP_CMUL THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
  REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The g-trace of tr_g Hess_g V is the Laplacian of the g-trace of V. *)

let S2E_TRHESS_TRACE_LAP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) V x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_tensor2_smooth atlas V /\ x IN topspace top
     ==> sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
           matrix_inv(g x)$i$j * (pde_trhess atlas g g V x)$i$j)) =
         rfa_lap atlas g (\x. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                                matrix_inv(g x)$i$j * (V x)$i$j))) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[pde_trhess; rfa_lap] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at atlas (x:A)))
                        (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `metric_local atlas (chart_at atlas (x:A)) (V:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
                S2E_LTRHESS_TRACE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_tensor2_smooth (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N^N)` THEN
      REWRITE_TAC[mfd_tensor2_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC LLAP_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC S2E_TRACE_SUM_CHART THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* A multiple of the g-trace of a family of tensor fields smooth up to time *)
(* a is a family of functions smooth up to time a.                          *)

let S2E_TFAM_TRACE_SFUN = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b (v:real->A->real^N^N) k.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     pde_tfam_from atlas a b v
     ==> pde_sfun_from atlas a b
           (\t x. k * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                        matrix_inv(g x)$i$j * (v t x)$i$j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c))
                  (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pde_tfam_from (atlas:((A->bool)#(A->real^N))->bool) a b (v:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\p. lift(k * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                  matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                                          (sndcart p))$i$j *
                  (matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) p):real^N^N)$i$j)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SNDCART_PASTECART; MATRIFY_VECTORIZE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC S2E_TRACE_SUM_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `\p:real^(1,N)finite_sum.
                    lift(matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                                                 (sndcart p))$i$j)`;
                 `\p:real^(1,N)finite_sum.
                    lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) p):real^N^N)$i$j)`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\p:real^(1,N)finite_sum.
         lift(matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                                      (sndcart p))$i$j)) =
      (\y. lift(matrix_inv(metric_local atlas c g y)$i$j)) o (sndcart o (\p. p))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "O" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS; o_THM;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
      MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX]];
    SUBGOAL_THEN
     `(\p:real^(1,N)finite_sum.
         lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) p):real^N^N)$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o FF`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN EXPAND_TAC "O" THEN ASM_REWRITE_TAC[]]);;

(* The data: k = h = g, f = psi g, v(0) = 0. *)

let S2E_MLIN_SCALAR_DATA = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) psi b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(psi x)) /\ &0 < b
     ==> ?v. pde_mlin_sol (top,atlas) (&0) b (\t:real. g) g (\t x. psi x %% g x)
                          (\x. mat 0) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[PDE_MLIN_STATEMENT]
    (ISPECL [`{}:A->bool`; `{}:N->bool`] PDE_MLIN_HOLDS)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas (g:A->real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tensor2_smooth] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TFAM_CONST THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_MX_TFAM_CONST THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mfd_tensor2_smooth] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      metric_local atlas (c:(A->bool)#(A->real^N)) (\x. (psi:A->real) x %% (g:A->real^N^N) x) =
      (\y. drop(lift(psi(chart_inv c y))) % vectorize(metric_local atlas c g y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; metric_local; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
                  VECTORIZE_CMUL; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((psi:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_tensor2_smooth atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[mfd_tensor2_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[mfd_tensor2_smooth; metric_local; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO] THEN
    REWRITE_TAC[o_DEF; VECTORIZE_0; SMOOTH_MAP_ON_CONST]]);;

let S2E_SUM2_LMUL = prove
 (`!c (f:num->num->real) g m n.
     sum(1..m) (\i. sum(1..n) (\j. f i j * (c * g i j))) =
     c * sum(1..m) (\i. sum(1..n) (\j. f i j * g i j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* The scalar forced heat equation. *)

let S2E_FORCED_HEAT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) psi b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(psi x)) /\ &0 < b
     ==> ?phi. pde_sfun_from atlas (&0) b phi /\
               (!x. x IN topspace top ==> phi (&0) x = &0) /\
               (!t x. &0 < t /\ t < b /\ x IN topspace top
                      ==> ((\s. phi s x) has_real_derivative
                           rfa_lap atlas g (phi t) x + psi x) (atreal t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `psi:A->real`; `b:real`] S2E_MLIN_SCALAR_DATA) THEN
  ASM_REWRITE_TAC[pde_mlin_sol] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t x. inv(&(dimindex(:N))) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                      matrix_inv((g:A->real^N^N) x)$i$j * ((v:real->A->real^N^N) t x)$i$j))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC S2E_TFAM_TRACE_SFUN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT; REAL_MUL_RZERO; SUM_0];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `&0`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_lap atlas (g:A->real^N^N)
      (\x. inv(&(dimindex(:N))) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
             matrix_inv(g x)$i$j * ((v:real->A->real^N^N) t x)$i$j))) x + (psi:A->real) x =
    inv(&(dimindex(:N))) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      matrix_inv(g x)$i$j * (pde_trhess atlas g g (v t) x + psi x %% g x)$i$j))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `\x. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                          matrix_inv((g:A->real^N^N) x)$i$j * ((v:real->A->real^N^N) t x)$i$j))`;
                   `inv(&(dimindex(:N)))`; `x:A`] S2E_LAP_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_TRACE_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(v:real->A->real^N^N) t`; `x:A`] S2E_TRHESS_TRACE_LAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; REAL_ADD_LDISTRIB;
                SUM_ADD_NUMSEG; S2E_SUM2_LMUL] THEN
    SUBGOAL_THEN `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                    matrix_inv((g:A->real^N^N) x)$i$j * g x$i$j)) = &(dimindex(:N))`
    SUBST1_TAC THENL
     [REWRITE_TAC[S2E_SUMPROD_TRACE] THEN MATCH_MP_TAC S2E_TRACE_SELF THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `x:A`] METRIC_LOCAL_AT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at atlas (x:A)))
                                        (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)))
                                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(MESON[LRG_METRIC_INVERTIBLE]
          `!U G y. metric_field U (G:real^N->real^N^N) /\ y IN U ==> invertible(G y)`) THEN
        EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                          (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE];
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[metric_field]) THEN
        DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` o
                   CONJUNCT2 o CONJUNCT2) THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The heat flow w = d/dt phi of the forced flow and the decay               *)
(* of its gradient on a surface with R >= rho > 0, by the maximum principle *)
(* (RFA_MAXP_SCALAR) applied to |grad w|^2 with the Bochner inequality      *)
(* S2E_MBOCHNER2_GE:  d/dt |grad w|^2 <= Lap |grad w|^2 - rho |grad w|^2.    *)
(* ------------------------------------------------------------------------- *)

let S2E_SMOOTH_SNDCART = prove
 (`!s. open s ==> smooth_map_on s (sndcart:real^(M,N)finite_sum->real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `\p:real^(M,N)finite_sum. p`]
                SMOOTH_MAP_ON_SNDCART_OPEN) THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX; SMOOTH_MAP_ON_ID]);;

let S2E_SFUN_CONST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (f:A->real).
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x))
     ==> pde_sfun_from atlas a b (\t:real. f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `&1` THEN
  EXISTS_TAC `(\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) o
              (sndcart:real^(1,N)finite_sum->real^N)` THEN
  REWRITE_TAC[REAL_LT_01; o_THM; SNDCART_PASTECART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; S2E_SMOOTH_SNDCART] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The chart representatives of a family on the open time interval. *)

let S2E_SFUN_CHART_SMOOTH = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b (u:real->A->real) c.
     pde_sfun_from atlas a b u /\ c IN atlas /\ open(IMAGE (SND c) (FST c))
     ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                       (\z. lift(u (drop(fstcart z)) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `u:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `FF:real^(1,N)finite_sum->real^1` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART;
                SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop s`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* The inner product of gradients depends only on values on the manifold, *)
(* and |grad f|^2 >= 0.                                                     *)

let S2E_GINNER_EQ = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a a' b b' x.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!y. y IN topspace top ==> a y = a' y /\ b y = b' y)
     ==> s2e_ginner atlas g a b x = s2e_ginner atlas g a' b' x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2E_LGINNER_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(MATCH_MP OPEN_IN_SUBSET
    (ASSUME `open_in top (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))`)) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let S2E_GINNER_POS = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= s2e_ginner atlas g f f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner; S2E_LGINNER_DOT] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at atlas (x:A)))
                        (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`] S2E_GINV_PSD) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* A function continuous at 0 that vanishes on (0,b) vanishes at 0. *)

let S2E_CONT_ZERO_RIGHT = prove
 (`!h b. &0 < b /\ h real_continuous atreal (&0) /\ (!s. &0 < s /\ s < b ==> h s = &0)
         ==> h(&0) = &0`,
  REPEAT STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  UNDISCH_TAC `h real_continuous atreal (&0)` THEN REWRITE_TAC[real_continuous_atreal] THEN
  DISCH_THEN(MP_TAC o SPEC `abs((h:real->real)(&0))`) THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d b / &2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d b / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The time derivative w of the forced flow phi solves the heat equation    *)
(* with w(0) = psi, and w = Lap phi + psi for positive times.               *)

let S2E_HEAT_FROM_FORCED = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) psi phi b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(psi x)) /\ &0 < b /\
     pde_sfun_from atlas (&0) b phi /\
     (!x. x IN topspace top ==> phi (&0) x = &0) /\
     (!t x. &0 < t /\ t < b /\ x IN topspace top
            ==> ((\s. phi s x) has_real_derivative rfa_lap atlas g (phi t) x + psi x) (atreal t))
     ==> pde_sfun_from atlas (&0) b (rfu_tder (&0) phi) /\
         (!t x. &0 < t /\ t < b /\ x IN topspace top
                ==> rfu_tder (&0) phi t x = rfa_lap atlas g (phi t) x + psi x) /\
         (!x. x IN topspace top ==> rfu_tder (&0) phi (&0) x = psi x) /\
         (!t x. &0 < t /\ t < b /\ x IN topspace top
                ==> ((\s. rfu_tder (&0) phi s x) has_real_derivative
                     rfa_lap atlas g (rfu_tder (&0) phi t) x) (atreal t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) (&0) b
                  (rfu_tder (&0) (phi:real->A->real))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_SFUN_TDER THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. &0 < t /\ t < b /\ x IN topspace top
          ==> rfu_tder (&0) (phi:real->A->real) t x =
              rfa_lap atlas (g:A->real^N^N) (phi t) x + psi x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; HAS_REAL_DERIVATIVE_ATREAL_WITHIN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\s. rfa_lap atlas (g:A->real^N^N) ((phi:real->A->real) s) x + (psi:A->real) x` THEN
    EXISTS_TAC `min t (b - t):real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC S2E_SFUN_LAP_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[]]] THEN
  (* the initial value *)
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `b:real`;
                 `rfu_tder (&0) (phi:real->A->real)`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FW:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `b:real`;
                 `phi:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real` (X_CHOOSE_THEN `FP:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `W = IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) (x:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s < b
        ==> rfu_tder (&0) (phi:real->A->real) s x =
            drop((FW:real^(1,N)finite_sum->real^1)
                   (pastecart (lift s) (SND (c:(A->bool)#(A->real^N)) x)))`
  (LABEL_TAC "W0") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `SND (c:(A->bool)#(A->real^N)) (x:A)`] o
      check (fun th -> is_forall(concl th) && s2e_mentions "rfu_tder" th &&
                       s2e_mentions "chart_inv" th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s < b
        ==> rfa_lap atlas (g:A->real^N^N) ((phi:real->A->real) s) x =
            llap (metric_local atlas c g)
                 (\y. drop((FP:real^(1,N)finite_sum->real^1)(pastecart (lift s) y))) (SND c x)`
  (LABEL_TAC "P0") THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rfa_lap] THEN MATCH_MP_TAC LLAP_LOCAL THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. drop((FW:real^(1,N)finite_sum->real^1)(pastecart (lift s) (SND c (x:A)))) -
         (llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
               (\y. drop((FP:real^(1,N)finite_sum->real^1)(pastecart (lift s) y))) (SND c x) +
          (psi:A->real) x)`; `b:real`] S2E_CONT_ZERO_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `drop(frechet_derivative (FW:real^(1,N)finite_sum->real^1)
                      (at (pastecart (lift(&0)) (SND (c:(A->bool)#(A->real^N)) (x:A))))
                      (pastecart (lift(&1)) (vec 0)))` THEN
        MATCH_MP_TAC GRGT_TIME_DERIVATIVE THEN
        EXISTS_TAC `interval(lift(&0 - d),lift b) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                     LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                      (\z. drop(frechet_derivative (FP:real^(1,N)finite_sum->real^1)
                                  (at (pastecart (lift(&0)) z)) (pastecart (lift(&1)) (vec 0))))
                      (SND c (x:A))` THEN
        MATCH_MP_TAC S2E_ST_LLAP_DERIV THEN
        EXISTS_TAC `interval(lift(&0 - d'),lift b) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                     LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
      SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "W0" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "P0" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_0] THEN DISCH_TAC THEN
  USE_THEN "W0" (MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `l = &0 ==> l + p = p`) THEN
  USE_THEN "P0" (MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[rfa_lap] THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                           (\y. &0) (SND c (x:A))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[RFA_LLAP_CONST]] THEN
  MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(z:real^N) IN W` THEN EXPAND_TAC "W" THEN ASM_SIMP_TAC[]);;

(* The exponential barrier. *)

let S2E_EXP_BARRIER = prove
 (`!Q0 rho t. ((\s. Q0 * exp(--rho * s)) has_real_derivative --rho * (Q0 * exp(--rho * t)))
              (atreal t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV
    `((\s. Q0 * exp(--rho * s)) has_real_derivative f') (atreal t)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

(* Gradient decay for the heat equation on a surface with R >= rho. *)

let S2E_GRAD_DECAY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) w b rho Q0.
     smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ &0 < b /\
     (!x. x IN topspace top ==> rho <= mfd_scalar atlas g x) /\
     pde_sfun_from atlas (&0) b w /\
     (!t x. &0 < t /\ t < b /\ x IN topspace top
            ==> ((\s. w s x) has_real_derivative rfa_lap atlas g (w t) x) (atreal t)) /\
     (!x. x IN topspace top ==> s2e_ginner atlas g (w (&0)) (w (&0)) x <= Q0)
     ==> !t x. &0 <= t /\ t < b /\ x IN topspace top
               ==> s2e_ginner atlas g (w t) (w t) x <= Q0 * exp(--rho * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = \t x. s2e_ginner atlas (g:A->real^2^2) ((w:real->A->real) t) (w t) x` THEN
  SUBGOAL_THEN `pde_sfun_from (atlas:((A->bool)#(A->real^2))->bool) (&0) b (Q:real->A->real)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC S2E_SFUN_GINNER THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. &0 < t /\ t < b /\ x IN topspace top
          ==> rfu_tder (&0) (w:real->A->real) t x = rfa_lap atlas (g:A->real^2^2) (w t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; HAS_REAL_DERIVATIVE_ATREAL_WITHIN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `topspace(top:A topology)`; `&0`; `b:real`;
                 `\t:real. (g:A->real^2^2)`; `Q:real->A->real`; `\t:real u:real. --rho * u`;
                 `\t:real. Q0 * exp(--rho * t)`] RFA_MAXP_SCALAR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN MESON_TAC[]] THEN
  ASM_REWRITE_TAC[GSYM compact_space; OPEN_IN_TOPSPACE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`]
                        S2E_SFUN_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^2)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^2)) INTER topspace top = FST c` SUBST1_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^2)))`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC S2E_SFUN_CHART_SMOOTH THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^2))->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    EXISTS_TAC `&2 * s2e_ginner atlas (g:A->real^2^2) ((w:real->A->real) t)
                       (rfa_lap atlas g (w t)) x` THEN
    SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x. lift((w:real->A->real) t x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC S2E_SFUN_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `&0`; `b:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `&0`; `b:real`; `w:real->A->real`; `w:real->A->real`; `t:real`; `x:A`]
                    S2E_SFUN_GINNER_DERIV) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) net
                                      ==> (f has_real_derivative b) net`) THEN
      SUBGOAL_THEN
       `s2e_ginner atlas (g:A->real^2^2) (rfu_tder (&0) (w:real->A->real) t) (w t) x =
        s2e_ginner atlas g (rfa_lap atlas g (w t)) (w t) x /\
        s2e_ginner atlas g (w t) (rfu_tder (&0) w t) x =
        s2e_ginner atlas g (w t) (rfa_lap atlas g (w t)) x`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC S2E_GINNER_EQ THEN EXISTS_TAC `top:A topology` THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `rfa_lap atlas (g:A->real^2^2) ((w:real->A->real) t)`; `(w:real->A->real) t`;
                     `x:A`] S2E_GINNER_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      DISCH_THEN(K ALL_TAC) THEN EXPAND_TAC "Q" THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `(w:real->A->real) t`; `x:A`] S2E_MBOCHNER2_GE) THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `(w:real->A->real) t`; `x:A`] S2E_GINNER_POS) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `rfa_lap atlas (g:A->real^2^2) ((w:real->A->real) t) x` REAL_LE_POW_2) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
        s2e_mentions "mfd_scalar" th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `rho * s2e_ginner atlas (g:A->real^2^2) ((w:real->A->real) t) (w t) x <=
                    mfd_scalar atlas g x * s2e_ginner atlas g (w t) (w t) x` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    REPEAT STRIP_TAC THEN EXISTS_TAC `abs rho` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[S2E_EXP_BARRIER];
    EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* The approximate Poisson equation.  On a closed connected                  *)
(* surface with R >= rho > 0, for smooth psi of mean zero and every e > 0   *)
(* there is a smooth u with |Lap u - psi| <= e: u = -phi(S) for the forced  *)
(* flow phi, since Lap phi(S) = w(S) - psi and |w(S)| is small by the       *)
(* gradient decay, the oscillation bound and int w(S) = 0.                  *)
(* ------------------------------------------------------------------------- *)

(* Smooth functions on a manifold are continuous. *)

let S2E_MFD_SMOOTH_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) f.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x))
     ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`;
                 `\t:real. (f:A->real)`] S2E_SFUN_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_SFUN_CONST THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | &0 <= t /\ t < &1}`;
                 `top:A topology`;
                 `\t:real x:A. (f:A->real) x`; `&0`] RFA_SLICE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  IN_ELIM_THM; ETA_AX; REAL_LE_REFL; REAL_LT_01]);;

(* The integral of a Laplacian vanishes; the volume is positive. *)

let S2E_INT_LAP_ZERO = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(f x))
     ==> mfd_has_integral (top,atlas) g (\x. rfa_lap atlas g f x) (topspace top) (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\x:A. &1`; `f:A->real`] S2E_IBP) THEN
  ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST; S2E_GINNER_CONST; REAL_MUL_LID; REAL_ADD_RID]);;

let S2E_INT_ONE_POS = prove
 (`!(top:A topology) atlas (g:A->real^N^N) x0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ x0 IN topspace top
     ==> mfd_has_integral (top,atlas) g (\x. &1) (topspace top)
                          (mfd_integral (top,atlas) g (topspace top) (\x. &1)) /\
         &0 < mfd_integral (top,atlas) g (topspace top) (\x. &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_has_integral (top,atlas) (g:A->real^N^N) (\x:A. &1) (topspace top)
                  (mfd_integral (top,atlas) g (topspace top) (\x. &1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN
    ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = mfd_integral (top,atlas) (g:A->real^N^N) (topspace top) (\x:A. &1)` THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `g:A->real^N^N`; `\x:A. &0 * &1`; `\x:A. &1`;
                         `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `\x:A. &1`; `topspace(top:A topology)`; `V:real`; `&0`]
                    MFD_HAS_INTEGRAL_CMUL) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\x:A. &1`; `x0:A`] RFU_MFD_INTEGRAL_ZERO_IMP) THEN
  ASM_REWRITE_TAC[REAL_POS; CONTINUOUS_ON_CONST] THEN REAL_ARITH_TAC);;

(* A function of mean zero with oscillation at most B is bounded by B. *)

let S2E_MEAN_ZERO_BOUND = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f B.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g f (topspace top) (&0) /\
     (!x y. x IN topspace top /\ y IN topspace top ==> abs(f x - f y) <= B)
     ==> !x. x IN topspace top ==> abs(f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] S2E_INT_ONE_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = mfd_integral (top,atlas) (g:A->real^N^N) (topspace top) (\x:A. &1)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!m. mfd_has_integral (top,atlas) (g:A->real^N^N) (\x:A. m * &1) (topspace top)
                                     (m * V)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `abs x <= B <=> ~(B < x) /\ ~(x < --B)`] THEN CONJ_TAC THEN
  DISCH_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\y:A. ((f:A->real) x - B) * &1`; `f:A->real`;
                   `topspace(top:A topology)`; `((f:A->real) x - B) * V`; `&0`]
                  MFD_HAS_INTEGRAL_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x <= &0 ==> F`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `\y:A. ((f:A->real) x + B) * &1`;
                   `topspace(top:A topology)`; `&0`; `((f:A->real) x + B) * V`]
                  MFD_HAS_INTEGRAL_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < --x ==> &0 <= x ==> F`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]]);;

(* Exponential smallness. *)

let S2E_EXP_SMALL = prove
 (`!C e rho. &0 <= C /\ &0 < e /\ &0 < rho
             ==> ?S. &0 < S /\ C * exp(--rho * S) <= e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `C / (e * rho) + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S = C / (e * rho) + &1` THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; GSYM real_div] THEN
  SIMP_TAC[REAL_EXP_POS_LT; REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPEC `rho * S` REAL_EXP_LE_X) THEN
  SUBGOAL_THEN `e * (&1 + rho * S) = e + C + e * rho` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    SUBGOAL_THEN `~(e = &0) /\ ~(rho = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * rho` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * (&1 + rho * S)` THEN
  CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The approximate Poisson equation. *)

let S2E_APPROX_POISSON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) psi rho e.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     connected_space top /\ riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(psi x)) /\
     mfd_has_integral (top,atlas) g psi (topspace top) (&0) /\
     &0 < rho /\ (!x. x IN topspace top ==> rho <= mfd_scalar atlas g x) /\ &0 < e
     ==> ?u. mfd_smooth atlas (\x. lift(u x)) /\
             !x. x IN topspace top ==> abs(rfa_lap atlas g u x - psi x) <= e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?H0. &0 <= H0 /\
                     !x. x IN topspace top ==> s2e_ginner atlas (g:A->real^2^2) psi psi x <= H0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `\x:A. s2e_ginner atlas (g:A->real^2^2) psi psi x`]
                  S2E_COMPACT_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`]
                          S2E_MFD_SMOOTH_CONTINUOUS) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_GINNER_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`]
                S2E_OSC_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OSC"))) THEN
  MP_TAC(ISPECL [`L pow 2 * H0`; `e pow 2`; `rho:real`] S2E_EXP_SMALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `psi:A->real`; `S + &1`] S2E_FORCED_HEAT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real->A->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `psi:A->real`; `phi:real->A->real`; `S + &1`] S2E_HEAT_FROM_FORCED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = rfu_tder (&0) (phi:real->A->real)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `w:real->A->real`; `S + &1`; `rho:real`; `H0:real`] S2E_GRAD_DECAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s2e_ginner atlas (g:A->real^2^2) ((w:real->A->real) (&0)) (w (&0)) x =
                  s2e_ginner atlas g psi psi x` SUBST1_TAC THENL
     [MATCH_MP_TAC S2E_GINNER_EQ THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN(ASSUME_TAC o SPEC `S:real`)] THEN
  ABBREV_TAC `K = sqrt(H0 * exp(--rho * S))` THEN
  SUBGOAL_THEN `&0 <= K /\ K pow 2 = H0 * exp(--rho * S)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `&0 <= H0 * exp(--rho * S)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `L * K <= e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_EQ; REAL_POW_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x. lift((phi:real->A->real) S x)) /\
                mfd_smooth atlas (\x. lift((w:real->A->real) S x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC S2E_SFUN_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `&0`; `S + &1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> abs((w:real->A->real) S x - w S y) <= L * K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "OSC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (fun th -> is_forall(concl th) &&
      s2e_mentions "exp" th)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (w:real->A->real) S x =
                    rfa_lap atlas (g:A->real^2^2) ((phi:real->A->real) S) x + psi x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_integral (top,atlas) (g:A->real^2^2) ((w:real->A->real) S)
                                 (topspace top) (&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `\x:A. rfa_lap atlas (g:A->real^2^2) ((phi:real->A->real) S) x`;
                   `psi:A->real`; `topspace(top:A topology)`; `&0`; `&0`]
                  MFD_HAS_INTEGRAL_ADD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_INT_LAP_ZERO THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `(w:real->A->real) S`; `L * K:real`] S2E_MEAN_ZERO_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `\x. --(&1) * (phi:real->A->real) S x` THEN CONJ_TAC THENL
   [REWRITE_TAC[] THEN MATCH_MP_TAC S2E_MFD_SMOOTH_CMUL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `(phi:real->A->real) S`; `--(&1)`; `x:A`] S2E_LAP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `abs((w:real->A->real) S x) <= L * K /\
                w S x = rfa_lap atlas (g:A->real^2^2) ((phi:real->A->real) S) x + psi x`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `L * K <= e` THEN UNDISCH_TAC `abs((w:real->A->real) S x) <= L * K` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hamilton's inequality on a closed connected surface with                  *)
(* R > 0 and int (R - r) = 0:  int (R - r)^2 <= int |grad R|^2 / R.         *)
(* Duality with the approximate potential u (S2E_APPROX_POISSON), the       *)
(* integrated Bochner inequality S2E_IBOCHNER2 and Cauchy-Schwarz.          *)
(* ------------------------------------------------------------------------- *)

let S2E_AMGM_CS = prove
 (`!A B C R. &0 <= A /\ &0 <= B /\ &0 < R /\ C pow 2 <= A * B
             ==> --C <= (A / R + R * B) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C pow 2 <= (A / R) * (R * B)` MP_TAC THENL
   [SUBGOAL_THEN `(A / R) * (R * B) = A * B` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A / R /\ &0 <= R * B` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SPEC_TAC(`A / R`,`a:real`) THEN SPEC_TAC(`R * B`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * b:real` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH]; ALL_TAC] THEN
  MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* Subtracting a constant does not change the gradient. *)

let S2E_GINNER_SUB_CONST = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f r b x.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\ x IN topspace top
     ==> s2e_ginner atlas g (\x. f x - r) b x = s2e_ginner atlas g f b x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner; rfa_lginner] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y) - r)
               (SND(chart_at atlas x) (x:A)) h =
        rfa_d1 (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) h`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  MP_TAC(ISPECL [`\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y)`;
                 `\y:real^N. --r`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                 `h:real^N`] RFA_D1_ADD_AT) THEN
  REWRITE_TAC[RFA_D1_CONST; REAL_ADD_RID; DIFFERENTIABLE_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
  REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Quotients of smooth functions. *)

let S2E_MFD_SMOOTH_DIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) f h.
     smooth_manifold_atlas top atlas /\
     mfd_smooth atlas (\x. lift(f x)) /\ mfd_smooth atlas (\x. lift(h x)) /\
     (!x. x IN topspace top ==> ~(h x = &0))
     ==> mfd_smooth atlas (\x. lift(f x / h x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                 `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`;
                 `\y. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`]
                SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((h:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* A limiting argument. *)

let S2E_LE_LIMIT = prove
 (`!P X V. &0 <= V /\ (!e. &0 < e ==> P <= X + e * V) ==> P <= X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(P - X) / (V + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_ARITH `&0 <= V ==> &0 < V + &1`] THEN
  SUBGOAL_THEN `(P - X) / (V + &1) * V < P - X` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= V ==> &0 < V + &1`; REAL_LT_LDIV_EQ;
                 REAL_FIELD `&0 < V + &1 ==> (a / (V + &1)) * V = (a * V) / (V + &1)`] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The pointwise inequality behind Hamilton's inequality. *)

let S2E_HAM_POINTWISE = prove
 (`!(top:A topology) atlas (g:A->real^N^N) R u r x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(R x)) /\ x IN topspace top /\ &0 < R x
     ==> (R x - r) pow 2 <=
         ((R x - r) * rfa_lap atlas g u x + s2e_ginner atlas g (\x. R x - r) u x) +
         (s2e_ginner atlas g R R x / R x) / &2 + (R x * s2e_ginner atlas g u u x) / &2 +
         (R x - r) * ((R x - r) - rfa_lap atlas g u x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `R:A->real`; `r:real`; `u:A->real`; `x:A`] S2E_GINNER_SUB_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s2e_ginner atlas (g:A->real^N^N) R R x`; `s2e_ginner atlas (g:A->real^N^N) u u x`;
                 `s2e_ginner atlas (g:A->real^N^N) R u x`; `(R:A->real) x`] S2E_AMGM_CS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC S2E_GINNER_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2E_GINNER_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2E_GINNER_CS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let S2E_MFD_SMOOTH_SUB = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) f h.
     smooth_manifold_atlas top atlas /\
     mfd_smooth atlas (\x. lift(f x)) /\ mfd_smooth atlas (\x. lift(h x))
     ==> mfd_smooth atlas (\x. lift(f x - h x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF; LIFT_SUB] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[MFDM_CHART]);;

(* One step: with an approximate potential u, |Lap u - (R - r)| <= e,      *)
(*   int (R - r)^2 <= int |grad R|^2 / R + e^2 vol.                          *)

let S2E_HAM_STEP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) r u e.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x) /\
     mfd_smooth atlas (\x. lift(u x)) /\
     (!x. x IN topspace top
          ==> abs(rfa_lap atlas g u x - (mfd_scalar atlas g x - r)) <= e)
     ==> mfd_integral (top,atlas) g (topspace top) (\x. (mfd_scalar atlas g x - r) pow 2) <=
         mfd_integral (top,atlas) g (topspace top)
           (\x. s2e_ginner atlas g (mfd_scalar atlas g) (mfd_scalar atlas g) x /
                mfd_scalar atlas g x) +
         e pow 2 * mfd_integral (top,atlas) g (topspace top) (\x. &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_smooth atlas (\x:A. lift(mfd_scalar atlas (g:A->real^2^2) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `u:A->real`] S2E_IBOCHNER2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `\x:A. mfd_scalar atlas (g:A->real^2^2) x - r`; `u:A->real`] S2E_IBP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_MFD_SMOOTH_SUB THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^2^2)` THEN
  SUBGOAL_THEN
   `!h:A->real. mfd_smooth atlas (\x. lift(h x))
                ==> mfd_has_integral (top,atlas) (g:A->real^2^2) h (topspace top)
                                     (mfd_integral (top,atlas) g (topspace top) h)`
  (LABEL_TAC "INT") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x:A. lift((R:A->real) x)) /\
    mfd_smooth atlas (\x:A. lift((R:A->real) x - r)) /\
    mfd_smooth atlas (\x:A. lift(rfa_lap atlas (g:A->real^2^2) u x)) /\
    mfd_smooth atlas (\x:A. lift(s2e_ginner atlas (g:A->real^2^2) R R x)) /\
    mfd_smooth atlas (\x:A. lift(s2e_ginner atlas (g:A->real^2^2) u u x))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC S2E_MFD_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
      MATCH_MP_TAC S2E_LAP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2E_GINNER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[ETA_AX]);
      MATCH_MP_TAC S2E_GINNER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `P = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. ((R:A->real) x - r) pow 2)` THEN
  ABBREV_TAC `X = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. s2e_ginner atlas g R R x / (R:A->real) x)` THEN
  ABBREV_TAC `Y = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. (R:A->real) x * s2e_ginner atlas g u u x)` THEN
  ABBREV_TAC `W = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. rfa_lap atlas g u x pow 2)` THEN
  ABBREV_TAC `Z = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. ((R:A->real) x - r) * ((R x - r) - rfa_lap atlas g u x))` THEN
  ABBREV_TAC `E = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                    (\x:A. (((R:A->real) x - r) - rfa_lap atlas g u x) pow 2)` THEN
  ABBREV_TAC `V = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top) (\x:A. &1)` THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^2^2) (\x:A. ((R:A->real) x - r) pow 2)
                     (topspace top) P /\
    mfd_has_integral (top,atlas) g (\x:A. s2e_ginner atlas g R R x / (R:A->real) x)
                     (topspace top) X /\
    mfd_has_integral (top,atlas) g (\x:A. (R:A->real) x * s2e_ginner atlas g u u x)
                     (topspace top) Y /\
    mfd_has_integral (top,atlas) g (\x:A. rfa_lap atlas g u x pow 2) (topspace top) W /\
    mfd_has_integral (top,atlas) g
      (\x:A. ((R:A->real) x - r) * ((R x - r) - rfa_lap atlas g u x)) (topspace top) Z /\
    mfd_has_integral (top,atlas) g
      (\x:A. (((R:A->real) x - r) - rfa_lap atlas g u x) pow 2) (topspace top) E /\
    mfd_has_integral (top,atlas) g (\x:A. &1) (topspace top) V`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "X"; "Y"; "W"; "Z"; "E"; "V"] THEN
    REPEAT CONJ_TAC THEN USE_THEN "INT" MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_POW_2; S2E_MFD_SMOOTH_CONST] THEN
    TRY(MATCH_MP_TAC S2E_MFD_SMOOTH_DIV THEN EXISTS_TAC `top:A topology` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN NO_TAC) THEN
    MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC S2E_MFD_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the integrated pointwise inequality *)
  SUBGOAL_THEN `P <= &0 + inv(&2) * X + inv(&2) * Y + Z` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
      `\x:A. ((R:A->real) x - r) pow 2`;
      `\x:A. (((R:A->real) x - r) * rfa_lap atlas (g:A->real^2^2) u x +
               s2e_ginner atlas g (\x. R x - r) u x) +
              inv(&2) * (s2e_ginner atlas g R R x / R x) +
              inv(&2) * (R x * s2e_ginner atlas g u u x) +
              (R x - r) * ((R x - r) - rfa_lap atlas g u x)`;
      `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN TRY CONJ_TAC) THEN
      TRY(MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `R:A->real`; `u:A->real`; `r:real`; `x:A`] S2E_HAM_POINTWISE) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* int (Lap u)^2 = P - 2 Z + E *)
  SUBGOAL_THEN `W = P - &2 * Z + E` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                         `g:A->real^2^2`; `\x:A. rfa_lap atlas (g:A->real^2^2) u x pow 2`;
                         `topspace(top:A topology)`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mfd_has_integral (top,atlas) (g:A->real^2^2)
        (\x:A. (((R:A->real) x - r) pow 2 -
                &2 * ((R x - r) * ((R x - r) - rfa_lap atlas g u x))) +
               ((R x - r) - rfa_lap atlas g u x) pow 2)
        (topspace top) ((P - &2 * Z) + E)`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_HAS_INTEGRAL_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  (* int err^2 <= e^2 vol *)
  SUBGOAL_THEN `E <= e pow 2 * V` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                         `g:A->real^2^2`;
                         `\x:A. (((R:A->real) x - r) - rfa_lap atlas (g:A->real^2^2) u x) pow 2`;
                         `\x:A. e pow 2 * &1`; `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      s2e_mentions "real_abs" th)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Hamilton's inequality. *)

let S2E_HAMILTON_INEQ = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     connected_space top /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x) /\
     mfd_has_integral (top,atlas) g (\x. mfd_scalar atlas g x - r) (topspace top) (&0)
     ==> mfd_integral (top,atlas) g (topspace top) (\x. (mfd_scalar atlas g x - r) pow 2) <=
         mfd_integral (top,atlas) g (topspace top)
           (\x. s2e_ginner atlas g (mfd_scalar atlas g) (mfd_scalar atlas g) x /
                mfd_scalar atlas g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_smooth atlas (\x:A. lift(mfd_scalar atlas (g:A->real^2^2) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rho. &0 < rho /\
                      !x. x IN topspace top ==> rho <= mfd_scalar atlas (g:A->real^2^2) x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `\x:A. inv(mfd_scalar atlas (g:A->real^2^2) x)`]
                  S2E_COMPACT_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_INV THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`]
                            S2E_MFD_SMOOTH_CONTINUOUS) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
      DISCH_THEN(X_CHOOSE_THEN `B:real` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
      EXISTS_TAC `inv B` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^2^2) x /\
                    abs(inv(mfd_scalar atlas g x)) <= B` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC S2E_LE_LIMIT THEN
  EXISTS_TAC `mfd_integral (top,atlas) (g:A->real^2^2) (topspace top) (\x:A. &1)` THEN
  SUBGOAL_THEN `mfd_has_integral (top,atlas) (g:A->real^2^2) (\x:A. &1) (topspace top)
                  (mfd_integral (top,atlas) g (topspace top) (\x. &1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN
    ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                         `g:A->real^2^2`; `\x:A. &0 * &1`; `\x:A. &1`;
                         `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                     `g:A->real^2^2`; `\x:A. &1`; `topspace(top:A topology)`;
                     `mfd_integral (top,atlas) (g:A->real^2^2) (topspace top) (\x:A. &1)`; `&0`]
                    MFD_HAS_INTEGRAL_CMUL) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `\x:A. mfd_scalar atlas (g:A->real^2^2) x - r`; `rho:real`; `sqrt e`]
                S2E_APPROX_POISSON) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC S2E_MFD_SMOOTH_SUB THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
    DISCH_THEN(X_CHOOSE_THEN `u:A->real` (STRIP_ASSUME_TAC o BETA_RULE))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `r:real`; `u:A->real`; `sqrt e`] S2E_HAM_STEP) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]);;

