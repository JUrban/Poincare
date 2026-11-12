(* ========================================================================= *)
(* pc_geo_dist: exponential map and distance.  Lengths of curves in a       *)
(* normal ball bound the radial distance (via the Gauss lemma), geodesic    *)
(* balls are metric balls (MFD_EXP_DIST, MFD_EXP_BALL), the equality case   *)
(* (MFD_EXP_DIST_EQUALITY), local minimization, normal charts, minimizing   *)
(* curves are geodesics.  The theorems named above belong to the geodesics   *)
(* API pc_geo_iface.                                                         *)
(*                                                                           *)
(* Cauchy-Schwarz for a symmetric positive semidefinite form.                *)
(* ========================================================================= *)

needs "src/pc_geo_gauss.ml";;
needs "src/pc_grg_dist2.ml";;

prioritize_real();;
type_invention_error := true;;

let GEOD_DISCRIMINANT = prove
 (`!A B C. &0 <= A /\ (!x. &0 <= x pow 2 * A + &2 * x * C + B)
           ==> C pow 2 <= A * B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `A = &0` THENL
   [ASM_CASES_TAC `C = &0` THENL
     [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `--(B + &1) / (&2 * C)`) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `~(C = &0) ==> &2 * (--(B + &1) / (&2 * C)) * C = --(B + &1)`] THEN
      REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `--C / A`) THEN
    SUBGOAL_THEN `(--C / A) pow 2 * A + &2 * (--C / A) * C + B = B - C pow 2 / A`
    SUBST1_TAC THENL [UNDISCH_TAC `~(A = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let GEOD_METRIC_CS = prove
 (`!(G:real^N^N) a b.
        (!u v. u dot (G ** v) = v dot (G ** u)) /\ (!u. &0 <= u dot (G ** u))
        ==> abs(a dot (G ** b)) <= sqrt(a dot (G ** a)) * sqrt(b dot (G ** b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a dot ((G:real^N^N) ** b)) pow 2 <= (a dot (G ** a)) * (b dot (G ** b))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOD_DISCRIMINANT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t % (a:real^N) + b` o check (fun th ->
      can (term_match [] `!u:real^N. &0 <= u dot ((G:real^N^N) ** u)`) (concl th))) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD;
                DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SPECL [`b:real^N`; `a:real^N`] th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
  ASM_SIMP_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Real-variable tools for the radial estimate.                              *)
(* ========================================================================= *)

(* If sqrt(B + e^2) - sqrt(A + e^2) <= L for all e > 0 then                *)
(* sqrt B - sqrt A <= L.                                                     *)

let GEOD_EPS_LIMIT = prove
 (`!A B L. &0 <= A /\ &0 <= B /\
           (!e. &0 < e ==> sqrt(B + e pow 2) - sqrt(A + e pow 2) <= L)
           ==> sqrt B - sqrt A <= L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(sqrt B - sqrt A - L) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e = (sqrt B - sqrt A - L) / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt B <= sqrt(B + e pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt A` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(A + e pow 2) <= sqrt A + e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(x + y) pow 2 = x pow 2 + &2 * x * y + y pow 2`] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN
    SUBGOAL_THEN `&0 <= sqrt A * e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Fundamental theorem of calculus as an upper bound. *)

let GEOD_FTC_BOUND = prove
 (`!f f' h a b.
        a <= b /\ h real_integrable_on real_interval[a,b] /\
        (!t. t IN real_interval[a,b]
             ==> (f has_real_derivative f' t) (atreal t within real_interval[a,b]) /\
                 f' t <= h t)
        ==> f b - f a <= real_integral (real_interval[a,b]) h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC [`f':real->real`; `h:real->real`; `real_interval[a,b]`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL];
    ASM_SIMP_TAC[]]);;

(* The pointwise bound used with the derivative of sqrt(q + e^2). *)

let GEOD_RATIO_BOUND = prove
 (`!X Q S h. X <= Q * h /\ &0 <= h /\ &0 <= Q /\ Q <= S /\ &0 < S
             ==> inv(&2 * S) * (&2 * X) <= h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(&2 * S) * (&2 * X) = X / S` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < S` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * h` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* Derivative of a quadratic form along a curve, as a real function. *)

let GEOD_QUAD_REAL_DERIV = prove
 (`!(A:real^N^N) (c:real->real^N) c' t s.
        (!u v. u dot (A ** v) = v dot (A ** u)) /\
        ((\u. c(drop u)) has_vector_derivative c') (at (lift t) within IMAGE lift s)
        ==> ((\t. c t dot (A ** c t)) has_real_derivative
             (&2 * (c t dot (A ** c')))) (atreal t within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  MP_TAC(ISPECL [`\x y:real^N. lift(x dot ((A:real^N^N) ** y))`;
                 `\u. (c:real->real^N)(drop u)`; `\u. (c:real->real^N)(drop u)`;
                 `c':real^N`; `c':real^N`; `lift t`; `IMAGE lift (s:real->bool)`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
  REWRITE_TAC[GEOG_DOT_BILINEAR; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `f = f' /\ (a:real^1) = b
    ==> (f has_vector_derivative a) net ==> (f' has_vector_derivative b) net`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[SPECL [`c':real^N`; `(c:real->real^N) t`] th]) THEN
  REAL_ARITH_TAC);;

(* Derivative of sqrt(q + e^2). *)

let GEOD_SQRT_EPS_DERIV = prove
 (`!q q' t s e.
        &0 <= q t /\ &0 < e /\ (q has_real_derivative q') (atreal t within s)
        ==> ((\t. sqrt(q t + e pow 2)) has_real_derivative
             (inv(&2 * sqrt(q t + e pow 2)) * q')) (atreal t within s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. sqrt((q:real->real) t + e pow 2)) = sqrt o (\t. q t + e pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`q:real->real`; `q':real`; `\t:real. e pow 2`; `&0`;
                   `atreal t within s`] HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_RID];
    REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_POW_LT]]);;

(* ========================================================================= *)
(* The radial estimate.  For a C^1 curve c in a normal ball                  *)
(* (in exponential coordinates) the length of exp o c is at least the        *)
(* change of |c|_x, by the Gauss lemma and Cauchy-Schwarz for g.             *)
(* ========================================================================= *)

(* C^1 curves in an open set of real^N, with the identity chart. *)

let GEOD_OPEN_C1_HAS_VD = prove
 (`!s (c:real->real^N) a b t.
        open s /\ mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\
        t IN real_interval[a,b]
        ==> c t IN s /\
            ((\u. c(drop u)) has_vector_derivative
             vector_derivative (\u. c(drop u)) (at (lift t) within interval[lift a,lift b]))
            (at (lift t) within interval[lift a,lift b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `c:real->real^N`;
                   `a:real`; `b:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^N->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool,\x:real^N. x) IN open_set_atlas s` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                 `open_set_atlas (s:real^N->bool)`; `c:real->real^N`;
                 `a:real`; `b:real`; `(s:real^N->bool,\x:real^N. x)`; `t:real`]
    GRGD_C1_CHART_HAS_VD) THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* Velocity of e o c for a smooth parametrization e. *)

let GEOD_PARAM_VELOCITY = prove
 (`!top atlas s (e:real^N->A) (c:real->real^N) a b t.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\ a < b /\
        t IN real_interval[a,b]
        ==> linear(mfd_differential (open_set_atlas (:real^N)) atlas e (c t)) /\
            mfd_velocity atlas (e o c) a b t =
            mfd_differential (open_set_atlas (:real^N)) atlas e (c t)
              (vector_derivative (\u. c(drop u)) (at (lift t) within interval[lift a,lift b]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^N))
                 (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)` THEN
    REWRITE_TAC[mfd_param; mfd_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real->real^N`; `a:real`; `b:real`; `t:real`]
    GEOD_OPEN_C1_HAS_VD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w = vector_derivative (\u. (c:real->real^N)(drop u))
                    (at (lift t) within interval[lift a,lift b])` THEN
  SUBGOAL_THEN `(e:real^N->A)((c:real->real^N) t) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)((c:real->real^N) t)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `e:real^N->A`; `s:real^N->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                           ((e:real^N->A)((c:real->real^N) t))`] GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                      ((e:real^N->A)((c:real->real^N) t))) (e y))
    differentiable (at (c t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `{u | u IN s /\
           (e:real^N->A) u IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                           ((e:real^N->A)((c:real->real^N) t)))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN
  REWRITE_TAC[mfd_velocity; o_THM] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  SUBGOAL_THEN
   `(\u. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                      ((e:real^N->A)((c:real->real^N) t))) (e(c(drop u)))) =
    (\y. SND(chart_at atlas (e(c t))) (e y)) o (\u. c(drop u))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* Pointwise: |<c, c'>_x| <= |c|_x |(exp o c)'|_g. *)

let GEOD_RADIAL_POINTWISE = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (c:real->real^N) a b t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\
        mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                      open_set_atlas (mfd_tball g x r)) c a b /\
        a < b /\ t IN real_interval[a,b]
        ==> abs(c t dot (g x ** vector_derivative (\u. c(drop u))
                                   (at (lift t) within interval[lift a,lift b])))
            <= mfd_tnorm g x (c t) *
               mfd_speed atlas g (mfd_exp (top,atlas) g x o c) a b t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`mfd_tball (g:A->real^N^N) x r`; `c:real->real^N`;
                 `a:real`; `b:real`; `t:real`] GEOD_OPEN_C1_HAS_VD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`;
                 `c:real->real^N`; `a:real`; `b:real`; `t:real`] GEOD_PARAM_VELOCITY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN
                mfd_exp_dom (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                  ((c:real->real^N) t) IN topspace top`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = vector_derivative (\u. (c:real->real^N)(drop u))
                    (at (lift t) within interval[lift a,lift b])` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) ((c:real->real^N) t)` THEN
  ABBREV_TAC `p = mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                    ((c:real->real^N) t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`; `w:real^N`]
    MFD_GAUSS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`; `(c:real->real^N) t`]
    MFD_GAUSS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `abs((D:real^N->real^N)((c:real->real^N) t) dot ((g:A->real^N^N) p ** D w)) <=
    sqrt(D(c t) dot (g p ** D(c t))) * sqrt(D w dot (g p ** D w))`
  MP_TAC THENL
   [MATCH_MP_TAC GEOD_METRIC_CS THEN MATCH_MP_TAC GEOG_G_SYM_POS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_tnorm; mfd_speed; o_THM]);;

(* The radial estimate. *)

let GEOD_RADIAL_CURVE = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (c:real->real^N) a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\
        mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                      open_set_atlas (mfd_tball g x r)) c a b
        ==> mfd_c1_curve (top,atlas) (mfd_exp (top,atlas) g x o c) a b /\
            mfd_tnorm g x (c b) - mfd_tnorm g x (c a) <=
            mfd_length atlas g (mfd_exp (top,atlas) g x o c) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`;
                 `\y. mpullback (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                            (mfd_exp (top,atlas) (g:A->real^N^N) x y)) o
                                 mfd_exp (top,atlas) g x)
                                (metric_local atlas
                                   (chart_at atlas (mfd_exp (top,atlas) g x y)) g) y`;
                 `c:real->real^N`; `a:real`; `b:real`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; REAL_SUB_REFL; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sym") (LABEL_TAC "pos")) THEN
  REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC GEOD_EPS_LIMIT THEN
  REPEAT CONJ_TAC THENL [USE_THEN "pos" MATCH_ACCEPT_TAC; USE_THEN "pos" MATCH_ACCEPT_TAC;
                         ALL_TAC] THEN
  X_GEN_TAC `ep:real` THEN DISCH_TAC THEN REWRITE_TAC[mfd_length] THEN
  MP_TAC(ISPECL
   [`\t. sqrt((c:real->real^N) t dot ((g:A->real^N^N) x ** c t) + ep pow 2)`;
    `\t. inv(&2 * sqrt((c:real->real^N) t dot ((g:A->real^N^N) x ** c t) + ep pow 2)) *
         (&2 * (c t dot (g x ** vector_derivative (\u. c(drop u))
                                     (at (lift t) within interval[lift a,lift b]))))`;
    `mfd_speed atlas (g:A->real^N^N)
       (mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) g x o (c:real->real^N)) a b`;
    `a:real`; `b:real`] GEOD_FTC_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mfd_tball (g:A->real^N^N) x r`; `c:real->real^N`;
                 `a:real`; `b:real`; `t:real`] GEOD_OPEN_C1_HAS_VD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GRGD_PARAM_FACTS]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`;
                 `a:real`; `b:real`; `t:real`] GEOD_RADIAL_POINTWISE) THEN
  ASM_REWRITE_TAC[mfd_tnorm] THEN DISCH_TAC THEN
  ABBREV_TAC `w = vector_derivative (\u. (c:real->real^N)(drop u))
                    (at (lift t) within interval[lift a,lift b])` THEN
  SUBGOAL_THEN `&0 <= (c:real->real^N) t dot ((g:A->real^N^N) x ** c t)` ASSUME_TAC THENL
   [USE_THEN "pos" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\t. (c:real->real^N) t dot ((g:A->real^N^N) x ** c t)`;
                   `&2 * ((c:real->real^N) t dot ((g:A->real^N^N) x ** w))`;
                   `t:real`; `real_interval[a,b]`; `ep:real`] GEOD_SQRT_EPS_DERIV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GEOD_QUAD_REAL_DERIV THEN
    ASM_REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN USE_THEN "sym" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GEOD_RATIO_BOUND THEN
  EXISTS_TAC `sqrt((c:real->real^N) t dot ((g:A->real^N^N) x ** c t))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs X <= Y ==> X <= Y`) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SPEED_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POS_LE];
    MATCH_MP_TAC SQRT_MONO_LE THEN MP_TAC(SPEC `ep:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_POW_LT]]);;

(* ========================================================================= *)
(* Lower bounds for lengths of curves from the centre of a                   *)
(* normal ball; geodesic balls are metric balls (MFD_EXP_DIST, MFD_EXP_BALL). *)
(* ========================================================================= *)

(* g x is uniformly positive definite. *)

let GEOD_TNORM_POS_DEF = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> ?m. &0 < m /\ !v. m * norm v pow 2 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `{SND (c0:(A->bool)#(A->real^N)) x}`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_SING; SING_SUBSET; IN_SING] THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SND (c0:(A->bool)#(A->real^N)) x`; `v:real^N`] o
    check (fun th -> can (term_match []
     `!y (v:real^N). y = SND (c0:(A->bool)#(A->real^N)) x ==> P y v`) (concl th))) THEN
  ASM_SIMP_TAC[]);;

(* Elementary facts on the norm |v|_x. *)

let GEOD_TNORM_BASIC = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> mfd_tnorm g x (vec 0) = &0 /\
            (!v. &0 <= mfd_tnorm g x v) /\
            (!v. mfd_tnorm g x v pow 2 = v dot (g x ** v)) /\
            (!t v. mfd_tnorm g x (t % v) = abs t * mfd_tnorm g x v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GEOG_G_SYM_POS) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[mfd_tnorm; SQRT_POS_LE; SQRT_POW_2; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO;
               SQRT_0; GRGD_QUAD_HOMOG] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]);;

(* Closed balls for |.|_x are compact. *)

let GEOD_TCBALL_COMPACT = prove
 (`!top atlas (g:A->real^N^N) (x:A) s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> compact {v:real^N | mfd_tnorm g x v <= s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < &0` THENL
   [SUBGOAL_THEN `{v:real^N | mfd_tnorm (g:A->real^N^N) x v <= s} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; REAL_NOT_LE] THEN
      X_GEN_TAC `v:real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (term_match []
        `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPACT_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_POS_DEF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `{v:real^N | mfd_tnorm (g:A->real^N^N) x v <= s} =
    {v | lift(v dot (g x ** v)) IN {y:real^1 | y$1 <= s pow 2}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_COMPONENT] THEN X_GEN_TAC `v:real^N` THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM th]) o
      check (fun th -> can (term_match []
        `!v:real^N. mfd_tnorm (g:A->real^N^N) x v pow 2 = v dot (g x ** v)`) (concl th))) THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM; LIFT_COMPONENT] THEN
    EXISTS_TAC `&1 + s pow 2 / m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_POW_2];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(v:real^N) pow 2 <= s pow 2 / m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (term_match []
        `!v:real^N. m * norm v pow 2 <= v dot ((g:A->real^N^N) x ** v)`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `norm(v:real^N) <= &1` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &0 <= y ==> x <= &1 + y`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(v:real^N) <= norm v pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN X_GEN_TAC `v:real^N` THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]);;

(* Images of closed |.|_x-balls inside a normal ball are closed. *)

let GEOD_EXP_IMAGE_CLOSED = prove
 (`!top atlas (g:A->real^N^N) (x:A) r s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ s < r
        ==> closed_in top (IMAGE (mfd_exp (top,atlas) g x) {v | mfd_tnorm g x v <= s})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (mfd_tball (g:A->real^N^N) x r)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; mfd_tball] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC GEOD_TCBALL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* A C^1 curve from x inside a normal ball, ending at exp_x w: |w|_x is at   *)
(* most its length.                                                          *)

let GEOD_LIFT_ENDPOINTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (gamma:real->A) b w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ mfd_c1_curve (top,atlas) gamma (&0) b /\
        (!t. &0 <= t /\ t <= b
             ==> gamma t IN IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r)) /\
        gamma(&0) = x /\ w IN mfd_tball g x r /\ gamma b = mfd_exp (top,atlas) g x w
        ==> mfd_tnorm g x w <= mfd_length atlas g gamma (&0) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vec 0 IN mfd_tball (g:A->real^N^N) x r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) x r` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th -> can (term_match []
      `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w. v IN mfd_tball (g:A->real^N^N) x r /\ w IN mfd_tball g x r /\
          mfd_exp (top,atlas) g x v = mfd_exp (top,atlas) g x w ==> v = w`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`; `gamma:real->A`;
                 `&0`; `b:real`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^N)(&0) = vec 0 /\ c b = w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `b:real`]
    GEOD_RADIAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^N^N) gamma (&0) b =
    mfd_length atlas g (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
    ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* A C^1 curve from x leaving exp_x(tball s) has length at least s. *)

let GEOD_EXIT_LOWER = prove
 (`!top atlas (g:A->real^N^N) (x:A) r s (gamma:real->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ &0 < s /\ s < r /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
        (?t. t IN real_interval[&0,&1] /\
             ~(gamma t IN IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x s)))
        ==> s <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x s SUBSET mfd_tball g x r` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x) (mfd_tball g x s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`atlas:((A->bool)#(A->real^N))->bool`; `mfd_tball (g:A->real^N^N) x r`] THEN
    ASM_SIMP_TAC[GEOF_TBALL_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x) (mfd_tball g x s)`]
    GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                        {v | mfd_tnorm g x v <= s}`; `t1:real`]
    GRGD_CLOSED_LEFT_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      MATCH_MP_TAC GEOD_EXP_IMAGE_CLOSED THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(gamma:real->A) u IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                   (mfd_tball g x s)`
      MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t
                             ==> (y:A) IN IMAGE (f:real^N->A) s ==> y IN IMAGE f t`) THEN
      REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s <= mfd_tnorm (g:A->real^N^N) x w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `~((gamma:real->A) t1 IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                    (mfd_tball g x s))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t1:real`; `&1`]
    MFD_LENGTH_COMBINE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `t1:real`; `&1`]
    MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `gamma:real->A`; `t1:real`;
                 `w:real^N`] GEOD_LIFT_ENDPOINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `u:real = t1` THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN
         `(gamma:real->A) u IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                     (mfd_tball g x s)`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `mfd_tball (g:A->real^N^N) x s SUBSET mfd_tball g x r` THEN
        SET_TAC[]];
      REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Curves from x to exp_x v are at least |v|_x long. *)

let GEOD_LENGTH_LOWER = prove
 (`!top atlas (g:A->real^N^N) (x:A) r v (gamma:real->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x v < r /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
        gamma(&1) = mfd_exp (top,atlas) g x v
        ==> mfd_tnorm g x v <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = (mfd_tnorm (g:A->real^N^N) x v + r) / &2` THEN
  SUBGOAL_THEN `&0 < s /\ s < r /\ mfd_tnorm (g:A->real^N^N) x v < s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (term_match []
      `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?t. t IN real_interval[&0,&1] /\
        ~((gamma:real->A) t IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                     (mfd_tball g x s))`
  THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `r:real`; `s:real`; `gamma:real->A`]
      GEOD_EXIT_LOWER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GEOD_LIFT_ENDPOINTS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `r:real`] THEN
  ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t
                         ==> (y:A) IN IMAGE (f:real^N->A) s ==> y IN IMAGE f t`) THEN
  REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* The radial geodesic t |-> exp_x(t v) on [0,1]. *)

let GEOD_RADIAL_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        (!t. &0 <= t /\ t <= &1 ==> t % v IN mfd_exp_dom (top,atlas) g x)
        ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g x v) (&0) (&1) /\
            mfd_geo (top,atlas) g x v (&0) = x /\
            mfd_geo (top,atlas) g x v (&1) = mfd_exp (top,atlas) g x v /\
            mfd_length atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) =
            mfd_tnorm g x v /\
            (!t. &0 <= t /\ t <= &1
                 ==> mfd_geo (top,atlas) g x v t = mfd_exp (top,atlas) g x (t % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\
            mfd_exp (top,atlas) g x (t % v) = mfd_geo (top,atlas) g x v t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_interval[&0,&1] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`; `&0`; `&1`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> can (term_match []
      `!t. &0 <= t /\ t <= &1
           ==> t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\ P t`) (concl th))) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID] THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Geodesic balls are metric balls.                                          *)
(* ------------------------------------------------------------------------- *)

let MFD_EXP_DIST = prove
 (`!top atlas (g:A->real^N^N) (x:A) r v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x v < r
        ==> mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x v) /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_RADIAL_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `mfd_tball (g:A->real^N^N) x r SUBSET
                          mfd_exp_dom (top,atlas) g x`) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `mfd_tnorm (g:A->real^N^N) x v` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) (x:A) (mfd_exp (top,atlas) (g:A->real^N^N) x v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN
    EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                   `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      REWRITE_TAC[GRGD_IN_LENGTHS] THEN X_GEN_TAC `L:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOD_LENGTH_LOWER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `r:real`] THEN ASM_REWRITE_TAC[]]]);;

let MFD_EXP_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r
        ==> IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r) =
            mfd_ball (top,atlas) g x r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `r:real`; `v:real^N`] MFD_EXP_DIST) THEN
    UNDISCH_TAC `(v:real^N) IN mfd_tball (g:A->real^N^N) x r` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `s = (mfd_dist (top,atlas) (g:A->real^N^N) x y + r) / &2` THEN
  SUBGOAL_THEN `&0 < s /\ s < r /\ mfd_dist (top,atlas) (g:A->real^N^N) x y < s`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
      mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1) /\
      gamma(&0) = (x:A) /\ gamma(&1) = y}`; `s:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE];
      ASM_REWRITE_TAC[GSYM mfd_dist]];
    ALL_TAC] THEN
  REWRITE_TAC[GRGD_IN_LENGTHS] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  ASM_CASES_TAC
   `?t. t IN real_interval[&0,&1] /\
        ~((gamma:real->A) t IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                     (mfd_tball g x s))`
  THENL
   [SUBGOAL_THEN `s <= mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)`
    MP_TAC THENL
     [MATCH_MP_TAC GEOD_EXIT_LOWER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `x:A`; `r:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1` o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) x s` THEN
  REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tools for the equality case: uniqueness of derivatives on a               *)
(* closed interval, positive definiteness of g, the equality case of        *)
(* Cauchy-Schwarz, injectivity of the differential of a parametrization.    *)
(* ========================================================================= *)

let GEOD_REAL_DERIV_UNIQUE = prove
 (`!f f' f'' a b t.
        a < b /\ t IN real_interval[a,b] /\
        (f has_real_derivative f') (atreal t within real_interval[a,b]) /\
        (f has_real_derivative f'') (atreal t within real_interval[a,b])
        ==> f' = f''`,
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (f:real->real) o drop`; `lift a`; `lift b`; `lift t`;
                 `lift f'`; `lift f''`] VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL) THEN
  ASM_REWRITE_TAC[LIFT_DROP; LIFT_EQ; GRGD_IN_INTERVAL_LIFT]);;

let GEOD_G_POS_DEF = prove
 (`!top atlas (g:A->real^N^N) p.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p IN topspace top
        ==> !u. ~(u = vec 0) ==> &0 < u dot (g p ** u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GEOD_TNORM_POS_DEF) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m * norm(u:real^N) pow 2` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]);;

(* Equality in Cauchy-Schwarz for a positive definite form. *)

let GEOD_CS_EQ = prove
 (`!(G:real^N^N) a b.
        (!u v. u dot (G ** v) = v dot (G ** u)) /\
        (!u. ~(u = vec 0) ==> &0 < u dot (G ** u)) /\
        &0 < a dot (G ** a) /\
        a dot (G ** b) = sqrt(a dot (G ** a)) * sqrt(b dot (G ** b))
        ==> b = (sqrt(b dot (G ** b)) / sqrt(a dot (G ** a))) % a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "pd")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 <= b dot ((G:real^N^N) ** b)` ASSUME_TAC THENL
   [ASM_CASES_TAC `b:real^N = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `sa = sqrt(a dot ((G:real^N^N) ** a))` THEN
  ABBREV_TAC `sb = sqrt(b dot ((G:real^N^N) ** b))` THEN
  SUBGOAL_THEN `&0 < sa` ASSUME_TAC THENL
   [EXPAND_TAC "sa" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a dot ((G:real^N^N) ** a) = sa pow 2 /\ b dot (G ** b) = sb pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sa"; "sb"] THEN CONJ_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REMOVE_THEN "pd" (MP_TAC o SPEC `b - (sb / sa) % a:real^N`) THEN
  MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
  REWRITE_TAC[REAL_NOT_LT; MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  USE_THEN "sym" (fun th -> REWRITE_TAC[SPECL [`b:real^N`; `a:real^N`] th]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
  UNDISCH_TAC `&0 < sa` THEN CONV_TAC REAL_FIELD);;

(* The differential of a smooth parametrization is injective. *)

let GEOD_PARAM_DIFF_INJ = prove
 (`!top atlas s (e:real^N->A) y h.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\ y IN s /\
        mfd_differential (open_set_atlas (:real^N)) atlas e y h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^N))
                 (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)` THEN
    REWRITE_TAC[mfd_param; mfd_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `k:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `e:real^N->A`; `s:real^N->bool`; `k:(A->bool)#(A->real^N)`]
    GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^N->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool,\x:real^N. x) IN open_set_atlas s` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `subtopology euclidean (s:real^N->bool)`;
                 `open_set_atlas (s:real^N->bool)`;
                 `k:(A->bool)#(A->real^N)`; `(s:real^N->bool,\x:real^N. x)`;
                 `IMAGE (e:real^N->A) s`; `e':A->real^N`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on
      (IMAGE (SND(k:(A->bool)#(A->real^N)))
        {p | p IN FST k INTER IMAGE (e:real^N->A) s /\
             (e':A->real^N) p IN s})
      ((\x:real^N. x) o e' o chart_inv k)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (open_set_atlas s) (IMAGE (e:real^N->A) s) (e':A->real^N)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:(A->bool)#(A->real^N)`;
                               `(s:real^N->bool,\x:real^N. x)`]) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `SND (k:(A->bool)#(A->real^N)) ((e:real^N->A) y) IN
    IMAGE (SND k) {p | p IN FST k INTER IMAGE e s /\
                       (e':A->real^N) p IN s}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER; FST] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. SND (k:(A->bool)#(A->real^N)) ((e:real^N->A) u)) differentiable (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{u | u IN s /\ (e:real^N->A) u IN FST(k:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N)))
    differentiable (at (SND k ((e:real^N->A) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `IMAGE (SND(k:(A->bool)#(A->real^N)))
        {p | p IN FST k INTER IMAGE (e:real^N->A) s /\
             (e':A->real^N) p IN s}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u. SND (k:(A->bool)#(A->real^N)) ((e:real^N->A) u)`;
    `(\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N))`;
    `frechet_derivative (\u. SND (k:(A->bool)#(A->real^N)) ((e:real^N->A) u)) (at y)`;
    `frechet_derivative ((\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N)))
       (at ((\u. SND k ((e:real^N->A) u)) y))`;
    `y:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(((\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N))) o
     (\u. SND k ((e:real^N->A) u)) has_derivative (\h:real^N. h)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z:real^N. z` THEN
    UNDISCH_TAC `open {u | u IN s /\ (e:real^N->A) u IN FST(k:(A->bool)#(A->real^N))}` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s /\ (e:real^N->A) z IN FST(k:(A->bool)#(A->real^N))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ball(y:real^N,d) SUBSET
                   {u | u IN s /\ (e:real^N->A) u IN FST(k:(A->bool)#(A->real^N))}` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative ((\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N)))
       (at (SND k ((e:real^N->A) y))) o
    frechet_derivative (\u. SND k (e u)) (at y) = (\h:real^N. h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC
     [`((\x:real^N. x) o (e':A->real^N) o chart_inv (k:(A->bool)#(A->real^N))) o
       (\u. SND k ((e:real^N->A) u))`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_differential (open_set_atlas (:real^N))
                 (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) y h = vec 0` THEN
  ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `h:real^N` o check (fun th -> can (term_match []
    `(f:real^N->real^N) o (g:real^N->real^N) = (\h:real^N. h)`) (concl th))) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC
   `frechet_derivative ((\x:real^N. x) o (e':A->real^N) o
                        chart_inv (k:(A->bool)#(A->real^N)))
                       (at (SND k ((e:real^N->A) y)))` LINEAR_0) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* The equality case MFD_EXP_DIST_EQUALITY: a                                *)
(* C^1 curve from x to exp_x v of length |v|_x is a monotone                 *)
(* reparametrization of the radial geodesic.                                 *)
(* ========================================================================= *)

(* A curve from x to exp_x v of length |v|_x stays in the normal ball and   *)
(* lifts to exponential coordinates.                                         *)

let GEOD_EQ_LIFT = prove
 (`!top atlas (g:A->real^N^N) (x:A) r v (gamma:real->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x v < r /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
        gamma(&1) = mfd_exp (top,atlas) g x v /\
        mfd_length atlas g gamma (&0) (&1) = mfd_tnorm g x v
        ==> ?c. mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                              open_set_atlas (mfd_tball g x r)) c (&0) (&1) /\
                (!t. t IN real_interval[&0,&1]
                     ==> c t IN mfd_tball g x r /\
                         gamma t = mfd_exp (top,atlas) g x (c t)) /\
                c(&0) = vec 0 /\ c(&1) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = (mfd_tnorm (g:A->real^N^N) x v + r) / &2` THEN
  SUBGOAL_THEN `&0 < s /\ s < r /\ mfd_tnorm (g:A->real^N^N) x v < s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (term_match []
      `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> (gamma:real->A) t IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                       (mfd_tball g x s)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `r:real`; `s:real`; `gamma:real->A`]
      GEOD_EXIT_LOWER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`; `gamma:real->A`;
                 `&0`; `&1`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(gamma:real->A) t IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                 (mfd_tball g x s)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
                  ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t
                           ==> (y:A) IN IMAGE (f:real^N->A) s ==> y IN IMAGE f t`) THEN
    REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real->real^N` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `vec 0 IN mfd_tball (g:A->real^N^N) x r /\ v IN mfd_tball g x r`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_REAL_INTERVAL];
    ASM_MESON_TAC[REAL_POS; REAL_LE_REFL];
    ASM_MESON_TAC[REAL_POS; REAL_LE_REFL]]);;

(* Along such a lift, the length from 0 to t is |c t|_x. *)

let GEOD_EQ_LENGTH_NORM = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (c:real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\
        mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                      open_set_atlas (mfd_tball g x r)) c (&0) (&1) /\
        c(&0) = vec 0 /\
        mfd_length atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) =
        mfd_tnorm g x (c(&1))
        ==> !t. t IN real_interval[&0,&1]
                ==> mfd_length atlas g (mfd_exp (top,atlas) g x o c) (&0) t =
                    mfd_tnorm g x (c t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `&1`]
    GEOD_RADIAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x o (c:real->real^N)`;
                 `&0`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `t:real`]
    GEOD_RADIAL_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `t:real`; `&1`]
    GEOD_RADIAL_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N)(&0)) = &0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Where |c t|_x > 0 the velocity of c is radial, c' = (|gamma'|/|c|) c,    *)
(* and |c|_x has derivative |gamma'|.                                       *)

let GEOD_EQ_PROPORTIONAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (c:real->real^N) t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\
        mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                      open_set_atlas (mfd_tball g x r)) c (&0) (&1) /\
        (!t. t IN real_interval[&0,&1]
             ==> mfd_length atlas g (mfd_exp (top,atlas) g x o c) (&0) t =
                 mfd_tnorm g x (c t)) /\
        t IN real_interval[&0,&1] /\ &0 < mfd_tnorm g x (c t)
        ==> ((\t. mfd_tnorm g x (c t)) has_real_derivative
             mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t)
            (atreal t within real_interval[&0,&1]) /\
            vector_derivative (\u. c(drop u))
              (at (lift t) within interval[lift(&0),lift(&1)]) =
            (mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t /
             mfd_tnorm g x (c t)) % c t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `&1`]
    GEOD_RADIAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  (* the derivative of |c|_x *)
  SUBGOAL_THEN
   `((\t. mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)) has_real_derivative
     mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t)
    (atreal t within real_interval[&0,&1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\u. real_integral (real_interval[&0,u])
                      (mfd_speed atlas (g:A->real^N^N)
                         (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) (&1))` THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "len" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `u IN real_interval[&0,&1]`))]) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGD_LENGTH_SUBINTERVAL THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      UNDISCH_TAC `u IN real_interval[&0,&1]` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N)
                        (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) (&1)`;
                     `&0`; `&1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`mfd_tball (g:A->real^N^N) x r`; `c:real->real^N`;
                 `&0`; `&1`; `t:real`] GEOD_OPEN_C1_HAS_VD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`;
                 `c:real->real^N`; `&0`; `&1`; `t:real`] GEOD_PARAM_VELOCITY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN
                mfd_exp_dom (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                  ((c:real->real^N) t) IN topspace top`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = vector_derivative (\u. (c:real->real^N)(drop u))
                    (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  (* <c, c'>_x = |c|_x |gamma'| *)
  SUBGOAL_THEN
   `(c:real->real^N) t dot ((g:A->real^N^N) x ** w) =
    mfd_tnorm g x (c t) *
    mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`] (ISPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^N))->bool`] GEOG_G_SYM_POS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`(g:A->real^N^N) x`; `c:real->real^N`; `w:real^N`; `t:real`;
                   `real_interval[&0,&1]`] GEOD_QUAD_REAL_DERIV) THEN
    ASM_REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\t. mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)`;
      `mfd_speed atlas (g:A->real^N^N) (mfd_exp (top,atlas) g x o (c:real->real^N))
                 (&0) (&1) t`;
      `\t. mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)`;
      `mfd_speed atlas (g:A->real^N^N) (mfd_exp (top,atlas) g x o (c:real->real^N))
                 (&0) (&1) t`;
      `t:real`; `real_interval[&0,&1]`] HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\t. (c:real->real^N) t dot ((g:A->real^N^N) x ** c t)) has_real_derivative
       mfd_tnorm g x (c t) *
       mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t +
       mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t *
       mfd_tnorm g x (c t)) (atreal t within real_interval[&0,&1])`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\t. mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) *
                      mfd_tnorm g x (c t)` THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[GSYM REAL_POW_2];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\t. (c:real->real^N) t dot ((g:A->real^N^N) x ** c t)`;
      `&2 * ((c:real->real^N) t dot ((g:A->real^N^N) x ** w))`;
      `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) *
       mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t +
       mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t *
       mfd_tnorm g x (c t)`;
      `&0`; `&1`; `t:real`] GEOD_REAL_DERIV_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* equality in Cauchy-Schwarz at p = exp_x(c t) *)
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) ((c:real->real^N) t)` THEN
  ABBREV_TAC `p = mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                    ((c:real->real^N) t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`; `w:real^N`]
    MFD_GAUSS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`; `(c:real->real^N) t`]
    MFD_GAUSS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(D:real^N->real^N) w =
    (mfd_speed atlas (g:A->real^N^N) (mfd_exp (top,atlas) g x o (c:real->real^N))
               (&0) (&1) t / mfd_tnorm g x (c t)) % D(c t)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_speed atlas (g:A->real^N^N) (mfd_exp (top,atlas) g x o (c:real->real^N))
                (&0) (&1) t = sqrt((D:real^N->real^N) w dot (g p ** D w)) /\
      mfd_tnorm g x (c t) = sqrt(D(c t) dot (g p ** D(c t)))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[mfd_speed; o_THM; mfd_tnorm]; ALL_TAC] THEN
    MATCH_MP_TAC GEOD_CS_EQ THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`] GEOG_G_SYM_POS) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC GEOD_G_POS_DEF THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> can (term_match []
        `!v:real^N. mfd_tnorm (g:A->real^N^N) x v pow 2 = v dot (g x ** v)`) (concl th))) THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `sqrt((c:real->real^N) t dot ((g:A->real^N^N) x ** c t)) = mfd_tnorm g x (c t) /\
      sqrt((D:real^N->real^N) w dot (g p ** D w)) =
      mfd_speed atlas g (mfd_exp (top,atlas) g x o c) (&0) (&1) t`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[mfd_speed; o_THM; mfd_tnorm]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* injectivity of D *)
  MATCH_MP_TAC(VECTOR_ARITH `w - k % c = vec 0 ==> (w:real^N) = k % c`) THEN
  MATCH_MP_TAC GEOD_PARAM_DIFF_INJ THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `mfd_tball (g:A->real^N^N) x r`; `mfd_exp (top,atlas) (g:A->real^N^N) x`;
    `(c:real->real^N) t`] THEN
  ASM_SIMP_TAC[LINEAR_SUB; LINEAR_CMUL] THEN VECTOR_ARITH_TAC);;

let GEOD_TNORM_EQ_0 = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> (mfd_tnorm g x v = &0 <=> v = vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tnorm; SQRT_EQ_0] THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_G_POS_DEF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* A lift of length |c 1|_x with the length from 0 to t equal to |c t|_x is *)
(* radial: c t = (|c t|_x / |c 1|_x) c 1.                                    *)

let GEOD_EQ_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) r (c:real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\
        mfd_c1_curve (subtopology euclidean (mfd_tball g x r),
                      open_set_atlas (mfd_tball g x r)) c (&0) (&1) /\
        (!t. t IN real_interval[&0,&1]
             ==> mfd_length atlas g (mfd_exp (top,atlas) g x o c) (&0) t =
                 mfd_tnorm g x (c t)) /\
        &0 < mfd_tnorm g x (c(&1))
        ==> !t. t IN real_interval[&0,&1]
                ==> c t = (mfd_tnorm g x (c t) / mfd_tnorm g x (c(&1))) % c(&1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "len") ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) x r`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `&1`]
    GEOD_RADIAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* |c|_x is nondecreasing *)
  SUBGOAL_THEN
   `!t1 t2. &0 <= t1 /\ t1 <= t2 /\ t2 <= &1
            ==> mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t1) <= mfd_tnorm g x (c t2)`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t1 IN real_interval[&0,&1] /\ t2 IN real_interval[&0,&1]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "len" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `t1 IN real_interval[&0,&1]`)); GSYM(MATCH_MP th
      (ASSUME `t2 IN real_interval[&0,&1]`))]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x o (c:real->real^N)`;
                   `&0`; `t1:real`; `t2:real`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x o (c:real->real^N)`;
                   `t1:real`; `t2:real`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = {t | t IN real_interval[&0,&1] /\
                       &0 < mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)}` THEN
  SUBGOAL_THEN `is_realinterval S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[is_realinterval; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `y:real`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) a)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the unit vector c / |c|_x has zero derivative on S *)
  SUBGOAL_THEN
   `!t. t IN S
        ==> ((\s. inv(mfd_tnorm (g:A->real^N^N) x ((c:real->real^N)(drop s))) % c(drop s))
             has_vector_derivative vec 0)
            (at (lift t) within interval[lift(&0),lift(&1)])`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `t:real`]
      GEOD_EQ_PROPORTIONAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`mfd_tball (g:A->real^N^N) x r`; `c:real->real^N`;
                   `&0`; `&1`; `t:real`] GEOD_OPEN_C1_HAS_VD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `k = mfd_speed atlas (g:A->real^N^N)
                      (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) (&1) t` THEN
    SUBGOAL_THEN
     `((lift o (\s. inv(mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) s))) o drop)
       has_vector_derivative lift(--k / mfd_tnorm g x (c t) pow 2))
      (at (lift t) within interval[lift(&0),lift(&1)])`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
      MP_TAC(ISPECL [`\t. mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)`; `k:real`;
                     `t:real`; `real_interval[&0,&1]`] HAS_REAL_DERIVATIVE_INV_WITHIN) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; DISCH_THEN MATCH_ACCEPT_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x y:real^N. drop x % y`;
      `lift o (\s. inv(mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) s))) o drop`;
      `\u. (c:real->real^N)(drop u)`;
      `lift(--k / mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) pow 2)`;
      `(k / mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)) % c t`;
      `lift t`; `interval[lift(&0),lift(&1)]`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[BILINEAR_DROP_MUL]; ALL_TAC] THEN
    REWRITE_TAC[o_THM; LIFT_DROP] THEN
    MATCH_MP_TAC(MESON[]
     `(a:real^N) = b ==> (f has_vector_derivative a) net ==> (f has_vector_derivative b) net`) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LZERO] `a = &0 ==> a % (v:real^N) = vec 0`) THEN
    UNDISCH_TAC `&0 < mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. inv(mfd_tnorm (g:A->real^N^N) x ((c:real->real^N)(drop s))) % c(drop s)`;
    `IMAGE lift S`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM IS_REALINTERVAL_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\h:real^1. vec 0:real^N) = (\h. drop h % vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift(&0),lift(&1)]` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (LABEL_TAC "const")) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(t:real) IN S` THENL
   [SUBGOAL_THEN
     `inv(mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)) % c t =
      inv(mfd_tnorm g x (c(&1))) % c(&1)`
    ASSUME_TAC THENL
     [USE_THEN "const" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN S`);
                                            MATCH_MP th (ASSUME `&1 IN S`)]);
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t)` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) %
      (inv(mfd_tnorm g x (c t)) % c t)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC; real_div]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^N) t = vec 0 /\ mfd_tnorm (g:A->real^N^N) x (c t) = &0`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `~((t:real) IN S)` THEN EXPAND_TAC "S" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(c:real->real^N) t` o check (fun th -> can (term_match []
        `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`] GEOD_TNORM_EQ_0) THEN
      ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* The equality case MFD_EXP_DIST_EQUALITY.                                  *)
(* ------------------------------------------------------------------------- *)

let MFD_EXP_DIST_EQUALITY = prove
 (`!top atlas (g:A->real^N^N) x r v gamma.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x v < r /\
       mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
       gamma(&1) = mfd_exp (top,atlas) g x v /\
       mfd_length atlas g gamma (&0) (&1) = mfd_tnorm g x v
       ==> !t. &0 <= t /\ t <= &1
               ==> ?s. &0 <= s /\ s <= &1 /\
                       gamma t = mfd_exp (top,atlas) g x (s % v) /\
                       mfd_length atlas g gamma (&0) t = s * mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `v:real^N`; `gamma:real->A`]
    GEOD_EQ_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lift")
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`; `&0`; `&1`]
    GEOD_RADIAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> mfd_length atlas (g:A->real^N^N) gamma (&0) t =
            mfd_length atlas g (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) t`
  (LABEL_TAC "leq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_LENGTH_EQ THEN
    REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "lift" (MP_TAC o SPEC `u:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^N^N) (mfd_exp (top,atlas) g x o (c:real->real^N))
               (&0) (&1) = mfd_tnorm g x (c(&1))`
  ASSUME_TAC THENL
   [USE_THEN "leq" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`]
    GEOD_EQ_LENGTH_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "len") THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t IN real_interval[&0,&1]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^N^N) gamma (&0) t = mfd_tnorm g x ((c:real->real^N) t)`
  ASSUME_TAC THENL
   [USE_THEN "leq" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `&0 <= t`) (ASSUME `t <= &1`))]) THEN
    USE_THEN "len" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t = mfd_exp (top,atlas) (g:A->real^N^N) x ((c:real->real^N) t)`
  ASSUME_TAC THENL
   [USE_THEN "lift" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) <= mfd_tnorm g x v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x o (c:real->real^N)`;
                   `&0`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x o (c:real->real^N)`;
                   `t:real`; `&1`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "len" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`)]) THEN
    UNDISCH_TAC `mfd_length atlas (g:A->real^N^N)
                   (mfd_exp (top,atlas) g x o (c:real->real^N)) (&0) (&1) =
                 mfd_tnorm g x (c(&1))` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mfd_tnorm (g:A->real^N^N) x v = &0` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS; REAL_MUL_LZERO; VECTOR_MUL_LZERO] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(c:real->real^N) t` o check (fun th -> can (term_match []
        `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(c:real->real^N) t`] GEOD_TNORM_EQ_0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) x v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (term_match []
      `!v:real^N. &0 <= mfd_tnorm (g:A->real^N^N) x v`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `mfd_tnorm (g:A->real^N^N) x ((c:real->real^N) t) / mfd_tnorm g x v` THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID;
               REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `c:real->real^N`] GEOD_EQ_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Geodesics are locally minimizing.                                         *)
(* ========================================================================= *)

let MFD_GEODESIC_LOCALLY_MINIMIZING = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\ t0 IN J
        ==> ?e. &0 < e /\
                !a b. t0 - e < a /\ a <= b /\ b < t0 + e
                      ==> real_interval[a,b] SUBSET J /\
                          mfd_dist (top,atlas) g (gamma a) (gamma b) =
                          mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic]) THEN
  SUBGOAL_THEN `!t. t IN J ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology euclideanreal J,top:A topology) gamma`)
        (concl th))) THEN
    SIMP_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t0`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`; `W:A->bool`;
                 `t0:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  ABBREV_TAC `c0 = mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t0)
                     (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gamma t0)` THEN
  SUBGOAL_THEN `&0 <= c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t0`] GEOG_G_SYM_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = d / (&2 * c0 + &2)` THEN
  SUBGOAL_THEN `&0 < m /\ m * (&2 * c0 + &2) = d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min e1 m` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[a,b] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "near" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(a - t0) < e1 /\ abs(b - t0) < e1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a IN J /\ b IN J /\ (gamma:real->A) a IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `y = (gamma:real->A) a` THEN
  ABBREV_TAC `w = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a` THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "unif" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:A) IN W`))) THEN
  STRIP_TAC THEN
  (* the geodesic s |-> gamma(s + a) is the maximal geodesic from y with velocity w *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&1`; `a:real`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; VECTOR_MUL_LID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (gamma:real->A)(t + a)`; `{t | t + a IN J}`;
                 `y:A`; `w:real^N`] MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ADD_LID] THEN ASM_MESON_TAC[REAL_ADD_LID];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `b - a IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) y w /\
                mfd_geo (top,atlas) g y w (b - a) = (gamma:real->A) b`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b - a`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b - a`) THEN
    ASM_REWRITE_TAC[REAL_ARITH `(b - a) + a = b`] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `w:real^N`; `b - a`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) y w = c0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c0"; "y"; "w"] THEN
    MATCH_MP_TAC MFD_GEODESIC_SPEED THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) * c0 < d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&2 * m) * c0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `d:real`; `(b - a) % w:real^N`] MFD_EXP_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(b - a) = b - a` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

