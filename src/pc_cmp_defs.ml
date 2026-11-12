(* ========================================================================= *)
(* Unit pc_cmp_defs (comparison-geometry layer CMP): vocabulary and the      *)
(* statement constants S1-S8 of the CMP results used by other layers         *)
(* (dimension-generic where the proofs allow it; 3-dimensional instances for *)
(* the P2C and P2B units), with sanity lemmas.                               *)
(* ========================================================================= *)

needs "src/pc_geo_defs.ml";;
needs "src/pc_grg_voldefs.ml";;
needs "src/pc_lrg_lap.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Definitions.                                                              *)
(* ========================================================================= *)

(* Model functions for constant curvature k: sn'' + k sn = 0, sn 0 = 0,      *)
(* sn' 0 = 1 (MT p. 18, Petersen Sec 6.4), and their derivative cs.  sinh  *)
(* and cosh are written with exp (HOL has no real sinh).                     *)

let cmp_sn = new_definition
 `cmp_sn (k:real) (t:real) =
    if &0 < k then sin(sqrt k * t) / sqrt k
    else if k = &0 then t
    else (exp(sqrt(--k) * t) - exp(--(sqrt(--k) * t))) / (&2 * sqrt(--k))`;;

let cmp_cs = new_definition
 `cmp_cs (k:real) (t:real) =
    if &0 < k then cos(sqrt k * t)
    else if k = &0 then &1
    else (exp(sqrt(--k) * t) + exp(--(sqrt(--k) * t))) / &2`;;

(* Volume of the ball of radius r in the N-dimensional space form of        *)
(* curvature k: N |B^N| int_0^r sn_k^(N-1) (for k > 0 only meaningful for  *)
(* r <= pi / sqrt k).  The argument s only fixes the dimension type.        *)

let cmp_vmodel = new_definition
 `cmp_vmodel (s:N->bool) (k:real) (r:real) =
    &(dimindex(:N)) * measure(ball(vec 0:real^N,&1)) *
    real_integral (real_interval[&0,r]) (\t. cmp_sn k t pow (dimindex(:N) - 1))`;;

(* The tangent space at p in the coordinates of a frame E (w |-> E w):      *)
(* the matrix of d(exp_p) at E w composed with E, in the preferred chart at  *)
(* exp_p(E w), and the pullback of g by exp_p in these coordinates (normal  *)
(* coordinates for an orthonormal frame E).  The product is chart           *)
(* independent although g alone is given in preferred coordinates.         *)

let cmp_dexp = new_definition
 `cmp_dexp (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
           (p:A) (E:real^N^N) (w:real^N) =
    matrix(\h. mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g p) (E ** w) (E ** h))`;;

let cmp_expmetric = new_definition
 `cmp_expmetric (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                (g:A->real^N^N) (p:A) (E:real^N^N) (w:real^N) =
    transp(cmp_dexp (top,atlas) g p E w) **
    g(mfd_exp (top,atlas) g p (E ** w)) **
    cmp_dexp (top,atlas) g p E w`;;

(* Hessian of a function f at y for a local metric G: lnabla 1 of the        *)
(* differential (as in LRG_LLAP_LNABLA of pc_lrg_lap and p2b_mfd_hess),      *)
(* so that llap G f y is its G-trace.                                        *)

let cmp_lhess = new_definition
 `cmp_lhess (G:real^N->real^N^N) (f:real^N->real) (y:real^N) (u:real^N) (v:real^N) =
    lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(f x)) (at z) (w 1)))
      y (\m. if m = 1 then u else v)`;;

(* ========================================================================= *)
(* Statement constants of the CMP results (dimension-generic).  n = N =      *)
(* dimindex(:N); Ricci bounds in the form Ric >= -(n-1) K g, Ric <= (n-1) K  *)
(* g; Laplacian and gradient in the preferred chart at x.  The arguments     *)
(* (u:A->bool) (n:N->bool) only fix the types.                               *)
(* ========================================================================= *)

(* S1 (MT Thm 1.34, Petersen Lemmas 7.1.3-7.1.4, local form): sharp relative *)
(* volume comparison under Ric >= -(n-1) K on a ball with compact closure,   *)
(* and the absolute bound vol B(x,r) <= V_{-K}(r).                           *)

let CMP_RELVOL_STATEMENT = new_definition
 `CMP_RELVOL_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x K R r1 r2 v1 v2.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\ &0 <= K /\
       compact_in top (top closure_of mfd_ball (top,atlas) g x R) /\
       (!y w. y IN mfd_ball (top,atlas) g x R
              ==> --(&(dimindex(:N) - 1) * K) * (w dot (g y ** w)) <=
                  mfd_ricci atlas g y w w) /\
       &0 < r1 /\ r1 <= r2 /\ r2 <= R /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r1) v1 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r2) v2
       ==> v2 * cmp_vmodel (:N) (--K) r1 <= v1 * cmp_vmodel (:N) (--K) r2 /\
           v1 <= cmp_vmodel (:N) (--K) r1`;;

(* S2 (Gunther-Bishop; the volume bound in the proof of MT Prop 1.35):      *)
(* sec <= K on an injectivity ball of radius r <= pi / sqrt K gives          *)
(* vol B(x,r) >= V_K(r).                                                      *)

let CMP_GUNTHER_STATEMENT = new_definition
 `CMP_GUNTHER_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x K r v.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\ &0 <= K /\
       &0 < r /\ sqrt K * r <= pi /\ mfd_inj_ball (top,atlas) g x r /\
       (!y e1 e2. y IN mfd_ball (top,atlas) g x r /\ ~collinear {vec 0,e1,e2}
                  ==> mfd_sectional atlas g y e1 e2 <= K) /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v
       ==> cmp_vmodel (:N) K r <= v`;;

(* S3 (MT Lemma 1.32, with sec <= K instead of |Rm| <= K and the domain of  *)
(* exp explicit): no conjugate points before pi / sqrt K, and exp_x is a    *)
(* local diffeomorphism on the tangent ball of that radius.                 *)

let CMP_CONJUGATE_RADIUS_STATEMENT = new_definition
 `CMP_CONJUGATE_RADIUS_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x K.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\ &0 < K /\
       mfd_tball g x (pi / sqrt K) SUBSET mfd_exp_dom (top,atlas) g x /\
       (!y e1 e2. y IN mfd_ball (top,atlas) g x (pi / sqrt K) /\
                  ~collinear {vec 0,e1,e2}
                  ==> mfd_sectional atlas g y e1 e2 <= K)
       ==> !v. v IN mfd_tball g x (pi / sqrt K)
               ==> (!h. mfd_differential (open_set_atlas (:real^N)) atlas
                          (mfd_exp (top,atlas) g x) v h = vec 0
                        ==> h = vec 0) /\
                   ?U. open U /\ v IN U /\ U SUBSET mfd_tball g x (pi / sqrt K) /\
                       mfd_param top atlas U (mfd_exp (top,atlas) g x)`;;

(* S4 (for local Shi): the exp_x pullback on the tangent ball of radius rho  *)
(* with K rho^2 <= 1 and |Rm| <= K on B(x,rho), in the coordinates of an    *)
(* orthonormal frame E: a metric field, Euclidean at 0, comparable to the   *)
(* Euclidean metric within a factor 2, radial vectors fixed (Gauss lemma),  *)
(* and two-sided Hessian bounds of r = |w| on the orthogonal complement of  *)
(* the radial direction (1/r - K r <= ct_K, ct_{-K} <= 1/r + K r).          *)

let CMP_EXP_PULLBACK_STATEMENT = new_definition
 `CMP_EXP_PULLBACK_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x E K rho.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < rho /\ K * rho pow 2 <= &1 /\
       mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
       (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K)
       ==> metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) g x E) /\
           cmp_expmetric (top,atlas) g x E (vec 0) = mat 1 /\
           (!w a. norm w < rho
                  ==> inv(&2) * (a dot a) <= a dot (cmp_expmetric (top,atlas) g x E w ** a) /\
                      a dot (cmp_expmetric (top,atlas) g x E w ** a) <= &2 * (a dot a)) /\
           (!w. norm w < rho ==> cmp_expmetric (top,atlas) g x E w ** w = w) /\
           (!w a. &0 < norm w /\ norm w < rho
                  ==> (inv(norm w) - K * norm w) *
                      (a dot (cmp_expmetric (top,atlas) g x E w ** a) -
                       (w dot a) pow 2 / norm w pow 2) <=
                      cmp_lhess (cmp_expmetric (top,atlas) g x E) (\z. norm z) w a a /\
                      cmp_lhess (cmp_expmetric (top,atlas) g x E) (\z. norm z) w a a <=
                      (inv(norm w) + K * norm w) *
                      (a dot (cmp_expmetric (top,atlas) g x E w ** a) -
                       (w dot a) pow 2 / norm w pow 2))`;;

(* S5 (MT Prop 1.20, Jacobi's theorem): along a minimizing geodesic          *)
(* t |-> exp_x(t v), t in [0,1], every proper initial arc is minimizing,    *)
(* its minimizer is unique, and exp_x is nonsingular at t v for t < 1.       *)

let CMP_MINIMIZING_GEODESIC_STATEMENT = new_definition
 `CMP_MINIMIZING_GEODESIC_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x v.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       v IN mfd_exp_dom (top,atlas) g x /\
       mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v
       ==> !t. &0 <= t /\ t < &1
               ==> mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (t % v)) =
                   t * mfd_tnorm g x v /\
                   (!w. w IN mfd_exp_dom (top,atlas) g x /\
                        mfd_exp (top,atlas) g x w = mfd_exp (top,atlas) g x (t % v) /\
                        mfd_tnorm g x w <= t * mfd_tnorm g x v
                        ==> w = t % v) /\
                   (!h. mfd_differential (open_set_atlas (:real^N)) atlas
                          (mfd_exp (top,atlas) g x) (t % v) h = vec 0
                        ==> h = vec 0)`;;

(* S6 (MT Claim 3.24, the static part of Prop 3.21): along a minimizing     *)
(* geodesic of length d >= 2 r0 with Ric <= (n-1) K on the end balls,       *)
(* int_0^d Ric(X,X) <= 2(n-1)(2/3 K r0 + 1/r0); with the [0,1]              *)
(* parametrization (speed d) the integral of Ric(gamma',gamma') is d times. *)

let CMP_RICCI_INTEGRAL_STATEMENT = new_definition
 `CMP_RICCI_INTEGRAL_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g x v K r0.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       v IN mfd_exp_dom (top,atlas) g x /\
       mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
       &0 < r0 /\ &2 * r0 <= mfd_tnorm g x v /\
       (!y w. y IN mfd_ball (top,atlas) g x r0 UNION
                   mfd_ball (top,atlas) g (mfd_exp (top,atlas) g x v) r0
              ==> mfd_ricci atlas g y w w <=
                  &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
       ==> (\t. mfd_ricci atlas g (mfd_geo (top,atlas) g x v t)
                  (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
                  (mfd_vel atlas (mfd_geo (top,atlas) g x v) t))
           real_integrable_on real_interval[&0,&1] /\
           real_integral (real_interval[&0,&1])
             (\t. mfd_ricci atlas g (mfd_geo (top,atlas) g x v t)
                    (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
                    (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)) <=
           mfd_tnorm g x v * &2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0)`;;

(* S7 (Calabi; Petersen Lemma 7.1.9, MT Thm 1.33 trace part): Laplacian      *)
(* comparison for d_p in the barrier sense on a complete manifold with       *)
(* Ric >= -(n-1) K: at x <> p an upper barrier smooth near x with gradient   *)
(* norm 1 and Laplacian <= (n-1)(1/d + sqrt K) + e.                          *)

let CMP_LAPLACIAN_BARRIER_STATEMENT = new_definition
 `CMP_LAPLACIAN_BARRIER_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g p K.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       p IN topspace top /\ &0 <= K /\
       (!y w. y IN topspace top
              ==> --(&(dimindex(:N) - 1) * K) * (w dot (g y ** w)) <=
                  mfd_ricci atlas g y w w)
       ==> !x e. x IN topspace top /\ mfd_joinable (top,atlas) p x /\ ~(x = p) /\
                 &0 < e
                 ==> ?W phi.
                       open_in top W /\ x IN W /\ mfd_smooth_on atlas W (lift o phi) /\
                       (!y. y IN W
                            ==> mfd_joinable (top,atlas) p y /\
                                mfd_dist (top,atlas) g p y <= phi y) /\
                       phi x = mfd_dist (top,atlas) g p x /\
                       lgrad2 (metric_local atlas (chart_at atlas x) g)
                              (phi o chart_inv (chart_at atlas x))
                              (SND(chart_at atlas x) x) = &1 /\
                       llap (metric_local atlas (chart_at atlas x) g)
                            (phi o chart_inv (chart_at atlas x))
                            (SND(chart_at atlas x) x) <=
                       &(dimindex(:N) - 1) *
                       (inv(mfd_dist (top,atlas) g p x) + sqrt K) + e`;;

(* S8 (barrier at infinity for maximum principles on complete flows): the    *)
(* same for d_p^2 at every point, p included: Laplacian                      *)
(* <= 2n + 2(n-1) sqrt K d + e.                                              *)

let CMP_LAPLACIAN_BARRIER_SQ_STATEMENT = new_definition
 `CMP_LAPLACIAN_BARRIER_SQ_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas g p K.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       p IN topspace top /\ &0 <= K /\
       (!y w. y IN topspace top
              ==> --(&(dimindex(:N) - 1) * K) * (w dot (g y ** w)) <=
                  mfd_ricci atlas g y w w)
       ==> !x e. x IN topspace top /\ mfd_joinable (top,atlas) p x /\ &0 < e
                 ==> ?W phi.
                       open_in top W /\ x IN W /\ mfd_smooth_on atlas W (lift o phi) /\
                       (!y. y IN W
                            ==> mfd_joinable (top,atlas) p y /\
                                mfd_dist (top,atlas) g p y pow 2 <= phi y) /\
                       phi x = mfd_dist (top,atlas) g p x pow 2 /\
                       lgrad2 (metric_local atlas (chart_at atlas x) g)
                              (phi o chart_inv (chart_at atlas x))
                              (SND(chart_at atlas x) x) =
                       &4 * mfd_dist (top,atlas) g p x pow 2 /\
                       llap (metric_local atlas (chart_at atlas x) g)
                            (phi o chart_inv (chart_at atlas x))
                            (SND(chart_at atlas x) x) <=
                       &2 * &(dimindex(:N)) +
                       &2 * &(dimindex(:N) - 1) * sqrt K * mfd_dist (top,atlas) g p x + e`;;

(* ========================================================================= *)
(* Sanity lemmas for the vocabulary.                                         *)
(* ========================================================================= *)

let CMP_SN_ZERO = prove
 (`!k. cmp_sn k (&0) = &0`,
  GEN_TAC THEN REWRITE_TAC[cmp_sn; REAL_MUL_RZERO; SIN_0; REAL_NEG_0; REAL_EXP_0] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL] THEN MESON_TAC[]);;

let CMP_CS_ZERO = prove
 (`!k. cmp_cs k (&0) = &1`,
  GEN_TAC THEN REWRITE_TAC[cmp_cs; REAL_MUL_RZERO; COS_0; REAL_NEG_0; REAL_EXP_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[]);;

let CMP_SN_FLAT = prove
 (`!t. cmp_sn (&0) t = t`,
  REWRITE_TAC[cmp_sn; REAL_LT_REFL]);;

let CMP_CS_FLAT = prove
 (`!t. cmp_cs (&0) t = &1`,
  REWRITE_TAC[cmp_cs; REAL_LT_REFL]);;

let CMP_SN_POS_CURV = prove
 (`!k t. &0 < k ==> cmp_sn k t = sin(sqrt k * t) / sqrt k /\
                    cmp_cs k t = cos(sqrt k * t)`,
  SIMP_TAC[cmp_sn; cmp_cs]);;

(* The negative-curvature model functions are sinh and cosh. *)

let CMP_SN_NEG_CURV = prove
 (`!K t. &0 < K
         ==> cmp_sn (--K) t =
             (exp(sqrt K * t) - exp(--(sqrt K * t))) / (&2 * sqrt K) /\
             cmp_cs (--K) t = (exp(sqrt K * t) + exp(--(sqrt K * t))) / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_sn; cmp_cs; REAL_NEG_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < K ==> ~(&0 < --K) /\ ~(--K = &0)`]);;

(* The flat model volume is the Euclidean volume of the ball. *)

let CMP_VMODEL_FLAT = prove
 (`!r. &0 <= r ==> cmp_vmodel (:N) (&0) r = measure(ball(vec 0:real^N,r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_vmodel; CMP_SN_FLAT] THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. t pow (dimindex(:N) - 1)) has_real_integral
     (r pow dimindex(:N) / &(dimindex(:N)) - &0 pow dimindex(:N) / &(dimindex(:N))))
    (real_interval[&0,r])`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN
    SUBGOAL_THEN `~(&(dimindex(:N)) = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&(dimindex(:N)) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `r:real`; `&1`] MEASURE_BALL_SCALING) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(&(dimindex(:N)) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 pow dimindex(:N) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ZERO; DIMINDEX_NONZERO]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

