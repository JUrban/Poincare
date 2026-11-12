(* ========================================================================= *)
(* pc_geo_defs: definitions of the geodesics layer: velocity, geodesics,     *)
(* maximal geodesics, the exponential map and its chart form, tangent norms  *)
(* and balls, orthonormal frames, Gaussian normal charts, fields along       *)
(* curves, covariant derivative along curves, parallel and Jacobi fields,    *)
(* conjugate points, injectivity radii, local isometries, the geodesic       *)
(* spray, and the statement constant KILLING_HOPF_S3_STATEMENT.  Conventions *)
(* of pc_mfd_riem: g : A -> real^N^N and tangent vectors at x in the         *)
(* preferred chart chart_at atlas x; curves real -> A.                       *)
(*                                                                           *)
(* The definitions (mfd_differential is in pc_mfd_diff.ml).                  *)
(* ========================================================================= *)

needs "src/pc_mfd_diff.ml";;
needs "src/pc_grg_dist.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Velocity at a time t of a curve defined near t, in preferred coordinates  *)
(* at gamma t (two-sided derivative; mfd_velocity of pc_grg_dist is the      *)
(* derivative within a closed interval).                                     *)
(* ------------------------------------------------------------------------- *)

let mfd_vel = new_definition
 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) (t:real) =
    vector_derivative (\s. SND(chart_at atlas (gamma t)) (gamma(drop s)))
                      (at (lift t))`;;

(* ------------------------------------------------------------------------- *)
(* Geodesics on an open interval J (Morgan-Tian Def 1.17): gamma is          *)
(* continuous on J and in every chart c the chart curve SND c o gamma and a  *)
(* velocity field v solve y' = v, v' = -Gamma(y)(v,v) on the (open) set of   *)
(* times mapped into the chart.                                              *)
(* ------------------------------------------------------------------------- *)

let mfd_geodesic = new_definition
 `mfd_geodesic (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N) (gamma:real->A) (J:real->bool) <=>
    is_realinterval J /\ real_open J /\
    continuous_map (subtopology euclideanreal J,top) gamma /\
    !c. c IN atlas
        ==> ?v. !t. t IN J /\ gamma t IN FST c
                    ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                        (at (lift t)) /\
                        ((\s. v(drop s)) has_vector_derivative
                         --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                        (v t) (v t)))
                        (at (lift t))`;;

(* The maximal interval of the geodesic with initial point x and velocity v *)
(* (union of all geodesic intervals through 0), and the maximal geodesic     *)
(* (unspecified outside its interval).                                       *)

let mfd_geo_maxint = new_definition
 `mfd_geo_maxint (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                 (g:A->real^N^N) (x:A) (v:real^N) =
    UNIONS {J | &0 IN J /\
                ?gamma. mfd_geodesic (top,atlas) g gamma J /\
                        gamma(&0) = x /\ mfd_vel atlas gamma (&0) = v}`;;

let mfd_geo = new_definition
 `mfd_geo (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
          (g:A->real^N^N) (x:A) (v:real^N) =
    @gamma. mfd_geodesic (top,atlas) g gamma (mfd_geo_maxint (top,atlas) g x v) /\
            gamma(&0) = x /\ mfd_vel atlas gamma (&0) = v`;;

(* The exponential map at x and its maximal domain (MT Def 1.22).           *)

let mfd_exp_dom = new_definition
 `mfd_exp_dom (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
              (g:A->real^N^N) (x:A) =
    {v:real^N | &1 IN mfd_geo_maxint (top,atlas) g x v}`;;

let mfd_exp = new_definition
 `mfd_exp (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
          (g:A->real^N^N) (x:A) (v:real^N) =
    mfd_geo (top,atlas) g x v (&1)`;;

(* The exponential map in the coordinates (y,w) of a chart c of the tangent *)
(* bundle (y = SND c x, w = the vector in chart c coordinates), and its     *)
(* domain.                                                                   *)

let mfd_exp_chart = new_definition
 `mfd_exp_chart (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                (g:A->real^N^N) (c:(A->bool)#(A->real^N))
                (z:real^(N,N)finite_sum) =
    mfd_exp (top,atlas) g (chart_inv c (fstcart z))
            (chart_jac c (chart_at atlas (chart_inv c (fstcart z)))
                       (chart_inv c (fstcart z)) (sndcart z))`;;

let mfd_exp_chart_dom = new_definition
 `mfd_exp_chart_dom (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                    (g:A->real^N^N) (c:(A->bool)#(A->real^N)) =
    {z:real^(N,N)finite_sum |
       fstcart z IN IMAGE (SND c) (FST c) /\
       chart_jac c (chart_at atlas (chart_inv c (fstcart z)))
                 (chart_inv c (fstcart z)) (sndcart z)
       IN mfd_exp_dom (top,atlas) g (chart_inv c (fstcart z))}`;;

(* Norm and balls in the tangent space at x for the metric g x.             *)

let mfd_tnorm = new_definition
 `mfd_tnorm (g:A->real^N^N) (x:A) (v:real^N) = sqrt(v dot (g x ** v))`;;

let mfd_tball = new_definition
 `mfd_tball (g:A->real^N^N) (x:A) (r:real) =
    {v:real^N | mfd_tnorm g x v < r}`;;

(* Orthonormal frames at x and Gaussian normal coordinates (MT Def 1.22):   *)
(* the chart exp_x(E w) |-> w on the image of ball(0,r).                     *)

let mfd_orthonormal_frame = new_definition
 `mfd_orthonormal_frame (g:A->real^N^N) (x:A) (E:real^N^N) <=>
    transp E ** g x ** E = mat 1`;;

let mfd_normal_chart = new_definition
 `mfd_normal_chart (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) (x:A) (E:real^N^N) (r:real) =
    (IMAGE (\w. mfd_exp (top,atlas) g x (E ** w)) (ball(vec 0,r)),
     (\y. @w. w IN ball(vec 0,r) /\ mfd_exp (top,atlas) g x (E ** w) = y))`;;

(* ------------------------------------------------------------------------- *)
(* Vector fields along a curve: Y t is a tangent vector at gamma t in        *)
(* preferred coordinates; mfd_field_rep gives it in the coordinates of a     *)
(* chart c.  mfd_covd is the covariant derivative along gamma (computed in  *)
(* the preferred chart at gamma t).                                          *)
(* ------------------------------------------------------------------------- *)

let mfd_field_rep = new_definition
 `mfd_field_rep (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)
                (Y:real->real^N) (c:(A->bool)#(A->real^N)) (t:real) =
    chart_jac (chart_at atlas (gamma t)) c (gamma t) (Y t)`;;

let mfd_field_diff = new_definition
 `mfd_field_diff (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)
                 (Y:real->real^N) (J:real->bool) <=>
    !t. t IN J
        ==> (\s. mfd_field_rep atlas gamma Y (chart_at atlas (gamma t)) (drop s))
            differentiable at (lift t)`;;

let mfd_covd = new_definition
 `mfd_covd (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
           (gamma:real->A) (Y:real->real^N) (t:real) =
    vector_derivative
      (\s. mfd_field_rep atlas gamma Y (chart_at atlas (gamma t)) (drop s))
      (at (lift t)) +
    christoffel (metric_local atlas (chart_at atlas (gamma t)) g)
                (SND(chart_at atlas (gamma t)) (gamma t))
                (mfd_vel atlas gamma t) (Y t)`;;

(* Parallel fields and Jacobi fields along gamma on J (Jacobi equation of   *)
(* MT p. 12, D_t D_t Y + R(Y,gamma')gamma' = 0; unlike MT we do not require *)
(* Y = 0 at the initial point), conjugate points (MT Def 1.19).              *)

let mfd_parallel = new_definition
 `mfd_parallel (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
               (gamma:real->A) (J:real->bool) (Y:real->real^N) <=>
    mfd_field_diff atlas gamma Y J /\
    !t. t IN J ==> mfd_covd atlas g gamma Y t = vec 0`;;

let mfd_jacobi = new_definition
 `mfd_jacobi (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (gamma:real->A) (J:real->bool) (Y:real->real^N) <=>
    mfd_field_diff atlas gamma Y J /\
    mfd_field_diff atlas gamma (mfd_covd atlas g gamma Y) J /\
    !t. t IN J
        ==> mfd_covd atlas g gamma (mfd_covd atlas g gamma Y) t +
            mfd_riemann atlas g (gamma t) (Y t) (mfd_vel atlas gamma t)
                        (mfd_vel atlas gamma t) = vec 0`;;

let mfd_conjugate = new_definition
 `mfd_conjugate (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                (gamma:real->A) (J:real->bool) (a:real) (b:real) <=>
    a IN J /\ b IN J /\ ~(a = b) /\
    ?Y. mfd_jacobi atlas g gamma J Y /\ Y a = vec 0 /\ Y b = vec 0 /\
        ?t. t IN J /\ ~(Y t = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Injectivity radius.  mfd_inj_ball x r: exp_x is defined on the tangent    *)
(* ball of radius r and is a diffeomorphism of it onto an open subset of M   *)
(* (MT Def 1.26 is the sup of such r).  The intrinsic radius (as in the Lean *)
(* formalization qinz1yang/differential-geometry) only asks for injectivity  *)
(* of exp_x on the ball.  Both sups are meaningful only when bounded (e.g.   *)
(* compact M); use mfd_inj_ball as the predicate form of "r <= inj(x)".      *)
(* ------------------------------------------------------------------------- *)

let mfd_inj_ball = new_definition
 `mfd_inj_ball (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N) (x:A) (r:real) <=>
    mfd_tball g x r SUBSET mfd_exp_dom (top,atlas) g x /\
    mfd_param top atlas (mfd_tball g x r) (mfd_exp (top,atlas) g x)`;;

let mfd_injrad = new_definition
 `mfd_injrad (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
             (g:A->real^N^N) (x:A) =
    sup {r | &0 < r /\ mfd_inj_ball (top,atlas) g x r}`;;

let mfd_injrad_intrinsic = new_definition
 `mfd_injrad_intrinsic (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                       (g:A->real^N^N) (x:A) =
    sup {r | &0 < r /\ mfd_tball g x r SUBSET mfd_exp_dom (top,atlas) g x /\
             !v w. v IN mfd_tball g x r /\ w IN mfd_tball g x r /\
                   mfd_exp (top,atlas) g x v = mfd_exp (top,atlas) g x w
                   ==> v = w}`;;

(* ------------------------------------------------------------------------- *)
(* Local isometries on an open set W (no inverse, same dimension): smooth   *)
(* in chart pairs and pulling g' back to g, as in mfd_isometry of            *)
(* pc_grg_dist.                                                              *)
(* ------------------------------------------------------------------------- *)

let mfd_local_isometry = new_definition
 `mfd_local_isometry (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                     (g:A->real^N^N)
                     (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
                     (g':B->real^N^N) (W:A->bool) (f:A->B) <=>
    open_in top W /\ continuous_map (subtopology top W,top') f /\
    mfd_smooth_map atlas atlas' W f /\
    !c c' y. c IN atlas /\ c' IN atlas' /\
             y IN IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'}
             ==> metric_local atlas c g y =
                 mpullback (SND c' o f o chart_inv c) (metric_local atlas' c' g') y`;;

(* ------------------------------------------------------------------------- *)
(* The geodesic spray of a local metric G: the vector field on the chart     *)
(* tangent bundle U x real^N whose integral curves are (y,y') for geodesics. *)
(* ------------------------------------------------------------------------- *)

let geo_spray = new_definition
 `geo_spray (G:real^N->real^N^N) (z:real^(N,N)finite_sum) =
    pastecart (sndcart z)
              (--(christoffel G (fstcart z) (sndcart z) (sndcart z)))`;;

(* ------------------------------------------------------------------------- *)
(* Killing-Hopf in dimension 3 (MT Thm 1.11(2), n = 3, lambda = 1), compact  *)
(* case, in the isometry form: the argument only fixes the type A.           *)
(* ------------------------------------------------------------------------- *)

let KILLING_HOPF_S3_STATEMENT = new_definition
 `KILLING_HOPF_S3_STATEMENT (u:A->bool) <=>
    !top atlas (g:A->real^3^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ ~(topspace top = {}) /\ simply_connected_space top /\
        riemannian_metric atlas g /\
        (!x v w. x IN topspace top /\ ~collinear {vec 0,v,w}
                 ==> mfd_sectional atlas g x v w = &1)
        ==> ?f f'. mfd_isometry
                     (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                     round3_metric (top,atlas) g f f'`;;

(* ========================================================================= *)
(* Sanity theorems.  The hypotheses of                                       *)
(* KILLING_HOPF_S3_STATEMENT are satisfiable (the round S^3), so the        *)
(* statement is not vacuous; christoffel G y 0 0 = 0 for every G, hence     *)
(* constant curves are geodesics without any hypothesis on g.               *)
(* ========================================================================= *)

let KILLING_HOPF_HYPOTHESES_SPHERE3 = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^4,&1)))
                         sphere3_atlas /\
   compact_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   ~(topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) = {}) /\
   simply_connected_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   riemannian_metric sphere3_atlas round3_metric /\
   (!x u v. x IN topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
            ~collinear {vec 0,u,v}
            ==> mfd_sectional sphere3_atlas round3_metric x u v = &1)`,
  REWRITE_TAC[POINCARE_SMOOTH_HYPOTHESES_SPHERE_3; ROUND3_METRIC] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[ROUND3_SECTIONAL]);;

(* The constant curve is a geodesic: proved from the definition (checks    *)
(* that christoffel G y 0 0 = 0 holds without any hypothesis on G).          *)

let GEO_CHRISTOFFEL_ZERO = prove
 (`!(G:real^N->real^N^N) y. christoffel G y (vec 0) (vec 0) = vec 0`,
  REWRITE_TAC[christoffel; MATRIX_VECTOR_MUL_RZERO; VEC_COMPONENT; DOT_LZERO] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(lambda k. &0):real^N = vec 0` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

let MFD_GEODESIC_CONST_PROVED = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        x IN topspace top
        ==> mfd_geodesic (top,atlas) g (\t. x) (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_geodesic] THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; REAL_OPEN_UNIV] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  EXISTS_TAC `\t:real. vec 0:real^N` THEN
  REWRITE_TAC[GEO_CHRISTOFFEL_ZERO; VECTOR_NEG_0] THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]);;

