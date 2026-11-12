(* ========================================================================= *)
(* pc_geo_iface: the API of the geodesics layer.  This file loads the units  *)
(* that prove its names, so that dependents load pc_geo_iface for the whole  *)
(* layer; the comments below list each name with the unit that proves it.    *)
(* Where the names are proved: GEO_LOCAL_HOMEO_SC_BIJECTIVE (pc_geo_cover,   *)
(* from pc_top_cover), GEO_MANIFOLD_LOCALLY_PATH_CONNECTED and               *)
(* GEO_BIJECTIVE_LOCAL_DIFFEO (pc_mfd_diff), the names of the sections       *)
(* pc_geo_local, pc_geo_max, pc_geo_flow, pc_geo_covd, pc_geo_param,         *)
(* pc_geo_gauss, pc_geo_dist and pc_geo_hr (those units; pc_geo_dist proves  *)
(* four of its six names), MFD_COVD_COMMUTATOR (pc_cmp_comm) and             *)
(* MFD_PARALLEL_INNER, MFD_JACOBI_LINEAR, MFD_JACOBI_TANGENTIAL              *)
(* (pc_cmp_gfacts), MFD_PARALLEL_EXISTS_UNIQUE (pc_geo_par),                 *)
(* MFD_JACOBI_EXISTS_UNIQUE (pc_geo_jacobi), the variation and d(exp)        *)
(* theorems (pc_geo_jvar), constant curvature (pc_geo_const) and local       *)
(* isometries, Cartan, MFD_INJ_BALL_MONO (pc_geo_lisom), the round 3-sphere  *)
(* (pc_geo_s3), MFD_MINIMIZING_IMP_GEODESIC (pc_cmp_min) and the             *)
(* Killing-Hopf theorem (pc_geo_kh), injectivity radius (pc_geo_inj),        *)
(* conjugate points (pc_geo_conj) and Gaussian normal coordinates            *)
(* (pc_geo_normal).  The ODE names used in MFD_GEODESIC_SPRAY come from      *)
(* pc_ode_defs.ml (definitions only).                                        *)
(* ========================================================================= *)

needs "src/pc_geo_defs.ml";;
needs "src/pc_ode_defs.ml";;
needs "src/pc_geo_cover.ml";;
needs "src/pc_geo_local.ml";;
needs "src/pc_geo_max.ml";;
needs "src/pc_geo_flow.ml";;
needs "src/pc_geo_covd.ml";;
needs "src/pc_geo_param.ml";;
needs "src/pc_geo_gauss.ml";;
needs "src/pc_geo_dist.ml";;
needs "src/pc_cmp_comm.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_cmp_gfacts.ml";;
needs "src/pc_geo_par.ml";;
needs "src/pc_geo_jacobi.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_geo_s3.ml";;
needs "src/pc_cmp_min.ml";;
needs "src/pc_geo_kh.ml";;
needs "src/pc_geo_inj.ml";;
needs "src/pc_geo_conj.ml";;
needs "src/pc_geo_normal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* pc_geo_local.  Chart level: the geodesic equation is chart independent   *)
(* (pc_lrg naturality LCHRISTOFFEL_PULLBACK), local existence, uniqueness,  *)
(* smoothness (the ODE package, pc_ode_vf), constant speed,                 *)
(* reparametrization, the ODE link with the spray, the flat teeth test.     *)
(* ------------------------------------------------------------------------- *)

(* MFD_GEODESIC_CHART_TRANS: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_CONST: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_SUBINTERVAL: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_EXISTS_LOCAL: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_UNIQUE: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_VEL_CHART: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_SMOOTH: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_SPEED: proved in pc_geo_local.ml (loaded above). *)

(* MFD_GEODESIC_AFFINE: proved in pc_geo_local.ml (loaded above). *)

(* A geodesic, read in a chart c along a time segment inside the chart, is  *)
(* the flow of the spray of the chart metric (ODE package, autonomous form). *)

(* MFD_GEODESIC_SPRAY: proved in pc_geo_local.ml (loaded above). *)

(* Teeth tests: in flat real^N geodesics are the affine lines, exp_x v = x+v *)

(* MFD_GEODESIC_EUCLIDEAN: proved in pc_geo_local.ml (loaded above). *)

(* MFD_EXP_EUCLIDEAN: proved in pc_geo_local.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_max.  Maximal geodesics (Hausdorff: no branching), group and       *)
(* rescaling laws, the link with the C^1 curves and lengths of the pc_grg    *)
(* units.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* MFD_GEO_MAXINT_OUTSIDE: proved in pc_geo_max.ml (loaded above). *)

(* MFD_GEO_MAXIMAL: proved in pc_geo_max.ml (loaded above). *)

(* MFD_GEO_MAXIMAL_UNIQUE: proved in pc_geo_max.ml (loaded above). *)

(* MFD_GEO_SHIFT: proved in pc_geo_max.ml (loaded above). *)

(* MFD_GEO_RESCALE: proved in pc_geo_max.ml (loaded above). *)

(* MFD_GEODESIC_C1_CURVE: proved in pc_geo_max.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_flow.  The exponential map: domain, smoothness (jointly on the     *)
(* tangent bundle, in chart coordinates), d(exp_x) at 0, normal and         *)
(* uniformly normal neighbourhoods (inverse function theorem), the escape    *)
(* lemma and geodesic completeness of compact manifolds.                     *)
(* ------------------------------------------------------------------------- *)

(* MFD_EXP_DOM: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_EXP_RADIAL: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_EXP_SMOOTH: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_EXP_CHART_SMOOTH: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_EXP_DIFFERENTIAL_ZERO: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_EXP_LOCAL_DIFFEO: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_UNIFORMLY_NORMAL: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_GEO_ESCAPE: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_COMPACT_GEO_COMPLETE: proved in pc_geo_flow.ml (loaded above). *)

(* MFD_LOCAL_PARAM: proved in pc_geo_param.ml (loaded above). *)


(* ------------------------------------------------------------------------- *)
(* pc_geo_covd.  Covariant derivative along curves: chart form, metric      *)
(* compatibility, geodesics have parallel velocity, the symmetry lemma for  *)
(* two-parameter maps (torsion freeness).                                    *)
(* ------------------------------------------------------------------------- *)

(* MFD_COVD_CHART: proved in pc_geo_covd.ml (loaded above). *)

(* MFD_COVD_METRIC: proved in pc_geo_covd.ml (loaded above). *)

(* MFD_GEODESIC_VEL_PARALLEL: proved in pc_geo_covd.ml (loaded above). *)

(* D_s d_t f = D_t d_s f for a map f(s,t), smooth in every chart.           *)

(* MFD_COVD_SYMMETRY: proved in pc_geo_covd.ml (loaded above). *)

(* D_s D_t Z - D_t D_s Z = R(f_s,f_t) Z (proved in pc_cmp_comm.ml, a unit
   on top of pc_geo_covd). *)

(* MFD_COVD_COMMUTATOR: proved in pc_cmp_comm.ml (loaded above). *)


(* ------------------------------------------------------------------------- *)
(* pc_geo_jacobi.  Parallel transport and Jacobi fields along geodesics     *)
(* (linear ODE in charts, ODE_LINEAR_INTERVAL), the Jacobi equation for     *)
(* variations through geodesics (MT p. 12), d(exp) by Jacobi fields         *)
(* (MT p. 14-15), the Gauss lemma, conjugate points and singular exp.        *)
(* ------------------------------------------------------------------------- *)

(* MFD_PARALLEL_EXISTS_UNIQUE: proved in pc_geo_par.ml (loaded above). *)

(* MFD_PARALLEL_INNER: proved in pc_cmp_gfacts.ml (loaded above). *)

(* MFD_JACOBI_EXISTS_UNIQUE: proved in pc_geo_jacobi.ml (loaded above). *)

(* MFD_JACOBI_LINEAR: proved in pc_cmp_gfacts.ml (loaded above). *)

(* MFD_JACOBI_TANGENTIAL: proved in pc_cmp_gfacts.ml (loaded above). *)

(* The variation field of a smooth family of geodesics is a Jacobi field.   *)

(* MFD_GEODESIC_VARIATION_JACOBI: proved in pc_geo_jvar.ml (loaded above). *)

(* MFD_EXP_DIFFERENTIAL_JACOBI: proved in pc_geo_jvar.ml (loaded above). *)

(* MFD_GAUSS_LEMMA: proved in pc_geo_gauss.ml (loaded above). *)

(* MFD_EXP_SINGULAR_CONJUGATE: proved in pc_geo_conj.ml (loaded above). *)

(* Teeth tests: no conjugate points in flat space; antipodal points of the   *)
(* round S^3 are conjugate along great circles (the definition has content). *)

(* MFD_NOT_CONJUGATE_EUCLIDEAN: proved in pc_geo_conj.ml (loaded above). *)

(* MFD_CONJUGATE_SPHERE3_PI: proved in pc_geo_s3.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_dist.  Exponential map and distance: geodesic balls are metric    *)
(* balls, radial geodesics minimize, geodesics locally minimize, Gaussian   *)
(* normal coordinates; minimizing constant-speed curves are geodesics.      *)
(* ------------------------------------------------------------------------- *)

(* MFD_EXP_DIST: proved in pc_geo_dist.ml (loaded above) *)

(* MFD_EXP_BALL: proved in pc_geo_dist.ml (loaded above) *)

(* MFD_GEODESIC_LOCALLY_MINIMIZING: proved in pc_geo_dist.ml (loaded above) *)

(* MFD_NORMAL_CHART: proved in pc_geo_normal.ml (loaded above). *)

(* MFD_MINIMIZING_IMP_GEODESIC: proved in pc_cmp_min.ml (loaded above). *)

(* Equality case of MFD_EXP_DIST (pc_geo_dist). *)

(* MFD_EXP_DIST_EQUALITY: proved in pc_geo_dist.ml (loaded above) *)


(* ------------------------------------------------------------------------- *)
(* pc_geo_hr.  Hopf-Rinow (MT Thm 1.18 and the standard equivalences) and   *)
(* minimizing geodesics.                                                     *)
(* ------------------------------------------------------------------------- *)

(* MFD_EXP_TOTAL_MINIMIZING: proved in pc_geo_hr.ml (loaded above) *)

(* MFD_COMPLETE_GEO_COMPLETE: proved in pc_geo_hr.ml (loaded above) *)

(* MFD_HOPF_RINOW: proved in pc_geo_hr.ml (loaded above) *)

(* MFD_HOPF_RINOW_POINT: proved in pc_geo_hr.ml (loaded above) *)

(* MFD_COMPLETE_MINIMIZING_GEODESIC: proved in pc_geo_hr.ml (loaded above) *)

(* MFD_COMPLETE_EXP_ONTO: proved in pc_geo_hr.ml (loaded above) *)

(* Local Hopf-Rinow (pc_geo_hr). *)

(* MFD_LOCAL_HOPF_RINOW: proved in pc_geo_hr.ml (loaded above) *)


(* ------------------------------------------------------------------------- *)
(* pc_geo_inj.  Injectivity radius: monotonicity, closure under increasing   *)
(* unions, uniform positivity on compact manifolds, comparison with the      *)
(* intrinsic radius (injectivity of exp_x only, as in the Lean formalization *)
(* qinz1yang/differential-geometry).                                         *)
(* ------------------------------------------------------------------------- *)

(* MFD_INJ_BALL_MONO: proved in pc_geo_lisom.ml (loaded above). *)

(* MFD_INJ_BALL_SUP: proved in pc_geo_inj.ml (loaded above). *)

(* MFD_INJRAD_COMPACT: proved in pc_geo_inj.ml (loaded above). *)

(* MFD_INJRAD_LE_INTRINSIC: proved in pc_geo_inj.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_cover.  General topology: manifolds are locally path connected    *)
(* (proved in pc_mfd_diff); a local homeomorphism from a compact Hausdorff  *)
(* path-connected space to a Hausdorff simply connected space is a          *)
(* bijection (proved in pc_geo_cover, from pc_top_cover); a bijective local *)
(* diffeomorphism is a diffeomorphism (proved in pc_mfd_diff).              *)
(* ------------------------------------------------------------------------- *)

(* GEO_MANIFOLD_LOCALLY_PATH_CONNECTED: proved in pc_mfd_diff.ml (loaded via pc_geo_defs). *)

(* GEO_LOCAL_HOMEO_SC_BIJECTIVE: proved in pc_geo_cover.ml (loaded above). *)

(* GEO_BIJECTIVE_LOCAL_DIFFEO: proved in pc_mfd_diff.ml (loaded via pc_geo_defs). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_const.  Constant curvature, local isometries, Cartan's lemma.     *)
(* ------------------------------------------------------------------------- *)

(* MFD_SECTIONAL_CONST_RIEMANN: proved in pc_geo_const.ml (loaded above). *)

(* MFD_JACOBI_CONST1: proved in pc_geo_const.ml (loaded above). *)

(* MFD_EXP_DIFFERENTIAL_CONST1: proved in pc_geo_const.ml (loaded above). *)

(* MFD_LOCAL_ISOMETRY_GEODESIC: proved in pc_geo_lisom.ml (loaded above). *)

(* MFD_LOCAL_ISOMETRY_EXP: proved in pc_geo_lisom.ml (loaded above). *)

(* MFD_LOCAL_ISOMETRY_RIGID: proved in pc_geo_lisom.ml (loaded above). *)

(* MFD_CARTAN_CONST1: proved in pc_geo_lisom.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_s3.  The model: the round S^3 (sphere3_atlas, round3_metric of    *)
(* pc_rf_basic) carries the metric induced from real^4, great circles are   *)
(* geodesics, exp at q is explicit and maps the tangent ball of radius pi   *)
(* diffeomorphically onto the sphere minus -q.                               *)
(* ------------------------------------------------------------------------- *)

(* SPHERE3_ROUND_INDUCED: proved in pc_geo_s3.ml (loaded above). *)

(* SPHERE3_GREAT_CIRCLE: proved in pc_geo_s3.ml (loaded above). *)

(* SPHERE3_EXP: proved in pc_geo_s3.ml (loaded above). *)

(* SPHERE3_EXP_BALL_PI: proved in pc_geo_s3.ml (loaded above). *)

(* Teeth test of the injectivity radius: inj = pi on the round S^3.          *)

(* MFD_INJRAD_SPHERE3: proved in pc_geo_s3.ml (loaded above). *)

(* ------------------------------------------------------------------------- *)
(* pc_geo_kh.  Killing-Hopf in dimension 3 (MT Thm 1.11(2) for n = 3,       *)
(* lambda = 1), compact case, by Cartan's lemma, rigidity and the covering  *)
(* argument; the component form used for RFS_LISTED_SC_S3_STATEMENT (its     *)
(* rfs_space_form case, with the body of rfs_space_form written out).        *)
(* ------------------------------------------------------------------------- *)

(* KILLING_HOPF_S3_ISOMETRY: proved in pc_geo_kh.ml (loaded above). *)

(* KILLING_HOPF_S3: proved in pc_geo_kh.ml (loaded above). *)

(* KILLING_HOPF_COMPONENT: proved in pc_geo_kh.ml (loaded above). *)

