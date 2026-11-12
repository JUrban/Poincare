(* ========================================================================= *)
(* pc_mfd_fields: a small vocabulary for fields on manifolds: the Lie        *)
(* derivative llie of a matrix field along a vector field and the Riemannian *)
(* divergence ldiv on open sets of real^N; the divergence mfd_div of a       *)
(* vector field on a manifold (preferred coordinates); smooth                *)
(* symmetric-2-tensor-type fields mfd_tensor2_smooth (matrices in preferred  *)
(* coordinates with the transformation law of metrics).  Basic facts:        *)
(* locality, metrics are smooth tensor fields, linearity of chart            *)
(* representatives.  (The pullback of a metric by a map is                   *)
(* mfd_pullback_metric of pc_mfd_restrict.)                                  *)
(* ========================================================================= *)

needs "src/pc_lrg.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

(* Lie derivative of a matrix field G along a vector field X on real^N:     *)
(* (L_X G)_ij = X^k d_k G_ij + G_kj d_i X^k + G_ik d_j X^k.                  *)

let llie = new_definition
 `llie (X:real^N->real^N) (G:real^N->real^N^N) (y:real^N) =
    mderiv G y (X y) +
    transp(matrix(frechet_derivative X (at y))) ** G y +
    G y ** matrix(frechet_derivative X (at y))`;;

(* Riemannian divergence d_i Z^i + Gamma^i_ik Z^k of a vector field.         *)

let ldiv = new_definition
 `ldiv (G:real^N->real^N^N) (Z:real^N->real^N) (y:real^N) =
    trace(matrix(frechet_derivative Z (at y))) +
    sum(1..dimindex(:N)) (\i. (christoffel G y (basis i) (Z y))$i)`;;

(* The divergence of a vector field Z on a manifold (Z given by its          *)
(* coordinate vectors in the preferred charts, as for mfd_vrep).             *)

let mfd_div = new_definition
 `mfd_div (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Z:A->real^N) (x:A) =
    ldiv (metric_local atlas (chart_at atlas x) g)
         (mfd_vrep atlas Z (chart_at atlas x)) (SND(chart_at atlas x) x)`;;

(* Smooth fields of bilinear forms (matrices in preferred coordinates,       *)
(* transforming like metrics): all chart representatives are smooth.         *)

let mfd_tensor2_smooth = new_definition
 `mfd_tensor2_smooth (atlas:((A->bool)#(A->real^N))->bool) (v:A->real^N^N) <=>
    !c. c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c))
              ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c v)`;;

(* ------------------------------------------------------------------------- *)
(* Locality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MDERIV_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y w.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> mderiv G1 y w = mderiv G2 y w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[o_THM]);;

let LLIE_LOCAL = prove
 (`!(X1:real^N->real^N) X2 (G1:real^N->real^N^N) G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> X1 z = X2 z /\ G1 z = G2 z)
        ==> llie X1 G1 y = llie X2 G2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(X1:real^N->real^N) y = X2 y /\ (G1:real^N->real^N^N) y = G2 y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (X1:real^N->real^N) (at y) = frechet_derivative X2 (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. mderiv (G1:real^N->real^N^N) y w = mderiv G2 y w` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MDERIV_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[llie]);;

let LDIV_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 (Z1:real^N->real^N) Z2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z /\ Z1 z = Z2 z)
        ==> ldiv G1 Z1 y = ldiv G2 Z2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Z1:real^N->real^N) y = Z2 y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Z1:real^N->real^N) (at y) = frechet_derivative Z2 (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. christoffel (G1:real^N->real^N^N) y u v = christoffel G2 y u v`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ldiv]);;

(* ------------------------------------------------------------------------- *)
(* Chart representatives are linear in the field; metrics are smooth tensor  *)
(* fields; smooth tensor fields form a vector space.                         *)
(* ------------------------------------------------------------------------- *)

let METRIC_LOCAL_ADD = prove
 (`!atlas c (g:A->real^N^N) h.
        metric_local atlas c (\x. g x + h x) =
        (\y. metric_local atlas c g y + metric_local atlas c h y)`,
  REWRITE_TAC[metric_local; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB]);;

let METRIC_LOCAL_SUB = prove
 (`!atlas c (g:A->real^N^N) h.
        metric_local atlas c (\x. g x - h x) =
        (\y. metric_local atlas c g y - metric_local atlas c h y)`,
  REWRITE_TAC[metric_local; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB]);;

let RIEMANNIAN_METRIC_TENSOR2_SMOOTH = prove
 (`!atlas (g:A->real^N^N).
        riemannian_metric atlas g ==> mfd_tensor2_smooth atlas g`,
  REWRITE_TAC[riemannian_metric; metric_field; mfd_tensor2_smooth] THEN
  MESON_TAC[]);;

let MFD_TENSOR2_SMOOTH_ADD = prove
 (`!top atlas (g:A->real^N^N) h.
        smooth_manifold_atlas top atlas /\
        mfd_tensor2_smooth atlas g /\ mfd_tensor2_smooth atlas h
        ==> mfd_tensor2_smooth atlas (\x. g x + h x)`,
  REWRITE_TAC[mfd_tensor2_smooth; METRIC_LOCAL_ADD; o_DEF; VECTORIZE_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let MFD_TENSOR2_SMOOTH_SUB = prove
 (`!top atlas (g:A->real^N^N) h.
        smooth_manifold_atlas top atlas /\
        mfd_tensor2_smooth atlas g /\ mfd_tensor2_smooth atlas h
        ==> mfd_tensor2_smooth atlas (\x. g x - h x)`,
  REWRITE_TAC[mfd_tensor2_smooth; METRIC_LOCAL_SUB; o_DEF; VECTORIZE_SUB] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let MFD_TENSOR2_SMOOTH_CMUL = prove
 (`!top atlas (g:A->real^N^N) k.
        smooth_manifold_atlas top atlas /\ mfd_tensor2_smooth atlas g
        ==> mfd_tensor2_smooth atlas (\x. k %% g x)`,
  REWRITE_TAC[mfd_tensor2_smooth; METRIC_LOCAL_CMUL; o_DEF; VECTORIZE_CMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

