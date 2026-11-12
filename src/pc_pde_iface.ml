(* ========================================================================= *)
(* Unit pc_pde_iface: the statement layer of the PDE part.  First the        *)
(* manifold-level definitions read by the statements (families smooth up to  *)
(* an initial time, tr_k Hess_h, the linear system of the iteration, finite  *)
(* chart covers and chart bounds, the Ricci-DeTurck operator and flow, the   *)
(* Kotschwar density, the frozen-coefficient step).  Then the statement      *)
(* constants: Part 1 the statements I1-I7 of the PDE layer used by the rest  *)
(* of the proof (proved in pc_pde_final, pc_rf_unique and pc_rf_glue),       *)
(* Part 2 the statements R1-R3 proved in other layers, Part 3 the            *)
(* intermediate statements M1, M2, M3, M5.  Names: llie, ldiv, mfd_div,      *)
(* mfd_tensor2_smooth (pc_mfd_fields), mfd_pullback_metric                   *)
(* (pc_mfd_restrict).                                                        *)
(* ========================================================================= *)

needs "src/pc_pde_base.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_lrg_tensor.ml";;
needs "src/pc_mfd_fields.ml";;
needs "src/pc_mfd_restrict.ml";;

prioritize_real();;
type_invention_error := true;;

(* Time-dependent families of bilinear forms (matrices in preferred          *)
(* coordinates) smooth in every chart up to the initial time a (as in        *)
(* ricci_flow_from).                                                         *)
let pde_tfam_from = new_definition
 `pde_tfam_from (atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
                (v:real->A->real^N^N) <=>
    !c. c IN atlas
        ==> ?e F. &0 < e /\
                  smooth_map_on
                    (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) F /\
                  !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                        ==> F(pastecart (lift t) y) =
                            (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas c (v t) y)`;;

(* Scalar families e : real -> A -> real smooth in charts up to time a.     *)
let pde_sfun_from = new_definition
 `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
                (e:real->A->real) <=>
    !c. c IN atlas
        ==> ?d F. &0 < d /\
                  smooth_map_on
                    (interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST c)) F /\
                  !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                        ==> F(pastecart (lift t) y) = lift(e t (chart_inv c y))`;;

(* The K-trace of the H-Hessian of a field of bilinear forms V, locally:     *)
(* (tr_K Hess_H V)_ij = sum_pq K^pq (nabla^2 V)(e_i,e_j;e_p,e_q).            *)
let pde_ltrhess = new_definition
 `pde_ltrhess (K:real^N->real^N^N) (H:real^N->real^N^N) (V:real^N->real^N^N)
              (y:real^N) =
    (lambda i j.
       sum(1..dimindex(:N))
        (\p. sum(1..dimindex(:N))
          (\q. matrix_inv(K y)$p$q *
               lnabla_iter 2 2 H (lmetric2 V) y
                 (\m. if m = 1 then basis i else if m = 2 then basis j
                      else if m = 3 then basis p else basis q)))):real^N^N`;;

(* tr_k Hess_h v on a manifold, in preferred coordinates.                    *)
let pde_trhess = new_definition
 `pde_trhess (atlas:((A->bool)#(A->real^N))->bool) (k:A->real^N^N) (h:A->real^N^N)
             (v:A->real^N^N) (x:A) =
    pde_ltrhess (metric_local atlas (chart_at atlas x) k)
                (metric_local atlas (chart_at atlas x) h)
                (metric_local atlas (chart_at atlas x) v)
                (SND(chart_at atlas x) x)`;;

(* Solutions of d/dt v = tr_k(t) Hess_h v + f(t) on [a,b), smooth up to a,   *)
(* with v(a) = v0.                                                           *)
let pde_mlin_sol = new_definition
 `pde_mlin_sol (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (a:real) (b:real) (k:real->A->real^N^N) (h:A->real^N^N)
               (f:real->A->real^N^N) (v0:A->real^N^N) (v:real->A->real^N^N) <=>
    pde_tfam_from atlas a b v /\
    (!x. x IN topspace top ==> v a x = v0 x) /\
    (!t x i j. a < t /\ t < b /\ x IN topspace top /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. v s x$i$j) has_real_derivative
                    (pde_trhess atlas (k t) h (v t) x + f t x)$i$j) (atreal t))`;;

(* Finite chart covers: charts cs i (i < n0) of the atlas with compact      *)
(* pieces ks i of their images; the inverse images of the interiors of the  *)
(* pieces cover the space.                                                   *)
let pde_cover = new_definition
 `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (n0:num)
            (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool) <=>
    (!i. i < n0 ==> cs i IN atlas /\ compact(ks i) /\
                    ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))) /\
    topspace top = UNIONS {IMAGE (chart_inv (cs i)) (interior(ks i)) | i < n0}`;;

(* Chart C^m bounds of size B on the pieces, and lower bound 1/B.          *)
let pde_cbound = new_definition
 `pde_cbound (atlas:((A->bool)#(A->real^N))->bool) (n0:num)
             (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool)
             (m:num) (B:real) (g:A->real^N^N) <=>
    !i. i < n0
        ==> (!l y. l IN pde_index_lists m (:N) /\ y IN ks i
                   ==> norm(iterated_partial l
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) g) y) <= B) /\
            (!y v. y IN ks i ==> norm v pow 2 <= B * (v dot (metric_local atlas (cs i) g y ** v)))`;;

(* The DeTurck vector field W(g,h)^k = g^ij (Gamma(g)^k_ij - Gamma(h)^k_ij), *)
(* in preferred coordinates.                                                 *)
let pde_deturck = new_definition
 `pde_deturck (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (h:A->real^N^N)
              (x:A) =
    vsum(1..dimindex(:N))
     (\i. vsum(1..dimindex(:N))
       (\j. matrix_inv(g x)$i$j %
            (christoffel (metric_local atlas (chart_at atlas x) g)
                         (SND(chart_at atlas x) x) (basis i) (basis j) -
             christoffel (metric_local atlas (chart_at atlas x) h)
                         (SND(chart_at atlas x) x) (basis i) (basis j))))`;;

(* Local Ricci matrix, local DeTurck field, local Ricci-DeTurck operator     *)
(* -2 Ric(G) + L_W G with W = W(G,H); the manifold operator is the local   *)
(* one in preferred coordinates.                                             *)
let pde_lricci_matrix = new_definition
 `pde_lricci_matrix (G:real^N->real^N^N) (y:real^N) =
    (lambda i j. lricci G y (basis i) (basis j)):real^N^N`;;

let pde_ldeturck = new_definition
 `pde_ldeturck (H:real^N->real^N^N) (G:real^N->real^N^N) (y:real^N) =
    vsum(1..dimindex(:N))
     (\i. vsum(1..dimindex(:N))
       (\j. matrix_inv(G y)$i$j %
            (christoffel G y (basis i) (basis j) - christoffel H y (basis i) (basis j))))`;;

let pde_lrdt = new_definition
 `pde_lrdt (H:real^N->real^N^N) (G:real^N->real^N^N) (y:real^N) =
    --(&2) %% pde_lricci_matrix G y + llie (pde_ldeturck H G) G y`;;

let pde_rdt_rhs = new_definition
 `pde_rdt_rhs (atlas:((A->bool)#(A->real^N))->bool) (h:A->real^N^N) (g:A->real^N^N)
              (x:A) =
    pde_lrdt (metric_local atlas (chart_at atlas x) h)
             (metric_local atlas (chart_at atlas x) g) (SND(chart_at atlas x) x)`;;

(* Ricci-DeTurck flows with background h on [a,b), smooth up to a.          *)
let pde_rdt_flow_from = new_definition
 `pde_rdt_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                    (h:A->real^N^N) (a:real) (b:real) (g:real->A->real^N^N) <=>
    smooth_manifold_atlas top atlas /\ a < b /\
    (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
    pde_tfam_from atlas a b g /\
    (!t x i j. a < t /\ t < b /\ x IN topspace top /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. g s x$i$j) has_real_derivative
                    (pde_rdt_rhs atlas h (g t) x)$i$j) (atreal t))`;;

(* Kotschwar density |G1-G2|^2 + |Gamma1-Gamma2|^2 + |Rm1-Rm2|^2 (norms of G1). *)
let pde_kot_density = new_definition
 `pde_kot_density (G1:real^N->real^N^N) (G2:real^N->real^N^N) (y:real^N) =
    ltnorm2 2 G1 (\z u. lmetric2 G1 z u - lmetric2 G2 z u) y +
    ltnorm2 3 G1 (\z u. u 3 dot (G1 z ** (christoffel G1 z (u 1) (u 2) -
                                           christoffel G2 z (u 1) (u 2)))) y +
    ltnorm2 4 G1 (\z u. u 4 dot (G1 z ** (lriemann G1 z (u 1) (u 2) (u 3) -
                                           lriemann G2 z (u 1) (u 2) (u 3)))) y`;;

let pde_mkot_density = new_definition
 `pde_mkot_density (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N)
                   (g2:A->real^N^N) (x:A) =
    pde_kot_density (metric_local atlas (chart_at atlas x) g1)
                    (metric_local atlas (chart_at atlas x) g2)
                    (SND(chart_at atlas x) x)`;;

(* The frozen-coefficient step of the Ricci-DeTurck iteration (background   *)
(* and initial metric h).                                                    *)
let pde_rdt_step = new_definition
 `pde_rdt_step (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
               (h:A->real^N^N) (g:real->A->real^N^N) (v:real->A->real^N^N) <=>
    pde_mlin_sol (top,atlas) a b g h
      (\t x. pde_rdt_rhs atlas h (g t) x - pde_trhess atlas (g t) h (g t) x) h v`;;

(* ========================================================================= *)
(* The statement constants.  Each argument u, n only fixes a type (carrier   *)
(* A, dimension N).                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Part 1. The statements of the PDE layer used by the rest of the proof.    *)
(* ------------------------------------------------------------------------- *)

(* I1. Short-time existence (MT Thm 3.11, existence; Hamilton, DeTurck),    *)
(* smooth up to the initial time.                                           *)

let PDE_STE_STATEMENT = new_definition
 `PDE_STE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g0:A->real^N^N) a.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g0
        ==> ?b g. a < b /\ ricci_flow_from (top,atlas) a b g /\
                  !x. x IN topspace top ==> g a x = g0 x`;;

(* I2. Uniform short-time existence: for a fixed finite chart cover the     *)
(* existence time depends only on chart C^m bounds of the initial metric.   *)

let PDE_STE_UNIFORM_STATEMENT = new_definition
 `PDE_STE_UNIFORM_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks
        ==> ?m. !B. ?tau. &0 < tau /\
                  !(g0:A->real^N^N) a.
                      riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks m B g0
                      ==> ?g. ricci_flow_from (top,atlas) a (a + tau) g /\
                              !x. x IN topspace top ==> g a x = g0 x`;;

(* I3. Uniqueness (MT Thm 3.11, second part, cited there from Hamilton):    *)
(* two flows smooth up to the same initial time with the same initial       *)
(* metric agree on the common interval.                                      *)

let PDE_UNIQUENESS_STATEMENT = new_definition
 `PDE_UNIQUENESS_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b b'
     (g:real->A->real^N^N) g'.
        hausdorff_space top /\ compact_space top /\
        ricci_flow_from (top,atlas) a b g /\ ricci_flow_from (top,atlas) a b' g' /\
        (!x. x IN topspace top ==> g' a x = g a x)
        ==> !t x. a <= t /\ t < b /\ t < b' /\ x IN topspace top ==> g' t x = g t x`;;

(* I4. Extension criterion (MT Prop 4.12): a flow on [a,b) with bounded      *)
(* curvature extends past b.                                                 *)

let PDE_EXTENSION_STATEMENT = new_definition
 `PDE_EXTENSION_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g:real->A->real^N^N) B.
        hausdorff_space top /\ compact_space top /\ 2 <= dimindex(:N) /\
        ricci_flow_from (top,atlas) a b g /\
        (!t x. a <= t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= B)
        ==> ?b' g'. b < b' /\ ricci_flow_from (top,atlas) a b' g' /\
                    !t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x`;;

(* I5. Maximal flows: the flow from g0 exists for all times, or on [a,b)     *)
(* with unbounded curvature (the slab condition rfs_slab_maximal of          *)
(* pc_rfs_history).                                                          *)

let PDE_MAXIMAL_FLOW_STATEMENT = new_definition
 `PDE_MAXIMAL_FLOW_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g0:A->real^N^N) a.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        2 <= dimindex(:N) /\ riemannian_metric atlas g0
        ==> ?g. (!x. x IN topspace top ==> g a x = g0 x) /\
                ((!b. a < b ==> ricci_flow_from (top,atlas) a b g) \/
                 (?b. a < b /\ ricci_flow_from (top,atlas) a b g /\
                      !B. ?t x. a <= t /\ t < b /\ x IN topspace top /\
                                B < mfd_rm_norm atlas (g t) x))`;;

(* I6. Existence time controlled by curvature (MT Prop 4.11 curvature part,  *)
(* Claim 15.1 first part, with dimensional constants c, C instead of MT's    *)
(* 2^-4 and 2, which depend on MT's undefined norm).                         *)

let PDE_CURVATURE_TIME_STATEMENT = new_definition
 `PDE_CURVATURE_TIME_STATEMENT (u:A->bool) (n:N->bool) <=>
    ?c C. &0 < c /\ &0 < C /\
      !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g0:A->real^N^N) a K.
          hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
          2 <= dimindex(:N) /\ riemannian_metric atlas g0 /\ &0 < K /\
          (!x. x IN topspace top ==> mfd_rm_norm atlas g0 x <= K)
          ==> ?b g. a + c / K < b /\ ricci_flow_from (top,atlas) a b g /\
                    (!x. x IN topspace top ==> g a x = g0 x) /\
                    !t x. a <= t /\ t <= a + c / K /\ x IN topspace top
                          ==> mfd_rm_norm atlas (g t) x <= C * K`;;

(* I7. Gluing in time (MT Prop 3.12), on any manifold: a flow on (a,b) whose *)
(* chart matrices converge with all spatial derivatives, locally uniformly,  *)
(* to those of g b as t -> b-, followed by a flow from g b on [b,c), is a    *)
(* flow on (a,c).                                                            *)

let PDE_GLUE_STATEMENT = new_definition
 `PDE_GLUE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b c
     (g:real->A->real^N^N).
        ricci_flow_on (top,atlas) a b g /\ ricci_flow_from (top,atlas) b c g /\
        (!cc K l e. cc IN atlas /\ compact K /\ K SUBSET IMAGE (SND cc) (FST cc) /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ &0 < e
                    ==> ?d. &0 < d /\
                            !t y. b - d < t /\ t < b /\ y IN K
                                  ==> norm(iterated_partial l
                                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                              metric_local atlas cc (g t)) y -
                                           iterated_partial l
                                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                              metric_local atlas cc (g b)) y) < e)
        ==> ricci_flow_on (top,atlas) a c g`;;

(* ------------------------------------------------------------------------- *)
(* Part 2. Statements proved in other layers: R1, R2 in the Ricci-flow       *)
(* analysis units, R3 (the interval form of SMT_REQ_MFLOW_STATEMENT) in      *)
(* pc_mfd_flow.                                                              *)
(* ------------------------------------------------------------------------- *)

(* R1 (RFA_R1, pc_rfa_r1).  Bounded curvature on a finite interval gives     *)
(* chart C^m bounds of every order, uniformly in time (Hamilton's global     *)
(* derivative estimates on compact M, metric equivalence, Christoffel        *)
(* evolution; Topping Thm 5.3.1 proof).                                      *)

let PDE_REQ_DERIV_BOUNDS_STATEMENT = new_definition
 `PDE_REQ_DERIV_BOUNDS_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks a b
     (g:real->A->real^N^N) B.
        hausdorff_space top /\ compact_space top /\ 2 <= dimindex(:N) /\
        pde_cover (top,atlas) n0 cs ks /\ ricci_flow_from (top,atlas) a b g /\
        (!t x. a <= t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= B)
        ==> !m. ?B'. !t. a <= t /\ t < b ==> pde_cbound atlas n0 cs ks m B' (g t)`;;

(* R2 (RFA_R2, pc_rfa_doubling).  Doubling-time estimate for the curvature  *)
(* (MT Prop 4.11, [14] Lemma 6.1), dimensional constants.                   *)

let PDE_REQ_RM_DOUBLING_STATEMENT = new_definition
 `PDE_REQ_RM_DOUBLING_STATEMENT (u:A->bool) (n:N->bool) <=>
    ?c C. &0 < c /\ &0 < C /\
      !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
       (g:real->A->real^N^N) K.
          hausdorff_space top /\ compact_space top /\ 2 <= dimindex(:N) /\
          ricci_flow_from (top,atlas) a b g /\ &0 < K /\
          (!x. x IN topspace top ==> mfd_rm_norm atlas (g a) x <= K)
          ==> !t x. a <= t /\ t < b /\ t <= a + c / K /\ x IN topspace top
                    ==> mfd_rm_norm atlas (g t) x <= C * K`;;

(* R3 (PDE_REQ_MFLOW, pc_mfd_flow; the interval form of SMT_REQ_MFLOW).      *)
(* Flows of time-dependent vector fields on a compact manifold, smooth on    *)
(* an open time interval (a,b), with initial time s in (a,b).                *)

let PDE_REQ_MFLOW_STATEMENT = new_definition
 `PDE_REQ_MFLOW_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) a b s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        (!c. c IN atlas
             ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                   (\z. mfd_vrep atlas (X (drop(fstcart z))) c (sndcart z))) /\
        a < s /\ s < b
        ==> ?Phi:real->A->A.
              (!x. x IN topspace top ==> Phi s x = x) /\
              (!t. a < t /\ t < b
                   ==> ?Psi. mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                                        (Phi t) Psi) /\
              (!c t x. c IN atlas /\ a < t /\ t < b /\ x IN topspace top /\ Phi t x IN FST c
                       ==> ((\r. SND c (Phi (drop r) x)) has_vector_derivative
                            mfd_vrep atlas (X t) c (SND c (Phi t x))) (at (lift t))) /\
              (!c c'. c IN atlas /\ c' IN atlas
                      ==> smooth_map_on
                            {pastecart (lift t) y | a < t /\ t < b /\
                                                    y IN IMAGE (SND c) (FST c) /\
                                                    Phi t (chart_inv c y) IN FST c'}
                            (\z. SND c' (Phi (drop(fstcart z)) (chart_inv c (sndcart z)))))`;;

(* ------------------------------------------------------------------------- *)
(* Part 3. Intermediate statements of the PDE layer.                         *)
(* ------------------------------------------------------------------------- *)

(* M1. Uniform existence for the Ricci-DeTurck flow with background g0 and   *)
(* initial metric g0 (the analytic core: torus theory, parametrix on M,      *)
(* frozen-coefficient iteration).                                            *)

let PDE_RDT_UNIFORM_STATEMENT = new_definition
 `PDE_RDT_UNIFORM_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks
        ==> ?m. !B. ?tau. &0 < tau /\
                  !(g0:A->real^N^N) a.
                      riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks m B g0
                      ==> ?gb. pde_rdt_flow_from (top,atlas) g0 a (a + tau) gb /\
                               !x. x IN topspace top ==> gb a x = g0 x`;;

(* M2. The DeTurck gauge: a Ricci-DeTurck flow becomes a Ricci flow after    *)
(* pulling back by the flow phi of -W (d/dt phi = -W(gb,h) o phi,            *)
(* phi a = id; this sign of the generating field is that of CLN (2.52),      *)
(* MT's sketch has the opposite sign).                                       *)

let PDE_GAUGE_STATEMENT = new_definition
 `PDE_GAUGE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (h:A->real^N^N) a b
     (gb:real->A->real^N^N).
        hausdorff_space top /\ compact_space top /\ riemannian_metric atlas h /\
        pde_rdt_flow_from (top,atlas) h a b gb
        ==> ?(phi:real->A->A) g.
              (!x. x IN topspace top ==> phi a x = x) /\
              (!t. a <= t /\ t < b
                   ==> ?psi. mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                                        (phi t) psi) /\
              (!t x. a <= t /\ t < b /\ x IN topspace top
                     ==> g t x = mfd_pullback_metric atlas atlas (phi t) (gb t) x) /\
              (!x. x IN topspace top ==> g a x = gb a x) /\
              ricci_flow_from (top,atlas) a b g`;;

(* M3. Linear theory on M: existence for d/dt v = tr_k Hess_h v + f.        *)

let PDE_MLIN_STATEMENT = new_definition
 `PDE_MLIN_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (k:real->A->real^N^N) (h:A->real^N^N) f v0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        a < b /\ riemannian_metric atlas h /\
        (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
        pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
        mfd_tensor2_smooth atlas v0
        ==> ?v. pde_mlin_sol (top,atlas) a b k h f v0 v`;;

(* M5. Kotschwar's pointwise inequality for two Ricci flows from the same   *)
(* initial metric on a compact manifold: on each [a,b'] the density          *)
(* e = |g1 - g2|^2 + |Gamma1 - Gamma2|^2 + |Rm1 - Rm2|^2 (norms of g1)       *)
(* is smooth up to a, and e_t <= div Z + C e for a smooth field family Z.    *)

let PDE_KOT_POINTWISE_STATEMENT = new_definition
 `PDE_KOT_POINTWISE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g1:real->A->real^N^N) g2 b'.
        hausdorff_space top /\ compact_space top /\
        ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
        (!x. x IN topspace top ==> g1 a x = g2 a x) /\ a < b' /\ b' < b
        ==> ?C (Z:real->A->real^N) (e':real->A->real).
              pde_sfun_from atlas a b' (\s. pde_mkot_density atlas (g1 s) (g2 s)) /\
              pde_sfun_from atlas a b' e' /\
              (!c. c IN atlas
                   ==> smooth_map_on (interval(lift a,lift b') PCROSS IMAGE (SND c) (FST c))
                         (\z. mfd_vrep atlas (Z (drop(fstcart z))) c (sndcart z))) /\
              (!t x. a < t /\ t < b' /\ x IN topspace top
                     ==> ((\s. pde_mkot_density atlas (g1 s) (g2 s) x) has_real_derivative
                          e' t x) (atreal t) /\
                         e' t x <= mfd_div atlas (g1 t) (Z t) x +
                                   C * pde_mkot_density atlas (g1 t) (g2 t) x)`;;

