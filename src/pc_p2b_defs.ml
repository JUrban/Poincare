(* ========================================================================= *)
(* Unit pc_p2b_defs (Part 2B, MT Ch 2, 9, 10): the Part 2B vocabulary, the   *)
(* statements of the Part 2B layer, and the composition steps proved from    *)
(* them.  Defined elsewhere and loaded here: p2b_kappa_solution and          *)
(* p2b_hs_sep, the Part 3 statements P2_PROP_2_19, P2_PROP_2_19_SEP,         *)
(* P2_PROP_9_79_SLICE, P2_PROP_9_79_NECK, P2_PROP_9_79_OPEN, P2_COR_9_95,    *)
(* P2_THM_10_2, P2_SEP_LIMIT and the Part 2C vocabulary (pc_p3_iface); the   *)
(* Part 2C statements A2-A8, A16 (pc_p2c_iface); APX_A6, APX_A7              *)
(* (pc_apx_defs).  The vocabulary of the comparison-geometry track           *)
(* (p2b_dist_regular, p2b_parallel_on, p2b_locally_split, p2b_line_fn,       *)
(* p2b_mfd_hess) is in unit pc_cmp_pdefs; the statements that use it, the    *)
(* weak-regularity and L-geometry inputs and the full chain follow in later  *)
(* Part 2B units.                                                            *)
(*                                                                           *)
(* The vocabulary (V1-V6) comes first, then the statements (S1-S9) and the   *)
(* proved steps (P1-P7).                                                     *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2b_kreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V1. The view of a flow defined for t <= 0 (kappa-solutions).              *)
(* ------------------------------------------------------------------------- *)

let p2b_kview = new_definition
 `p2b_kview (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
            (g:real->B->real^3^3) =
    rfs_flow_view (top,atlas) {t | t <= &0} g`;;

(* ------------------------------------------------------------------------- *)
(* V2. The class of the route (neck spheres separate, local orientability),  *)
(* p2b_lorient and p2b_ksep: in unit pc_p2b_kreq.                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* V3. Round slices (constant positive sectional curvature, MT Thm 9.93(1)), *)
(* any dimension N (N = 2 for the surfaces of MT Cor 9.50).                  *)
(* ------------------------------------------------------------------------- *)

let p2b_round = new_definition
 `p2b_round (top:B topology,atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) <=>
    ?k. &0 < k /\
        !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> mfd_sectional atlas g x u v = k`;;

(* ------------------------------------------------------------------------- *)
(* V4. The shrinking round cylinder S^2 x R and its orientable Z/2 quotient *)
(* (MT Prop 9.83 (2),(3), Thm 9.93 (5),(6)): a covering of the manifold by  *)
(* the model real^3 minus the origin, one-to-one or two-to-one through      *)
(* rfs_twist, locally a parametrization, every slice t <= 0 equal to lam    *)
(* times cylinder_flow (t / lam) (scalar curvature 1/(lam - t)).             *)
(* ------------------------------------------------------------------------- *)

let p2b_cyl_model = new_definition
 `p2b_cyl_model (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                (g:real->B->real^3^3) <=>
    ?p lam. &0 < lam /\
            IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
            (!y. ~(y = vec 0)
                 ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
            ((!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) \/
             (!y z. ~(y = vec 0) /\ ~(z = vec 0)
                    ==> (p y = p z <=> z = y \/ z = rfs_twist y))) /\
            !t y. t <= &0 /\ ~(y = vec 0)
                  ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y`;;

(* Two-dimensional kappa-solutions (MT Def 9.2 in dimension 2, with the     *)
(* curvature bound on compact time intervals as p2b_kappa_solution):        *)
(* noncollapsing with r^2.                                                   *)

let p2b_kappa_solution2 = new_definition
 `p2b_kappa_solution2 (kappa:real)
    (top:B topology,atlas:((B->bool)#(B->real^2))->bool) (g:real->B->real^2^2) <=>
    &0 < kappa /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    connected_space top /\ ~(topspace top = {}) /\
    (!a. a < &0
         ==> ricci_flow_on (top,atlas) a (&0) g /\ riemannian_metric atlas (g(&0))) /\
    (!t. t <= &0 ==> mfd_complete (top,atlas) (g t)) /\
    (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional atlas (g t) x u v) /\
    (!a. a <= &0
         ==> ?K. !t x. a <= t /\ t <= &0 /\ x IN topspace top
                       ==> mfd_rm_norm atlas (g t) x <= K) /\
    (!t. t <= &0 ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g t) x) /\
    (!t x r. t <= &0 /\ x IN topspace top /\ &0 < r /\
             (!s y. t - r pow 2 < s /\ s <= t /\ y IN mfd_ball (top,atlas) (g t) x r
                    ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2))
             ==> ?v. mfd_has_volume (top,atlas) (g t) (mfd_ball (top,atlas) (g t) x r) v /\
                     kappa * r pow 2 <= v)`;;

(* ------------------------------------------------------------------------- *)
(* V5. Canonical-neighbourhood alternatives with an evolving neck of         *)
(* normalized length L, p2b_canon_L: in unit pc_p2b_kreq.                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* V6. Parabolic rescaling of a view by Q around time t, and the incomplete *)
(* limit tube of MT Prop 10.7 (the object a failure of Thm 10.2 produces,    *)
(* ruled out by the cone argument): U = H(annulus 1 2), connected,           *)
(* separating, finite diameter, R bounded near norm 1 and R -> infinity at  *)
(* the end E (norm -> 2); a view V with V(0) = (top,atlas,g) that is a Ricci *)
(* flow with Rm >= 0 on every relatively compact open X over                 *)
(* (sup_X (-1/R), 0]; near E every point is the centre of an evolving       *)
(* 2eps-neck of normalized length 1/2 whose central sphere separates the     *)
(* two ends.                                                                 *)
(* ------------------------------------------------------------------------- *)

let p2b_rescale_view = new_definition
 `p2b_rescale_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) (t:real) (Q:real) =
    (\s. rfs_vtop V (t + s / Q)),
    (\s. rfs_vatlas V (t + s / Q)),
    (\s y. Q %% rfs_vmetric V (t + s / Q) y)`;;

let p2b_bad_tube = new_definition
 `p2b_bad_tube (eps:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
    (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
    (H:real^3->B) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ connected_space top /\ apx_sphere_sep top atlas /\
    mfd_param top atlas (annulus (&1) (&2)) H /\
    IMAGE H (annulus (&1) (&2)) = topspace top /\
    (?D. !x y. x IN topspace top /\ y IN topspace top
               ==> mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= D) /\
    (?B0. !y. y IN annulus (&1) (&3 / &2) ==> mfd_scalar atlas g (H y) <= B0) /\
    (!B0. ?r. r < &2 /\ !y. r < norm y /\ norm y < &2 ==> B0 <= mfd_scalar atlas g (H y)) /\
    (!x. x IN topspace top ==> &0 < mfd_scalar atlas g x) /\
    p2c_regular_view V /\
    rfs_vtop V (&0) = top /\ rfs_vatlas V (&0) = atlas /\ rfs_vmetric V (&0) = g /\
    (!X a. open_in top X /\ compact_in top (top closure_of X) /\
           (!x. x IN X ==> --inv(mfd_scalar atlas g x) < a) /\ a < &0
           ==> p2c_vflow V X a (&0)) /\
    (!t x u v. t <= &0 /\ x IN topspace(rfs_vtop V t) /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional (rfs_vatlas V t) (rfs_vmetric V t) x u v) /\
    (?r1. &1 < r1 /\ r1 < &2 /\
          !y. r1 < norm y /\ norm y < &2
              ==> ?e. rfs_evolving_neck V (&2 * eps) (H y) (&0) (&1 / &2) e /\
                      ?r2 r3. &1 < r2 /\ r2 < r3 /\ r3 < &2 /\
                              !w1 w2. &1 < norm w1 /\ norm w1 < r2 /\
                                      r3 < norm w2 /\ norm w2 < &2
                                      ==> apx_separates top (IMAGE e (sphere(vec 0,&1)))
                                                        (H w1) (H w2))`;;

(* ========================================================================= *)
(* The statements of the Part 2B units (MT Ch 9 and 10) and the statements   *)
(* about other layers that do not use the comparison-geometry vocabulary;    *)
(* the Part 3 statements themselves are in pc_p3_iface under their P2_       *)
(* names.                                                                    *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* S1. MT Cor 4.39 on kappa-solutions, Prop 9.83, the 2-d classification,    *)
(* Prop 9.58, Thm 9.59 (Tao), Lemma 9.65 (Tao), Thm 9.64, Cor 9.71, Prop     *)
(* 9.85 (non-neck base point), the canonical neighbourhoods of noncompact    *)
(* and compact kappa-solutions.                                              *)
(* ------------------------------------------------------------------------- *)

let P2B_KSOL_DRDT_STATEMENT = new_definition
 `P2B_KSOL_DRDT_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g
       ==> !t x dR. t < &0 /\ x IN topspace top /\
                    ((\s. mfd_scalar atlas (g s) x) has_real_derivative dR) (atreal t)
                    ==> &0 <= dR`;;

let P2B_PROP_9_83_STATEMENT = new_definition
 `P2B_PROP_9_83_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_lorient top atlas
       ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 < mfd_sectional atlas (g(&0)) x u v) \/
           p2b_cyl_model (top,atlas) g`;;

let P2B_KSOL2_ROUND_STATEMENT = new_definition
 `P2B_KSOL2_ROUND_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^2^2).
       p2b_kappa_solution2 kappa (top,atlas) g /\ mfd_orientable top atlas
       ==> compact_space top /\ !t. t <= &0 ==> p2b_round (top,atlas) (g t)`;;

let P2B_PROP_9_58_STATEMENT = new_definition
 `P2B_PROP_9_58_STATEMENT (w:B->bool) <=>
    ?kappa0. &0 < kappa0 /\
      !kappa top atlas (g:real->B->real^3^3).
         p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
         ~p2b_round (top,atlas) (g(&0))
         ==> p2b_kappa_solution kappa0 (top,atlas) g`;;

let P2B_THM_9_59_STATEMENT = new_definition
 `P2B_THM_9_59_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p eta.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       ~compact_space top /\ p IN topspace top /\ &0 < eta
       ==> ?r0. !r v. r0 <= r /\
                      mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p r) v
                      ==> v <= eta * r pow 3`;;

let P2B_LEMMA_9_65_STATEMENT = new_definition
 `P2B_LEMMA_9_65_STATEMENT (w:B->bool) <=>
    !kappa r. &0 < kappa /\ &0 < r
      ==> ?Cr. !top atlas (g:real->B->real^3^3) p q.
                  p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                  p IN topspace top /\ mfd_scalar atlas (g(&0)) p = &1 /\
                  q IN mfd_ball (top,atlas) (g(&0)) p r
                  ==> mfd_scalar atlas (g(&0)) q <= Cr`;;

let P2B_THM_9_64_STATEMENT = new_definition
 `P2B_THM_9_64_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:num->real->B->real^3^3) p.
       &0 < kappa /\
       (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
            p k IN topspace(top k) /\ mfd_scalar (atlas k) (g k (&0)) (p k) = &1)
       ==> ?sub (top':B topology) atlas' g' pl.
              p3_subseq sub /\
              (!Tl. &0 < Tl
                    ==> p3_flow_limit (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                      (p o sub) (\k. &0) (\k. &1) (top',atlas') g' pl Tl) /\
              p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas' /\
              mfd_scalar atlas' (g'(&0)) pl = &1`;;

let P2B_COR_9_71_STATEMENT = new_definition
 `P2B_COR_9_71_STATEMENT (w:B->bool) <=>
    ?C. &0 < C /\
      !kappa top atlas (g:real->B->real^3^3) x t.
         p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
         x IN topspace top /\ t <= &0
         ==> sqrt(rfs_scalar_grad2 atlas (g t) x) <=
             C * mfd_scalar atlas (g t) x * sqrt(mfd_scalar atlas (g t) x) /\
             abs(rfs_scalar_lap atlas (g t) x + &2 * rfs_ric_norm2 atlas (g t) x) <=
             C * mfd_scalar atlas (g t) x pow 2`;;

let P2B_PROP_9_85_STATEMENT = new_definition
 `P2B_PROP_9_85_STATEMENT (w:B->bool) <=>
    ?eps2. &0 < eps2 /\
      !eps. &0 < eps /\ eps <= eps2
        ==> ?D D1. &1 < D /\ &1 < D1 /\
              !kappa top atlas (g:real->B->real^3^3) p.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 ~compact_space top /\
                 (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
                 p IN topspace top /\
                 ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps p (&0) e)
                 ==> (!x. x IN topspace top /\
                          ~(x IN mfd_ball (top,atlas) (g(&0)) p
                                   (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))))
                          ==> ?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps x (&0) e) /\
                     (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p
                                     (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
                              ~collinear {vec 0,u,v}
                              ==> inv D1 * mfd_scalar atlas (g(&0)) p <
                                  mfd_sectional atlas (g(&0)) x u v /\
                                  mfd_sectional atlas (g(&0)) x u v <
                                  D1 * mfd_scalar atlas (g(&0)) p)`;;

let P2B_KSOL_NONCOMPACT_CANON_STATEMENT = new_definition
 `P2B_KSOL_NONCOMPACT_CANON_STATEMENT (w:B->bool) <=>
    ?eps2. &0 < eps2 /\
      !eps. &0 < eps /\ eps <= eps2
        ==> ?C0. &1 < C0 /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 ~compact_space top /\ x IN topspace top
                 ==> p3_canon_at (p2b_kview (top,atlas) g) C0 eps x (&0)`;;

let P2B_KSOL_COMPACT_CANON_STATEMENT = new_definition
 `P2B_KSOL_COMPACT_CANON_STATEMENT (w:B->bool) <=>
    ?eps3. &0 < eps3 /\
      !eps. &0 < eps /\ eps <= eps3
        ==> ?C1. &1 < C1 /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 compact_space top /\ x IN topspace top
                 ==> p3_canon_at (p2b_kview (top,atlas) g) C1 eps x (&0)`;;

(* The canonv form of the compact case, with the volume clause p3_comp_vol  *)
(* on the C-component alternative (Vol U > C^-1 R(x)^(-3/2); from the       *)
(* universal kappa0 of Prop 9.58, abs Rm <= R/2 and dR/dt >= 0).            *)

let P2B_KSOL_COMPACT_CANON_V_STATEMENT = new_definition
 `P2B_KSOL_COMPACT_CANON_V_STATEMENT (w:B->bool) <=>
    ?eps3. &0 < eps3 /\
      !eps. &0 < eps /\ eps <= eps3
        ==> ?C1. &1 < C1 /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 compact_space top /\ x IN topspace top
                 ==> p3_canonv_at (p2b_kview (top,atlas) g) C1 eps x (&0)`;;

(* ------------------------------------------------------------------------- *)
(* S2. Cor 9.94 for the class p2b_ksep (and with evolving necks of length   *)
(* L), monotonicity in C (needs a genuine metric on the slice: with a junk  *)
(* metric R need not be bounded on a compact component, and the sup in      *)
(* rfs_c_component could make larger C harder), and the extension of a      *)
(* strong neck at time 0 of a kappa-solution to length a > 1 (MT p. 243).   *)
(* See pc_p2b_lim, pc_p2b_canonv and pc_p2b_close95.                         *)
(* ------------------------------------------------------------------------- *)

let P2B_CANON_MONO_C_STATEMENT = new_definition
 `P2B_CANON_MONO_C_STATEMENT (u:A->bool) <=>
    !V C C' eps (x:A) t.
       &1 < C /\ C <= C' /\
       smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
       riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
       p3_canon_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) C eps x t
       ==> p3_canon_at V C' eps x t`;;

(* Monotonicity in C of the canonv form (the volume clause is weaker for     *)
(* larger C).                                                                *)

let P2B_CANON_MONO_C_V_STATEMENT = new_definition
 `P2B_CANON_MONO_C_V_STATEMENT (u:A->bool) <=>
    !V C C' eps (x:A) t.
       &1 < C /\ C <= C' /\
       smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
       riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
       p3_canonv_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) C eps x t
       ==> p3_canonv_at V C' eps x t`;;

let P2B_COR_9_94_KSEP_STATEMENT = new_definition
 `P2B_COR_9_94_KSEP_STATEMENT (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps. &0 < eps /\ eps <= epsp
        ==> ?C. &1 < C /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 x IN topspace top
                 ==> p3_canon_at (p2b_kview (top,atlas) g) C eps x (&0)`;;

(* Cor 9.94 for the class in canonv form. *)

let P2B_COR_9_94_KSEP_V_STATEMENT = new_definition
 `P2B_COR_9_94_KSEP_V_STATEMENT (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps. &0 < eps /\ eps <= epsp
        ==> ?C. &1 < C /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 x IN topspace top
                 ==> p3_canonv_at (p2b_kview (top,atlas) g) C eps x (&0)`;;

let P2B_COR_9_94_L_STATEMENT = new_definition
 `P2B_COR_9_94_L_STATEMENT (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps L. &0 < eps /\ eps <= epsp /\ &1 <= L
        ==> ?C0. &1 < C0 /\
              !C kappa top atlas (g:real->B->real^3^3) x.
                 C0 <= C /\ p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 x IN topspace top
                 ==> p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)`;;

let P2B_KSOL_NECK_EXTEND_STATEMENT = new_definition
 `P2B_KSOL_NECK_EXTEND_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) eps x e.
       p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\
       rfs_strong_neck (p2b_kview (top,atlas) g) eps x (&0) e
       ==> ?a. &1 < a /\ rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) a e`;;

(* ------------------------------------------------------------------------- *)
(* S3. MT Prop 9.79 beyond the Part 3 forms (unit pc_p2b_979): the           *)
(* non-uniform same-eps neck transfer for evolving necks of any normalized   *)
(* length (to length L < a), and the cap transfer A16 of pc_p2c_iface with a *)
(* re-centring factor K, 2C <= C', eps' <= eps0 and a complete target.  The  *)
(* neck forms ask for a regular source view (the neck chart must be smooth   *)
(* in every slice of its time interval) and riemannian metrics on the target *)
(* slices; P2B_PROP_9_79_NECK_FIX is P2_PROP_9_79_NECK with these            *)
(* hypotheses.  The uniform slice and cap transfers ask for a curvature      *)
(* bound on the source neighbourhood (delta depends on the bound Kr): the    *)
(* bound is on the squared norms of Rm, nabla Rm and nabla^2 Rm of the       *)
(* normalized metric R(x) g at every point of U (MT-style derivative bounds  *)
(* abs(nabla^l Rm) <= c R^(1+l/2)); P2B_PROP_9_79_SLICE_FIX is               *)
(* P2_PROP_9_79_SLICE with this bound.  Clause (8) of caps and C-components  *)
(* involves R, grad R and Lap R + 2 abs(Ric)^2, whose change under a C^4     *)
(* small perturbation is bounded by its size times a polynomial in these     *)
(* curvature derivatives; a bound on abs Rm alone gives no elementary        *)
(* estimate.                                                                 *)
(* ------------------------------------------------------------------------- *)

let P2B_NECK_OPEN_STATEMENT = new_definition
 `P2B_NECK_OPEN_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V eps x t a e.
       &0 < eps /\ eps < &1 / &4 /\ &1 < a /\
       p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) /\
       rfs_evolving_neck V eps x t a e
       ==> ?delta. &0 < delta /\
             !V' t' Q' psi.
                (!s. --a < s /\ s <= &0
                     ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                               (rfs_vatlas V' (t' + s / Q')) /\
                         riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                           (rfs_vmetric V' (t' + s / Q'))) /\
                p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
                  (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                      (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
                ==> ?e'. rfs_strong_neck V' eps (psi x) t' e'`;;

let P2B_NECK_OPEN_L_STATEMENT = new_definition
 `P2B_NECK_OPEN_L_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V eps x t a L e.
       &0 < eps /\ eps < &1 / &4 /\ &1 <= L /\ L < a /\
       p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) /\
       rfs_evolving_neck V eps x t a e
       ==> ?delta. &0 < delta /\
             !V' t' Q' psi.
                (!s. --a < s /\ s <= &0
                     ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                               (rfs_vatlas V' (t' + s / Q')) /\
                         riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                           (rfs_vmetric V' (t' + s / Q'))) /\
                p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
                  (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                      (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
                ==> ?e'. rfs_evolving_neck V' eps (psi x) t' L e'`;;

let P2B_PROP_9_79_NECK_FIX_STATEMENT = new_definition
 `P2B_PROP_9_79_NECK_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
    !eps eps' a. &0 < eps /\ eps < eps' /\ eps' < &1 / &4 /\ &1 < a
      ==> ?delta. &0 < delta /\
            !V x t e V' t' Q' psi.
               p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) /\
               rfs_evolving_neck V eps x t a e /\
               (!s. --a < s /\ s <= &0
                    ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                              (rfs_vatlas V' (t' + s / Q')) /\
                        riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                          (rfs_vmetric V' (t' + s / Q'))) /\
               p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
                 (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                     (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
               ==> ?e'. rfs_strong_neck V' eps' (psi x) t' e'`;;

let P2B_PROP_9_79_SLICE_FIX_STATEMENT = new_definition
 `P2B_PROP_9_79_SLICE_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
               rfs_canonical_nbhd (top,atlas) g C eps x U /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               (U IN connected_components_of top
                ==> IMAGE psi U IN connected_components_of top') /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U'. U' SUBSET IMAGE psi U /\
                        rfs_canonical_nbhd (top',atlas') g' C' eps' (psi x) U'`;;

let P2B_PROP_9_79_CAP_FIX_STATEMENT = new_definition
 `P2B_PROP_9_79_CAP_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U Y psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
               rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U' Y'. U' SUBSET IMAGE psi U /\
                           rfs_cap (top',atlas') g' C' eps' U' Y' /\ psi x IN Y'`;;

(* ------------------------------------------------------------------------- *)
(* S4. Transfer of canonical neighbourhoods from a kappa-solution limit to   *)
(* the sequence (the body of MT's proof of Cor 9.95), and the passage of     *)
(* separation and local orientability to geometric limits (units pc_p2b_ltr  *)
(* and pc_p2b_lim; P2_SEP_LIMIT itself is in pc_p3_iface).  For regular      *)
(* views the slices at the base times must be complete; the view forms of    *)
(* the limit statements ask for regular views (without smooth slices the     *)
(* neck charts of the limit cannot be carried to them), and the              *)
(* kappa-solutions of KSEP_LIMIT are Hausdorff (a compact closure must be    *)
(* closed; p2c_kappa_sol includes hausdorff_space).                          *)
(* ------------------------------------------------------------------------- *)

let P2B_LIMIT_TRANSFER_STATEMENT = new_definition
 `P2B_LIMIT_TRANSFER_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
    !C eps hs x t Q top atlas g xl kappa.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\
            x n IN topspace(rfs_top_at (hs n) (t n))) /\
       (!Tl. &0 < Tl
             ==> p3_flow_limit (\n. rfs_view (hs n)) x t Q
                               (top:B topology,atlas) g xl Tl) /\
       p2b_kappa_solution kappa (top,atlas) g /\
       p3_canon_at (p2b_kview (top,atlas) g) C eps xl (&0)
       ==> ?N. !n. N <= n ==> p3_canon_at (rfs_view (hs n)) C eps (x n) (t n)`;;

(* The transfer in canonv form, with the same C (the volume clause is a     *)
(* strict, scale-invariant inequality, open under the C^0 closeness of the  *)
(* pulled-back metrics).                                                    *)

let P2B_LIMIT_TRANSFER_V_STATEMENT = new_definition
 `P2B_LIMIT_TRANSFER_V_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
    !C eps hs x t Q top atlas g xl kappa.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\
            x n IN topspace(rfs_top_at (hs n) (t n))) /\
       (!Tl. &0 < Tl
             ==> p3_flow_limit (\n. rfs_view (hs n)) x t Q
                               (top:B topology,atlas) g xl Tl) /\
       p2b_kappa_solution kappa (top,atlas) g /\
       p3_canonv_at (p2b_kview (top,atlas) g) C eps xl (&0)
       ==> ?N. !n. N <= n ==> p3_canonv_at (rfs_view (hs n)) C eps (x n) (t n)`;;

let P2B_LIMIT_TRANSFER_VIEW_STATEMENT = new_definition
 `P2B_LIMIT_TRANSFER_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
    !C eps L V x t Q top atlas g xl kappa.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\ &1 <= L /\
       (!n. p2c_regular_view (V n:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            x n IN topspace(rfs_vtop (V n) (t n)) /\
            mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                         (rfs_vmetric (V n) (t n))) /\
       (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl) /\
       p2b_kappa_solution kappa (top,atlas) g /\
       p2b_canon_L (p2b_kview (top,atlas) g) C eps (L + &1) xl (&0)
       ==> ?N. !n. N <= n ==> p2b_canon_L (V n) C eps L (x n) (t n)`;;

let P2B_SEP_LIMIT_VIEW_STATEMENT = new_definition
 `P2B_SEP_LIMIT_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q top atlas g xl Tl.
       (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            !s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
       p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl
       ==> apx_sphere_sep top atlas`;;

let P2B_LORIENT_LIMIT_STATEMENT = new_definition
 `P2B_LORIENT_LIMIT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !hs x t Q top atlas g xl Tl.
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\
            x n IN topspace(rfs_top_at (hs n) (t n)) /\
            !k. k <= hs_count (hs n)
                ==> mfd_orientable (hs_top (hs n) k) (hs_atlas (hs n) k)) /\
       p3_flow_limit (\n. rfs_view (hs n)) x t Q (top:B topology,atlas) g xl Tl
       ==> p2b_lorient top atlas`;;

let P2B_LORIENT_LIMIT_VIEW_STATEMENT = new_definition
 `P2B_LORIENT_LIMIT_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q top atlas g xl Tl.
       (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            !s. ~(topspace(rfs_vtop (V n) s) = {})
                ==> mfd_orientable (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
       p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl
       ==> p2b_lorient top atlas`;;

let P2B_KSEP_LIMIT_STATEMENT = new_definition
 `P2B_KSEP_LIMIT_STATEMENT (w:B->bool) <=>
    !top atlas (g:num->real->B->real^3^3) x t Q top' atlas' g' xl J.
       (!k. hausdorff_space (top k) /\ p2b_ksep (top k) (atlas k) /\
            smooth_manifold_atlas (top k) (atlas k:((B->bool)#(B->real^3))->bool)) /\
       p3_flow_limit_on (\k. p2b_kview (top k,atlas k) (g k)) x t Q J
                        (top':B topology,atlas') g' xl
       ==> p2b_ksep top' atlas'`;;

(* ------------------------------------------------------------------------- *)
(* S5. Variants of the statements A3-A6 of pc_p2c_iface (the FIX forms) with *)
(* slice separation, the kappa-solution notion p2b_kappa_solution and        *)
(* complete slices at the base times; each is implied by the form of         *)
(* pc_p2c_iface (section P4).                                                *)
(* ------------------------------------------------------------------------- *)

(* A3 FIX (P2B_COR_9_95_VIEW_FIX_STATEMENT): in unit pc_p2b_kreq. *)

let P2B_NONNEG_BOUNDED_FIX_STATEMENT = new_definition
 `P2B_NONNEG_BOUNDED_FIX_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas a g.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         hausdorff_space (top:A topology) /\ a < &0 /\
         rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a (&0) g /\
         connected_space top /\ mfd_complete (top,atlas) (g (&0)) /\
         apx_sphere_sep top atlas /\
         (!t x u v. a < t /\ t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         (!x. x IN topspace top /\ &4 < mfd_scalar atlas (g (&0)) x
              ==> ?U. rfs_canonical_nbhd (top,atlas) (g (&0)) C eps x U)
         ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g (&0)) x <= K`;;

(* A5 FIX, A5L FIX and A6 FIX (P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT,          *)
(* P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT, P2B_AVR_ZERO_FIX_STATEMENT): in    *)
(* unit pc_p2b_kreq.                                                         *)

(* ------------------------------------------------------------------------- *)
(* S6. MT Thm 10.2 in two halves around the bad tube (units pc_p2b_tube,    *)
(* pc_p2b_cone): a failure for regular views produces a bad tube (Sec 10.3, *)
(* Prop 10.7), and no bad tube exists (Secs 10.4-10.6, smooth-cone route).  *)
(* The view of a bad tube is regular.                                        *)
(* ------------------------------------------------------------------------- *)

let P2B_BAD_TUBE_FROM_FAILURE_STATEMENT = new_definition
 `P2B_BAD_TUBE_FROM_FAILURE_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
         (!D0 D. &0 < D0 /\ &0 < D
                 ==> ?V x t y.
                        p2c_regular_view (V:(real->A topology)#
                                            (real->((A->bool)#(A->real^3))->bool)#
                                            (real->A->real^3^3)) /\
                        rfs_pinched V /\ (!s. s < &0 ==> rfs_vtop V s = discrete_topology {}) /\
                        (!s. apx_sphere_sep (rfs_vtop V s) (rfs_vatlas V s)) /\
                        x IN topspace(rfs_vtop V t) /\
                        (!y' s. s <= t /\ y' IN topspace(rfs_vtop V s) /\
                                &4 * rfs_vscalar V t x <= rfs_vscalar V s y'
                                ==> p3_canon_at V C eps y' s) /\
                        D0 <= rfs_vscalar V t x /\
                        y IN rfs_vball V t x (A * inv(sqrt(rfs_vscalar V t x))) /\
                        D * rfs_vscalar V t x < rfs_vscalar V t y)
         ==> ?top atlas g Vb H. p2b_bad_tube eps (top:B topology,atlas) g Vb H`;;

let P2B_NO_BAD_TUBE_STATEMENT = new_definition
 `P2B_NO_BAD_TUBE_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps. &0 < eps /\ eps <= eps0
        ==> !top atlas g V H. ~p2b_bad_tube eps (top:B topology,atlas) g V H`;;

(* ------------------------------------------------------------------------- *)
(* S7. Statements about other layers (Ricci flow analysis, Part 2C,          *)
(* comparison geometry) that do not use the comparison-geometry vocabulary:  *)
(* Hamilton's trace Harnack inequality for complete flows with abs Rm        *)
(* bounded on the time interval, the compactness of based ancient flows      *)
(* (complete limit at time 0), local compactness for regular views (Thm 5.6  *)
(* for incomplete limits; the limit view is regular, since its evolving      *)
(* necks are read in the atlases of earlier slices), Toponogov (complete;    *)
(* and in compact convex regions), Bishop-Gromov, first variation,           *)
(* separation for sec > 0.  The local compactness form                       *)
(* P2B_REQ_P2C_LOCAL_COMPACT_STATEMENT is false as stated and is not used:   *)
(* the proof uses P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT (pc_p2b_lcreqn) and  *)
(* P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT (pc_p2b_lcreqg).                    *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_RFA_HARNACK_STATEMENT = new_definition
 `P2B_REQ_RFA_HARNACK_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) a b.
       hausdorff_space top /\ a < b /\ rfs_flow_upto (top,atlas) a b g /\
       (!t. a < t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
       (!t x u v. a < t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g t) x u v) /\
       (?K. !t x. a < t /\ t <= b /\ x IN topspace top
                  ==> mfd_rm_norm atlas (g t) x <= K)
       ==> !t x dR. a < t /\ t < b /\ x IN topspace top /\
                    ((\s. mfd_scalar atlas (g s) x) has_real_derivative dR) (atreal t)
                    ==> &0 <= dR + mfd_scalar atlas (g t) x / (t - a) /\
                        !X. &0 <= dR + mfd_scalar atlas (g t) x / (t - a) +
                                  &2 * drop(frechet_derivative
                                         (\y. lift(lscalar (metric_local atlas
                                                    (chart_at atlas x) (g t)) y))
                                         (at (SND(chart_at atlas x) x)) X) +
                                  &2 * mfd_ricci atlas (g t) x X X`;;

let P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT = new_definition
 `P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (w:B->bool) <=>
    !top atlas (g:num->real->B->real^3^3) x Q.
       (!k. hausdorff_space (top k) /\
            smooth_manifold_atlas (top k) (atlas k:((B->bool)#(B->real^3))->bool) /\
            (!a. a < &0 ==> rfs_flow_upto (top k,atlas k) a (&0) (g k)) /\
            (!t. t <= &0 ==> mfd_complete (top k,atlas k) (g k t)) /\
            x k IN topspace(top k) /\ &0 < Q k) /\
       (!A a. &0 < A /\ a < &0
              ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                                 y IN mfd_ball (top k,atlas k) (g k (&0)) (x k)
                                         (A * inv(sqrt(Q k)))
                                 ==> mfd_rm_norm (atlas k) (g k (s / Q k)) y <= CA * Q k) /\
       (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
          !k. N <= k
              ==> ?v. mfd_has_volume (top k,atlas k) (g k (&0))
                        (mfd_ball (top k,atlas k) (g k (&0)) (x k) (r0 * inv(sqrt(Q k)))) v /\
                      kappa * (r0 * inv(sqrt(Q k))) pow 3 <= v)
       ==> ?sub (top':B topology) atlas' g' xl.
              p3_subseq sub /\
              (!Tl. &0 < Tl
                    ==> p3_flow_limit
                          (\k. rfs_flow_view (top (sub k),atlas (sub k)) {t | t <= &0}
                                             (g (sub k)))
                          (x o sub) (\k. &0) (Q o sub) (top',atlas') g' xl Tl) /\
              (!s. s <= &0 ==> riemannian_metric atlas' (g' s)) /\
              mfd_complete (top',atlas') (g' (&0))`;;

let P2B_REQ_P2C_LOCAL_COMPACT_STATEMENT = new_definition
 `P2B_REQ_P2C_LOCAL_COMPACT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V U z.
       (!n. p2c_regular_view (V n:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            open_in (rfs_vtop (V n) (&0)) (U n) /\ (z n:A) IN U n) /\
       (!delta. &0 < delta
                ==> ?K tau N. &0 < tau /\
                      !n y. N <= n /\ y IN U n /\
                            rfs_vball (V n) (&0) y delta SUBSET U n
                            ==> rfs_persists (V n) (rfs_vball (V n) (&0) y (delta / &2))
                                             (--tau) (&0) /\
                                !s y'. --tau < s /\ s <= &0 /\
                                       y' IN rfs_vball (V n) (&0) y (delta / &2)
                                       ==> mfd_rm_norm (rfs_vatlas (V n) s)
                                                       (rfs_vmetric (V n) s) y' <= K) /\
       (!delta. &0 < delta
                ==> ?kappa N. &0 < kappa /\
                      !n y. N <= n /\ y IN U n /\
                            rfs_vball (V n) (&0) y delta SUBSET U n
                            ==> ?v. mfd_has_volume (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                      (rfs_vmetric (V n) (&0))
                                      (rfs_vball (V n) (&0) y (delta / &2)) v /\
                                    kappa * (delta / &2) pow 3 <= v) /\
       (?delta0. &0 < delta0 /\ !n. rfs_vball (V n) (&0) (z n) delta0 SUBSET U n)
       ==> ?sub (top:B topology) atlas g zl W phi Vl.
              p3_subseq sub /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\ zl IN topspace top /\
              (!k. open_in top (W k) /\ zl IN W k /\ compact_in top (top closure_of W k) /\
                   top closure_of W k SUBSET W (SUC k)) /\
              UNIONS {W k | k IN (:num)} = topspace top /\
              (!k. phi k zl = z (sub k)) /\
              (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
                   ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V (sub k)) (&0))
                                    (rfs_vatlas (V (sub k)) (&0))
                                    (IMAGE (phi k) (W k)) (phi k) psi) /\
              (!K m eta. compact_in top K /\ &0 < eta
                         ==> ?k0. !k. k0 <= k
                                      ==> K SUBSET W k /\
                                          !y. y IN K
                                              ==> lck_dist2 m
                                                    (metric_local atlas (chart_at atlas y) g)
                                                    (rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                                       (phi k o chart_inv (chart_at atlas y))
                                                       (rfs_vmetric (V (sub k)) (&0)))
                                                    (SND(chart_at atlas y) y) < eta) /\
              (!delta A. &0 < delta /\ &0 < A
                         ==> ?k0. !k gamma.
                                k0 <= k /\
                                mfd_c1_curve (rfs_vtop (V (sub k)) (&0),
                                              rfs_vatlas (V (sub k)) (&0)) gamma (&0) (&1) /\
                                gamma (&0) = z (sub k) /\
                                mfd_length (rfs_vatlas (V (sub k)) (&0))
                                           (rfs_vmetric (V (sub k)) (&0)) gamma (&0) (&1) <= A /\
                                (!s. &0 <= s /\ s <= &1
                                     ==> gamma s IN U (sub k) /\
                                         rfs_vball (V (sub k)) (&0) (gamma s) delta
                                         SUBSET U (sub k))
                                ==> ?y'. y' IN W k /\ phi k y' = gamma (&1)) /\
              p2c_regular_view Vl /\
              rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\ rfs_vmetric Vl (&0) = g /\
              (!X a. open_in top X /\ compact_in top (top closure_of X) /\ a < &0 /\
                     (?Kb N. !k. N <= k
                                 ==> X SUBSET W k /\
                                     rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                                     !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                                           ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                           (rfs_vmetric (V (sub k)) s) y <= Kb)
                     ==> p2c_vflow Vl X a (&0) /\
                         !m eta b. a < b /\ &0 < eta
                           ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN X
                                            ==> lck_dist2 m
                                                  (metric_local (rfs_vatlas Vl s)
                                                     (chart_at (rfs_vatlas Vl s) y)
                                                     (rfs_vmetric Vl s))
                                                  (rfs_pullback (rfs_vatlas (V (sub k)) s)
                                                     (phi k o chart_inv
                                                        (chart_at (rfs_vatlas Vl s) y))
                                                     (rfs_vmetric (V (sub k)) s))
                                                  (SND(chart_at (rfs_vatlas Vl s) y) y) < eta)`;;

let P2B_REQ_CMP_TOPONOGOV_STATEMENT = new_definition
 `P2B_REQ_CMP_TOPONOGOV_STATEMENT (w:B->bool) <=>
    !top atlas g p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\
       &0 < L1 /\ &0 < L2 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`;;

let P2B_REQ_CMP_LOCAL_TOPONOGOV_STATEMENT = new_definition
 `P2B_REQ_CMP_LOCAL_TOPONOGOV_STATEMENT (w:B->bool) <=>
    !top atlas g D p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       compact_in top D /\
       (!y z. y IN D /\ z IN D
              ==> ?gamma. apx_shortest (top,atlas) g gamma (&0) (&1) /\
                          gamma (&0) = y /\ gamma (&1) = z /\
                          !s. &0 <= s /\ s <= &1 ==> gamma s IN D) /\
       p IN D /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\ &0 < L1 /\ &0 < L2 /\
       (!s. &0 <= s /\ s <= L1
            ==> s % v1 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v1) IN D) /\
       (!s. &0 <= s /\ s <= L2
            ==> s % v2 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v2) IN D) /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`;;

let P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT = new_definition
 `P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT (w:B->bool) <=>
    !top atlas g p r1 r2 v1 v2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\ &0 < r1 /\ r1 <= r2 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r1) v1 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r2) v2
       ==> v2 / r2 pow 3 <= v1 / r1 pow 3 /\ v1 <= &4 / &3 * pi * r1 pow 3`;;

let P2B_REQ_CMP_FIRST_VARIATION_STATEMENT = new_definition
 `P2B_REQ_CMP_FIRST_VARIATION_STATEMENT (w:B->bool) <=>
    !top atlas g p gamma a b c.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
       mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
       (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
              mfd_exp (top,atlas) g (gamma t) v = p /\
              mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
              ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                  --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v)
       ==> !s t. a <= s /\ s <= t /\ t <= b
                 ==> mfd_dist (top,atlas) g p (gamma s) +
                     c * mfd_length atlas g gamma s t
                     <= mfd_dist (top,atlas) g p (gamma t)`;;

let P2B_REQ_CMP_POS_SEP_STATEMENT = new_definition
 `P2B_REQ_CMP_POS_SEP_STATEMENT (u:A->bool) <=>
    !top atlas g.
       hausdorff_space top /\ connected_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas g x u v)
       ==> apx_sphere_sep top atlas`;;

(* ------------------------------------------------------------------------- *)
(* S8. The Appendix statements A.4, A.6, A.7 (pc_apx_defs) restated for      *)
(* constant-speed minimizers (MFD_MINIMIZING_IMP_GEODESIC assumes constant   *)
(* speed, and Hopf-Rinow and the limits of Claim 10.3 give such curves).     *)
(* Each is implied by the Appendix statement (section P5); the Part 2B       *)
(* routes use these forms.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2B_APX_A4_CS_STATEMENT = new_definition
 `P2B_APX_A4_CS_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e gamma a b.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               apx_shortest (top,atlas) g gamma a b /\ a < b /\
               (!t. t IN real_interval[a,b]
                    ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
               (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
               inv(&100 * eps) * inv(sqrt(mfd_scalar atlas g x))
               < mfd_length atlas g gamma a b /\
               apx_sfun (rfs_neck_dom eps) e (gamma a) <
               apx_sfun (rfs_neck_dom eps) e (gamma b)
               ==> !t. a <= t /\ t <= b
                       ==> (&1 - alpha) * sqrt(mfd_scalar atlas g x) *
                           mfd_speed atlas g gamma a b t
                           <= drop(vector_derivative
                                    (\s. lift(apx_sfun (rfs_neck_dom eps) e (gamma(drop s))))
                                    (at (lift t) within interval[lift a,lift b]))`;;

let P2B_APX_A6_CS_STATEMENT = new_definition
 `P2B_APX_A6_CS_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e gamma a b r.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         apx_shortest (top,atlas) g gamma a b /\ a < b /\
         (!t. t IN real_interval[a,b]
              ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
         (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
         inv(&100 * eps) * inv(sqrt(mfd_scalar atlas g x))
         < mfd_length atlas g gamma a b /\
         sphere(vec 0,r) SUBSET rfs_neck_dom eps
         ==> !t1 t2. a <= t1 /\ t1 <= b /\ a <= t2 /\ t2 <= b /\
                     gamma t1 IN IMAGE e (sphere(vec 0,r)) /\
                     gamma t2 IN IMAGE e (sphere(vec 0,r))
                     ==> gamma t1 = gamma t2`;;

let P2B_APX_A7_CS_STATEMENT = new_definition
 `P2B_APX_A7_CS_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e gamma a b r.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         apx_shortest (top,atlas) g gamma a b /\ a < b /\
         (!t. t IN real_interval[a,b]
              ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
         (!c d. a <= c /\ c < d /\ d <= b /\
                (!t. c < t /\ t < d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
                (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
                (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
                ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x))
                    <= mfd_length atlas g gamma c d) /\
         sphere(vec 0,r) SUBSET rfs_neck_dom eps
         ==> !t1 t2. a <= t1 /\ t1 <= b /\ a <= t2 /\ t2 <= b /\
                     gamma t1 IN IMAGE e (sphere(vec 0,r)) /\
                     gamma t2 IN IMAGE e (sphere(vec 0,r))
                     ==> gamma t1 = gamma t2`;;

(* ------------------------------------------------------------------------- *)
(* S9. Two statements of local Riemannian geometry (LRG) used by pc_p2b_979. *)
(* P2B_REQ_LRG_BASE_STATEMENT: change of base of the C^k distance between    *)
(* arbitrary metrics (pc_lrg_stab has the cylinder case,                     *)
(* LCK_DIST_CYLINDER_BASE): if G1 is within 1/2 of G0 in C^k at y, the C^k   *)
(* size of G2 - G1 measured with G0 is at most M(k) times the one measured   *)
(* with G1 (the connections differ by a tensor controlled by the C^k         *)
(* closeness, so M depends on k only).  P2B_REQ_LRG_RM_NEAR_STATEMENT: the   *)
(* curvature tensor is bounded at metrics C^2-close to one with bounded      *)
(* curvature (used for the uniform neck form with eps' up to 1/4).  Both     *)
(* pointwise at y.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_LRG_BASE_STATEMENT = new_definition
 `P2B_REQ_LRG_BASE_STATEMENT <=>
    !k. ?M. &0 <= M /\
      !s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y`;;

let P2B_REQ_LRG_RM_NEAR_STATEMENT = new_definition
 `P2B_REQ_LRG_RM_NEAR_STATEMENT <=>
    !K0. ?K. !s (G0:real^3->real^3^3) G y.
       metric_field s G0 /\ metric_field s G /\ y IN s /\
       lrm_deriv_norm2 0 G0 y <= K0 /\ lck_dist2 2 G0 G y <= &1 / &4
       ==> lrm_deriv_norm2 0 G y <= K`;;

(* ========================================================================= *)
(* Proved steps.  The sup junk value, the clauses of kappa-solutions and     *)
(* their views, Cor 4.39 from the Harnack inequality, the forms of           *)
(* pc_p2c_iface imply the FIX forms, the Appendix statements imply the       *)
(* constant-speed forms, and the compositions Cor 9.94, Cor 9.95             *)
(* (P2_COR_9_95 and the view form), Thm 10.2 for views (the statement A2 of  *)
(* pc_p2c_iface) from its two halves and the history form P2_THM_10_2.       *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* P1. HOL's sup of an unbounded set of reals is the unspecified value sup   *)
(* {} (the reason why the volume clause of rfs_cap is junk-sensitive in      *)
(* incomplete manifolds).                                                    *)
(* ------------------------------------------------------------------------- *)

let P2B_SUP_UNBOUNDED_JUNK = prove
 (`!s:real->bool. ~(?b. !x. x IN s ==> x <= b) ==> sup s = sup {}`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sup; NOT_IN_EMPTY] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `a - &1`) THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* P2. Kappa-solutions: the Part 2C notion, the clauses used below, the      *)
(* time-0 slice of the view.                                                 *)
(* ------------------------------------------------------------------------- *)

let P2B_KAPPA_SOLUTION_P2C = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g ==> p2c_kappa_sol kappa (top,atlas) g`,
  SIMP_TAC[p2b_kappa_solution]);;

let P2B_KSOL_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> hausdorff_space top /\
         (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
         (!t. t <= &0 ==> mfd_complete (top,atlas) (g t)) /\
         (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         (!a. a <= &0
              ==> ?K. !t x. a <= t /\ t <= &0 /\ x IN topspace top
                            ==> mfd_rm_norm atlas (g t) x <= K)`,
  SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]);;

let P2B_KVIEW_SLICE0 = prove
 (`!top atlas (g:real->B->real^3^3).
     rfs_vtop (p2b_kview (top,atlas) g) (&0) = top /\
     rfs_vatlas (p2b_kview (top,atlas) g) (&0) = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) g) (&0) = g (&0)`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric;
              IN_ELIM_THM; REAL_LE_REFL]);;

let P2B_KSOL_SLICE0 = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g (&0))`,
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o
    check (fun th -> can (term_match [] `!a. a < &0 ==> P a`) (concl th))) THEN
  REWRITE_TAC[rfs_flow_upto] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* P3. MT Cor 4.39 from the Harnack inequality                               *)
(* (P2B_REQ_RFA_HARNACK_STATEMENT): dR/dt >= 0 on kappa-solutions.           *)
(* ------------------------------------------------------------------------- *)

let P2B_DRDT_LEMMA = prove
 (`!dR R t. t < &0 /\ (!a. a < t ==> &0 <= dR + R / (t - a)) ==> &0 <= dR`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `c = (&2 * (abs R + &1)) / --dR` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - c`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `t - (t - x) = x`] THEN
  SUBGOAL_THEN `R / c < --dR` MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN EXPAND_TAC "c" THEN
  SUBGOAL_THEN `--dR * (&2 * (abs R + &1)) / --dR = &2 * (abs R + &1)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2B_KSOL_DRDT_FROM_HARNACK = prove
 (`!(w:B->bool). P2B_REQ_RFA_HARNACK_STATEMENT w ==> P2B_KSOL_DRDT_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_RFA_HARNACK_STATEMENT; P2B_KSOL_DRDT_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "harnack") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "flow")
    (CONJUNCTS_THEN2 (LABEL_TAC "compl") (CONJUNCTS_THEN2 (LABEL_TAC "sec")
     (LABEL_TAC "bnd"))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `dR:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B_DRDT_LEMMA THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) t) x` THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  REMOVE_THEN "harnack" (MP_TAC o SPECL [`top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `a:real`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REMOVE_THEN "flow" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REMOVE_THEN "compl" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      REMOVE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REMOVE_THEN "bnd" (MP_TAC o SPEC `a:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:B`; `dR:real`]) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* P4. The forms of pc_p2c_iface imply the FIX forms (A3, A4, A5, A6, A16).  *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_95_VIEW_ORIG_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_COR_9_95_VIEW_STATEMENT u w ==> P2B_COR_9_95_VIEW_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_COR_9_95_VIEW_STATEMENT; P2B_COR_9_95_VIEW_FIX_STATEMENT;
              p2b_canon_L] THEN
  DISCH_THEN(X_CHOOSE_THEN `epsp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `epsp:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C95:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`; `kappa:real`] THEN
  STRIP_TAC THEN REMOVE_THEN "c" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
                        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                        `xl:B`; `kappa:real`] THEN
  ASM_SIMP_TAC[P2B_KAPPA_SOLUTION_P2C] THEN ASM_MESON_TAC[]);;

let P2B_NONNEG_BOUNDED_ORIG_IMP_FIX = prove
 (`!(u:A->bool). P2C_REQ_NONNEG_BOUNDED_STATEMENT u ==> P2B_NONNEG_BOUNDED_FIX_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_STATEMENT; P2B_NONNEG_BOUNDED_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "h" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `a:real`] THEN ASM_REWRITE_TAC[]);;

let P2B_KAPPA_NECKS_ROUND_ORIG_IMP_FIX = prove
 (`!(w:B->bool).
     P2C_REQ_KAPPA_NECKS_ROUND_STATEMENT w ==> P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_KAPPA_NECKS_ROUND_STATEMENT; P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPECL [`eps:real`; `kappa:real`; `top:B topology`;
                    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ASM_SIMP_TAC[P2B_KAPPA_SOLUTION_P2C]);;

let P2B_AVR_ZERO_ORIG_IMP_FIX = prove
 (`!(w:B->bool). P2C_REQ_AVR_ZERO_STATEMENT w ==> P2B_AVR_ZERO_FIX_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_AVR_ZERO_STATEMENT; P2B_AVR_ZERO_FIX_STATEMENT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN
  ASM_SIMP_TAC[P2B_KAPPA_SOLUTION_P2C]);;

(* A5L FIX implies A5 FIX (L = 1: rfs_strong_neck is the evolving neck of   *)
(* normalized length 1).                                                     *)

let P2B_KAPPA_NECKS_ROUND_L_FIX_IMP_FIX = prove
 (`!w:B->bool. P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT w
               ==> P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT; P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT;
              rfs_strong_neck] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The slice form of A4 (P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT,            *)
(* pc_p2b_kreq) implies A4 FIX (the slice at time 0 of the flow).           *)

let P2B_NONNEG_BOUNDED_SLICE_IMP_FIX = prove
 (`!u:A->bool. P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT u ==> P2B_NONNEG_BOUNDED_FIX_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT; P2B_NONNEG_BOUNDED_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `g:real->A->real^3^3`] THEN
  STRIP_TAC THEN
  USE_THEN "h" (MP_TAC o SPECL [`C:real`; `eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) (&0)`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2B_CAP_ORIG_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_PROP_9_79_CAP_STATEMENT u w ==> P2B_PROP_9_79_CAP_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_PROP_9_79_CAP_STATEMENT; P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "orig") THEN
  MAP_EVERY EXISTS_TAC [`&2`; `&1 / &8`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "orig" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "d" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`; `psi':B->A`]) THEN
  ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* P5. The Appendix statements A.4, A.6, A.7 imply their constant-speed      *)
(* forms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let P2B_APX_A4_CS = prove
 (`!u:A->bool. APX_A4_STATEMENT u ==> P2B_APX_A4_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A4_STATEMENT; P2B_APX_A4_CS_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "h") THEN X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `alpha:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps1:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`]) THEN
  ASM_REWRITE_TAC[]);;

let P2B_APX_A6_CS = prove
 (`!u:A->bool. APX_A6_STATEMENT u ==> P2B_APX_A6_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A6_STATEMENT; P2B_APX_A6_CS_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps1:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`; `r:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`; `r:real`]) THEN
  ASM_REWRITE_TAC[]);;

let P2B_APX_A7_CS = prove
 (`!u:A->bool. APX_A7_STATEMENT u ==> P2B_APX_A7_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A7_STATEMENT; P2B_APX_A7_CS_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps1:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`; `r:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                       `gamma:real->A`; `a:real`; `b:real`; `r:real`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P6. Slices of history views: empty before time 0 and separating when the *)
(* stages separate (the empty space has no neck charts).                     *)
(* ------------------------------------------------------------------------- *)

let P2B_APX_SPHERE_SEP_EMPTY = prove
 (`!atlas:((A->bool)#(A->real^3))->bool. apx_sphere_sep (discrete_topology {}) atlas`,
  GEN_TAC THEN REWRITE_TAC[apx_sphere_sep; mfd_neck_chart; mfd_param; mfd_diffeo] THEN
  X_GEN_TAC `e:real^3->A` THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in (discrete_topology ({}:A->bool))
                       (IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)))` THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^3`) THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let P2B_RFS_VIEW_PARTS = prove
 (`!hs:(A)rfs_history.
     rfs_vtop (rfs_view hs) = rfs_top_at hs /\ rfs_vatlas (rfs_view hs) = rfs_atlas_at hs /\
     rfs_vmetric (rfs_view hs) = rfs_metric_at hs`,
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2B_RFS_TOP_AT_NEG = prove
 (`!hs:(A)rfs_history s. s < &0 ==> rfs_top_at hs s = discrete_topology {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at; rfs_live] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2B_HS_SEP_SLICES = prove
 (`!hs:(A)rfs_history s.
     rfs_history_ok hs /\ p2b_hs_sep hs
     ==> apx_sphere_sep (rfs_top_at hs s) (rfs_atlas_at hs s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfs_top_at; rfs_atlas_at] THEN
  COND_CASES_TAC THEN REWRITE_TAC[P2B_APX_SPHERE_SEP_EMPTY] THEN
  UNDISCH_TAC `p2b_hs_sep (hs:(A)rfs_history)` THEN REWRITE_TAC[p2b_hs_sep] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfs_horizon] THEN ASM_MESON_TAC[rfs_live]; SIMP_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* P7. Compositions: Cor 9.94 from its noncompact and compact cases and      *)
(* monotonicity in C; Cor 9.95 (P2_COR_9_95) from Cor 9.94, the transfer and *)
(* the passage of separation (P2_SEP_LIMIT) and local orientability to the   *)
(* limit; the FIX form of A3 from the length-L forms; Thm 10.2 for views     *)
(* (the statement A2 of pc_p2c_iface) from its two halves; the history form  *)
(* P2_THM_10_2 from the view form with P2C_HISTORY_REGULAR.                  *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_94_FROM_PARTS = prove
 (`!(w:B->bool).
     P2B_KSOL_NONCOMPACT_CANON_STATEMENT w /\ P2B_KSOL_COMPACT_CANON_STATEMENT w /\
     P2B_CANON_MONO_C_STATEMENT w
     ==> P2B_COR_9_94_KSEP_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_STATEMENT; P2B_KSOL_COMPACT_CANON_STATEMENT;
              P2B_COR_9_94_KSEP_STATEMENT; P2B_CANON_MONO_C_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h3")))
      (LABEL_TAC "mono"))) THEN
  EXISTS_TAC `min eps2 eps3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  REMOVE_THEN "h3" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
  REMOVE_THEN "h2" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  EXISTS_TAC `max C0 C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `x:B`] THEN
  STRIP_TAC THEN REMOVE_THEN "mono" MATCH_MP_TAC THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [EXISTS_TAC `C1:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    REMOVE_THEN "c1" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `C0:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    REMOVE_THEN "c0" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]]);;


(* On a connected noncompact slice the component alternatives of a          *)
(* canonical neighbourhood are void, so canon_at gives canonv_at.           *)

let P2B_CANONV_NONCOMPACT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t.
     connected_space (rfs_vtop V t) /\ ~compact_space (rfs_vtop V t) /\
     p3_canon_at V C eps x t
     ==> p3_canonv_at V C eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `eps:real`; `x:A`; `t:real`] THEN
  REWRITE_TAC[p3_canon_at; p3_canonv_at; rfs_strong_canonical; p3_strong_canonv;
              rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `U:A->bool`))) THEN
  SUBGOAL_THEN `~(U IN connected_components_of ((TM:real->A topology) t) /\
                  compact_in (TM t) U)` (LABEL_TAC "nocomp") THENL
   [ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN STRIP_TAC THEN
    UNDISCH_TAC `compact_in ((TM:real->A topology) t) U` THEN
    ASM_REWRITE_TAC[GSYM compact_space];
    ALL_TAC] THEN
  SUBGOAL_THEN `~rfs_c_component ((TM:real->A topology) t,AT t) (G t) C U /\
                ~rfs_round_component (TM t,AT t) (G t) eps U` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_c_component; rfs_round_component] THEN
    USE_THEN "nocomp" MP_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  EXISTS_TAC `U:A->bool` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[]);;

(* Cor 9.94 for the class in canonv form, from the noncompact case           *)
(* (canon_at, through P2B_CANONV_NONCOMPACT) and the canonv compact case.    *)

let P2B_COR_9_94_V_FROM_PARTS = prove
 (`!(w:B->bool).
     P2B_KSOL_NONCOMPACT_CANON_STATEMENT w /\ P2B_KSOL_COMPACT_CANON_V_STATEMENT w /\
     P2B_CANON_MONO_C_V_STATEMENT w
     ==> P2B_COR_9_94_KSEP_V_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_STATEMENT; P2B_KSOL_COMPACT_CANON_V_STATEMENT;
              P2B_COR_9_94_KSEP_V_STATEMENT; P2B_CANON_MONO_C_V_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h3")))
      (LABEL_TAC "mono"))) THEN
  EXISTS_TAC `min eps2 eps3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  REMOVE_THEN "h3" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
  REMOVE_THEN "h2" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  EXISTS_TAC `max C0 C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `x:B`] THEN
  STRIP_TAC THEN REMOVE_THEN "mono" MATCH_MP_TAC THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [EXISTS_TAC `C1:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    REMOVE_THEN "c1" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `C0:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    MATCH_MP_TAC P2B_CANONV_NONCOMPACT THEN REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
      SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "c0" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]]);;

(* P2_COR_9_95_STATEMENT concludes p3_canonv_at; the proof runs on the       *)
(* canonv parts (COR_9_94_KSEP_V, CANON_MONO_C_V, LIMIT_TRANSFER_V).         *)

let P2B_COR_9_95_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_COR_9_94_KSEP_V_STATEMENT w /\ P2B_CANON_MONO_C_V_STATEMENT w /\
     P2B_LIMIT_TRANSFER_V_STATEMENT u w /\ P2_SEP_LIMIT_STATEMENT u w /\
     P2B_LORIENT_LIMIT_STATEMENT u w
     ==> P2_COR_9_95_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_COR_9_94_KSEP_V_STATEMENT; P2_COR_9_95_STATEMENT;
              P2B_CANON_MONO_C_V_STATEMENT; P2B_LIMIT_TRANSFER_V_STATEMENT;
              P2_SEP_LIMIT_STATEMENT; P2B_LORIENT_LIMIT_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `epsp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h94")))
    (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `epst:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "transfer")))
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (LABEL_TAC "lor"))))) THEN
  EXISTS_TAC `min epsp epst` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  REMOVE_THEN "h94" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C94:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c94"))) THEN
  EXISTS_TAC `C94:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                       `Q:num->real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `xl:B`; `kappa:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hist")
             (CONJUNCTS_THEN2 (LABEL_TAC "lim") ASSUME_TAC))) THEN
  SUBGOAL_THEN `p3_flow_limit (\n. rfs_view ((hs:num->(A)rfs_history) n)) x t Q
                  (top:B topology,atlas) g xl (&1)` ASSUME_TAC THENL
   [USE_THEN "lim" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(xl:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (\n. rfs_view ((hs:num->(A)rfs_history) n)) x t Q
                   (top:B topology,atlas) g xl (&1)` THEN
    REWRITE_TAC[p3_flow_limit] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ksep (top:B topology) atlas` ASSUME_TAC THENL
   [REWRITE_TAC[p2b_ksep] THEN CONJ_TAC THENL
     [REMOVE_THEN "sep" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                            `Q:num->real`; `g:real->B->real^3^3`; `xl:B`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "hist" (fun th -> MESON_TAC[th]);
      REMOVE_THEN "lor" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                            `Q:num->real`; `g:real->B->real^3^3`; `xl:B`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "hist" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  REMOVE_THEN "transfer" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
                        `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:real->B->real^3^3`; `xl:B`; `kappa:real`] THEN
  SUBGOAL_THEN `p3_canonv_at (p2b_kview (top:B topology,atlas) g) C eps xl (&0)`
  ASSUME_TAC THENL
   [REMOVE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `C94:real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
    REMOVE_THEN "c94" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < C /\ &0 < eps /\ eps <= epst` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "hist" (fun th -> MESON_TAC[th]));;

let P2B_THM_10_2_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_BAD_TUBE_FROM_FAILURE_STATEMENT u w /\ P2B_NO_BAD_TUBE_STATEMENT w
     ==> P2C_REQ_THM_10_2_VIEW_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_BAD_TUBE_FROM_FAILURE_STATEMENT; P2B_NO_BAD_TUBE_STATEMENT;
              P2C_REQ_THM_10_2_VIEW_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bad")))
    (X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nobad")))) THEN
  EXISTS_TAC `min eps0 eps1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  REMOVE_THEN "nobad" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  REMOVE_THEN "bad" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`D0:real`; `D:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`D0:real`; `D:real`]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_AND_EXISTS_THM] THEN REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let P2B_COR_9_95_VIEW_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_COR_9_94_L_STATEMENT w /\ P2B_LIMIT_TRANSFER_VIEW_STATEMENT u w /\
     P2B_SEP_LIMIT_VIEW_STATEMENT u w /\ P2B_LORIENT_LIMIT_VIEW_STATEMENT u w
     ==> P2B_COR_9_95_VIEW_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_COR_9_94_L_STATEMENT; P2B_COR_9_95_VIEW_FIX_STATEMENT;
              P2B_LIMIT_TRANSFER_VIEW_STATEMENT; P2B_SEP_LIMIT_VIEW_STATEMENT;
              P2B_LORIENT_LIMIT_VIEW_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `epsp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h94")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `epst:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "transfer")))
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (LABEL_TAC "lor")))) THEN
  EXISTS_TAC `min epsp epst` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "h94" (MP_TAC o SPECL [`eps:real`; `L + &1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c94"))) THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`; `kappa:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hist")
             (CONJUNCTS_THEN2 (LABEL_TAC "lim") ASSUME_TAC))) THEN
  SUBGOAL_THEN `p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) x t Q
                  (top:B topology,atlas) g xl (&1)` ASSUME_TAC THENL
   [USE_THEN "lim" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(xl:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit (V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q
                   (top:B topology,atlas) g xl (&1)` THEN
    REWRITE_TAC[p3_flow_limit] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ksep (top:B topology) atlas` ASSUME_TAC THENL
   [REWRITE_TAC[p2b_ksep] THEN CONJ_TAC THENL
     [REMOVE_THEN "sep" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `x:num->A`; `t:num->real`; `Q:num->real`; `g:real->B->real^3^3`; `xl:B`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "hist" (fun th -> MESON_TAC[th]);
      REMOVE_THEN "lor" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `x:num->A`; `t:num->real`; `Q:num->real`; `g:real->B->real^3^3`; `xl:B`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "hist" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_canon_L (p2b_kview (top:B topology,atlas) g) C eps (L + &1) xl (&0)`
  ASSUME_TAC THENL
   [REMOVE_THEN "c94" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "transfer" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
                        `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:real->B->real^3^3`; `xl:B`; `kappa:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < C /\ &0 < eps /\ eps <= epst` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "hist" (fun th -> MESON_TAC[th]));;

let P2B_THM_10_2_HIST = prove
 (`!u:A->bool.
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> P2_THM_10_2_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_THM_10_2_VIEW_STATEMENT; P2C_HISTORY_REGULAR_STATEMENT;
              P2_THM_10_2_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v")))
    (LABEL_TAC "reg")) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "v" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D0:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w"))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `t:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "w" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `x:A`; `t:real`]) THEN
  REWRITE_TAC[P2B_RFS_VIEW_PARTS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[P2B_RFS_TOP_AT_NEG; P2B_HS_SEP_SLICES] THEN
  USE_THEN "reg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2B_PROP_9_79_NECK_ORIG_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2_PROP_9_79_NECK_STATEMENT u w ==> P2B_PROP_9_79_NECK_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2_PROP_9_79_NECK_STATEMENT; P2B_PROP_9_79_NECK_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`eps:real`; `eps':real`; `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "h" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `e:real^3->A`; `Q':real`] THEN
  ASM_SIMP_TAC[]);;

let P2B_NECK_P2C_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_NECK_FIX_STATEMENT u w ==> P2B_PROP_9_79_NECK_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_NECK_FIX_STATEMENT; P2B_PROP_9_79_NECK_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`eps:real`; `eps':real`; `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "h" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `e:real^3->A`; `Q':real`] THEN
  ASM_SIMP_TAC[]);;

let P2B_SLICE_ORIG_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2_PROP_9_79_SLICE_STATEMENT u w ==> P2B_PROP_9_79_SLICE_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2_PROP_9_79_SLICE_STATEMENT; P2B_PROP_9_79_SLICE_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "orig"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "orig" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REMOVE_THEN "d" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2B_SLICE_P2C_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_SLICE_FIX_STATEMENT u w ==> P2B_PROP_9_79_SLICE_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_SLICE_FIX_STATEMENT; P2B_PROP_9_79_SLICE_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "orig"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "orig" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REMOVE_THEN "d" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2B_CAP_P2C_IMP_FIX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_CAP_FIX_STATEMENT u w ==> P2B_PROP_9_79_CAP_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_REQ_CAP_FIX_STATEMENT; P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "orig"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "orig" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REMOVE_THEN "d" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `Y:A->bool`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[]);;

