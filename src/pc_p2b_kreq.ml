(* ========================================================================= *)
(* Unit pc_p2b_kreq (Part 2B): the class vocabulary of the Part 2B route     *)
(* (p2b_lorient, p2b_ksep), the canonical-neighbourhood alternatives with an *)
(* evolving neck of normalized length L (p2b_canon_L), the FIX forms of the  *)
(* statements A3, A5, A6 of pc_p2c_iface (P2B_COR_9_95_VIEW_FIX,             *)
(* P2B_KAPPA_NECKS_ROUND_FIX, P2B_AVR_ZERO_FIX) with the length-L form       *)
(* A5L_FIX of A5 (P2B_KAPPA_NECKS_ROUND_L_FIX), the slice form of A4 and the *)
(* flat-forward statement P2B_REQ_FLAT_FORWARD_STATEMENT.  These definitions *)
(* are in a unit of their own so that pc_p2c_iface can state its routes with *)
(* them; pc_p2b_defs loads this unit and proves that the forms of            *)
(* pc_p2c_iface imply the FIX forms (ORIG_IMP_FIX).  This unit needs only    *)
(* pc_p3_iface and pc_apx_defs (not pc_p2c_iface).                           *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_apx_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V2. The class of the route: neck spheres separate and relatively compact  *)
(* open subsets are orientable (excludes RP^2 x I; passes to geometric       *)
(* limits, unlike orientability of the whole manifold).                      *)
(* ------------------------------------------------------------------------- *)

let p2b_lorient = new_definition
 `p2b_lorient (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) <=>
    !W. open_in top W /\ compact_in top (top closure_of W)
        ==> mfd_orientable (subtopology top W) (restrict_atlas atlas W)`;;

let p2b_ksep = new_definition
 `p2b_ksep (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) <=>
    apx_sphere_sep top atlas /\ p2b_lorient top atlas`;;

(* ------------------------------------------------------------------------- *)
(* V5. Canonical-neighbourhood alternatives with an evolving neck of         *)
(* normalized length L (as in A3 of pc_p2c_iface; L = 1 is p3_canon_at).     *)
(* ------------------------------------------------------------------------- *)

let p2b_canon_L = new_definition
 `p2b_canon_L (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) (C:real) (eps:real) (L:real) (x:A) (t:real) <=>
    (?e. rfs_evolving_neck V eps x t L e) \/
    (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
    (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
    (?U. x IN U /\ rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`;;

(* ------------------------------------------------------------------------- *)
(* Variants of the statements A3, A5, A6 of pc_p2c_iface (the FIX forms)     *)
(* with slice separation, the kappa-solution notion p2b_kappa_solution and   *)
(* complete slices at the base times; each is implied by the form of         *)
(* pc_p2c_iface (pc_p2b_defs, section P4).  A4 FIX is in pc_p2b_defs.        *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_95_VIEW_FIX_STATEMENT = new_definition
 `P2B_COR_9_95_VIEW_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps L. &0 < eps /\ eps <= epsp /\ &1 <= L
        ==> ?C95. &1 < C95 /\
              !C V x t Q top atlas g xl kappa.
                 C95 <= C /\
                 (!n. p2c_regular_view (V n:(real->A topology)#
                                            (real->((A->bool)#(A->real^3))->bool)#
                                            (real->A->real^3^3)) /\
                      x n IN topspace(rfs_vtop (V n) (t n)) /\
                      mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                   (rfs_vmetric (V n) (t n)) /\
                      (!s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
                      !s. ~(topspace(rfs_vtop (V n) s) = {})
                          ==> mfd_orientable (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
                 (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl) /\
                 p2b_kappa_solution kappa (top,atlas) g
                 ==> ?N. !n. N <= n ==> p2b_canon_L (V n) C eps L (x n) (t n)`;;

let P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT = new_definition
 `P2B_KAPPA_NECKS_ROUND_FIX_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps kappa top atlas g.
         &0 < eps /\ eps <= eps0 /\ p2b_kappa_solution kappa (top:B topology,atlas) g /\
         p2b_ksep top atlas /\
         (!t x. t <= &0 /\ x IN topspace top ==> ?e. rfs_neck (top,atlas) (g t) eps x e)
         ==> !delta t x. &0 < delta /\ t <= &0 /\ x IN topspace top
                         ==> ?e. rfs_strong_neck (rfs_flow_view (top,atlas) {s | s <= &0} g)
                                                 delta x t e`;;

let P2B_AVR_ZERO_FIX_STATEMENT = new_definition
 `P2B_AVR_ZERO_FIX_STATEMENT (w:B->bool) <=>
    !kappa top atlas g x eps.
       p2b_kappa_solution kappa (top:B topology,atlas) g /\ p2b_ksep top atlas /\
       x IN topspace top /\ &0 < eps
       ==> ?A v. &0 < A /\
                 mfd_has_volume (top,atlas) (g (&0)) (mfd_ball (top,atlas) (g (&0)) x A) v /\
                 v < eps * A pow 3`;;

(* A5L_FIX: A5 FIX with an evolving neck of every normalized length L >= 1  *)
(* (the length-L form A5L of A5 in pc_p2c_iface, with p2b_kappa_solution    *)
(* and p2b_ksep; L = 1 gives A5 FIX, P2B_KAPPA_NECKS_ROUND_L_FIX_IMP_FIX in *)
(* pc_p2b_defs).                                                            *)

let P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT = new_definition
 `P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps kappa top atlas g.
         &0 < eps /\ eps <= eps0 /\ p2b_kappa_solution kappa (top:B topology,atlas) g /\
         p2b_ksep top atlas /\
         (!t x. t <= &0 /\ x IN topspace top ==> ?e. rfs_neck (top,atlas) (g t) eps x e)
         ==> !delta L t x. &0 < delta /\ &1 <= L /\ t <= &0 /\ x IN topspace top
                           ==> ?e. rfs_evolving_neck
                                     (rfs_flow_view (top,atlas) {s | s <= &0} g)
                                     delta x t L e`;;

(* The slice form of A4 (Prop 2.19 is a slice statement; MT uses it at      *)
(* Claim 11.7 and Prop 11.10 where only local flows exist).                 *)

let P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT = new_definition
 `P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         hausdorff_space (top:B topology) /\
         smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
         riemannian_metric atlas (g:B->real^3^3) /\
         connected_space top /\ mfd_complete (top,atlas) g /\
         apx_sphere_sep top atlas /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas g x u v) /\
         (!x. x IN topspace top /\ &4 < mfd_scalar atlas g x
              ==> ?U. rfs_canonical_nbhd (top,atlas) g C eps x U)
         ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas g x <= K`;;

(* ------------------------------------------------------------------------- *)
(* Flat forward (a Part 2B lemma, proved as P2B_FLAT_FORWARD_BODY in         *)
(* pc_p2b_flatfwd).                                                          *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_FLAT_FORWARD_STATEMENT = new_definition
 `P2B_REQ_FLAT_FORWARD_STATEMENT (u:A->bool) <=>
    !top atlas a b (g:real->A->real^3^3) t0 K.
       hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < t0 /\ t0 < b /\
       (!t. t0 <= t /\ t < b ==> mfd_complete (top,atlas) (g t)) /\
       (!t x. t0 <= t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
       (!t x v1 v2. t0 <= t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                    ==> &0 <= mfd_sectional atlas (g t) x v1 v2) /\
       (!x. x IN topspace top ==> mfd_scalar atlas (g t0) x = &0)
       ==> !t x. t0 <= t /\ t < b /\ x IN topspace top ==> mfd_scalar atlas (g t) x = &0`;;

