(* ========================================================================= *)
(* Unit pc_p2b_c994req (statements, plus the composing chain theorem): MT    *)
(* Thm 9.93 / Cor 9.94 in the length-L form P2B_COR_9_94_L_STATEMENT         *)
(* (pc_p2b_defs), split into pieces (a) Prop 9.83 for p2b_ksep on X1, (b)    *)
(* Lemma 9.84 / Prop 9.85 with evolving necks of length L, (c) the topology  *)
(* at a soul (MT Lemma A.10, Prop 9.85 (2)), (d) Cor 9.88 with length L, (e) *)
(* Thm 9.89 / Claim 9.90 / Prop 9.91 with length L, (g) all-neck manifolds   *)
(* contain a line (A5L only), (h) the cylinder model has necks of every      *)
(* length, and (f) the assembly; the top route                               *)
(* P2B_COR_9_94_L_ROUTE_STATEMENT has the inputs X1, THM_9_64, PROP_9_58,    *)
(* LEMMA_9_65, COR_9_71, COR_9_44, ASYM_SOLITON; P2B_C994_CHAIN composes the *)
(* piece routes.                                                             *)
(*                                                                           *)
(* The hypotheses of P2B_CYL_MODEL_NECKS_STATEMENT (h) include (!t. t <= &0  *)
(* ==> riemannian_metric atlas (g t)), needed to compute mfd_scalar through  *)
(* p; its users (b) and (d) apply (h) to kappa-solutions, which have it.     *)
(* The route of (b), P2B_PROP_9_85L_ROUTE_STATEMENT, has the input           *)
(* P2B_SOUL_TOPOLOGY_STATEMENT (c): Lemma 2.20's separation at the closest   *)
(* non-neck point needs a soul base point (MT Prop 9.85(2), Lemma A.10); MT  *)
(* Remark 9.86 (any non-neck base point) is stated without proof; (b) is     *)
(* proved at the soul and reduced to general base points.  (c) is also an    *)
(* input of (d).                                                             *)
(* ========================================================================= *)

needs "src/pc_p2b_chainstmts.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* (a) MT Prop 9.83 for the class p2b_ksep: positive curvature at time 0 or *)
(* the cylinder model (one-to-one or the orientable Z/2 quotient) for all   *)
(* t <= 0.  Route: a zero plane at time 0 gives zero planes at all earlier  *)
(* times (RFA_P2B_REQ_SMP_SPLIT_PT), X1 at each s0 < 0, and the final slice *)
(* by continuity of the flow at 0 (X1 is stated for open ends).  Compact    *)
(* manifolds: X1 is impossible there (the model is noncompact), so a zero   *)
(* plane does not occur (MT p. 240, S^2 x S^1 is not kappa-noncollapsed).   *)
(* ------------------------------------------------------------------------- *)

let P2B_PROP_9_83K_STATEMENT = new_definition
 `P2B_PROP_9_83K_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas
       ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 < mfd_sectional atlas (g(&0)) x u v) \/
           p2b_cyl_model (top,atlas) g`;;

let P2B_PROP_9_83K_ROUTE_STATEMENT = new_definition
 `P2B_PROP_9_83K_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_CYL_STATEMENT w ==> P2B_PROP_9_83K_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* (h) The one-to-one cylinder model (the first alternative of              *)
(* p2b_cyl_model, unpacked): every point at every time t <= 0 is the centre *)
(* of an evolving delta-neck of every length L, for every delta > 0.  The   *)
(* neck is p after a power map y |-> norm y pow (a - 1) % y (it matches the *)
(* radial factor lam / (lam - t)) and a dilation; the closeness is exactly  *)
(* 0 (lck_dist2 is covariant for the cylinder metric, which is dilation     *)
(* invariant).  No inputs.                                                    *)
(* ------------------------------------------------------------------------- *)

let P2B_CYL_MODEL_NECKS_STATEMENT = new_definition
 `P2B_CYL_MODEL_NECKS_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) p lam.
       smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\ &0 < lam /\
       (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
       IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
       (!y. ~(y = vec 0)
            ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
       (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
       (!t y. t <= &0 /\ ~(y = vec 0)
              ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y)
       ==> !delta L t x. &0 < delta /\ &1 <= L /\ t <= &0 /\ x IN topspace top
                         ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) delta x t L e`;;

(* ------------------------------------------------------------------------- *)
(* (g) All points neck centres.  For the A5L route of pc_p2b_chainstmts      *)
(* (pc_p2b_a5l); not an input of the chain below.  By APX_A19 a compact such *)
(* manifold would lie in one eps-tube, which is not compact; otherwise both  *)
(* sides of a neck sphere have noncompact closure (a compact side would lie  *)
(* in a tube, against the tube chart), so there are two ends and             *)
(* APXT_TWO_ENDS_LINE gives a line.  No inputs.                              *)
(* ------------------------------------------------------------------------- *)

let P2B_ALL_NECK_LINE_STATEMENT = new_definition
 `P2B_ALL_NECK_LINE_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps top atlas (g:B->real^3^3).
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ connected_space top /\
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         mfd_complete (top,atlas) g /\ apx_sphere_sep top atlas /\ ~(topspace top = {}) /\
         (!x. x IN topspace top ==> ?e. rfs_neck (top,atlas) g eps x e)
         ==> ~compact_space top /\
             ?lam:real->B. !s t. lam s IN topspace top /\
                                 mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)`;;

(* ------------------------------------------------------------------------- *)
(* (c) Topology at a soul p (every other point regular for d_p, the output  *)
(* of CMP_R5_SOUL): (1) p is not in the middle two thirds of any eps-neck   *)
(* (MT Lemma A.10, Prop 9.85 (2): otherwise a distance ball about p is a    *)
(* slab with two boundary spheres, while the regular field of CMP_R6 makes  *)
(* every distance sphere connected); (2) the side of a neck sphere that     *)
(* contains p carries a ball chart b that continues the neck radially on    *)
(* the collar, as rfs_cap asks (flow of a regular field equal to the radial *)
(* field of the neck near the sphere and to the radial geodesic field near  *)
(* p).  No inputs.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2B_SOUL_TOPOLOGY_STATEMENT = new_definition
 `P2B_SOUL_TOPOLOGY_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps top atlas (g:B->real^3^3) p.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ connected_space top /\
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         mfd_complete (top,atlas) g /\ p IN topspace top /\
         (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x)
         ==> (!z e. rfs_neck (top,atlas) g eps z e
                    ==> ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * eps)))) /\
             (!z e. rfs_neck (top,atlas) g eps z e /\ ~(p IN IMAGE e (rfs_neck_dom eps)) /\
                    apx_separates top (IMAGE e (sphere(vec 0,&1))) p (e(&4 / &3 % basis 1))
                    ==> ?b f f'. mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\
                                 p IN IMAGE b (ball(vec 0,&1)) /\
                                 IMAGE b (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1)) /\
                                 (!y. y IN annulus (&1) (&2) ==> b y = e(radial_ext f y)))`;;

(* ------------------------------------------------------------------------- *)
(* (b) MT Lemma 9.84 and Prop 9.85 (1) with evolving necks of length L and  *)
(* any base point that is not the centre of a strong eps-neck (MT Remark    *)
(* 9.86): D = D(eps,L), D1 = D1(eps,L).  Route: compactness (THM_9_64 with  *)
(* the uniform kappa0 of PROP_9_58; positive curvature is not round), the   *)
(* limit is positively curved by (a) since its base point is no strong      *)
(* neck centre (Prop 9.79 parts 2 to 4), necks of length L far out in the   *)
(* limit (limits along points with d^2 R -> infinity contain a line: split, *)
(* a zero plane, (a), the model, (h)), Claim 9.87 by LEMMA_9_65, transfer  *)
(* by P2B_NECK_OPEN_L.                                                       *)
(* ------------------------------------------------------------------------- *)

let P2B_PROP_9_85L_STATEMENT = new_definition
 `P2B_PROP_9_85L_STATEMENT (w:B->bool) <=>
    ?eps2. &0 < eps2 /\
      !eps L. &0 < eps /\ eps <= eps2 /\ &1 <= L
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
                          ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) L e) /\
                     (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p
                                     (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
                              ~collinear {vec 0,u,v}
                              ==> inv D1 * mfd_scalar atlas (g(&0)) p <
                                  mfd_sectional atlas (g(&0)) x u v /\
                                  mfd_sectional atlas (g(&0)) x u v <
                                  D1 * mfd_scalar atlas (g(&0)) p)`;;

let P2B_PROP_9_85L_ROUTE_STATEMENT = new_definition
 `P2B_PROP_9_85L_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
    P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
    P2B_SOUL_TOPOLOGY_STATEMENT w
    ==> P2B_PROP_9_85L_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* (d) MT Cor 9.88 with length L, noncompact case.  Positive curvature:     *)
(* the soul p (CMP_R5_SOUL) is no strong neck centre ((c) part 1), so (b)   *)
(* applies at p; a neck sphere just outside the D-ball bounds a ball chart  *)
(* ((c) part 2), which with an adjacent outer neck is a (C,eps)-cap whose   *)
(* core contains the D-ball (constants: D1, the diameter, Bishop-Gromov for *)
(* the volume, kappa0 of PROP_9_58 for the noncollapsing clause, COR_9_71   *)
(* for the derivative clauses); points outside are L-neck centres.  Not     *)
(* positive: by (a) the model; one-to-one: (h); the Z/2 quotient: L-necks   *)
(* away from the core and an explicit twisted cap (rfs_twisted_chart) about *)
(* it.  (The soul is no neck centre by (c) part 1, so (g) is not needed.)   *)
(* ------------------------------------------------------------------------- *)

let P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT = new_definition
 `P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT (w:B->bool) <=>
    ?eps2. &0 < eps2 /\
      !eps L. &0 < eps /\ eps <= eps2 /\ &1 <= L
        ==> ?C0. &1 < C0 /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 ~compact_space top /\ x IN topspace top
                 ==> p2b_canon_L (p2b_kview (top,atlas) g) C0 eps L x (&0)`;;

let P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT = new_definition
 `P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_PROP_9_83K_STATEMENT w /\ P2B_PROP_9_85L_STATEMENT w /\
    P2B_SOUL_TOPOLOGY_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
    P2B_PROP_9_58_STATEMENT w /\ P2B_COR_9_71_STATEMENT w
    ==> P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* (e) MT Thm 9.89, Claim 9.90, Prop 9.91 with length L, compact case.      *)
(* Positive curvature by (a).  Round slice: an eps-round component.  Not    *)
(* round: PROP_9_58 gives kappa0; large diameter against R: a sequence and  *)
(* THM_9_64 give a noncompact limit, (d) there, transfer back by            *)
(* P2B_NECK_OPEN_L and P2B_PROP_9_79_OPEN_TYPED (Claim 9.90); small         *)
(* diameter: a C-component (curvature and volume from PROP_9_58 and         *)
(* THM_9_64, derivatives from COR_9_71; S^3 or RP^3 from APX_A25 at a very  *)
(* negative time, where the diameter is large because the asymptotic        *)
(* soliton (ASYM_SOLITON) is not compact (COR_9_44)).                        *)
(* ------------------------------------------------------------------------- *)

let P2B_KSOL_COMPACT_CANON_L_STATEMENT = new_definition
 `P2B_KSOL_COMPACT_CANON_L_STATEMENT (w:B->bool) <=>
    ?eps3. &0 < eps3 /\
      !eps L. &0 < eps /\ eps <= eps3 /\ &1 <= L
        ==> ?C1. &1 < C1 /\
              !kappa top atlas (g:real->B->real^3^3) x.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 compact_space top /\ x IN topspace top
                 ==> p2b_canon_L (p2b_kview (top,atlas) g) C1 eps L x (&0)`;;

let P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT = new_definition
 `P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_PROP_9_83K_STATEMENT w /\ P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT w /\
    P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\
    P2B_COR_9_71_STATEMENT w /\ P2B_COR_9_44_STATEMENT w /\
    P2B_ASYM_SOLITON_STATEMENT w
    ==> P2B_KSOL_COMPACT_CANON_L_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* (f) The assembly: the two cases with C = max C0 C1 and the                *)
(* monotonicity of p2b_canon_L in C (the cap and C-component clauses, as in *)
(* P2B_CANON_MONO_C of pc_p2b_lim).                                          *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_94_L_CASES_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_94_L_CASES_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT w /\ P2B_KSOL_COMPACT_CANON_L_STATEMENT w
    ==> P2B_COR_9_94_L_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* The top route and the composition of the piece routes.                   *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_94_L_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_94_L_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_CYL_STATEMENT w /\ P2B_THM_9_64_STATEMENT w /\
    P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
    P2B_COR_9_71_STATEMENT w /\ P2B_COR_9_44_STATEMENT w /\
    P2B_ASYM_SOLITON_STATEMENT w
    ==> P2B_COR_9_94_L_STATEMENT w`;;

let P2B_C994_CHAIN = prove
 (`!w:B->bool.
     P2B_PROP_9_83K_ROUTE_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
     P2B_SOUL_TOPOLOGY_STATEMENT w /\
     P2B_PROP_9_85L_ROUTE_STATEMENT w /\ P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT w /\
     P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT w /\ P2B_COR_9_94_L_CASES_ROUTE_STATEMENT w
     ==> P2B_COR_9_94_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_PROP_9_83K_ROUTE_STATEMENT; P2B_PROP_9_85L_ROUTE_STATEMENT;
              P2B_KSOL_NONCOMPACT_CANON_L_ROUTE_STATEMENT;
              P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT;
              P2B_COR_9_94_L_CASES_ROUTE_STATEMENT; P2B_COR_9_94_L_ROUTE_STATEMENT] THEN
  MESON_TAC[]);;

