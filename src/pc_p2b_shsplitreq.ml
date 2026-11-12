(* ========================================================================= *)
(* pc_p2b_shsplitreq (statement only): P2B_SHRINKER_SPLIT_CYL_STATEMENT, the *)
(* splitting step of SPLIT_ROUND: a complete connected Hausdorff shrinker    *)
(* slice with sec >= 0, bounded R, R > 0 somewhere, p2b_lorient and a global *)
(* unit parallel field Y is the one-to-one round cylinder model, with Y its  *)
(* unit axial field.  Proved in pc_p2b_shsplit (P2B_SHRINKER_SPLIT_CYL).     *)
(* ========================================================================= *)

(* ========================================================================= *)
(* SPLIT_ROUND applies the statement to the time-0 slice of the asymptotic   *)
(* soliton of the split flow, with Y the limit field of P2BPL_LIMIT_FIELD    *)
(* (pc_p2b_parfieldreq) and the curvature bound P2B_GSPLIT_SLICE_BOUND_ROUTE *)
(* (pc_p2b_x0r) applied to the soliton flow.                                 *)
(*                                                                           *)
(* A complete connected shrinker slice (Ric + Hess f = g / 2) with sec >= 0, *)
(* bounded and not identically zero scalar curvature, relatively compact     *)
(* open subsets orientable, and a global unit parallel field Y is the round *)
(* cylinder: a one-to-one local parametrization p of the whole slice by     *)
(* real^3 minus the origin with p^* g = lam cylinder_flow(0) (necessarily    *)
(* lam = 1), and Y = dp(y / sqrt(2 lam)), the unit axial field of the model. *)
(*                                                                           *)
(* Proof (pc_p2b_shsplit): Ric(Y,.) = 0 and the shrinker equation give       *)
(* Hess f(Y,.) = g(Y,.) / 2, so h = 2 Y(f) has gradient Y: a global          *)
(* primitive, no topology needed.  The level sets of h are regular and       *)
(* totally geodesic, h(Phi_r y) = h y + r along the flow of Y (pc_p2b_kfl,   *)
(* isometries), and a level set N is a 2-d shrinker with R = C e^f on N;     *)
(* then f is bounded above on N and sublevel sets of f are compact           *)
(* (P2BX46_F_PROPER), so N is compact; C > 0 (not flat), so K > 0 and N is   *)
(* round (the 2-d clause of P2B_REQ_RFA_SHRINKER_ROUND).  Cartan maps from   *)
(* the stereographic model, glued by a Mobius map, cover N; flowing them     *)
(* along Y gives the local isometry p, whose fibres are single points or     *)
(* antipodal pairs, and the antipodal case (RP^2 x R) is excluded by the     *)
(* orientability clause.                                                     *)
(*                                                                           *)
(* Degenerate cases: the flat Gaussian shrinker on real^3 has parallel      *)
(* fields and bounded R but is excluded by R > 0 somewhere; the round S^2 x *)
(* R satisfies everything (Y = d/dr, lam = 1); its Z/2 quotient has no      *)
(* global parallel unit field; compact shrinkers have no parallel field.    *)
(* ========================================================================= *)

needs "src/pc_p2b_shrinkreq.ml";;
needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_p2b_kreq.ml";;
needs "src/pc_mfd_diff.ml";;
needs "src/pc_rfs_geom.ml";;

prioritize_real();;
type_invention_error := true;;


let P2B_SHRINKER_SPLIT_CYL_STATEMENT = new_definition
 `P2B_SHRINKER_SPLIT_CYL_STATEMENT (w:B->bool) <=>
    !top atlas (g:B->real^3^3) f (Y:B->real^3).
       hausdorff_space top /\ connected_space top /\
       p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       (?K. !x. x IN topspace top ==> mfd_scalar atlas g x <= K) /\
       (?x. x IN topspace top /\ &0 < mfd_scalar atlas g x) /\
       p2b_lorient top atlas /\
       p2b_parallel_on atlas g (topspace top) Y /\
       (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1)
       ==> ?p lam. &0 < lam /\
                   IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
                   (!y. ~(y = vec 0)
                        ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
                   (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
                   (!y. ~(y = vec 0)
                        ==> rfs_pullback atlas p g y = lam %% cylinder_flow (&0) y) /\
                   (!y. ~(y = vec 0)
                        ==> Y(p y) =
                            mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                             (inv(sqrt(&2 * lam)) % y))`;;

