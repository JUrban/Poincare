(* ========================================================================= *)
(* pc_smt_defs: definitions and statement constants of the smooth topology   *)
(* part (Smale's theorem in radial form and its planar core, gluing of       *)
(* balls, twisted spheres, the weak disc theorem, sphere sums, product       *)
(* structures, orientability, the standard S^3), with sanity theorems. They  *)
(* are built on pc_mfd_examples.ml (the S^3 and S^2 atlases, open_set_atlas) *)
(* and pc_mfd_maps.ml (manifold maps); flows are those of the ODE package    *)
(* (definitions pc_ode_defs.ml). The items are labelled A1-A8 (definitions   *)
(* on real^N), S1-S8 (statements of the real^N core) and M1-M11 (statements  *)
(* at the manifold level).                                                   *)
(*                                                                           *)
(* Definitions on real^N.                                                    *)
(* ========================================================================= *)

needs "src/pc_mfd_maps.ml";;
needs "src/pc_ode_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* A1. Smoothness near a set: smooth on some open set containing it.         *)

let smooth_near = new_definition
 `smooth_near (k:real^M->bool) (f:real^M->real^N) <=>
    ?u. open u /\ k SUBSET u /\ smooth_map_on u f`;;

(* A2. Radial extension (cone) of a map of the unit sphere, |x| f(x/|x|); it *)
(* is vec 0 at vec 0.                                                        *)

let radial_ext = new_definition
 `radial_ext (f:real^N->real^N) (x:real^N) = norm x % f(inv(norm x) % x)`;;

(* A3. Diffeomorphisms of the unit sphere, extrinsically: f and g smooth     *)
(* near the sphere, mapping it to itself, inverse to each other there        *)
(* (equivalent to the intrinsic notion: a smooth map of the sphere extends   *)
(* radially).                                                                *)

let sphere_diffeo = new_definition
 `sphere_diffeo (f:real^N->real^N) (g:real^N->real^N) <=>
    smooth_near (sphere(vec 0,&1)) f /\ smooth_near (sphere(vec 0,&1)) g /\
    (!x. x IN sphere(vec 0,&1)
         ==> f x IN sphere(vec 0,&1) /\ g x IN sphere(vec 0,&1) /\
             g(f x) = x /\ f(g x) = x)`;;

(* A4. Jointly smooth one-parameter families on R x u (time first).          *)

let smooth_family = new_definition
 `smooth_family (u:real^M->bool) (H:real->real^M->real^N) <=>
    smooth_map_on ((:real^1) PCROSS u)
                  (\z. H (drop(fstcart z)) (sndcart z))`;;

(* A5. Isotopies of diffeomorphisms of R^N (K t is the inverse of H t).      *)

let diffeo_isotopy = new_definition
 `diffeo_isotopy (H:real->real^N->real^N) (K:real->real^N->real^N) <=>
    smooth_family (:real^N) H /\ smooth_family (:real^N) K /\
    !t. diffeomorphism_on (:real^N) (:real^N) (H t) (K t)`;;

(* A6. Isotopies of diffeomorphisms of the unit sphere (extrinsic form).     *)

let sphere_isotopy = new_definition
 `sphere_isotopy (J:real->real^N->real^N) (J':real->real^N->real^N) <=>
    (?u. open u /\ sphere(vec 0,&1) SUBSET u /\
         smooth_family u J /\ smooth_family u J') /\
    (!t x. x IN sphere(vec 0,&1)
           ==> J t x IN sphere(vec 0,&1) /\ J' t x IN sphere(vec 0,&1) /\
               J' t (J t x) = x /\ J t (J' t x) = x)`;;

(* A7. The real-time view of the flow ode_vf_flow of the ODE package on R^N  *)
(* (used for complete fields).                                               *)

let vf_rflow = new_definition
 `vf_rflow (v:real^N->real^N) (t:real) (x:real^N) =
    ode_vf_flow v (:real^N) (lift t) x`;;

(* A8. Transversality of a planar field to the segment [a,b].                *)

let transversal_on = new_definition
 `transversal_on (v:real^2->real^2) (a:real^2) (b:real^2) <=>
    !x. x IN segment[a,b]
        ==> ~((b - a)$1 * (v x)$2 - (b - a)$2 * (v x)$1 = &0)`;;


(* ------------------------------------------------------------------------- *)
(* Statement constants of the real^N core.                                   *)
(* ------------------------------------------------------------------------- *)

(* S1. Smale, radial form: every diffeomorphism of S^2 extends to a norm-    *)
(* preserving diffeomorphism of R^3 equal to the radial extension on 1/2 <=  *)
(* |x| <= 2 (both orientations).                                             *)

let SMT_SMALE_RADIAL_STATEMENT = new_definition
 `SMT_SMALE_RADIAL_STATEMENT <=>
    !f g:real^3->real^3.
        sphere_diffeo f g
        ==> ?h k. diffeomorphism_on (:real^3) (:real^3) h k /\
                  (!x. norm(h x) = norm x) /\
                  (!x. &1 / &2 <= norm x /\ norm x <= &2
                       ==> h x = radial_ext f x)`;;

(* S2. Every diffeomorphism of S^2 is joined to an orthogonal map by a       *)
(* smooth isotopy of S^2, stationary outside [0,1].                          *)

let SMT_SPHERE_ISOTOPY_STATEMENT = new_definition
 `SMT_SPHERE_ISOTOPY_STATEMENT <=>
    !f g:real^3->real^3.
        sphere_diffeo f g
        ==> ?J J' Q. sphere_isotopy J J' /\ orthogonal_transformation Q /\
                     (!t x. t <= &0 /\ x IN sphere(vec 0,&1) ==> J t x = Q x) /\
                     (!t x. &1 <= t /\ x IN sphere(vec 0,&1) ==> J t x = f x)`;;

(* S3. Compactly supported diffeomorphisms of R^2 are isotopic to the        *)
(* identity through diffeomorphisms supported in one ball, by an isotopy     *)
(* stationary outside [0,1].                                                 *)

let SMT_PLANAR_ISOTOPY_STATEMENT = new_definition
 `SMT_PLANAR_ISOTOPY_STATEMENT <=>
    !f g:real^2->real^2 r.
        diffeomorphism_on (:real^2) (:real^2) f g /\
        (!x. r <= norm x ==> f x = x)
        ==> ?H K. diffeo_isotopy H K /\
                  (!t x. t <= &0 ==> H t x = f x) /\
                  (!t x. &1 <= t ==> H t x = x) /\
                  (?R. !t x. R <= norm x ==> H t x = x)`;;

(* S3a. Smooth angle and modulus of a nonvanishing planar field equal to e_1 *)
(* outside a ball.                                                           *)

let SMT_SMOOTH_ANGLE_STATEMENT = new_definition
 `SMT_SMOOTH_ANGLE_STATEMENT <=>
    !v:real^2->real^2 r.
        smooth_map_on (:real^2) v /\ (!x. ~(v x = vec 0)) /\
        (!x. r <= norm x ==> v x = basis 1)
        ==> ?theta rho:real^2->real.
                smooth_map_on (:real^2) (\x. lift(theta x)) /\
                smooth_map_on (:real^2) (\x. lift(rho x)) /\
                (!x. &0 < rho x) /\
                (!x. r <= norm x ==> theta x = &0 /\ rho x = &1) /\
                (!x. v x = rho x % vector[cos(theta x); sin(theta x)])`;;

(* S3b. The forward half-orbit of a smooth nonvanishing planar field is      *)
(* unbounded.                                                                *)

let SMT_NO_BOUNDED_HALF_ORBIT_STATEMENT = new_definition
 `SMT_NO_BOUNDED_HALF_ORBIT_STATEMENT <=>
    !v:real^2->real^2 x.
        smooth_map_on (:real^2) v /\ (!y. ~(v y = vec 0))
        ==> ~bounded (IMAGE (\t. ode_vf_flow v (:real^2) t x)
                            {t | t IN ode_vf_maxint v (:real^2) x /\ &0 <= drop t})`;;

(* S3c. Straightening a family of nonvanishing fields equal to e_1 outside a *)
(* ball, by flowing from the line x$1 = -r.                                  *)

let SMT_STRAIGHTENING_STATEMENT = new_definition
 `SMT_STRAIGHTENING_STATEMENT <=>
    !V:real->real^2->real^2 r.
        smooth_family (:real^2) V /\ &0 < r /\
        (!s x. ~(V s x = vec 0)) /\
        (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s x. s <= &0 ==> V s x = V (&0) x) /\
        (!s x. &1 <= s ==> V s x = V (&1) x)
        ==> (!s y. ode_vf_maxint (V s) (:real^2) y = (:real^1)) /\
            ?Psi Psi' tau sigma R.
                (!s x. Psi s x =
                       ode_vf_flow (V s) (:real^2) (lift(x$1 + r)) (vector[--r; x$2])) /\
                diffeo_isotopy Psi Psi' /\
                (!s x. frechet_derivative (Psi s) (at x) (basis 1) =
                       V s (Psi s x)) /\
                (!s x. x$1 <= --r \/ r <= abs(x$2) ==> Psi s x = x) /\
                (!s x. R <= x$1
                       ==> Psi s x = vector[x$1 + tau s (x$2); sigma s (x$2)]) /\
                (!s f. (!x. f differentiable at x) /\
                       (!x. x$1 <= --r ==> f x = x) /\
                       (!x. frechet_derivative f (at x) (basis 1) = V s (f x))
                       ==> !x. f x = Psi s x)`;;

(* S3d. End correction: a compactly supported isotopy from h to I from a     *)
(* straightening isotopy.                                                    *)

let SMT_END_CORRECTION_STATEMENT = new_definition
 `SMT_END_CORRECTION_STATEMENT <=>
    !Psi Psi':real->real^2->real^2 tau sigma:real->real->real h r R.
        diffeo_isotopy Psi Psi' /\
        (!x. Psi (&0) x = x) /\ (!x. Psi (&1) x = h x) /\
        (!s x. x$1 <= --r \/ r <= abs(x$2) ==> Psi s x = x) /\
        (!s x. R <= x$1
               ==> Psi s x = vector[x$1 + tau s (x$2); sigma s (x$2)]) /\
        (!x. R <= norm x ==> h x = x)
        ==> ?H K. diffeo_isotopy H K /\
                  (!t x. t <= &0 ==> H t x = h x) /\
                  (!t x. &1 <= t ==> H t x = x) /\
                  (?R'. !t x. R' <= norm x ==> H t x = x)`;;

(* S4a. x + U t x with Lipschitz constant c < 1 is an isotopy of             *)
(* diffeomorphisms.                                                          *)

let SMT_PERTURB_ID_STATEMENT = new_definition
 `SMT_PERTURB_ID_STATEMENT (n:N->bool) <=>
    !U:real->real^N->real^N c.
        smooth_family (:real^N) U /\ &0 <= c /\ c < &1 /\
        (!t x y. norm(U t x - U t y) <= c * norm(x - y))
        ==> ?G. diffeo_isotopy (\t x. x + U t x) G`;;

(* S4b. Compactly supported isotopies from I to a diffeomorphism equal to L  *)
(* in GL+(N) near 0.                                                         *)

let SMT_LINEAR_GERM_STATEMENT = new_definition
 `SMT_LINEAR_GERM_STATEMENT (n:N->bool) <=>
    !L:real^N->real^N.
        linear L /\ &0 < det(matrix L)
        ==> ?H K e. diffeo_isotopy H K /\ &0 < e /\
                    (!t x. t <= &0 ==> H t x = x) /\
                    (!t x. &1 <= t ==> H t x = H (&1) x) /\
                    (!x. norm x <= e ==> H (&1) x = L x) /\
                    (?R. !t x. R <= norm x ==> H t x = x)`;;

(* S5. The region between two positive smooth radial graphs over S^2 is a    *)
(* radial image of the closed annulus 1 <= |x| <= 2.                         *)

let SMT_RADIAL_GRAPH_STATEMENT = new_definition
 `SMT_RADIAL_GRAPH_STATEMENT <=>
    !u1 u2:real^3->real.
        smooth_near (sphere(vec 0,&1)) (\x. lift(u1 x)) /\
        smooth_near (sphere(vec 0,&1)) (\x. lift(u2 x)) /\
        (!x. x IN sphere(vec 0,&1) ==> &0 < u1 x /\ u1 x < u2 x)
        ==> ?P P'. diffeomorphism_on ((:real^3) DELETE vec 0)
                                     ((:real^3) DELETE vec 0) P P' /\
                   (!x. ~(x = vec 0)
                        ==> inv(norm(P x)) % P x = inv(norm x) % x) /\
                   (!x. norm x = &1 ==> P x = u1 x % x) /\
                   (!x. norm x = &1 ==> P(&2 % x) = u2 x % x) /\
                   (!x. ~(x = vec 0)
                        ==> (&1 <= norm x /\ norm x <= &2 <=>
                             u1(inv(norm x) % x) <= norm(P x) /\
                             norm(P x) <= u2(inv(norm x) % x)))`;;

(* S6. Local diffeomorphisms of S^2 are diffeomorphisms.                     *)

let SMT_SPHERE_COVERING_STATEMENT = new_definition
 `SMT_SPHERE_COVERING_STATEMENT <=>
    !f:real^3->real^3.
        smooth_near (sphere(vec 0,&1)) f /\
        (!x. x IN sphere(vec 0,&1) ==> f x IN sphere(vec 0,&1)) /\
        (!x h. x IN sphere(vec 0,&1) /\ orthogonal x h /\
               frechet_derivative f (at x) h = vec 0 ==> h = vec 0)
        ==> ?g. sphere_diffeo f g`;;

(* S7. Pole normalization: f is isotopic to Q o f1 with Q orthogonal and f1  *)
(* = I near basis 3.                                                         *)

let SMT_SPHERE_POLE_STATEMENT = new_definition
 `SMT_SPHERE_POLE_STATEMENT <=>
    !f g:real^3->real^3.
        sphere_diffeo f g
        ==> ?J J' Q f1 g1 e.
              sphere_isotopy J J' /\ orthogonal_transformation Q /\
              sphere_diffeo f1 g1 /\ &0 < e /\
              (!t x. t <= &0 /\ x IN sphere(vec 0,&1) ==> J t x = f x) /\
              (!t x. &1 <= t /\ x IN sphere(vec 0,&1) ==> J t x = Q(f1 x)) /\
              (!x. x IN sphere(vec 0,&1) /\ norm(x - basis 3) < e ==> f1 x = x)`;;

(* S3b (i). A bounded forward half-orbit is periodic or returns to a         *)
(* straight transversal segment (first return, injective arc).               *)

let SMT_TRANSVERSE_RETURN_STATEMENT = new_definition
 `SMT_TRANSVERSE_RETURN_STATEMENT <=>
    !v:real^2->real^2 x.
        smooth_map_on (:real^2) v /\ (!y. ~(v y = vec 0)) /\
        (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        bounded (IMAGE (\t. vf_rflow v t x) {t | &0 <= t})
        ==> (?t0 T. &0 < T /\ vf_rflow v (t0 + T) x = vf_rflow v t0 x) \/
            (?t0 T. &0 <= t0 /\ &0 < T /\
                    ~(vf_rflow v (t0 + T) x = vf_rflow v t0 x) /\
                    transversal_on v (vf_rflow v t0 x) (vf_rflow v (t0 + T) x) /\
                    (!s t. s IN real_interval[&0,T] /\ t IN real_interval[&0,T] /\
                           vf_rflow v (t0 + s) x = vf_rflow v (t0 + t) x ==> s = t) /\
                    (!t. &0 < t /\ t < T
                         ==> ~(vf_rflow v (t0 + t) x IN
                               segment[vf_rflow v t0 x,vf_rflow v (t0 + T) x])))`;;

(* S3b (ii). Orbit arc and segment (or a periodic orbit) bound an open U     *)
(* whose closure is a closed disc, forward or backward invariant.            *)

let SMT_RETURN_DISK_STATEMENT = new_definition
 `SMT_RETURN_DISK_STATEMENT <=>
    !v:real^2->real^2 a T.
        smooth_map_on (:real^2) v /\ (!y. ~(v y = vec 0)) /\
        (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\ &0 < T /\
        (!s t. s IN real_interval[&0,T] /\ t IN real_interval[&0,T] /\
               vf_rflow v s a = vf_rflow v t a ==> s = t \/ {s,t} = {&0,T}) /\
        (~(vf_rflow v T a = a)
         ==> transversal_on v a (vf_rflow v T a) /\
             (!t. &0 < t /\ t < T ==> ~(vf_rflow v t a IN segment[a,vf_rflow v T a])))
        ==> ?U. open U /\ connected U /\ bounded U /\ ~(U = {}) /\
                frontier U = IMAGE (\t. vf_rflow v t a) (real_interval[&0,T]) UNION
                             segment[a,vf_rflow v T a] /\
                closure U homeomorphic cball(vec 0:real^2,&1) /\
                ((!t x. &0 <= t /\ x IN closure U ==> vf_rflow v t x IN closure U) \/
                 (!t x. t <= &0 /\ x IN closure U ==> vf_rflow v t x IN closure U))`;;

(* S3b (iii). A forward-invariant compact set homeomorphic to a closed ball  *)
(* contains a zero of the field.                                             *)

let SMT_INVARIANT_DISK_ZERO_STATEMENT = new_definition
 `SMT_INVARIANT_DISK_ZERO_STATEMENT (n:N->bool) <=>
    !v:real^N->real^N D.
        smooth_map_on (:real^N) v /\
        (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        D homeomorphic cball(vec 0:real^N,&1) /\
        (!t x. &0 <= t /\ x IN D ==> vf_rflow v t x IN D)
        ==> ?x. x IN D /\ v x = vec 0`;;

(* S8. Compactly supported planar isotopies transported to S^2 by stereo2_n  *)
(* (projection from the north pole basis 3) are sphere isotopies fixing the  *)
(* pole.                                                                     *)

let SMT_STEREO_TRANSPORT_STATEMENT = new_definition
 `SMT_STEREO_TRANSPORT_STATEMENT <=>
    !H K:real->real^2->real^2 R.
        diffeo_isotopy H K /\ (!t x. R <= norm x ==> H t x = x)
        ==> ?J J'. sphere_isotopy J J' /\
                   (!t x. x IN sphere(vec 0,&1) /\ ~(x = basis 3)
                          ==> J t x = stereo2_n_inv (H t (stereo2_n x))) /\
                   (!t. J t (basis 3) = basis 3)`;;

(* ------------------------------------------------------------------------- *)
(* Statement constants at the manifold level.                                *)
(* ------------------------------------------------------------------------- *)

(* M1. Re-capping: complements of closed unit balls of two ball charts       *)
(* diffeomorphic by a map that is radial on a collar give diffeomorphic      *)
(* manifolds (by a map equal to F away from the ball).                       *)

let SMT_GLUE_BALL_STATEMENT = new_definition
 `SMT_GLUE_BALL_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX topY atlasY b c F G f g.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        mfd_ball_chart topX atlasX b /\ mfd_ball_chart topY atlasY c /\
        sphere_diffeo f g /\
        mfd_diffeo topX atlasX (topspace topX DIFF IMAGE b (cball(vec 0,&1)))
                   topY atlasY (topspace topY DIFF IMAGE c (cball(vec 0,&1))) F G /\
        (?r. &1 < r /\ !x. x IN annulus (&1) r ==> F(b x) = c(radial_ext f x))
        ==> ?H K. mfd_diffeo topX atlasX (topspace topX)
                             topY atlasY (topspace topY) H K /\
                  (!p. p IN topspace topX DIFF IMAGE b (ball(vec 0,&2))
                       ==> H p = F p)`;;

(* M2. Twisted spheres: two closed balls with disjoint open cores glued by a *)
(* radial collar map form S^3.                                               *)

let SMT_TWISTED_SPHERE_STATEMENT = new_definition
 `SMT_TWISTED_SPHERE_STATEMENT (u:A->bool) <=>
    !top atlas b1 b2 f g.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_ball_chart top atlas b1 /\ mfd_ball_chart top atlas b2 /\
        sphere_diffeo f g /\
        topspace top = IMAGE b1 (cball(vec 0,&1)) UNION IMAGE b2 (cball(vec 0,&1)) /\
        DISJOINT (IMAGE b1 (ball(vec 0,&1))) (IMAGE b2 (ball(vec 0,&1))) /\
        (?r. &1 < r /\
             !x. x IN annulus (&1) r
                 ==> b1 x = b2(inv(norm x) % f(inv(norm x) % x)))
        ==> mfd_diffeomorphic top atlas
              (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas`;;

(* M3. Weak disc theorem: two ball charts of a connected manifold agree on   *)
(* cball(0,3/2) after a compactly supported diffeomorphism and an orthogonal *)
(* map of the domain.                                                        *)

let SMT_DISC_STATEMENT = new_definition
 `SMT_DISC_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas b b'.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        connected_space top /\
        mfd_ball_chart top atlas b /\ mfd_ball_chart top atlas b'
        ==> ?Phi Psi Q K.
                mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                           Phi Psi /\
                orthogonal_transformation Q /\
                compact_in top K /\
                (!p. p IN topspace top DIFF K ==> Phi p = p) /\
                (!x. norm x <= &3 / &2 ==> Phi(b x) = b'(Q x))`;;

(* M3'. Several disjoint balls at once (dimension at least 2).               *)

let SMT_DISC_MULTI_STATEMENT = new_definition
 `SMT_DISC_MULTI_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas I b b'.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        connected_space top /\ 2 <= dimindex(:N) /\ FINITE (I:num->bool) /\
        (!i. i IN I
             ==> mfd_ball_chart top atlas (b i) /\ mfd_ball_chart top atlas (b' i)) /\
        (!i j. i IN I /\ j IN I /\ ~(i = j)
               ==> DISJOINT (IMAGE (b i) (cball(vec 0,&3 / &2)))
                            (IMAGE (b j) (cball(vec 0,&3 / &2))) /\
                   DISJOINT (IMAGE (b' i) (cball(vec 0,&3 / &2)))
                            (IMAGE (b' j) (cball(vec 0,&3 / &2))))
        ==> ?Phi Psi Q K.
                mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                           Phi Psi /\
                compact_in top K /\
                (!p. p IN topspace top DIFF K ==> Phi p = p) /\
                (!i. i IN I ==> orthogonal_transformation (Q i)) /\
                (!i x. i IN I /\ norm x <= &1 ==> Phi(b i x) = b' i (Q i x))`;;

(* M4. The complement of the open core of any ball chart of S^3 is a closed  *)
(* ball with an inversion-type collar match.                                 *)

let SMT_S3_BALL_COMPLEMENT_STATEMENT = new_definition
 `SMT_S3_BALL_COMPLEMENT_STATEMENT <=>
    !b:real^3->real^4.
        mfd_ball_chart (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas b
        ==> ?c Q. mfd_ball_chart (subtopology euclidean (sphere(vec 0,&1)))
                                 sphere3_atlas c /\
                  orthogonal_transformation Q /\
                  sphere(vec 0,&1) =
                    IMAGE b (cball(vec 0,&1)) UNION IMAGE c (cball(vec 0,&1)) /\
                  DISJOINT (IMAGE b (ball(vec 0,&1))) (IMAGE c (ball(vec 0,&1))) /\
                  (!x. x IN annulus (&1) (&3 / &2)
                       ==> b x = c(inv(norm x pow 2) % Q x))`;;

(* M5. Sphere sums, unit law: if the capped inner side Z is S^3, then X is   *)
(* diffeomorphic to the capped outer side Y.                                 *)

let SMT_SPHERE_SUM_STATEMENT = new_definition
 `SMT_SPHERE_SUM_STATEMENT (u:A->bool) (v:B->bool) (w:C->bool) <=>
    !topX atlasX e X1 X2 topY atlasY cY FY GY topZ atlasZ cZ FZ GZ.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        hausdorff_space topZ /\
        smooth_manifold_atlas topZ (atlasZ:((C->bool)#(C->real^3))->bool) /\
        mfd_neck_chart topX atlasX e /\
        open_in topX X1 /\ open_in topX X2 /\ DISJOINT X1 X2 /\
        DISJOINT X1 (IMAGE e (sphere(vec 0,&1))) /\
        DISJOINT X2 (IMAGE e (sphere(vec 0,&1))) /\
        topspace topX = X1 UNION X2 UNION IMAGE e (sphere(vec 0,&1)) /\
        IMAGE e (annulus (&1) (&2)) SUBSET X1 /\
        IMAGE e (annulus (&1 / &2) (&1)) SUBSET X2 /\
        mfd_ball_chart topY atlasY cY /\
        mfd_diffeo topX atlasX X1
                   topY atlasY (topspace topY DIFF IMAGE cY (cball(vec 0,&1)))
                   FY GY /\
        (!x. x IN annulus (&1) (&2) ==> FY(e x) = cY x) /\
        mfd_ball_chart topZ atlasZ cZ /\
        mfd_diffeo topX atlasX X2
                   topZ atlasZ (topspace topZ DIFF IMAGE cZ (cball(vec 0,&1)))
                   FZ GZ /\
        (!x. x IN annulus (&1 / &2) (&1) ==> FZ(e x) = cZ(inv(norm x pow 2) % x)) /\
        mfd_diffeomorphic topZ atlasZ
          (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
        ==> mfd_diffeomorphic topX atlasX topY atlasY`;;

(* M6. Product structure from a function without critical points, starting   *)
(* at a neck sphere.                                                         *)

let SMT_PRODUCT_STATEMENT = new_definition
 `SMT_PRODUCT_STATEMENT (u:A->bool) <=>
    !top atlas W (f:A->real) e a b.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        mfd_regular_on atlas W f /\
        a < b /\ compact_in top {x | x IN W /\ a <= f x /\ f x <= b} /\
        mfd_neck_chart top atlas e /\ IMAGE e (annulus (&1 / &2) (&2)) SUBSET W /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e x) = a + log(norm x)) /\
        {x | x IN W /\ f x = a} = IMAGE e (sphere(vec 0,&1))
        ==> ?E eps. &0 < eps /\
                    mfd_param top atlas (annulus (&2 / &3) (exp(b - a + eps))) E /\
                    (!x. x IN annulus (&2 / &3) (&1) ==> E x = e x) /\
                    (!x. x IN annulus (&2 / &3) (exp(b - a + eps))
                         ==> f(E x) = a + log(norm x)) /\
                    {x | x IN W /\ a <= f x /\ f x <= b} =
                    IMAGE E {x | &1 <= norm x /\ norm x <= exp(b - a)}`;;

(* M6b. Two-ended product structure between two neck spheres.                *)

let SMT_PRODUCT2_STATEMENT = new_definition
 `SMT_PRODUCT2_STATEMENT (u:A->bool) <=>
    !top atlas W (f:A->real) e0 e1 a b.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        mfd_regular_on atlas W f /\
        a < b /\ compact_in top {x | x IN W /\ a <= f x /\ f x <= b} /\
        mfd_neck_chart top atlas e0 /\ mfd_neck_chart top atlas e1 /\
        IMAGE e0 (annulus (&1 / &2) (&2)) SUBSET W /\
        IMAGE e1 (annulus (&1 / &2) (&2)) SUBSET W /\
        DISJOINT (IMAGE e0 (annulus (&1 / &2) (&2)))
                 (IMAGE e1 (annulus (&1 / &2) (&2))) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e0 x) = a + log(norm x)) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e1 x) = b + log(norm x)) /\
        {x | x IN W /\ f x = a} = IMAGE e0 (sphere(vec 0,&1)) /\
        {x | x IN W /\ f x = b} = IMAGE e1 (sphere(vec 0,&1))
        ==> ?E g g'.
              mfd_param top atlas
                (annulus (&2 / &3) (&3 / &2 * exp(b - a))) E /\
              sphere_diffeo g g' /\
              (!x. x IN annulus (&2 / &3) (&3 / &2) ==> E x = e0 x) /\
              (!x. x IN annulus (&2 / &3 * exp(b - a)) (&3 / &2 * exp(b - a))
                   ==> E x = e1(radial_ext g (exp(a - b) % x))) /\
              (!x. x IN annulus (&2 / &3) (&3 / &2 * exp(b - a))
                   ==> f(E x) = a + log(norm x)) /\
              {x | x IN W /\ a <= f x /\ f x <= b} =
              IMAGE E {x | &1 <= norm x /\ norm x <= exp(b - a)}`;;

(* M6'. Sublevel sets of a function whose only critical point is a minimum   *)
(* in Morse normal form are balls.                                           *)

let SMT_EXHAUSTION_BALL_STATEMENT = new_definition
 `SMT_EXHAUSTION_BALL_STATEMENT (u:A->bool) <=>
    !top atlas W (f:A->real) b c.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET W /\
        (!x. norm x < &2 ==> f(b x) = f(b(vec 0)) + norm x pow 2) /\
        mfd_regular_on atlas (W DELETE b(vec 0)) f /\
        f(b(vec 0)) + &1 < c /\
        compact_in top {x | x IN W /\ f x <= c}
        ==> ?B. mfd_ball_chart top atlas B /\
                IMAGE B (cball(vec 0,&1)) = {x | x IN W /\ f x <= c} /\
                (!x. norm x < &1 / &2 ==> B x = b x)`;;

(* M7. Simply connected manifolds are orientable.                            *)

let SMT_ORIENTABLE_STATEMENT = new_definition
 `SMT_ORIENTABLE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        simply_connected_space top
        ==> mfd_orientable top atlas`;;

(* M9. The standard pair of ball charts of S^3 (inverse stereographic        *)
(* projections, centred at the south and the north pole) and their inversion *)
(* relation.                                                                 *)

let SMT_S3_STANDARD_BALLS_STATEMENT = new_definition
 `SMT_S3_STANDARD_BALLS_STATEMENT <=>
    mfd_ball_chart (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
                   stereo3_n_inv /\
    mfd_ball_chart (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
                   stereo3_s_inv /\
    sphere(vec 0:real^4,&1) =
      IMAGE stereo3_n_inv (cball(vec 0,&1)) UNION
      IMAGE stereo3_s_inv (cball(vec 0,&1)) /\
    DISJOINT (IMAGE stereo3_n_inv (ball(vec 0,&1)))
             (IMAGE stereo3_s_inv (ball(vec 0,&1))) /\
    (!x. ~(x = vec 0)
         ==> stereo3_n_inv x = stereo3_s_inv(inv(norm x pow 2) % x))`;;

(* M10. A manifold diffeomorphic to the standard S^3 satisfies the           *)
(* conclusion of POINCARE_SMOOTH_STATEMENT.                                  *)

let SMT_POINCARE_CONVERSION_STATEMENT = new_definition
 `SMT_POINCARE_CONVERSION_STATEMENT (u:A->bool) <=>
    !top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_diffeomorphic top atlas
          (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
        ==> ?f:A->real^4.
              smooth_immersion_into atlas f /\
              homeomorphic_map (top,subtopology euclidean (sphere(vec 0,&1))) f`;;

(* M11. A closed simply connected X cut along finitely many disjoint neck    *)
(* spheres and capped gives Z; if every component of Z is S^3, then X is     *)
(* S^3.                                                                      *)

let SMT_SPHERE_SYSTEM_STATEMENT = new_definition
 `SMT_SPHERE_SYSTEM_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX topZ atlasZ I e cp cm F G.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\ ~(topspace topX = {}) /\
        simply_connected_space topX /\
        hausdorff_space topZ /\
        smooth_manifold_atlas topZ (atlasZ:((B->bool)#(B->real^3))->bool) /\
        FINITE (I:num->bool) /\
        (!i. i IN I
             ==> mfd_neck_chart topX atlasX (e i) /\
                 mfd_ball_chart topZ atlasZ (cp i) /\
                 mfd_ball_chart topZ atlasZ (cm i)) /\
        (!i j. i IN I /\ j IN I /\ ~(i = j)
               ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                            (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
        (!i j. i IN I /\ j IN I
               ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                            (IMAGE (cm j) (ball(vec 0,&2))) /\
                   (~(i = j)
                    ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                                 (IMAGE (cp j) (ball(vec 0,&2))) /\
                        DISJOINT (IMAGE (cm i) (ball(vec 0,&2)))
                                 (IMAGE (cm j) (ball(vec 0,&2))))) /\
        mfd_diffeo topX atlasX
          (topspace topX DIFF
           UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN I})
          topZ atlasZ
          (topspace topZ DIFF
           UNIONS {IMAGE (cp i) (cball(vec 0,&1)) UNION
                   IMAGE (cm i) (cball(vec 0,&1)) | i IN I})
          F G /\
        (!i x. i IN I /\ x IN annulus (&1) (&2) ==> F(e i x) = cp i x) /\
        (!i x. i IN I /\ x IN annulus (&1 / &2) (&1)
               ==> F(e i x) = cm i (inv(norm x pow 2) % x)) /\
        (!C. C IN connected_components_of topZ
             ==> mfd_diffeomorphic (subtopology topZ C) (restrict_atlas atlasZ C)
                   (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas)
        ==> mfd_diffeomorphic topX atlasX
              (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas`;;


(* ------------------------------------------------------------------------- *)
(* Sanity theorems for the definitions and statements.                       *)
(* ------------------------------------------------------------------------- *)

(* The identity is a diffeomorphism of the sphere, with radial extension the *)
(* identity, so the conclusion of SMT_SMALE_RADIAL_STATEMENT is satisfiable  *)
(* for f = I (a teeth test of the radial clause).                            *)

let SMT_SPHERE_DIFFEO_ID = prove
 (`sphere_diffeo (\x:real^N. x) (\x. x)`,
  REWRITE_TAC[sphere_diffeo; smooth_near] THEN
  MESON_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_ID]);;

let SMT_RADIAL_EXT_ID = prove
 (`radial_ext (\x:real^N. x) = (\x. x)`,
  REWRITE_TAC[FUN_EQ_THM; radial_ext] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_SIMP_TAC[NORM_0; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_MUL_ASSOC;
               REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]);;

let SMT_SMALE_CONCLUSION_ID = prove
 (`?h k. diffeomorphism_on (:real^3) (:real^3) h k /\
         (!x. norm(h x) = norm x) /\
         (!x. &1 / &2 <= norm x /\ norm x <= &2
              ==> h x = radial_ext (\x. x) x)`,
  MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
  SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_UNIV; SMT_RADIAL_EXT_ID]);;

(* The conversion statement M10 plus the claim that every closed simply      *)
(* connected smooth 3-manifold is diffeomorphic to the standard S^3 gives    *)
(* POINCARE_SMOOTH_STATEMENT.                                                *)

let SMT_HEADLINE_FROM_CONVERSION = prove
 (`!u:A->bool.
        SMT_POINCARE_CONVERSION_STATEMENT u /\
        (!top atlas.
            hausdorff_space top /\
            smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
            compact_space top /\ ~(topspace top = {}) /\
            simply_connected_space top
            ==> mfd_diffeomorphic top atlas
                  (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas)
        ==> POINCARE_SMOOTH_STATEMENT u`,
  REWRITE_TAC[SMT_POINCARE_CONVERSION_STATEMENT; POINCARE_SMOOTH_STATEMENT] THEN
  MESON_TAC[]);;

(* The standard pair of ball charts of S^3 is related by the inversion       *)
(* x / |x|^2 (the last clause of SMT_S3_STANDARD_BALLS_STATEMENT).           *)

let SMT_STEREO3_INVERSION = prove
 (`!x:real^3. ~(x = vec 0)
              ==> stereo3_n_inv x = stereo3_s_inv(inv(norm x pow 2) % x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` STEX_STEREO3_TRANSITION) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> can (find_term ((=) `stereo3_s`)) (lhand(concl th)))) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC STEX_STEREO3_S_LEFT THEN
  ASM_REWRITE_TAC[]);;

(* Teeth test for M2: the standard pair satisfies the collar hypothesis of   *)
(* SMT_TWISTED_SPHERE_STATEMENT with f = I.                                  *)

let SMT_TWISTED_STANDARD_TRANSITION = prove
 (`!x:real^3. x IN annulus (&1) (&2)
              ==> stereo3_n_inv x =
                  stereo3_s_inv(inv(norm x) % (\x. x) (inv(norm x) % x))`,
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN
  MATCH_MP_TAC SMT_STEREO3_INVERSION THEN
  REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC);;

