(* ========================================================================= *)
(* Unit pc_cm_defs: the Colding-Minicozzi core vocabulary of Part 4: the     *)
(* embedded target cm_target S G d and cm_emb, planar and S^2 map classes,   *)
(* energies, areas, traces, harmonic maps and spheres, sweepouts and their   *)
(* homotopies, balls in S^2 and the almost-harmonic property.  Definitions   *)
(* only, in the sections C0-C4 below; used by pc_cm_target.                  *)
(* ========================================================================= *)

needs "src/pc_p4_defs.ml";;
needs "src/pc_wan_defs.ml";;
needs "src/pc_wan_p4defs.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_mfd_embdefs.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* C0. The embedded target.                                                  *)
(* ------------------------------------------------------------------------- *)

let cm_tube = new_definition
 `cm_tube (S:real^K->bool) (d:real) = {z:real^K | ?p. p IN S /\ dist(z,p) < d}`;;

let cm_target = new_definition
 `cm_target (S:real^K->bool) (G:real^K->real^K^K) (d:real) <=>
    compact S /\ ~(S = {}) /\ &0 < d /\
    (!z. z IN cm_tube S d ==> closest_point S z IN S) /\
    smooth_map_on (cm_tube S d) (closest_point S) /\
    (!z. z IN S
         ==> transp(jacobian (closest_point S) (at z)) = jacobian (closest_point S) (at z) /\
             jacobian (closest_point S) (at z) ** jacobian (closest_point S) (at z) =
             jacobian (closest_point S) (at z)) /\
    (?C. &0 <= C /\
         (!x y. x IN S /\ y IN S
                ==> norm((mat 1 - jacobian (closest_point S) (at x)) ** (y - x))
                    <= C * norm(y - x) pow 2) /\
         (!z. z IN cm_tube S d
              ==> onorm(\v. jacobian (closest_point S) (at z) ** v -
                            jacobian (closest_point S) (at (closest_point S z)) ** v)
                  <= C * dist(z,closest_point S z))) /\
    smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
    (!z. transp(G z) = G z) /\
    (?lam Lam. &0 < lam /\ lam <= Lam /\
               !z v. lam * norm v pow 2 <= v dot (G z ** v) /\
                     v dot (G z ** v) <= Lam * norm v pow 2) /\
    (!z u v. z IN S
             ==> (jacobian (closest_point S) (at z) ** u) dot
                 (G z ** ((mat 1 - jacobian (closest_point S) (at z)) ** v)) = &0)`;;

(* The embedded closed Riemannian manifold: MFD_EMBEDDING_EXISTS,            *)
(* MFD_TUBULAR_NEIGHBOURHOOD, MFD_EMBED_NORMAL_QUADRATIC and E7              *)
(* (MFD_EMBED_AMBIENT_METRIC) of the embedding layer give data with this     *)
(* property.                                                                 *)

let cm_emb = new_definition
 `cm_emb (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
         (f:A->real^K) (G:real^K->real^K^K) (d:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
    ~(topspace top = {}) /\ riemannian_metric atlas g /\ mfd_embedding (top,atlas) f /\
    cm_target (IMAGE f (topspace top)) G d /\
    (!x. x IN topspace top
         ==> jacobian (closest_point (IMAGE f (topspace top))) (at (f x)) =
             mfd_tproj atlas f x) /\
    (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
           ==> metric_local atlas c g y =
               transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
               G(f(chart_inv c y)) **
               matrix(frechet_derivative (f o chart_inv c) (at y)))`;;

(* ------------------------------------------------------------------------- *)
(* C1. Maps from planar domains into S: W^{1,2}(s,S) (values in S a.e.),    *)
(* C^0 /\ W^{1,2}(closure s,S), the G-energy, energy minimizers (CM (1.13)) *)
(* and smooth G-harmonic maps (critical for projected variations).          *)
(* ------------------------------------------------------------------------- *)

let cm_wmap = new_definition
 `cm_wmap (S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) <=>
    wan_w12 s u /\ ?Z. negligible Z /\ !x. x IN s DIFF Z ==> u x IN S`;;

let cm_cmap = new_definition
 `cm_cmap (S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) <=>
    wan_w12 s u /\ u continuous_on closure s /\ !x. x IN closure s ==> u x IN S`;;

let cm_gen = new_definition
 `cm_gen (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) = wan_gdir s G u / &2`;;

let cm_minimizer = new_definition
 `cm_minimizer (S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) <=>
    cm_wmap S s u /\
    !w. cm_wmap S s w /\ wan_w120 s (\x. w x - u x) ==> cm_gen G s u <= cm_gen G s w`;;

let cm_harmonic = new_definition
 `cm_harmonic (S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) <=>
    smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
    !(phi:real^2->real^K) s'.
       open s' /\ bounded s' /\ closure s' SUBSET s /\ wan_vtest s' phi
       ==> ((\e. cm_gen G s' (\x. closest_point S (u x + e % phi x))) has_real_derivative &0)
           (atreal (&0))`;;

(* ------------------------------------------------------------------------- *)
(* C2. Maps from S^2 into S (radial extension to wan_shell, V4 of            *)
(* pc_wan_defs): the class C^0 /\ W^{1,2}(S^2,S), G-energy, area and the     *)
(* G-tangential trace of a symmetric ambient quadratic form Q, computed from *)
(* weak partials (for C^1 maps these are p4_s2_energy, p4_s2_area and        *)
(* p4_s2_trint of the chart picture, by E8 of the embedding layer and        *)
(* CM_P4_BRIDGE of pc_cm_target).                                            *)
(* ------------------------------------------------------------------------- *)

let cm_smap = new_definition
 `cm_smap (S:real^K->bool) (u:real^3->real^K) <=>
    u continuous_on sphere(vec 0,&1) /\ wan_s2_w12 u /\
    !y. y IN sphere(vec 0,&1) ==> u y IN S`;;

let cm_sen = new_definition
 `cm_sen (G:real^K->real^K^K) (u:real^3->real^K) = wan_gdir wan_shell G (wan_rext u) / &3`;;

let cm_wgram = new_definition
 `cm_wgram (s:real^3->bool) (G:real^K->real^K^K) (v:real^3->real^K) (z:real^3) =
    (lambda i j. wan_wd s i v z dot (G(v z) ** wan_wd s j v z)):real^3^3`;;

let cm_sarea = new_definition
 `cm_sarea (G:real^K->real^K^K) (u:real^3->real^K) =
    &2 / &3 * drop(integral wan_shell
                    (\z. lift(sqrt(p4_e2(cm_wgram wan_shell G (wan_rext u) z)))))`;;

let cm_strace = new_definition
 `cm_strace (G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^3->real^K) =
    &2 / &3 *
    drop(integral wan_shell
          (\z. lift(if p4_e2(cm_wgram wan_shell G (wan_rext u) z) = &0 then &0
                    else p4_e2_pol (cm_wgram wan_shell G (wan_rext u) z)
                                   (cm_wgram wan_shell Q (wan_rext u) z) /
                         sqrt(p4_e2(cm_wgram wan_shell G (wan_rext u) z)))))`;;

(* Harmonic spheres: smooth, nonconstant, critical for the G-energy under   *)
(* projected smooth variations.                                              *)

let cm_sharmonic = new_definition
 `cm_sharmonic (S:real^K->bool) (G:real^K->real^K^K) (u:real^3->real^K) <=>
    smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
    (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
    ~(?c. !y. y IN sphere(vec 0,&1) ==> u y = c) /\
    !phi:real^3->real^K.
       smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
       ==> ((\e. cm_sen G (\y. closest_point S (u y + e % phi y))) has_real_derivative &0)
           (atreal (&0))`;;

(* ------------------------------------------------------------------------- *)
(* C3. CM's sweepouts Omega (continuous into C^0 /\ W^{1,2}, point maps at  *)
(* t = 0, 1) and C^0 homotopies of sweepouts (end slices constant at every  *)
(* stage; this is what essentiality, an H_3 property, needs).               *)
(* ------------------------------------------------------------------------- *)

let cm_sweep = new_definition
 `cm_sweep (S:real^K->bool) (sigma:real^3->real->real^K) <=>
    continuous_map
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])),
       euclidean)
      (\(y,t). sigma y t) /\
    (!t. t IN real_interval[&0,&1] ==> cm_smap S (\y. sigma y t)) /\
    (!t. t IN real_interval[&0,&1]
         ==> ((\s. wan_dir wan_shell (\z. wan_rext (\y. sigma y s) z -
                                          wan_rext (\y. sigma y t) z))
              ---> &0) (atreal t within real_interval[&0,&1])) /\
    (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
            ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1))`;;

let cm_shomotopic = new_definition
 `cm_shomotopic (S:real^K->bool) (sigma1:real^3->real->real^K) (sigma2:real^3->real->real^K) <=>
    ?H:real->real^3->real->real^K.
       continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
            (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                           (subtopology euclideanreal (real_interval[&0,&1]))),
          euclidean)
         (\(s,(y,t)). H s y t) /\
       (!s y t. s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\
                t IN real_interval[&0,&1] ==> H s y t IN S) /\
       (!s y y'. s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                 ==> H s y (&0) = H s y' (&0) /\ H s y (&1) = H s y' (&1)) /\
       (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
              ==> H (&0) y t = sigma1 y t /\ H (&1) y t = sigma2 y t)`;;

(* ------------------------------------------------------------------------- *)
(* C4. Balls in S^2 (CM Sec 2: a subset with a stereographic projection     *)
(* onto a planar ball): images of cball(c,r) under y |-> Q (stereo2_n_inv y)*)
(* for a rotation Q; rho B uses cball(c, rho r).  The almost-harmonic       *)
(* property (B_Psi) of CM Thm 2.1 and (B) of Prop 2.2: on every finite      *)
(* family of disjoint balls of small G-Dirichlet integral, every energy     *)
(* minimizer on the (1/8)-balls with the boundary values of u is eta-close  *)
(* in Dirichlet integral (energy is conformally invariant, so all of this   *)
(* is computed on the planar balls).                                         *)
(* ------------------------------------------------------------------------- *)

let cm_capmap = new_definition
 `cm_capmap (Q:real^3^3) (y:real^2) = Q ** stereo2_n_inv y`;;

let cm_almost_harmonic = new_definition
 `cm_almost_harmonic (S:real^K->bool) (G:real^K->real^K^K) (e0:real) (eta:real)
                     (u:real^3->real^K) <=>
    !n (Q:num->real^3^3) (c:num->real^2) (r:num->real) (v:num->real^2->real^K).
       (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k) /\ det(Q k) = &1 /\ &0 < r k) /\
       (!k l. 1 <= k /\ k < l /\ l <= n
              ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                           (IMAGE (cm_capmap (Q l)) (cball(c l,r l)))) /\
       sum(1..n) (\k. wan_gdir (ball(c k,r k)) G (\y. u(cm_capmap (Q k) y))) < e0 /\
       (!k. 1 <= k /\ k <= n
            ==> cm_minimizer S G (ball(c k,r k / &8)) (v k) /\
                wan_w120 (ball(c k,r k / &8)) (\y. v k y - u(cm_capmap (Q k) y)))
       ==> sum(1..n) (\k. wan_dir (ball(c k,r k / &8))
                                  (\y. u(cm_capmap (Q k) y) - v k y)) <= eta`;;


