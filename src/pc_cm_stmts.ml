(* ========================================================================= *)
(* Unit pc_cm_stmts: the CM-core interface of Part 4.  The ten unit          *)
(* statement constants (CM_..._STATEMENT) of the Colding-Minicozzi 2008 core *)
(* (harmonic-map regularity, convexity, replacement, tightening,             *)
(* compactness), and the seven chain statements (CM_CHAIN_..._STATEMENT):    *)
(* each chain unit proves exactly one of them, an implication from the       *)
(* statement constants of pc_wan_defs and pc_wan_p4defs and the CM           *)
(* statements of other units.  Statements only.  The vocabulary (cm_target,  *)
(* cm_harmonic, ...) is in pc_cm_defs.                                       *)
(* ========================================================================= *)

needs "src/pc_cm_defs.ml";;

prioritize_real();;
type_invention_error := true;;

let CM_EPS_REG_STATEMENT = new_definition
 `CM_EPS_REG_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e C. &0 < e /\ (!k. &0 < C k) /\
                 !(a:real^2) r (u:real^2->real^K) l x.
                    &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
                    wan_gdir (ball(a,r)) G u <= e /\
                    ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
                    ==> r pow (LENGTH l) * norm(iterated_partial l u x)
                        <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)`;;

let CM_MINIMIZER_SMOOTH_STATEMENT = new_definition
 `CM_MINIMIZER_SMOOTH_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(a:real^2) r (u:real^2->real^K).
              &0 < r /\ cm_minimizer S G (ball(a,r)) u
              ==> ?w. cm_harmonic S G (ball(a,r)) w /\
                      negligible {x | x IN ball(a,r) /\ ~(u x = w x)}`;;

let CM_REMOVABLE_STATEMENT = new_definition
 `CM_REMOVABLE_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(a:real^2) r (u:real^2->real^K).
              &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
              wan_w12 (ball(a,r) DELETE a) u
              ==> ?w. cm_harmonic S G (ball(a,r)) w /\
                      !x. x IN ball(a,r) DELETE a ==> w x = u x`;;

let CM_HOPF_STATEMENT = new_definition
 `CM_HOPF_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(u:real^3->real^K) y v w.
              cm_sharmonic S G u /\ y IN sphere(vec 0,&1) /\
              v dot y = &0 /\ w dot y = &0 /\ v dot w = &0 /\ norm v = norm w
              ==> (jacobian (wan_rext u) (at y) ** v) dot
                  (G(u y) ** (jacobian (wan_rext u) (at y) ** v)) =
                  (jacobian (wan_rext u) (at y) ** w) dot
                  (G(u y) ** (jacobian (wan_rext u) (at y) ** w)) /\
                  (jacobian (wan_rext u) (at y) ** v) dot
                  (G(u y) ** (jacobian (wan_rext u) (at y) ** w)) = &0`;;

let CM_SPHERE_GAP_STATEMENT = new_definition
 `CM_SPHERE_GAP_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e. &0 < e /\ !u:real^3->real^K. cm_sharmonic S G u ==> e <= cm_sen G u`;;

let CM_CRITICAL_ISOLATED_STATEMENT = new_definition
 `CM_CRITICAL_ISOLATED_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(u:real^3->real^K) O.
              cm_sharmonic S G u /\ open_in (subtopology euclidean (sphere(vec 0,&1))) O /\
              ~(O = {})
              ==> ?y. y IN O /\ ~(jacobian (wan_rext u) (at y) = mat 0)`;;

let CM_CONVEXITY_STATEMENT = new_definition
 `CM_CONVEXITY_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e c. &0 < e /\ &0 < c /\
                 !(a:real^2) r (u:real^2->real^K) v.
                    &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
                    wan_gdir (ball(a,r)) G v <= e /\
                    cm_wmap S (ball(a,r)) u /\ wan_w120 (ball(a,r)) (\x. u x - v x)
                    ==> c * wan_dir (ball(a,r)) (\x. u x - v x)
                        <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v`;;

let CM_REPLACEMENT_STATEMENT = new_definition
 `CM_REPLACEMENT_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e C. &0 < e /\ &0 < C /\
             (!(a:real^2) r (u:real^2->real^K).
                 &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= e
                 ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                         wan_w120 (ball(a,r)) (\x. w x - u x) /\
                         cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                         (!x. x IN sphere(a,r) ==> w x = u x) /\
                         !w'. cm_minimizer S G (ball(a,r)) w' /\
                              wan_w120 (ball(a,r)) (\x. w' x - u x)
                              ==> negligible {x | x IN ball(a,r) /\ ~(w' x = w x)}) /\
             (!(a:real^2) r (u:num->real^2->real^K) u0 w w0.
                 &0 < r /\
                 (!n. cm_cmap S (ball(a,r)) (u n) /\ wan_gdir (ball(a,r)) G (u n) <= e /\
                      cm_minimizer S G (ball(a,r)) (w n) /\ cm_cmap S (ball(a,r)) (w n) /\
                      (!x. x IN sphere(a,r) ==> w n x = u n x)) /\
                 cm_cmap S (ball(a,r)) u0 /\ wan_gdir (ball(a,r)) G u0 <= e /\
                 cm_minimizer S G (ball(a,r)) w0 /\ cm_cmap S (ball(a,r)) w0 /\
                 (!x. x IN sphere(a,r) ==> w0 x = u0 x) /\
                 (!x. ((\n. u n x) --> u0 x) sequentially) /\
                 (!e'. &0 < e' ==> eventually (\n. !x. x IN cball(a,r) ==> norm(u n x - u0 x) < e')
                                              sequentially) /\
                 ((\n. wan_dir (ball(a,r)) (\x. u n x - u0 x)) ---> &0) sequentially
                 ==> (!e'. &0 < e' ==> eventually (\n. !x. x IN cball(a,r) ==> norm(w n x - w0 x) < e')
                                                  sequentially) /\
                     ((\n. wan_dir (ball(a,r)) (\x. w n x - w0 x)) ---> &0) sequentially) /\
             (!(a:real^2) r (u1:real^2->real^K) u2 w1 w2 E.
                 &0 < r /\
                 cm_cmap S (ball(a,r)) u1 /\ cm_cmap S (ball(a,r)) u2 /\
                 wan_gdir (ball(a,r)) G u1 <= E /\ wan_gdir (ball(a,r)) G u2 <= E /\ E <= e /\
                 cm_minimizer S G (ball(a,r)) w1 /\ wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\
                 cm_minimizer S G (ball(a,r)) w2 /\ wan_w120 (ball(a,r)) (\x. w2 x - u2 x)
                 ==> abs(cm_gen G (ball(a,r)) w1 - cm_gen G (ball(a,r)) w2)
                     <= C * sup {norm(u1 x - u2 x) | x IN cball(a,r)} * E +
                        C * sqrt(wan_dir (ball(a,r)) (\x. u1 x - u2 x)) * sqrt E)`;;

let CM_TIGHTEN_STATEMENT = new_definition
 `CM_TIGHTEN_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e0 Psi. &0 < e0 /\ Psi real_continuous_on {x | &0 <= x} /\ Psi(&0) = &0 /\
                    (!x. &0 <= x ==> &0 <= Psi x) /\
                    !(gamma0:real^3->real->real^K) W.
                       cm_sweep S gamma0 /\ &0 < W /\
                       (!t. t IN real_interval[&0,&1] ==> ~cm_sharmonic S G (\y. gamma0 y t))
                       ==> ?gamma. cm_sweep S gamma /\ cm_shomotopic S gamma0 gamma /\
                                   (!t. t IN real_interval[&0,&1]
                                        ==> cm_sen G (\y. gamma y t) <= cm_sen G (\y. gamma0 y t)) /\
                                   (!t. t IN real_interval[&0,&1] /\
                                        W / &2 <= cm_sen G (\y. gamma0 y t)
                                        ==> cm_almost_harmonic S G e0
                                              (Psi(cm_sen G (\y. gamma0 y t) -
                                                   cm_sen G (\y. gamma y t)))
                                              (\y. gamma y t))`;;

let CM_COMPACTNESS_STATEMENT = new_definition
 `CM_COMPACTNESS_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?eSU. &0 < eSU /\
             !e0 E0 (u:num->real^3->real^K) eta T.
                &0 < e0 /\ e0 < eSU /\ (eta ---> &0) sequentially /\ closed T /\
                (!k y. y IN sphere(vec 0,&1) ==> u k y IN T) /\
                (!k. cm_smap S (u k) /\ cm_sen G (u k) <= E0 /\
                     cm_sen G (u k) - inv(&k + &1) < cm_sarea G (u k) /\
                     cm_almost_harmonic S G e0 (eta k) (u k))
                ==> ?(r:num->num) m (v:num->real^3->real^K).
                       (!j k. j < k ==> r j < r k) /\
                       (!i. 1 <= i /\ i <= m ==> cm_sharmonic S G (v i)) /\
                       (!i y. 1 <= i /\ i <= m /\ y IN sphere(vec 0,&1) ==> v i y IN T) /\
                       ((\j. cm_sarea G (u (r j))) ---> sum(1..m) (\i. cm_sarea G (v i)))
                         sequentially /\
                       !Q:real^K->real^K^K.
                          smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
                          (!z. transp(Q z) = Q z)
                          ==> ((\j. cm_strace G Q (u (r j))) --->
                               sum(1..m) (\i. cm_strace G Q (v i))) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* The chain statements.  K is the ambient dimension (7 for 3-manifolds via  *)
(* MFD_EMBEDDING_EXISTS), 2 the planar domain, A the type of the manifold in *)
(* the Part 4 statements.  CM_D7_UNIFORMIZATION_STATEMENT is not a           *)
(* hypothesis of the width chain: it is proved in pc_an_beltrami (theorem    *)
(* CM_D7_UNIFORMIZATION).                                                    *)
(* ------------------------------------------------------------------------- *)

let CM_CHAIN_HM_REGULARITY_STATEMENT = new_definition
 `CM_CHAIN_HM_REGULARITY_STATEMENT (kk:K->bool) <=>
  WAN_W12_C1_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
    WAN_MUL_W12_STATEMENT (:2) (:K) /\
    WAN_POISSON_ENERGY_STATEMENT (:K) /\ WAN_CAMPANATO_STATEMENT (:2) (:K) /\
    WAN_POINCARE_BALL_STATEMENT (:2) (:K) /\ WAN_COURANT_LEBESGUE_STATEMENT (:K) /\
    WAN_CIRCLE_ACL_STATEMENT (:K) /\ WAN_POLAR_DIR_STATEMENT (:K) /\
    WAN_HARM_GRAD_OSC_STATEMENT (:2) /\ WAN_MAX_PRINCIPLE_DISC_STATEMENT /\
    WAN_DIRICHLET_DISC_STATEMENT (:K) /\ WAN_LOGPOT_C1A_QUANT_STATEMENT /\
    WAN_SCHAUDER_2D_STATEMENT /\ WAN_CAUCHY_HOLDER_STATEMENT /\ WAN_SUBMEAN_2D_STATEMENT /\
    WAN_WEYL_STATEMENT (:2) /\ WAN_REMOVABLE_POINT_STATEMENT (:2) (:K) /\
    WAN_S2_STEREO_STATEMENT (:K) /\ WAN_DIR_CONFORMAL_2D_STATEMENT (:K)
    ==> CM_EPS_REG_STATEMENT (:K) /\ CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\
        CM_REMOVABLE_STATEMENT (:K) /\ CM_HOPF_STATEMENT (:K) /\
        CM_SPHERE_GAP_STATEMENT (:K) /\ CM_CRITICAL_ISOLATED_STATEMENT (:K)`;;

let CM_CHAIN_HM_CONVEXITY_STATEMENT = new_definition
 `CM_CHAIN_HM_CONVEXITY_STATEMENT (kk:K->bool) <=>
  WAN_HARDY_BALL_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
    WAN_W12_C1_STATEMENT (:2) (:K) /\ WAN_W120_CONT_STATEMENT (:2) (:K) /\
    CM_EPS_REG_STATEMENT (:K)
    ==> CM_CONVEXITY_STATEMENT (:K)`;;

let CM_CHAIN_HM_DIRICHLET_STATEMENT = new_definition
 `CM_CHAIN_HM_DIRICHLET_STATEMENT (kk:K->bool) <=>
  WAN_RELLICH0_STATEMENT (:2) (:K) /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\
    WAN_WEAK_PARTIALS_CONV_STATEMENT (:2) (:K) /\ WAN_RADON_RIESZ_G_STATEMENT (:2) (:K) /\
    WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
    WAN_CHAIN_LIP_W12_STATEMENT (:2) (:K) (:K) /\ WAN_GLUE_W12_STATEMENT (:2) (:K) /\
    WAN_COURANT_LEBESGUE_STATEMENT (:K) /\ WAN_COURANT_LEBESGUE_BDRY_STATEMENT (:K) /\
    WAN_POISSON_ENERGY_STATEMENT (:K) /\ WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT (:K) /\
    CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K) /\
    CM_CONVEXITY_STATEMENT (:K)
    ==> CM_REPLACEMENT_STATEMENT (:K)`;;

let CM_CHAIN_CM_REPLACEMENT_STATEMENT = new_definition
 `CM_CHAIN_CM_REPLACEMENT_STATEMENT (kk:K->bool) <=>
  CM_REPLACEMENT_STATEMENT (:K) /\ CM_CONVEXITY_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K) /\
    WAN_WIRTINGER_VEC_STATEMENT (:K) /\ WAN_POLAR_DIR_STATEMENT (:K) /\
    WAN_CIRCLE_ACL_STATEMENT (:K) /\ WAN_GLUE_W12_STATEMENT (:2) (:K) /\
    WAN_MUL_W12_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
    WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_W12_DIFFEO_STATEMENT (:2) (:K) /\
    WAN_DIR_CONFORMAL_2D_STATEMENT (:K) /\ WAN_S2_STEREO_STATEMENT (:K)
    ==> CM_TIGHTEN_STATEMENT (:K)`;;

let CM_CHAIN_CM_COMPACTNESS_STATEMENT = new_definition
 `CM_CHAIN_CM_COMPACTNESS_STATEMENT (kk:K->bool) <=>
  CM_EPS_REG_STATEMENT (:K) /\ CM_REMOVABLE_STATEMENT (:K) /\ CM_HOPF_STATEMENT (:K) /\
    CM_SPHERE_GAP_STATEMENT (:K) /\ CM_REPLACEMENT_STATEMENT (:K) /\
    CM_CONVEXITY_STATEMENT (:K) /\
    WAN_RELLICH_LOC_STATEMENT (:2) (:K) /\ WAN_WEAK_PARTIALS_CONV_STATEMENT (:2) (:K) /\
    WAN_POINCARE0_STATEMENT (:2) (:K) /\ WAN_WIRTINGER_VEC_STATEMENT (:K) /\
    WAN_POLAR_DIR_STATEMENT (:K) /\ WAN_CIRCLE_ACL_STATEMENT (:K) /\
    WAN_REMOVABLE_POINT_STATEMENT (:2) (:K) /\ WAN_W12_DIFFEO_STATEMENT (:2) (:K) /\
    WAN_DIR_CONFORMAL_2D_STATEMENT (:K) /\ WAN_S2_STEREO_STATEMENT (:K)
    ==> CM_COMPACTNESS_STATEMENT (:K)`;;

let CM_CHAIN_CM_WIDTH_STATEMENT = new_definition
 `CM_CHAIN_CM_WIDTH_STATEMENT (aa:A->bool) <=>
  CM_TIGHTEN_STATEMENT (:7) /\ CM_COMPACTNESS_STATEMENT (:7) /\
    CM_REPLACEMENT_STATEMENT (:7) /\ CM_HOPF_STATEMENT (:7) /\
    CM_CRITICAL_ISOLATED_STATEMENT (:7) /\ CM_SPHERE_GAP_STATEMENT (:7) /\
    WAN_W12_C1_STATEMENT (:3) (:7) /\ WAN_CHAIN_W12_STATEMENT (:3) (:7) (:7) /\
    WAN_CHAIN_LIP_W12_STATEMENT (:2) (:7) (:7) /\
    WAN_S2_STEREO_STATEMENT (:7) /\ WAN_DIR_CONFORMAL_2D_STATEMENT (:7)
    ==> CM_GOOD_SWEEPOUT_STATEMENT (:A)`;;

let CM_CHAIN_CM_LEMMA122_STATEMENT = new_definition
 `CM_CHAIN_CM_LEMMA122_STATEMENT (aa:A->bool) <=>
  WAN_CAUCHY_HOLDER_STATEMENT ==> CM_HARMONIC_SPHERE_STATEMENT (:A)`;;

(* Sanity: the chain statements are closed terms of type bool. *)

let CM_STMTS_CLOSED = prove
 (`(!kk:K->bool. CM_CHAIN_HM_REGULARITY_STATEMENT kk = CM_CHAIN_HM_REGULARITY_STATEMENT (:K)) /\
   (!aa:A->bool. CM_CHAIN_CM_WIDTH_STATEMENT aa = CM_CHAIN_CM_WIDTH_STATEMENT (:A))`,
  REWRITE_TAC[CM_CHAIN_HM_REGULARITY_STATEMENT; CM_CHAIN_CM_WIDTH_STATEMENT]);;

