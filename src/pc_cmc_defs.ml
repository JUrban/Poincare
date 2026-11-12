(* ========================================================================= *)
(* Unit pc_cmc_defs: the planar vocabulary and the internal statement       *)
(* constants of the chain unit pc_cm_compactness (Colding-Minicozzi 2008,   *)
(* Prop 2.2 with Prop A.3 and (1.19); the chain statement is                *)
(* CM_CHAIN_CM_COMPACTNESS_STATEMENT of pc_cm_stmts).                       *)
(*                                                                           *)
(* Planar maps w : real^2 -> real^K are the standard-chart pictures         *)
(* u o stereo2_n_inv of maps u of S^2 (possibly rescaled by similarities).  *)
(* Their GLOBAL weak partials wan_wd (:real^2) i w are used throughout:     *)
(*   cmc_pmap S w       : continuous, values in S, weak partials in L^2;    *)
(*   cmc_gram G w x     : the 2x2 G-Gram matrix of the weak partials;       *)
(*   cmc_tden G Q w x   : the density of the tangential G-trace of Q times  *)
(*                        the area element (0 where the Gram matrix is      *)
(*                        singular), the planar form of cm_strace;          *)
(*   cmc_pen, cmc_ptr   : integrals of the energy density (trace of the     *)
(*                        Gram matrix, NOT halved) and of cmc_tden on a set;*)
(*   cmc_ah S G e0 eta w: the property (B) of CM Prop 2.2 for planar balls  *)
(*                        in one chart (cm_almost_harmonic with all         *)
(*                        rotations equal);                                  *)
(*   cmc_pharm S G b    : planar harmonic maps of finite energy (bubbles);  *)
(*   cmc_ann y r1 r2    : the open annulus around y;                        *)
(*   cmc_angd y x g1 g2 : the derivative in the unit angular direction at x *)
(*                        (around y) of a map with partials g1, g2.         *)
(* Internal statement constants (proved in the units pc_cmc_xfer, _cyl,    *)
(* _global, _tree, _sphere from the hypotheses of the chain statement):     *)
(*   CMC_XFER_STATEMENT, CMC_SIM_STATEMENT, CMC_CYL_STATEMENT,              *)
(*   CMC_TIGHT_STATEMENT, CMC_PLANAR_BUBBLES_STATEMENT, CMC_SPHERE_STATEMENT.*)
(* ========================================================================= *)

needs "src/pc_hm_reg_cov.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Planar vocabulary.                                                        *)
(* ------------------------------------------------------------------------- *)

let cmc_ann = new_definition
 `cmc_ann (y:real^2) (r1:real) (r2:real) =
    {x:real^2 | r1 < norm(x - y) /\ norm(x - y) < r2}`;;

let cmc_angd = new_definition
 `cmc_angd (y:real^2) (x:real^2) (g1:real^K) (g2:real^K) =
    inv(norm(x - y)) % (--((x - y)$2) % g1 + (x - y)$1 % g2)`;;

let cmc_pmap = new_definition
 `cmc_pmap (S:real^K->bool) (w:real^2->real^K) <=>
    w continuous_on (:real^2) /\ (!x. w x IN S) /\
    !i. 1 <= i /\ i <= 2
        ==> ?g. g IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i w g`;;

let cmc_gram = new_definition
 `cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) (x:real^2) =
    (lambda i j. wan_wd (:real^2) i w x dot
                 (G(w x) ** wan_wd (:real^2) j w x)):real^2^2`;;

let cmc_tden = new_definition
 `cmc_tden (G:real^K->real^K^K) (Q:real^K->real^K^K) (w:real^2->real^K) (x:real^2) =
    if det(cmc_gram G w x) = &0 then &0
    else (trace(cmc_gram G w x) * trace(cmc_gram Q w x) -
          trace(cmc_gram G w x ** cmc_gram Q w x)) /
         sqrt(det(cmc_gram G w x))`;;

let cmc_pen = new_definition
 `cmc_pen (G:real^K->real^K^K) (E:real^2->bool) (w:real^2->real^K) =
    drop(integral E (\x. lift(trace(cmc_gram G w x))))`;;

let cmc_ptr = new_definition
 `cmc_ptr (G:real^K->real^K^K) (Q:real^K->real^K^K) (E:real^2->bool)
          (w:real^2->real^K) =
    drop(integral E (\x. lift(cmc_tden G Q w x)))`;;

let cmc_ah = new_definition
 `cmc_ah (S:real^K->bool) (G:real^K->real^K^K) (e0:real) (eta:real)
         (w:real^2->real^K) <=>
    !n (c:num->real^2) (r:num->real) (v:num->real^2->real^K).
       (!k. 1 <= k /\ k <= n ==> &0 < r k) /\
       (!k l. 1 <= k /\ k < l /\ l <= n
              ==> DISJOINT (cball(c k,r k)) (cball(c l,r l))) /\
       sum(1..n) (\k. wan_gdir (ball(c k,r k)) G w) < e0 /\
       (!k. 1 <= k /\ k <= n
            ==> cm_minimizer S G (ball(c k,r k / &8)) (v k) /\
                wan_w120 (ball(c k,r k / &8)) (\y. v k y - w y))
       ==> sum(1..n) (\k. wan_dir (ball(c k,r k / &8)) (\y. w y - v k y)) <= eta`;;

let cmc_pharm = new_definition
 `cmc_pharm (S:real^K->bool) (G:real^K->real^K^K) (b:real^2->real^K) <=>
    cm_harmonic S G (:real^2) b /\
    !i. 1 <= i /\ i <= 2
        ==> (\x. partial_derivative i b x) IN lspace (:real^2) (&2)`;;

(* ------------------------------------------------------------------------- *)
(* CMC_XFER_STATEMENT: maps of S^2 in the standard chart (energy, area,    *)
(* trace; the area is half the trace of G) and under rotations (unit        *)
(* pc_cmc_xfer).                                                             *)
(* ------------------------------------------------------------------------- *)

let CMC_XFER_STATEMENT = new_definition
 `CMC_XFER_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> (!u:real^3->real^K.
               cm_smap S u
               ==> cmc_pmap S (\y. u(stereo2_n_inv y)) /\
                   cm_sen G u = wan_gdir (:real^2) G (\y. u(stereo2_n_inv y)) / &2 /\
                   cm_sarea G u = cmc_ptr G G (:real^2) (\y. u(stereo2_n_inv y)) / &2 /\
                   !Q:real^K->real^K^K.
                      smooth_map_on (:real^K)
                        ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
                      (!z. transp(Q z) = Q z)
                      ==> cm_strace G Q u =
                          cmc_ptr G Q (:real^2) (\y. u(stereo2_n_inv y))) /\
           (!(u:real^3->real^K) (R:real^3^3).
               orthogonal_matrix R /\ det R = &1 /\ cm_smap S u
               ==> cm_smap S (\y. u(R ** y)) /\
                   cm_sen G (\y. u(R ** y)) = cm_sen G u /\
                   cm_sarea G (\y. u(R ** y)) = cm_sarea G u /\
                   !Q:real^K->real^K^K.
                      smooth_map_on (:real^K)
                        ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
                      (!z. transp(Q z) = Q z)
                      ==> cm_strace G Q (\y. u(R ** y)) = cm_strace G Q u) /\
           (!(u:real^3->real^K) (R:real^3^3).
               orthogonal_matrix R /\ det R = &1 /\ cm_sharmonic S G u
               ==> cm_sharmonic S G (\y. u(R ** y)))`;;

(* ------------------------------------------------------------------------- *)
(* CMC_SIM_STATEMENT: planar similarities z |-> a + lam z (unit           *)
(* pc_cmc_xfer): weak partials, energy and trace integrals, property (B).   *)
(* ------------------------------------------------------------------------- *)

let CMC_SIM_STATEMENT = new_definition
 `CMC_SIM_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(w:real^2->real^K) (a:real^2) lam.
              cmc_pmap S w /\ &0 < lam
              ==> cmc_pmap S (\z. w(a + lam % z)) /\
                  (!i. 1 <= i /\ i <= 2
                       ==> ?N. negligible N /\
                               !z. ~(z IN N)
                                   ==> wan_wd (:real^2) i (\z. w(a + lam % z)) z =
                                       lam % wan_wd (:real^2) i w (a + lam % z)) /\
                  (!E. lebesgue_measurable E
                       ==> cmc_pen G E (\z. w(a + lam % z)) =
                           cmc_pen G (IMAGE (\z. a + lam % z) E) w) /\
                  (!Q E. ((vectorize:real^K^K->real^(K,K)finite_prod) o Q)
                           continuous_on (:real^K) /\
                         lebesgue_measurable E
                         ==> cmc_ptr G Q E (\z. w(a + lam % z)) =
                             cmc_ptr G Q (IMAGE (\z. a + lam % z) E) w) /\
                  (!e0 eta. cmc_ah S G e0 eta w
                            ==> cmc_ah S G e0 eta (\z. w(a + lam % z)))`;;

(* ------------------------------------------------------------------------- *)
(* CMC_CYL_STATEMENT (unit pc_cmc_cyl): CM Prop B.1 in a unified form, on  *)
(* planar annuli.  U is smooth near the closed annulus                      *)
(* rho e^(-2l) <= |x - y| <= rho e^(2l), q = p + c U takes values in S, the *)
(* partials of U are tangent to S at q, U satisfies the projected           *)
(* Euler-Lagrange equation P(q)(Lap U + c sum_i Gamma(q)(d_i U, d_i U)) = 0  *)
(* and the explicit system Lap U = c sum_i B(q)(d_i U, d_i U), and          *)
(* |x - y| |d_i U(x)| <= M with c M <= g.  For c > 0 this is a harmonic map *)
(* q of S scaled by 1/c; c = 0 is CM's case of an affine limit (Remark B.7).*)
(* Conclusion: the angular energy on the middle annulus (cylinder           *)
(* coordinates t in [-l,l]) is at most delta times the Dirichlet integral   *)
(* on the double annulus (t in [-2l,2l]).                                   *)
(* ------------------------------------------------------------------------- *)

let CMC_CYL_STATEMENT = new_definition
 `CMC_CYL_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !delta. &0 < delta
           ==> ?l g. &1 <= l /\ &0 < g /\
                 !s (U:real^2->real^K) (p:real^K) c (y:real^2) rho M.
                    open s /\ &0 < rho /\ &0 <= c /\ &0 <= M /\ c * M <= g /\
                    {x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                                norm(x - y) <= rho * exp(&2 * l)} SUBSET s /\
                    smooth_map_on s U /\
                    (!x. x IN s ==> p + c % U x IN S) /\
                    (!x i. x IN s /\ 1 <= i /\ i <= 2
                           ==> hmr_tp S (p + c % U x) ** partial_derivative i U x =
                               partial_derivative i U x) /\
                    (!x. x IN s
                         ==> hmr_tp S (p + c % U x) **
                             (hmr_vlap U x +
                              c % vsum(1..2)
                                    (\i. christoffel G (p + c % U x)
                                           (partial_derivative i U x)
                                           (partial_derivative i U x))) = vec 0) /\
                    (!x. x IN s
                         ==> hmr_vlap U x =
                             c % vsum(1..2)
                                   (\i. hmr_bq S G (p + c % U x)
                                          (partial_derivative i U x)
                                          (partial_derivative i U x))) /\
                    (!x. rho * exp(--(&2 * l)) <= norm(x - y) /\
                         norm(x - y) <= rho * exp(&2 * l)
                         ==> norm(x - y) * norm(partial_derivative 1 U x) <= M /\
                             norm(x - y) * norm(partial_derivative 2 U x) <= M)
                    ==> drop(integral (cmc_ann y (rho * exp(--l)) (rho * exp l))
                               (\x. lift(norm(cmc_angd y x (partial_derivative 1 U x)
                                                          (partial_derivative 2 U x))
                                         pow 2)))
                        <= delta *
                           drop(integral (cmc_ann y (rho * exp(--(&2 * l)))
                                                    (rho * exp(&2 * l)))
                                  (\x. lift(norm(partial_derivative 1 U x) pow 2 +
                                            norm(partial_derivative 2 U x) pow 2)))`;;

(* ------------------------------------------------------------------------- *)
(* CMC_TIGHT_STATEMENT: after a subsequence and a rotation, the energy of   *)
(* the standard-chart maps is uniformly small near infinity (unit           *)
(* pc_cmc_sphere; pigeonhole over disjoint caps and the local theory).      *)
(* ------------------------------------------------------------------------- *)

let CMC_TIGHT_STATEMENT = new_definition
 `CMC_TIGHT_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?eT. &0 < eT /\
             !e0 E0 (u:num->real^3->real^K) eta.
                &0 < e0 /\ e0 < eT /\ (eta ---> &0) sequentially /\
                (!k. cm_smap S (u k) /\ cm_sen G (u k) <= E0 /\
                     cm_almost_harmonic S G e0 (eta k) (u k))
                ==> ?(s:num->num) R.
                       (!m n. m < n ==> s m < s n) /\
                       orthogonal_matrix R /\ det R = &1 /\
                       !e. &0 < e
                           ==> ?r. &0 < r /\
                                   eventually
                                     (\j. cmc_pen G {y:real^2 | r < norm y}
                                            (\y. u (s j) (R ** stereo2_n_inv y)) < e)
                                     sequentially`;;

(* ------------------------------------------------------------------------- *)
(* CMC_PLANAR_BUBBLES_STATEMENT: the planar bubble theorem (CM App. B and  *)
(* Prop A.3 in the standard chart; units pc_cmc_dens to pc_cmc_tree).       *)
(* Hypotheses: (B) with eta -> 0, values in a closed T, bounded energy,     *)
(* (A) as energy minus twice the area (= trace of G) eventually below any  *)
(* e > 0, tightness at infinity.  Conclusion: a subsequence and harmonic    *)
(* maps b 0, ..., b m of finite energy (b 0 is the weak limit, the others   *)
(* are bubbles; constant maps allowed) carrying all trace integrals.        *)
(* ------------------------------------------------------------------------- *)

let CMC_PLANAR_BUBBLES_STATEMENT = new_definition
 `CMC_PLANAR_BUBBLES_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?eB. &0 < eB /\
             !e0 E (w:num->real^2->real^K) eta TT.
                &0 < e0 /\ e0 < eB /\ (eta ---> &0) sequentially /\ closed TT /\
                (!j x. w j x IN TT) /\
                (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E /\
                     cmc_ah S G e0 (eta j) (w j)) /\
                (!e. &0 < e
                     ==> eventually
                           (\j. wan_gdir (:real^2) G (w j) - cmc_ptr G G (:real^2) (w j) < e)
                           sequentially) /\
                (!e. &0 < e
                     ==> ?r. &0 < r /\
                             eventually (\j. cmc_pen G {y:real^2 | r < norm y} (w j) < e)
                                        sequentially)
                ==> ?(t:num->num) m (b:num->real^2->real^K).
                       (!p q. p < q ==> t p < t q) /\
                       (!i. i <= m ==> cmc_pharm S G (b i) /\ (!x. b i x IN TT)) /\
                       !Q:real^K->real^K^K.
                          smooth_map_on (:real^K)
                            ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
                          (!z. transp(Q z) = Q z)
                          ==> ((\j. cmc_ptr G Q (:real^2) (w (t j))) --->
                               sum(0..m) (\i. cmc_ptr G Q (:real^2) (b i))) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* CMC_SPHERE_STATEMENT: a planar harmonic map of finite energy is the     *)
(* standard-chart picture of a map of S^2 (removable singularity at the     *)
(* pole), which is constant or a harmonic sphere (unit pc_cmc_sphere).       *)
(* ------------------------------------------------------------------------- *)

let CMC_SPHERE_STATEMENT = new_definition
 `CMC_SPHERE_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !(b:real^2->real^K) TT.
              cmc_pharm S G b /\ closed TT /\ (!x. b x IN TT)
              ==> ?v:real^3->real^K.
                     cm_smap S v /\ (!y. y IN sphere(vec 0,&1) ==> v y IN TT) /\
                     (!x. v(stereo2_n_inv x) = b x) /\
                     ((?c. !x. b x = c) \/ cm_sharmonic S G v)`;;

(* ------------------------------------------------------------------------- *)
(* Sanity: the statement constants are closed terms of type bool.           *)
(* ------------------------------------------------------------------------- *)

let CMC_DEFS_CLOSED = prove
 (`(!kk:K->bool. CMC_PLANAR_BUBBLES_STATEMENT kk = CMC_PLANAR_BUBBLES_STATEMENT (:K)) /\
   (!kk:K->bool. CMC_CYL_STATEMENT kk = CMC_CYL_STATEMENT (:K)) /\
   (!kk:K->bool. CMC_XFER_STATEMENT kk = CMC_XFER_STATEMENT (:K))`,
  REWRITE_TAC[CMC_PLANAR_BUBBLES_STATEMENT; CMC_CYL_STATEMENT; CMC_XFER_STATEMENT]);;

