(* ========================================================================= *)
(* pc_wan_p4defs: the vocabulary and statement constants of the weak         *)
(* analysis part used in Part 4: the vocabulary wan_ckal, wan_ctr, wan_gdir, *)
(* wan_grad, eighteen statement constants in seven items, the S^2 bridge     *)
(* WAN_S2_DIR_C1_STATEMENT (the other statement constants are in             *)
(* pc_wan_defs), and sanity checks. The statements are proved in the other   *)
(* pc_wan files, except WAN_CAUCHY_HOLDER_STATEMENT, WAN_TRUNC_W12_STATEMENT *)
(* and WAN_S2_DIR_C1_STATEMENT, which are stated only.                       *)
(* ========================================================================= *)

needs "src/pc_wan_defs.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_p4_defs.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Vocabulary: scale-invariant C^(k,al) bounds on a set (derivatives of     *)
(* order j weighted by r^j, the top order Hoelder seminorm by r^(k+al)),    *)
(* the planar Cauchy transform (normalised to invert d/dzbar, as in the     *)
(* Pompeiu formula CAUCHY_TRANSFORM_INVERTS_DBAR of 100/green.ml), the      *)
(* Dirichlet integral with a variable ambient metric G.                      *)
(* ------------------------------------------------------------------------- *)

let wan_ckal = new_definition
 `wan_ckal (s:real^N->bool) k al r (f:real^N->real^K) A <=>
    (!l x. LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ x IN s
           ==> r pow (LENGTH l) * norm(iterated_partial l f x) <= A) /\
    (!l x y. LENGTH l = k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
             x IN s /\ y IN s
             ==> r rpow (&k + al) * norm(iterated_partial l f x - iterated_partial l f y)
                 <= A * norm(x - y) rpow al)`;;

let wan_ctr = new_definition
 `wan_ctr (a:complex->complex) (z:complex) =
    --(Cx(inv pi)) * integral (:complex) (\w. a w / (w - z))`;;

let wan_gdir = new_definition
 `wan_gdir (s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) =
    sum(1..dimindex(:N))
       (\i. drop(integral s (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))))`;;

let wan_grad = new_definition
 `wan_grad (h:real^N->real) (x:real^N) = (lambda i. wan_dpart i h x):real^N`;;

(* ------------------------------------------------------------------------- *)
(* Item 1 (quantitative).  (a) bounded Laplacian in the plane gives a       *)
(* C^(1,al) representative on the half ball with scale-invariant bounds;    *)
(* (b) planar Schauder (Korn): f in C^(k,al) gives C^(k+2,al);              *)
(* (c) the Cauchy transform of a bounded compactly supported function is    *)
(* Hoelder, with d/dzbar equal to the function in the weak sense.           *)
(* ------------------------------------------------------------------------- *)

let WAN_LOGPOT_C1A_QUANT_STATEMENT = new_definition
 `WAN_LOGPOT_C1A_QUANT_STATEMENT <=>
    !al. &0 < al /\ al < &1
         ==> ?C. &0 < C /\
                 !(a:real^2) r (u:real^2->real) (f:real^2->real) M U.
                    &0 < r /\ wan_w12 (ball(a,r)) (\x. lift(u x)) /\
                    (\x. lift(f x)) measurable_on ball(a,r) /\
                    (!x. x IN ball(a,r) ==> abs(f x) <= M) /\
                    (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                    (!phi. wan_test (ball(a,r)) phi
                           ==> vsum(1..2)
                                 (\i. integral (ball(a,r))
                                        (\x. wan_dpart i phi x %
                                             wan_wd (ball(a,r)) i (\y. lift(u y)) x)) =
                               --(integral (ball(a,r)) (\x. lift(f x * phi x))))
                    ==> ?w. continuously_differentiable 1 (ball(a,r / &2)) (\x. lift(w x)) /\
                            negligible {x | x IN ball(a,r / &2) /\ ~(u x = w x)} /\
                            (!x. x IN ball(a,r / &2)
                                 ==> abs(w x) <= C * (M * r pow 2 + U) /\
                                     r * norm(wan_grad w x) <= C * (M * r pow 2 + U)) /\
                            (!x y. x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
                                   ==> r rpow (&1 + al) * norm(wan_grad w x - wan_grad w y)
                                       <= C * (M * r pow 2 + U) * norm(x - y) rpow al)`;;

let WAN_SCHAUDER_2D_STATEMENT = new_definition
 `WAN_SCHAUDER_2D_STATEMENT <=>
    !k al. &0 < al /\ al < &1
           ==> ?C. &0 < C /\
                   !(a:real^2) r (u:real^2->real) (f:real^2->real) A U.
                      &0 < r /\ wan_w12 (ball(a,r)) (\x. lift(u x)) /\
                      continuously_differentiable k (ball(a,r)) (\x. lift(f x)) /\
                      wan_ckal (ball(a,r)) k al r (\x. lift(f x)) A /\
                      (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                      (!phi. wan_test (ball(a,r)) phi
                             ==> vsum(1..2)
                                   (\i. integral (ball(a,r))
                                          (\x. wan_dpart i phi x %
                                               wan_wd (ball(a,r)) i (\y. lift(u y)) x)) =
                                 --(integral (ball(a,r)) (\x. lift(f x * phi x))))
                      ==> ?w. continuously_differentiable (k + 2) (ball(a,r / &2))
                                (\x. lift(w x)) /\
                              negligible {x | x IN ball(a,r / &2) /\ ~(u x = w x)} /\
                              wan_ckal (ball(a,r / &2)) (k + 2) al r (\x. lift(w x))
                                       (C * (r pow 2 * A + U))`;;

let WAN_CAUCHY_HOLDER_STATEMENT = new_definition
 `WAN_CAUCHY_HOLDER_STATEMENT <=>
    !al. &0 < al /\ al < &1
         ==> ?C. &0 < C /\
                 !(a:complex->complex) c R M.
                    &0 < R /\ a measurable_on (:complex) /\
                    (!z. norm(a z) <= M) /\ (!z. ~(z IN ball(c,R)) ==> a z = Cx(&0))
                    ==> (!z. (\w. a w / (w - z)) absolutely_integrable_on (:complex)) /\
                        (!z w. norm(wan_ctr a z - wan_ctr a w)
                               <= C * M * R rpow (&1 - al) * norm(z - w) rpow al) /\
                        (!phi. wan_test (:complex) phi
                               ==> integral (:complex)
                                     (\z. wan_ctr a z * wirtinger_dbar (\w. Cx(phi w)) z) =
                                   --(integral (:complex) (\z. a z * Cx(phi z))))`;;

(* ------------------------------------------------------------------------- *)
(* Item 2.  (a) Campanato's characterization; (b) the Dirichlet integral of *)
(* the harmonic (Poisson) extension of circle data; (c) mean-oscillation    *)
(* decay of gradients of harmonic functions with exponent N + 2;            *)
(* (d) maximum principle on the closed disc (scalar and convex-ball forms). *)
(* ------------------------------------------------------------------------- *)

let WAN_CAMPANATO_STATEMENT = new_definition
 `WAN_CAMPANATO_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !al. &0 < al /\ al <= &1
         ==> ?C. &0 < C /\
                 !(a:real^N) r (u:real^N->real^K) Kc.
                    &0 < r /\ &0 <= Kc /\ u IN lspace (ball(a,r)) (&2) /\
                    (!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
                             ==> drop(integral (ball(x,rho))
                                        (\y. lift(norm(u y - inv(measure(ball(x,rho))) %
                                                          integral (ball(x,rho)) u) pow 2)))
                                 <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al))
                    ==> ?w. (!x y. x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
                                   ==> norm(w x - w y) <= C * Kc * norm(x - y) rpow al) /\
                            negligible {x | x IN ball(a,r / &2) /\ ~(u x = w x)}`;;

let WAN_POISSON_ENERGY_STATEMENT = new_definition
 `WAN_POISSON_ENERGY_STATEMENT (kk:K->bool) <=>
    !(a:real^2) r (f:real->real^K) (f':real->real^K).
       &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
       (!t. t IN real_interval[&0,&2 * pi]
            ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
       (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)]
       ==> ?h. h continuous_on cball(a,r) /\ (!t. h(wan_circ a r t) = f t) /\
               smooth_map_on (ball(a,r)) h /\
               (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
                      ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
               wan_w12 (ball(a,r)) h /\
               wan_dir (ball(a,r)) h
               <= drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(norm(f'(drop t)) pow 2)))`;;

let WAN_HARM_GRAD_OSC_STATEMENT = new_definition
 `WAN_HARM_GRAD_OSC_STATEMENT (n:N->bool) <=>
    ?C. &0 < C /\
        !(s:real^N->bool) (h:real^N->real) a r rho.
           open s /\ &0 < rho /\ rho <= r /\ cball(a,r) SUBSET s /\
           smooth_map_on s (\x. lift(h x)) /\
           (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0)
           ==> drop(integral (ball(a,rho))
                      (\x. lift(norm(wan_grad h x - inv(measure(ball(a,rho))) %
                                       integral (ball(a,rho)) (wan_grad h)) pow 2)))
               <= C * (rho / r) pow (dimindex(:N) + 2) *
                  drop(integral (ball(a,r))
                         (\x. lift(norm(wan_grad h x - inv(measure(ball(a,r))) %
                                          integral (ball(a,r)) (wan_grad h)) pow 2)))`;;

let WAN_MAX_PRINCIPLE_DISC_STATEMENT = new_definition
 `WAN_MAX_PRINCIPLE_DISC_STATEMENT <=>
    !(a:real^2) r (h:real^2->real) M.
       &0 < r /\ (\x. lift(h x)) continuous_on cball(a,r) /\
       smooth_map_on (ball(a,r)) (\x. lift(h x)) /\
       (!x. x IN ball(a,r) ==> llap (\y:real^2. mat 1) h x = &0) /\
       (!y. y IN sphere(a,r) ==> h y <= M)
       ==> !x. x IN cball(a,r) ==> h x <= M`;;

let WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT = new_definition
 `WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT (kk:K->bool) <=>
    !(a:real^2) r (h:real^2->real^K) c R.
       &0 < r /\ h continuous_on cball(a,r) /\ smooth_map_on (ball(a,r)) h /\
       (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
              ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
       (!y. y IN sphere(a,r) ==> h y IN cball(c,R))
       ==> !x. x IN cball(a,r) ==> h x IN cball(c,R)`;;

(* ------------------------------------------------------------------------- *)
(* Item 3.  (a) weak L^2 convergence of weak partials; (b) lower            *)
(* semicontinuity of the Dirichlet integral for a continuous, bounded,      *)
(* symmetric, positive semidefinite ambient metric G; (c) Radon-Riesz in    *)
(* the G form (G uniformly positive definite).                              *)
(* ------------------------------------------------------------------------- *)

let WAN_WEAK_PARTIALS_CONV_STATEMENT = new_definition
 `WAN_WEAK_PARTIALS_CONV_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:num->real^N->real^K) v M psi i.
       open s /\ (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\
       v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       psi IN lspace s (&2) /\ 1 <= i /\ i <= dimindex(:N)
       ==> wan_w12 s v /\
           ((\n. integral s (\x. lift(psi x dot wan_wd s i (u n) x))) -->
            integral s (\x. lift(psi x dot wan_wd s i v x))) sequentially`;;

let WAN_GDIR_LSC_STATEMENT = new_definition
 `WAN_GDIR_LSC_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (G:real^K->real^K^K) (u:num->real^N->real^K) v M E.
       open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
       (?B. !y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\
       (!y. transp(G y) = G y) /\ (!y w. &0 <= w dot (G y ** w)) /\
       (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       (?S. negligible S /\ !x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
       (!n. wan_gdir s G (u n) <= E)
       ==> wan_w12 s v /\ wan_gdir s G v <= E`;;

let WAN_RADON_RIESZ_G_STATEMENT = new_definition
 `WAN_RADON_RIESZ_G_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (G:real^K->real^K^K) (u:num->real^N->real^K) v M lam.
       open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
       (?B. !y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\
       (!y. transp(G y) = G y) /\ &0 < lam /\
       (!y w. lam * norm w pow 2 <= w dot (G y ** w)) /\
       (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       (?S. negligible S /\ !x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
       ((\n. wan_gdir s G (u n)) ---> wan_gdir s G v) sequentially
       ==> wan_w12 s v /\
           ((\n. wan_dir s (\x. u n x - v x)) ---> &0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Item 4.  Lipschitz chain rule (energy bound; e.g. the retraction onto a  *)
(* closed convex ball) and Stampacchia truncation max(u,c).                  *)
(* ------------------------------------------------------------------------- *)

let WAN_CHAIN_LIP_W12_STATEMENT = new_definition
 `WAN_CHAIN_LIP_W12_STATEMENT (n:N->bool) (kk:K->bool) (ll:L->bool) <=>
    !(s:real^N->bool) (u:real^N->real^K) (P:real^K->real^L) L.
       open s /\ bounded s /\ wan_w12 s u /\
       (!y z. norm(P y - P z) <= L * norm(y - z))
       ==> wan_w12 s (\x. P(u x)) /\
           wan_dir s (\x. P(u x)) <= L pow 2 * wan_dir s u`;;

let WAN_TRUNC_W12_STATEMENT = new_definition
 `WAN_TRUNC_W12_STATEMENT (n:N->bool) <=>
    !(s:real^N->bool) (u:real^N->real) c.
       open s /\ bounded s /\ wan_w12 s (\x. lift(u x))
       ==> wan_w12 s (\x. lift(max (u x) c)) /\
           !i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_wpd s i (\x. lift(max (u x) c))
                     (\x. if c < u x then wan_wd s i (\y. lift(u y)) x else vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Item 5.  Courant-Lebesgue at a boundary point x0 of the disc             *)
(* ball(a,R): arcs ball(a,R) INTER sphere(x0,r).                             *)
(* ------------------------------------------------------------------------- *)

let WAN_COURANT_LEBESGUE_BDRY_STATEMENT = new_definition
 `WAN_COURANT_LEBESGUE_BDRY_STATEMENT (kk:K->bool) <=>
    !(a:real^2) R x0 R0 d E (u:real^2->real^K).
       &0 < R /\ x0 IN sphere(a,R) /\ &0 < R0 /\ &0 < d /\ d < &1 /\
       u continuous_on (ball(a,R) INTER ball(x0,R0)) /\
       wan_w12 (ball(a,R) INTER ball(x0,R0)) u /\
       wan_dir (ball(a,R) INTER ball(x0,R0)) u <= &2 * E
       ==> ?r. d * R0 < r /\ r < sqrt d * R0 /\
               !y z. y IN ball(a,R) INTER sphere(x0,r) /\ z IN ball(a,R) INTER sphere(x0,r)
                     ==> norm(u y - u z) <= sqrt(&4 * pi * E / log(inv d))`;;

(* ------------------------------------------------------------------------- *)
(* Item 6.  W^(1,2) under C^1 diffeomorphisms with bounded derivatives;     *)
(* conformal invariance of the Dirichlet integral in the plane; the S^2     *)
(* Dirichlet integral in the stereographic chart (stereo2_n_inv of          *)
(* pc_mfd_examples) for W^(1,2) maps.                                        *)
(* ------------------------------------------------------------------------- *)

let WAN_W12_DIFFEO_STATEMENT = new_definition
 `WAN_W12_DIFFEO_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) t (Phi:real^N->real^N) Psi (u:real^N->real^K).
       open s /\ open t /\
       continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
       (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
       (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
       (?B. !x. x IN t ==> onorm(frechet_derivative Phi (at x)) <= B) /\
       (?B. !y. y IN s ==> onorm(frechet_derivative Psi (at y)) <= B) /\
       wan_w12 s u
       ==> wan_w12 t (\x. u(Phi x)) /\
           !i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_wpd t i (\x. u(Phi x))
                     (\x. vsum(1..dimindex(:N))
                            (\j. (frechet_derivative Phi (at x) (basis i))$j %
                                 wan_wd s j u (Phi x)))`;;

let WAN_DIR_CONFORMAL_2D_STATEMENT = new_definition
 `WAN_DIR_CONFORMAL_2D_STATEMENT (kk:K->bool) <=>
    !(s:real^2->bool) t (Phi:real^2->real^2) Psi (u:real^2->real^K).
       open s /\ open t /\
       continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
       (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
       (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
       (!x. x IN t ==> ?c. transp(jacobian Phi (at x)) ** jacobian Phi (at x) = c %% mat 1) /\
       wan_w12 s u /\ wan_w12 t (\x. u(Phi x))
       ==> wan_dir t (\x. u(Phi x)) = wan_dir s u`;;

let WAN_S2_STEREO_STATEMENT = new_definition
 `WAN_S2_STEREO_STATEMENT (kk:K->bool) <=>
    (!(u:real^3->real^K).
        wan_s2_w12 u
        ==> wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
            (!i. 1 <= i /\ i <= 2
                 ==> ?v. v IN lspace (:real^2) (&2) /\
                         wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) v) /\
            wan_dir (:real^2) (\y. u(stereo2_n_inv y)) = wan_s2_dir u) /\
    (!(u:real^3->real^K).
        wan_rext u IN lspace wan_shell (&2) /\
        wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
        (!i. 1 <= i /\ i <= 2
             ==> ?v. v IN lspace (:real^2) (&2) /\
                     wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) v)
        ==> wan_s2_w12 u)`;;

(* ------------------------------------------------------------------------- *)
(* Item 7.  Points are removable for W^(1,2) in dimension at least 2.       *)
(* ------------------------------------------------------------------------- *)

let WAN_REMOVABLE_POINT_STATEMENT = new_definition
 `WAN_REMOVABLE_POINT_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) a (u:real^N->real^K).
       open s /\ 2 <= dimindex(:N) /\ wan_w12 (s DIFF {a}) u
       ==> wan_w12 s u /\
           !i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_wpd s i u (wan_wd (s DIFF {a}) i u)`;;

(* ------------------------------------------------------------------------- *)
(* S2.4 The 2-sphere: for C^1 maps the shell Dirichlet integral is the     *)
(* round S^2 Dirichlet integral, written with p4_s2_integral (pc_p4_defs).  *)
(* ------------------------------------------------------------------------- *)

let WAN_S2_DIR_C1_STATEMENT = new_definition
 `WAN_S2_DIR_C1_STATEMENT (kk:K->bool) <=>
    !(u:real^3->real^K).
       continuously_differentiable 1 wan_shell (wan_rext u)
       ==> wan_s2_w12 u /\
           wan_s2_dir u =
           p4_s2_integral
             (\y. sum(1..3) (\i. norm(partial_derivative i (wan_rext u) y) pow 2))`;;


(* ------------------------------------------------------------------------- *)
(* Sanity checks: the G-weighted Dirichlet integral with G the identity is  *)
(* the Dirichlet integral; components of wan_grad; the zero map lies in     *)
(* every scale-invariant Hoelder class with A >= 0; the Cauchy transform of *)
(* the zero density vanishes.                                                *)
(* ------------------------------------------------------------------------- *)

let WAN_GDIR_ID = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_gdir s (\y. mat 1) u = wan_dir s u`,
  REWRITE_TAC[wan_gdir; wan_dir; MATRIX_VECTOR_MUL_LID; GSYM NORM_POW_2]);;

let WAN_GRAD_COMPONENT = prove
 (`!(h:real^N->real) x i.
     1 <= i /\ i <= dimindex(:N) ==> wan_grad h x$i = wan_dpart i h x`,
  SIMP_TAC[wan_grad; LAMBDA_BETA]);;

let WAN_CKAL_ZERO = prove
 (`!(s:real^N->bool) k al r A.
     &0 <= A ==> wan_ckal s k al r (\x:real^N. vec 0:real^K) A`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wan_ckal; TEXT_ITERATED_PARTIAL_ZERO; VECTOR_SUB_REFL; NORM_0;
              REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; NORM_POS_LE]);;

let WAN_CTR_ZERO = prove
 (`!z. wan_ctr (\w. Cx(&0)) z = Cx(&0)`,
  REWRITE_TAC[wan_ctr; complex_div; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; INTEGRAL_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO]);;

