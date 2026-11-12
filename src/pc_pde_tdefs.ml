(* ========================================================================= *)
(* Unit pc_pde_tdefs: the definitions of the torus layer (units              *)
(* pc_pde_torus, pc_pde_heat, pc_pde_tlin): Z^N-periodic maps, the unit-cube *)
(* Sobolev norms H^s (squared), linear second-order operators with scalar    *)
(* principal part, admissible periodic coefficients, smooth periodic         *)
(* solutions of u_t = L u + f, and the statement M4                          *)
(* (PDE_TORUS_LIN_STATEMENT).  The torus T^N = R^N / Z^N is never a type:    *)
(* maps live on real^N and periodicity is a predicate.                       *)
(*                                                                           *)
(* The definitions, the statement constant, basic facts.                     *)
(* ========================================================================= *)

needs "src/pc_pde_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* Z^N-periodic maps. *)

let pde_zper = new_definition
 `pde_zper (u:real^N->B) <=>
    !x i. 1 <= i /\ i <= dimindex(:N) ==> u(x + basis i) = u x`;;

(* The squared Sobolev norm H^s on the unit cube: the sum, over the index     *)
(* lists of length at most s, of the cube integrals of the squared norms of  *)
(* the iterated partials (each multi-index is counted with its orderings).   *)

let pde_hs2 = new_definition
 `pde_hs2 (s:num) (u:real^N->real^K) =
    sum (pde_index_lists s (:N))
        (\l. drop(integral (interval[vec 0,vec 1])
                           (\x. lift(norm(iterated_partial l u x) pow 2))))`;;

(* Linear second-order operators on R^K-valued maps with scalar (diagonal)  *)
(* principal part: sum_ij a_ij D_i D_j u + sum_i B_i D_i u + C u.           *)

let pde_lop = new_definition
 `pde_lop (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
          (cc:real->real^N->real^K^K) (u:real->real^N->real^K) (t:real) (x:real^N) =
    vsum(1..dimindex(:N))
      (\i. vsum(1..dimindex(:N))
             (\j. aa t x$i$j % partial_derivative i (partial_derivative j (u t)) x)) +
    vsum(1..dimindex(:N)) (\i. bb t x i ** partial_derivative i (u t) x) +
    cc t x ** u t x`;;

(* Admissible periodic coefficients on [0,tmax): smooth up to t = 0 (in the *)
(* sense of pde_upto), Z^N-periodic, principal part symmetric and uniformly *)
(* elliptic with constant lam.                                               *)

let pde_tcoeff = new_definition
 `pde_tcoeff (tmax:real) (lam:real) (aa:real->real^N->real^N^N)
             (bb:real->real^N->num->real^K^K) (cc:real->real^N->real^K^K) <=>
    &0 < lam /\
    pde_upto (&0) tmax (:real^N) (\t y. (vectorize:real^N^N->real^(N,N)finite_prod) (aa t y)) /\
    (!i. pde_upto (&0) tmax (:real^N)
           (\t y. (vectorize:real^K^K->real^(K,K)finite_prod) (bb t y i))) /\
    pde_upto (&0) tmax (:real^N) (\t y. (vectorize:real^K^K->real^(K,K)finite_prod) (cc t y)) /\
    (!t. pde_zper (aa t) /\ pde_zper (cc t) /\ !i. pde_zper (\y. bb t y i)) /\
    (!t y. &0 <= t /\ t < tmax
           ==> transp(aa t y) = aa t y /\
               !v. lam * norm v pow 2 <= v dot (aa t y ** v))`;;

(* Smooth periodic solutions of u_t = L u + f on [0,tmax) with u(0) = u0.   *)

let pde_tsol = new_definition
 `pde_tsol (tmax:real) (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
           (cc:real->real^N->real^K^K) (f:real->real^N->real^K)
           (u0:real^N->real^K) (u:real->real^N->real^K) <=>
    pde_upto (&0) tmax (:real^N) u /\
    (!t. &0 <= t /\ t < tmax ==> pde_zper (u t)) /\
    (!y. u (&0) y = u0 y) /\
    (!t y. &0 < t /\ t < tmax
           ==> ((\s. u (drop s) y) has_vector_derivative
                (pde_lop aa bb cc u t y + f t y)) (at (lift t)))`;;

(* M4: existence for admissible coefficients, smooth periodic data and      *)
(* forcing (continuity method from the flat heat equation).                  *)

let PDE_TORUS_LIN_STATEMENT = new_definition
 `PDE_TORUS_LIN_STATEMENT (n:N->bool) (k:K->bool) <=>
    !tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
     (cc:real->real^N->real^K^K) (f:real->real^N->real^K) u0.
        &0 < tmax /\ pde_tcoeff tmax lam aa bb cc /\
        pde_upto (&0) tmax (:real^N) f /\ (!t. pde_zper (f t)) /\
        smooth_map_on (:real^N) u0 /\ pde_zper u0
        ==> ?u. pde_tsol tmax aa bb cc f u0 u`;;

(* Basic facts. *)

let PDE_ZPER_CONST = prove
 (`!c:B. pde_zper (\x:real^N. c)`,
  REWRITE_TAC[pde_zper]);;

let PDE_ZPER_COMPOSE = prove
 (`!(u:real^N->B) (g:B->C). pde_zper u ==> pde_zper (\x. g(u x))`,
  SIMP_TAC[pde_zper]);;

let PDE_ZPER_ADD = prove
 (`!(u:real^N->real^K) v. pde_zper u /\ pde_zper v ==> pde_zper (\x. u x + v x)`,
  SIMP_TAC[pde_zper]);;

let PDE_ZPER_SUB = prove
 (`!(u:real^N->real^K) v. pde_zper u /\ pde_zper v ==> pde_zper (\x. u x - v x)`,
  SIMP_TAC[pde_zper]);;

let PDE_ZPER_CMUL = prove
 (`!(u:real^N->real^K) c. pde_zper u ==> pde_zper (\x. c % u x)`,
  SIMP_TAC[pde_zper]);;

let PDE_HS2_0 = prove
 (`!u:real^N->real^K.
        pde_hs2 0 u = drop(integral (interval[vec 0,vec 1]) (\x. lift(norm(u x) pow 2)))`,
  GEN_TAC THEN REWRITE_TAC[pde_hs2] THEN
  SUBGOAL_THEN `pde_index_lists 0 (:N) = {[]}` SUBST1_TAC THENL
   [REWRITE_TAC[pde_index_lists; EXTENSION; IN_ELIM_THM; IN_SING; LE] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[ALL];
    REWRITE_TAC[SUM_SING; iterated_partial]]);;

