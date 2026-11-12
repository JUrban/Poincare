(* Vendored copy of the library file src/ns_spacetime.ml from the Navier_Stokes
   development (github.com/hol-light-family/Navier_Stokes).
   Code unchanged except that its needs lines point to the vendored copies. *)

(* ========================================================================= *)
(* Space-time fields, the interface of Theorem 1.1 (a blowup candidate),     *)
(* and time-restricted versions of the classical notions of ns_statement.   *)
(*                                                                           *)
(* Space-time points are z = pastecart x (lift t) : real^(3,1)finite_sum     *)
(* with x:real^3 and t:real; coordinates 1, 2, 3 are space and 4 is time.    *)
(* Scalar space-time fields take values in real^1.                          *)
(* ========================================================================= *)

needs "src/ns_statement.ml";;
needs "src/ns_smooth.ml";;

type_invention_error := true;;

let ns_div = new_definition
 `ns_div (u:real^(3,1)finite_sum->real^3) z =
    sum(1..3) (\i. partial_derivative i u z$i)`;;

let ns_grad = new_definition
 `ns_grad (p:real^(3,1)finite_sum->real^1) z =
    (lambda i. drop(partial_derivative i p z)):real^3`;;

let ns_laplacian = new_definition
 `ns_laplacian (u:real^(3,1)finite_sum->real^N) z =
    vsum(1..3) (\j. partial_derivative j (partial_derivative j u) z)`;;

(* The momentum residual du/dt + (u . grad) u - nu Laplacian u + grad p.    *)
let ns_residual = new_definition
 `ns_residual nu (u:real^(3,1)finite_sum->real^3)
                 (p:real^(3,1)finite_sum->real^1) z =
    partial_derivative 4 u z +
    vsum(1..3) (\j. u z$j % partial_derivative j u z) -
    nu % ns_laplacian u z + ns_grad p z`;;

(* A blowup candidate at viscosity nu, in the form of Theorem 1.1 of the    *)
(* paper: velocity and pressure smooth for t < 1, vanishing for t <= t0 and *)
(* outside the compact set K; a force smooth on all of space-time and       *)
(* supported in K x [0,2]; the Navier-Stokes equations for t < 1; and an    *)
(* unbounded velocity.                                                       *)
let ns_blowup_candidate = new_definition
 `ns_blowup_candidate nu (u:real^(3,1)finite_sum->real^3)
                         (p:real^(3,1)finite_sum->real^1)
                         (f:real^(3,1)finite_sum->real^3) (K:real^3->bool) <=>
    compact K /\
    smooth_map_on {z | drop(sndcart z) < &1} u /\
    smooth_map_on {z | drop(sndcart z) < &1} p /\
    smooth_map_on (:real^(3,1)finite_sum) f /\
    (?t0. &0 < t0 /\
          !z. drop(sndcart z) < &1 /\ (drop(sndcart z) <= t0 \/ ~(fstcart z IN K))
              ==> u z = vec 0 /\ p z = vec 0) /\
    (!z. drop(sndcart z) <= &0 \/ &2 <= drop(sndcart z) \/ ~(fstcart z IN K)
         ==> f z = vec 0) /\
    (!z. drop(sndcart z) < &1 ==> ns_residual nu u p z = f z /\ ns_div u z = &0) /\
    ~bounded (IMAGE u {z | drop(sndcart z) < &1})`;;

(* Theorem 1.1 of the paper: a blowup candidate with bounded energy exists  *)
(* at every positive viscosity.                                              *)
let NS_THEOREM_1_1_STATEMENT = new_definition
 `NS_THEOREM_1_1_STATEMENT <=>
  !nu. &0 < nu
       ==> ?(u:real^(3,1)finite_sum->real^3) (p:real^(3,1)finite_sum->real^1)
            (f:real^(3,1)finite_sum->real^3) (K:real^3->bool).
             ns_blowup_candidate nu u p f K /\
             ?C. !t. &0 <= t /\ t < &1
                     ==> (\x. lift(norm(u(pastecart x (lift t))) pow 2))
                           integrable_on (:real^3) /\
                         drop(integral (:real^3)
                                (\x. lift(norm(u(pastecart x (lift t))) pow 2)))
                         <= C`;;

(* Curried classical views of space-time maps, and the index map from the   *)
(* classical convention (0 = time) to space-time coordinates (4 = time).    *)
let ns_curry = new_definition
 `ns_curry (g:real^(3,1)finite_sum->real^N) = \x t. g(pastecart x (lift t))`;;

let ns_curry_scalar = new_definition
 `ns_curry_scalar (g:real^(3,1)finite_sum->real^1) =
    \x t. drop(g(pastecart x (lift t)))`;;

let ns_st_index = new_definition
 `ns_st_index (k:num) = if k = 0 then 4 else k`;;

(* Classical C^m regularity on R^3 x [0,T]: the iterated partials of order *)
(* at most m are continuous on R^3 x [0,T], and those of order less than m *)
(* have all first partials (one-sided in time at t = 0) at points there.   *)
let ns_regular_upto = new_definition
 `ns_regular_upto m tmax (g:real^3->real->real) <=>
    !l. ALL (\k. k <= 3) l /\ LENGTH l <= m
        ==> (lift o (\z. ns_iter_partial l g (fstcart z) (drop(sndcart z))))
              continuous_on {z:real^(3,1)finite_sum | &0 <= drop(sndcart z) /\
                                                      drop(sndcart z) <= tmax} /\
            (LENGTH l < m
             ==> !k x t. k <= 3 /\ &0 <= t /\ t <= tmax
                         ==> ?d. ns_has_partial k (ns_iter_partial l g) x t d)`;;

(* The Navier-Stokes equations (1), (2) on R^3 x [0,tmax].                  *)
let ns_equations_upto = new_definition
 `ns_equations_upto (nu:real) tmax (f:real^3->real->real^3)
                    (u:real^3->real->real^3) (p:real^3->real->real) <=>
    !x t. &0 <= t /\ t <= tmax
          ==> (!i. 1 <= i /\ i <= 3
                   ==> ns_partial 0 (\x t. u x t$i) x t +
                       sum(1..3) (\j. u x t$j * ns_partial j (\x t. u x t$i) x t) =
                       nu * sum(1..3) (\j. ns_partial j (ns_partial j (\x t. u x t$i)) x t) -
                       ns_partial i p x t + f x t$i) /\
              sum(1..3) (\i. ns_partial i (\x t. u x t$i) x t) = &0`;;

let NS_EQUATIONS_UPTO = prove
 (`!nu f u p. ns_equations nu f u p <=> !tmax. ns_equations_upto nu tmax f u p`,
  REWRITE_TAC[ns_equations; ns_equations_upto] THEN
  MESON_TAC[REAL_LE_REFL]);;

let NS_SMOOTH_IMP_REGULAR_UPTO = prove
 (`!g m tmax. ns_smooth g ==> ns_regular_upto m tmax g`,
  REWRITE_TAC[ns_smooth; ns_regular_upto] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^(3,1)finite_sum | &0 <= drop(sndcart z)}` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

