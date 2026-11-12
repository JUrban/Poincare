(* Vendored copy of the library file src/ns_statement.ml from the Navier_Stokes
   development (github.com/hol-light-family/Navier_Stokes).
   Code unchanged except that its needs lines point to the vendored copies. *)

(* ========================================================================= *)
(* Clay Millennium problem for Navier-Stokes: breakdown alternatives (C) and *)
(* (D), stated clause by clause after Fefferman's official problem           *)
(* description (equations (1)-(11) there, plus the errata requiring the      *)
(* pressure to be periodic in the periodic setting).                         *)
(*                                                                           *)
(* Space-time fields are curried: g x t with x:real^3 and t:real.            *)
(* Partial derivatives are classical: index 0 is time (one-sided at t = 0,   *)
(* i.e. within t >= 0), indices 1, 2, 3 are the space coordinates.           *)
(* ========================================================================= *)

type_invention_error := true;;

let ns_has_partial = new_definition
 `ns_has_partial (k:num) (g:real^3->real->real) (x:real^3) (t:real) (d:real) <=>
    if k = 0 then ((\s. g x s) has_real_derivative d) (atreal t within {s | &0 <= s})
    else ((\s. g (x + s % basis k) t) has_real_derivative d) (atreal (&0))`;;

let ns_partial = new_definition
 `ns_partial (k:num) (g:real^3->real->real) (x:real^3) (t:real) =
    @d. ns_has_partial k g x t d`;;

let ns_iter_partial = define
 `(ns_iter_partial [] (g:real^3->real->real) = g) /\
  (ns_iter_partial (CONS (k:num) l) g = ns_partial k (ns_iter_partial l g))`;;

(* C-infinity on R^3 x [0,oo): every iterated partial derivative exists on   *)
(* the closed half-space and is continuous there.                            *)
let ns_smooth = new_definition
 `ns_smooth (g:real^3->real->real) <=>
    !l. ALL (\k. k <= 3) l
        ==> (lift o (\z. ns_iter_partial l g (fstcart z) (drop(sndcart z))))
              continuous_on {z:real^(3,1)finite_sum | &0 <= drop(sndcart z)} /\
            (!k x t. k <= 3 /\ &0 <= t
                     ==> ?d. ns_has_partial k (ns_iter_partial l g) x t d)`;;

let ns_smooth_field = new_definition
 `ns_smooth_field (v:real^3->real->real^3) <=>
    !i. 1 <= i /\ i <= 3 ==> ns_smooth (\x t. v x t$i)`;;

(* Equations (1) and (2) for x in R^3, t >= 0. *)
let ns_equations = new_definition
 `ns_equations (nu:real) (f:real^3->real->real^3)
               (u:real^3->real->real^3) (p:real^3->real->real) <=>
    !x t. &0 <= t
          ==> (!i. 1 <= i /\ i <= 3
                   ==> ns_partial 0 (\x t. u x t$i) x t +
                       sum(1..3) (\j. u x t$j * ns_partial j (\x t. u x t$i) x t) =
                       nu * sum(1..3) (\j. ns_partial j (ns_partial j (\x t. u x t$i)) x t) -
                       ns_partial i p x t + f x t$i) /\
              sum(1..3) (\i. ns_partial i (\x t. u x t$i) x t) = &0`;;

(* A smooth divergence-free initial field (time-independent). *)
let ns_initial_field = new_definition
 `ns_initial_field (u0:real^3->real^3) <=>
    ns_smooth_field (\x t. u0 x) /\
    !x. sum(1..3) (\i. ns_partial i (\x t. u0 x$i) x (&0)) = &0`;;

(* Condition (4). *)
let ns_initial_decay = new_definition
 `ns_initial_decay (u0:real^3->real^3) <=>
    !i l K. 1 <= i /\ i <= 3 /\ ALL (\k. 1 <= k /\ k <= 3) l
            ==> ?C. !x. abs(ns_iter_partial l (\x t. u0 x$i) x (&0))
                        <= C / (&1 + norm x) pow K`;;

(* Condition (5). *)
let ns_force_decay = new_definition
 `ns_force_decay (f:real^3->real->real^3) <=>
    !i l K. 1 <= i /\ i <= 3 /\ ALL (\k. k <= 3) l
            ==> ?C. !x t. &0 <= t
                          ==> abs(ns_iter_partial l (\x t. f x t$i) x t)
                              <= C / (&1 + norm x + t) pow K`;;

(* Condition (9). *)
let ns_force_decay_periodic = new_definition
 `ns_force_decay_periodic (f:real^3->real->real^3) <=>
    !i l K. 1 <= i /\ i <= 3 /\ ALL (\k. k <= 3) l
            ==> ?C. !x t. &0 <= t
                          ==> abs(ns_iter_partial l (\x t. f x t$i) x t)
                              <= C / (&1 + abs t) pow K`;;

(* Condition (7), bounded energy. *)
let ns_bounded_energy = new_definition
 `ns_bounded_energy (u:real^3->real->real^3) <=>
    ?C. !t. &0 <= t
            ==> (\x. lift(norm(u x t) pow 2)) integrable_on (:real^3) /\
                drop(integral (:real^3) (\x. lift(norm(u x t) pow 2))) < C`;;

(* (C): breakdown of Navier-Stokes solutions on R^3. *)
let NS_BREAKDOWN_R3_STATEMENT = new_definition
 `NS_BREAKDOWN_R3_STATEMENT <=>
  !nu. &0 < nu
       ==> ?(u0:real^3->real^3) (f:real^3->real->real^3).
              ns_initial_field u0 /\ ns_initial_decay u0 /\
              ns_smooth_field f /\ ns_force_decay f /\
              ~(?(u:real^3->real->real^3) (p:real^3->real->real).
                   ns_smooth_field u /\ ns_smooth p /\
                   ns_equations nu f u p /\ (!x. u x (&0) = u0 x) /\
                   ns_bounded_energy u)`;;

(* (D): breakdown of Navier-Stokes solutions on R^3 / Z^3. *)
let NS_BREAKDOWN_PERIODIC_STATEMENT = new_definition
 `NS_BREAKDOWN_PERIODIC_STATEMENT <=>
  !nu. &0 < nu
       ==> ?(u0:real^3->real^3) (f:real^3->real->real^3).
              ns_initial_field u0 /\
              (!x j. 1 <= j /\ j <= 3 ==> u0(x + basis j) = u0 x) /\
              ns_smooth_field f /\
              (!x t j. 1 <= j /\ j <= 3 /\ &0 <= t ==> f (x + basis j) t = f x t) /\
              ns_force_decay_periodic f /\
              ~(?(u:real^3->real->real^3) (p:real^3->real->real).
                   ns_smooth_field u /\ ns_smooth p /\
                   ns_equations nu f u p /\ (!x. u x (&0) = u0 x) /\
                   (!x t j. 1 <= j /\ j <= 3 /\ &0 <= t
                            ==> u (x + basis j) t = u x t /\
                                p (x + basis j) t = p x t))`;;

(* ========================================================================= *)
(* Basic facts about the classical partial derivatives, and a non-vacuity   *)
(* check of the breakdown statements.                                       *)
(* ========================================================================= *)

let NS_REAL_DERIVATIVE_UNIQUE_WITHIN = prove
 (`!f s t d1 d2.
     ~trivial_limit (atreal t within s) /\
     (f has_real_derivative d1) (atreal t within s) /\
     (f has_real_derivative d2) (atreal t within s)
     ==> d1 = d2`,
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; TRIVIAL_LIMIT_WITHINREAL_WITHIN] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (f:real->real) o drop`; `lift t`; `IMAGE lift s`;
                 `lift d1`; `lift d2`] VECTOR_DERIVATIVE_UNIQUE_WITHIN) THEN
  ASM_REWRITE_TAC[LIFT_EQ]);;

let NS_TRIVIAL_LIMIT_HALFLINE = prove
 (`!t. &0 <= t ==> ~trivial_limit (atreal t within {s | &0 <= s})`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{s:real | &0 <= s}`; `t:real`] TRIVIAL_LIMIT_WITHIN_REALINTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; is_realinterval] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `t + &1`) THEN ASM_REAL_ARITH_TAC]);;

let NS_PARTIAL_UNIQUE = prove
 (`!k g x t d. &0 <= t /\ ns_has_partial k g x t d ==> ns_partial k g x t = d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ns_partial] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `e:real` THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `ns_has_partial k g x t d` THEN REWRITE_TAC[ns_has_partial] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[NS_REAL_DERIVATIVE_UNIQUE_WITHIN; NS_TRIVIAL_LIMIT_HALFLINE; ASSUME `&0 <= t`];
    MESON_TAC[REAL_DERIVATIVE_UNIQUE_ATREAL]]);;

let NS_ITER_PARTIAL_ZERO = prove
 (`!l x t. &0 <= t ==> ns_iter_partial l (\x:real^3 t:real. &0) x t = &0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ns_iter_partial] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NS_PARTIAL_UNIQUE THEN
  ASM_REWRITE_TAC[ns_has_partial] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`\s:real. &0`; `&1`] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_01; HAS_REAL_DERIVATIVE_CONST];
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_CONST]]);;

let NS_SMOOTH_ZERO = prove
 (`ns_smooth (\x:real^3 t:real. &0)`,
  REWRITE_TAC[ns_smooth] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `(\z:real^(3,1)finite_sum. vec 0:real^1)` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; IN_ELIM_THM; o_THM] THEN
    SIMP_TAC[NS_ITER_PARTIAL_ZERO; LIFT_NUM];
    EXISTS_TAC `&0` THEN
    SUBGOAL_THEN `!s. &0 <= s ==> ns_iter_partial l (\x:real^3 t:real. &0) x s = &0`
      ASSUME_TAC THENL [SIMP_TAC[NS_ITER_PARTIAL_ZERO]; ALL_TAC] THEN
    REWRITE_TAC[ns_has_partial] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC [`\s:real. &0`; `&1`] THEN
      ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_01; HAS_REAL_DERIVATIVE_CONST];
      ASM_SIMP_TAC[NS_ITER_PARTIAL_ZERO; HAS_REAL_DERIVATIVE_CONST]]]);;

let NS_PARTIAL_ZERO = prove
 (`!k x t. &0 <= t ==> ns_partial k (\x:real^3 t:real. &0) x t = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[k:num]`; `x:real^3`; `t:real`] NS_ITER_PARTIAL_ZERO) THEN
  ASM_REWRITE_TAC[ns_iter_partial]);;

let NS_PARTIAL2_ZERO = prove
 (`!j k x t. &0 <= t ==> ns_partial j (ns_partial k (\x:real^3 t:real. &0)) x t = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[j:num; k]`; `x:real^3`; `t:real`] NS_ITER_PARTIAL_ZERO) THEN
  ASM_REWRITE_TAC[ns_iter_partial]);;


(* Non-vacuity check of the statements: with zero data the zero pair lies in *)
(* the solution classes, so the breakdown clauses are not trivially true.    *)
let NS_ZERO_SOLUTION = prove
 (`!nu. ns_initial_field (\x:real^3. vec 0) /\
        ns_smooth_field (\x:real^3 t:real. vec 0:real^3) /\
        ns_smooth (\x:real^3 t:real. &0) /\
        ns_equations nu (\x t. vec 0) (\x t. vec 0) (\x t. &0) /\
        ns_bounded_energy (\x:real^3 t:real. vec 0:real^3)`,
  GEN_TAC THEN
  REWRITE_TAC[ns_initial_field; ns_smooth_field; ns_equations; ns_bounded_energy;
              VEC_COMPONENT; NS_SMOOTH_ZERO; ETA_AX] THEN
  SIMP_TAC[NS_PARTIAL_ZERO; NS_PARTIAL2_ZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; REAL_SUB_REFL; REAL_ADD_LID;
              REAL_ADD_RID; REAL_SUB_RZERO; NORM_0] THEN
  EXISTS_TAC `&1` THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; LIFT_NUM; INTEGRABLE_0; INTEGRAL_0; DROP_VEC] THEN
  REAL_ARITH_TAC);;

