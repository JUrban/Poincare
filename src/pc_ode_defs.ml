(* ========================================================================= *)
(* pc_ode_defs: definitions of the ODE flow package (maximal solutions,      *)
(* flows, parametric and autonomous variants) and sanity lemmas.             *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* u solves u' = f(t,u) on the interval J, with its graph inside D. *)

let ode_solution = new_definition
 `ode_solution (f:real^(1,N)finite_sum->real^N) D J (u:real^1->real^N) <=>
    is_interval J /\
    !t. t IN J
        ==> pastecart t (u t) IN D /\
            (u has_vector_derivative f(pastecart t (u t))) (at t within J)`;;

(* f is locally Lipschitz in the state variable, uniformly in time. *)

let ode_locally_lipschitz = new_definition
 `ode_locally_lipschitz (f:real^(1,N)finite_sum->real^N) D <=>
    !z. z IN D
        ==> ?r L. &0 < r /\
                  !t x y. pastecart t x IN D INTER ball(z,r) /\
                          pastecart t y IN D INTER ball(z,r)
                          ==> norm(f(pastecart t x) - f(pastecart t y))
                              <= L * norm(x - y)`;;

(* The maximal interval through z: the union of all intervals carrying a    *)
(* solution through z.                                                      *)

let ode_maxint = new_definition
 `ode_maxint (f:real^(1,N)finite_sum->real^N) D (z:real^(1,N)finite_sum) =
    UNIONS {J | fstcart z IN J /\
                ?u. u(fstcart z) = sndcart z /\ ode_solution f D J u}`;;

(* The value at time t of the maximal solution through z (unspecified       *)
(* outside the maximal interval).                                           *)

let ode_flow = new_definition
 `ode_flow (f:real^(1,N)finite_sum->real^N) D (t:real^1)
           (z:real^(1,N)finite_sum) =
    (@u. u(fstcart z) = sndcart z /\ ode_solution f D (ode_maxint f D z) u) t`;;

(* The domain of the flow map w |-> ode_flow f D (fstcart w) (sndcart w).  *)

let ode_domain = new_definition
 `ode_domain (f:real^(1,N)finite_sum->real^N) D =
    {pastecart t z | z IN D /\ t IN ode_maxint f D z}`;;

(* Parameters in real^P as extra state components with zero speed. *)

let ode_param_field = new_definition
 `ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N) =
    \y. pastecart (g y) (vec 0:real^P)`;;

(* Autonomous vector fields X on U, as the time-dependent field             *)
(* (\z. X(sndcart z)) on (:real^1) PCROSS U with initial time 0.            *)

let ode_vf_maxint = new_definition
 `ode_vf_maxint (X:real^N->real^N) U (x:real^N) =
    ode_maxint (\z. X(sndcart z)) ((:real^1) PCROSS U) (pastecart (vec 0) x)`;;

let ode_vf_flow = new_definition
 `ode_vf_flow (X:real^N->real^N) U (t:real^1) (x:real^N) =
    ode_flow (\z. X(sndcart z)) ((:real^1) PCROSS U) t (pastecart (vec 0) x)`;;

let ode_vf_domain = new_definition
 `ode_vf_domain (X:real^N->real^N) U =
    {pastecart t x | x IN U /\ t IN ode_vf_maxint X U x}`;;

(* The problem x' = g(t,x,q), x(0) = h q: solution map on pastecart t q,    *)
(* and its domain for parameters q in H.                                    *)

let ode_param_sol = new_definition
 `ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                (h:real^Q->real^N) D (w:real^(1,Q)finite_sum) =
    fstcart(ode_flow (ode_param_field g) D (fstcart w)
              (pastecart (vec 0) (pastecart (h(sndcart w)) (sndcart w))))`;;

let ode_param_dom = new_definition
 `ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                (h:real^Q->real^N) D H =
    {pastecart t q | q IN H /\
                     t IN ode_maxint (ode_param_field g) D
                            (pastecart (vec 0) (pastecart (h q) q))}`;;

(* Sanity lemmas. *)

(* ------------------------------------------------------------------------- *)

let ODE_HAS_VECTOR_DERIVATIVE_WITHIN_SING = prove
 (`!(u:real^1->real^N) v t. (u has_vector_derivative v) (at t within {t})`,
  REWRITE_TAC[has_vector_derivative; has_derivative_within] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC LIM_TRIVIAL THEN REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_SING]]);;

(* A point of D carries the trivial solution on the one-point interval. *)

let ODE_SOLUTION_SING = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        z IN D ==> ode_solution f D {fstcart z} (\t. sndcart z)`,
  REWRITE_TAC[ode_solution; IS_INTERVAL_SING; IN_SING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PASTECART_FST_SND] THEN
  REWRITE_TAC[ODE_HAS_VECTOR_DERIVATIVE_WITHIN_SING]);;

let ODE_MAXINT_INITIAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        z IN D ==> fstcart z IN ode_maxint f D z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ode_maxint; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `{fstcart(z:real^(1,N)finite_sum)}` THEN
  REWRITE_TAC[IN_SING] THEN EXISTS_TAC `\t:real^1. sndcart(z:real^(1,N)finite_sum)` THEN
  ASM_SIMP_TAC[ODE_SOLUTION_SING]);;

(* Points outside D have empty maximal interval (teeth of the definition). *)

let ODE_MAXINT_OUTSIDE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        ~(z IN D) ==> ode_maxint f D z = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ode_maxint; EXTENSION; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[ode_solution] THEN
  ASM_MESON_TAC[PASTECART_FST_SND]);;

(* Constant solutions of a field vanishing along the constant. *)

let ODE_SOLUTION_CONST = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J x.
        is_interval J /\
        (!t. t IN J ==> pastecart t x IN D /\ f(pastecart t x) = vec 0)
        ==> ode_solution f D J (\t. x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ode_solution] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST]);;

(* The set of time-state points of the flow lies over D. *)

let ODE_DOMAIN_SUBSET = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
        ode_domain f D SUBSET (:real^1) PCROSS D`,
  REWRITE_TAC[ode_domain; SUBSET; IN_ELIM_THM; PCROSS; IN_UNIV] THEN
  MESON_TAC[]);;

