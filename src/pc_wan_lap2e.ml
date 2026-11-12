(* ========================================================================= *)
(* pc_wan_lap2e: the energy of the harmonic extension of circle data,        *)
(* WAN_POISSON_ENERGY.  For f periodic, absolutely continuous with f' in     *)
(* L^2, the Poisson integral h of f has wan_dir h <= int_0^2pi |f'|^2, by    *)
(* 2pi sum |k| |c_k|^2 <= 2pi sum k^2 |c_k|^2.                               *)
(*   - orthogonality of e^(int) and finite Parseval;                         *)
(*   - the circle data;                                                      *)
(*   - Fourier coefficients of f' (integration by parts) and Bessel;         *)
(*   - truncation of the Poisson kernel; harmonic polynomials u_N close      *)
(*     to the Poisson integral inside the disc;                              *)
(*   - the energy of harmonic polynomials (polar coordinates);               *)
(*   - the limit, monotone convergence, WAN_POISSON_ENERGY.                  *)
(* ========================================================================= *)

needs "src/pc_wan_lap2d.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Orthogonality of the exponentials on [0,2pi] and the finite Parseval      *)
(* identity (WANL_ANGLE_POW_INTEGRAL, WANL_UNIT_POW_CNJ,                     *)
(* WANL_ANGLE_ORTHOGONAL, WANL_VSUM_DELTA_MUL, WANL_FINITE_PARSEVAL),        *)
(* adapted from earlier HOL Light work; they use                             *)
(* WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH of pc_wan_lap2a.                       *)
(* ========================================================================= *)

let WANL_ANGLE_POW_INTEGRAL = prove
 (`!k. ((\x. cexp(ii * Cx(drop x)) pow k) has_integral
        (if k = 0 then Cx(&2 * pi) else Cx(&0)))
       (interval[vec 0,lift(&2 * pi)])`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\u:complex. u pow k`; `Cx(&0)`; `&1`; `Cx(&0)`]
    CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE) THEN
  REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_POW THEN REWRITE_TAC[HOLOMORPHIC_ON_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH) THEN
  DISCH_THEN(MP_TAC o SPEC `--ii` o MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
  SUBGOAL_THEN
   `--ii * Cx(&2) * Cx pi * ii * Cx(&0) pow k =
    (if k = 0 then Cx(&2 * pi) else Cx(&0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_ZERO] THEN COND_CASES_TAC THEN
    REWRITE_TAC[CX_MUL; COMPLEX_MUL_RZERO; COMPLEX_MUL_RID] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
  MP_TAC(SPEC `ii * Cx(drop x)` CEXP_NZ) THEN MP_TAC COMPLEX_POW_II_2 THEN
  ABBREV_TAC `c = cexp(ii * Cx(drop x))` THEN CONV_TAC COMPLEX_FIELD);;

let WANL_UNIT_POW_CNJ = prove
 (`!x m. cexp(ii * Cx(drop x)) pow m * cnj(cexp(ii * Cx(drop x)) pow m) =
         Cx(&1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_POW_2; COMPLEX_NORM_POW; NORM_CEXP_II;
              REAL_POW_ONE; COMPLEX_POW_ONE]);;

let WANL_ANGLE_ORTHOGONAL = prove
 (`!n m. ((\x. cexp(ii * Cx(drop x)) pow n * cnj(cexp(ii * Cx(drop x)) pow m))
          has_integral (if n = m then Cx(&2 * pi) else Cx(&0)))
         (interval[vec 0,lift(&2 * pi)])`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(ARITH_RULE `m:num <= n \/ n < m`) THENL
   [MP_TAC(SPEC `n - m:num` WANL_ANGLE_POW_INTEGRAL) THEN
    SUBGOAL_THEN `(n:num) - m = 0 <=> n = m` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[ADD_SUB2; COMPLEX_POW_ADD] THEN
    MP_TAC(SPECL [`x:real^1`; `m:num`] WANL_UNIT_POW_CNJ) THEN
    CONV_TAC COMPLEX_RING;
    MP_TAC(SPEC `m - n:num` WANL_ANGLE_POW_INTEGRAL) THEN
    SUBGOAL_THEN `~((m:num) - n = 0) /\ ~(n = m)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `cnj` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[LINEAR_CNJ; CNJ_CX; o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(n + SUC d) - n = SUC d`; COMPLEX_POW_ADD; CNJ_MUL] THEN
    MP_TAC(SPECL [`x:real^1`; `n:num`] WANL_UNIT_POW_CNJ) THEN
    CONV_TAC COMPLEX_RING]);;

let WANL_VSUM_DELTA_MUL = prove
 (`!s (k:num->complex) n A.
      FINITE s /\ n IN s
      ==> vsum s (\m. k m * (if n = m then A else Cx(&0))) = k n * A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. (k:num->complex) m * (if n = m then A else Cx(&0))`;
                 `s:num->bool`; `n:num`] VSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum (s DELETE n) (\m. (k:num->complex) m * (if n = m then A else Cx(&0))) =
    Cx(&0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_VEC_0]];
    CONV_TAC COMPLEX_RING]);;

let WANL_FINITE_PARSEVAL = prove
 (`!(c:num->complex) s.
      FINITE s
      ==> ((\x. lift(norm(vsum s (\n. c n * cexp(ii * Cx(drop x)) pow n))
                     pow 2))
           has_integral lift(&2 * pi * sum s (\n. norm(c n) pow 2)))
          (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. vsum (s:num->bool) (\n. vsum s (\m. ((c:num->complex) n * cnj(c m)) *
                    (cexp(ii * Cx(drop x)) pow n *
                     cnj(cexp(ii * Cx(drop x)) pow m)))))
     has_integral
     vsum s (\n. vsum s (\m. (c n * cnj(c m)) *
                    (if n = m then Cx(&2 * pi) else Cx(&0)))))
    (interval[vec 0,lift(&2 * pi)])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN REWRITE_TAC[WANL_ANGLE_ORTHOGONAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum (s:num->bool) (\n. vsum s (\m. ((c:num->complex) n * cnj(c m)) *
                  (if n = m then Cx(&2 * pi) else Cx(&0)))) =
    Cx(&2 * pi * sum s (\n. norm(c n) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum (s:num->bool) (\n. (c n * cnj((c:num->complex) n)) * Cx(&2 * pi))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      BETA_TAC THEN
      MP_TAC(ISPECL [`s:num->bool`; `\m. (c:num->complex) n * cnj(c m)`;
                     `n:num`; `Cx(&2 * pi)`] WANL_VSUM_DELTA_MUL) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM COMPLEX_NORM_POW_2; GSYM CX_POW; GSYM CX_MUL] THEN
      ASM_SIMP_TAC[VSUM_CX; SUM_RMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HAS_INTEGRAL_EQ)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `\x. Cx(norm(vsum (s:num->bool) (\n. (c:num->complex) n * cexp(ii * Cx(drop x)) pow n))
           pow 2)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[CX_POW; COMPLEX_NORM_POW_2] THEN
    ASM_SIMP_TAC[CNJ_VSUM; GSYM VSUM_COMPLEX_RMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    REWRITE_TAC[CNJ_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `\z:complex. lift(Re z)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF; RE_CX]);;

(* ========================================================================= *)
(* The circle data.  f is continuous (an indefinite integral                *)
(* plus a constant); G x = f(Arg(x - a)) is continuous on the circle and    *)
(* takes the value f t at wan_circ a r t.                                    *)
(* ========================================================================= *)

let WANL_PE_PERIODIC_INT = prove
 (`!(f:real->real^K) p.
        (!x. f(x + p) = f x) ==> !x n. integer n ==> f(x + n * p) = f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real->real^K) x$j`; `p:real`]
         WANL_REAL_PERIODIC_INTEGER_MULTIPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x:real`; `n:real`]) THEN
  ASM_REWRITE_TAC[]);;

let WANL_PE_ARG_CIRC = prove
 (`!r t. &0 < r
         ==> Arg(Cx r * cexp(ii * Cx t)) = t + --floor(t / (&2 * pi)) * (&2 * pi)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `t / (&2 * pi)` FLOOR) THEN
  ABBREV_TAC `k = floor(t / (&2 * pi))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `ii * Cx(t + --k * &2 * pi) = ii * Cx t + Cx(&2 * --k * pi) * ii`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_ADD; CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[CEXP_ADD] THEN
    MP_TAC(SPEC `--k:real` CEXP_INTEGER_2PI) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_RID];
    MATCH_MP_TAC(REAL_ARITH `k * p <= t ==> &0 <= t + --k * p`) THEN
    UNDISCH_TAC `k <= t / (&2 * pi)` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    MATCH_MP_TAC(REAL_ARITH `t < (k + &1) * p ==> t + --k * p < p`) THEN
    UNDISCH_TAC `t / (&2 * pi) < k + &1` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ]]);;

(* The data map is continuous on [0,2pi]. *)

let WANL_PE_DATA_CONT = prove
 (`!(f:real->real^K) f'.
        (!t. t IN real_interval[&0,&2 * pi]
             ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t]))
        ==> (f o drop) continuous_on interval[vec 0,lift(&2 * pi)]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. (f:real->real^K)(&0) +
                  integral (interval[vec 0,x]) (\s. (f':real->real^K)(drop s))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; o_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop x`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `(f:real->real^K)(&2 * pi) - f(&0)` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC]);;

(* The boundary map on the circle. *)

let WANL_PE_BOUNDARY = prove
 (`!(a:real^2) r (f:real->real^K) f'.
        &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
        (!t. t IN real_interval[&0,&2 * pi]
             ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t]))
        ==> (\x. f(Arg(x - a))) continuous_on sphere(a,r) /\
            (!t. (\x. f(Arg(x - a))) (a + r % cexp(ii * Cx t)) = f t) /\
            (!t. (\x. f(Arg(x - a))) (wan_circ a r t) = f t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. (f:real->real^K)(Arg(r % cexp(ii * Cx t))) = f t` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[COMPLEX_CMUL] THEN ASM_SIMP_TAC[WANL_PE_ARG_CIRC] THEN
    MP_TAC(ISPECL [`f:real->real^K`; `&2 * pi`] WANL_PE_PERIODIC_INT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; FLOOR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^2 = x`; WANL_WAN_CIRC] THEN
  SUBGOAL_THEN `(\x. (f:real->real^K)(Arg(x - a))) = (\z. f(Arg z)) o (\x. x - a)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE_ARG THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WANL_PE_DATA_CONT THEN EXISTS_TAC `f':real->real^K` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[REAL_ADD_LID];
    REWRITE_TAC[IN_IMAGE; IN_SPHERE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `dist(a:real^2,x) = r` THEN
    REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    UNDISCH_TAC `Cx(&0) = x - a` THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Fourier coefficients on [0,2pi] (unnormalized),                          *)
(* fc phi n = int_0^2pi phi(s) e^(-ins) ds; for absolutely continuous       *)
(* periodic phi, fc phi' n = i n fc phi n (integration by parts); Bessel:   *)
(* sum_(n=1..N) |fc psi n|^2 <= pi int_0^2pi psi^2.                          *)
(* ========================================================================= *)

let wanl_pe_fc = new_definition
 `wanl_pe_fc (phi:real->real) n =
    integral (interval[vec 0,lift(&2 * pi)])
             (\s. Cx(phi(drop s)) * cnj(cexp(ii * Cx(drop s)) pow n))`;;

let WANL_PE_CNJ_POW = prove
 (`!n t. cnj(cexp(ii * Cx t) pow n) = cexp(--ii * Cx(&n) * Cx t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CNJ_POW; CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX] THEN
  REWRITE_TAC[GSYM CEXP_N] THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let WANL_PE_EXP_DERIV = prove
 (`!n x. ((\x. cexp(--ii * Cx(&n) * Cx(drop x))) has_vector_derivative
          ((--ii * Cx(&n)) * cexp(--ii * Cx(&n) * Cx(drop x)))) (at x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(BETA_RULE(INST
    [`\z. cexp(--ii * Cx(&n) * z)`,`f:complex->complex`;
     `(--ii * Cx(&n)) * cexp(--ii * Cx(&n) * Cx(drop x))`,`f':complex`;
     `x:real^1`,`a:real^1`] HAS_VECTOR_DERIVATIVE_REAL_COMPLEX)) THEN
  DISCH_THEN MATCH_MP_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let WANL_PE_EXP_INTEGRAL = prove
 (`!n. 1 <= n
       ==> ((\s. cnj(cexp(ii * Cx(drop s)) pow n)) has_integral Cx(&0))
           (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:num` WANL_ANGLE_POW_INTEGRAL) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN(MP_TAC o ISPEC `cnj` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  REWRITE_TAC[LINEAR_CNJ; CNJ_CX; o_DEF]);;

(* Integration by parts: the coefficients of phi'. *)

let WANL_PE_FC_DERIV = prove
 (`!(phi:real->real) phi' n.
        (!t. phi(t + &2 * pi) = phi t) /\
        (\s. lift(phi'(drop s))) absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
        (!t. t IN real_interval[&0,&2 * pi]
             ==> ((\s. lift(phi'(drop s))) has_integral lift(phi t - phi(&0)))
                 (interval[vec 0,lift t])) /\
        1 <= n
        ==> wanl_pe_fc phi' n = ii * Cx(&n) * wanl_pe_fc phi n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ac") ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 <= &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. Cx((phi:real->real)(drop x))) continuous_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lift o (phi:real->real)`; `lift o (phi':real->real)`]
           WANL_PE_DATA_CONT) THEN
    REWRITE_TAC[o_THM; GSYM LIFT_SUB] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `\v:real^1. Cx(drop v)` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] LINEAR_CONTINUOUS_ON_COMPOSE)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. Cx((phi':real->real)(drop x))) has_integral Cx(&0)) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [USE_THEN "ac" (MP_TAC o SPEC `&2 * pi`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `\v:real^1. Cx(drop v)` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN ANTS_TAC THENL
     [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real->real)(&2 * pi) = phi(&0)` SUBST1_TAC THENL
     [ASM_MESON_TAC[REAL_ADD_LID]; REWRITE_TAC[REAL_SUB_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `E = \x. cexp(--ii * Cx(&n) * Cx(drop x))` THEN
  SUBGOAL_THEN `!x. cnj(cexp(ii * Cx(drop x)) pow n) = (E:real^1->complex) x`
  ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[WANL_PE_CNJ_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^1->complex)(lift(&2 * pi)) = Cx(&1) /\ E(vec 0) = Cx(&1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; COMPLEX_MUL_RZERO; CEXP_0] THEN
    MP_TAC(SPEC `--(&n)` CEXP_INTEGER_2PI) THEN
    SIMP_TAC[INTEGER_CLOSED] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^1->complex) continuous_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `x:real^1` THEN
    DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % ((--ii * Cx(&n)) * (E:real^1->complex) x)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[WANL_PE_EXP_DERIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\x. Cx((phi:real->real)(drop x) - phi(&0))`;
    `\x. (E:real^1->complex) x - Cx(&1)`;
    `\x. Cx((phi':real->real)(drop x))`;
    `\x. (--ii * Cx(&n)) * (E:real^1->complex) x`;
    `vec 0:real^1`; `lift(&2 * pi)`] ABSOLUTE_INTEGRATION_BY_PARTS) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; DROP_VEC; LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. Cx((phi':real->real)(drop x))) =
                    (\v. Cx(drop v)) o (\s. lift(phi'(drop s)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `drop x`) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; LIFT_DROP] THEN
      DISCH_THEN(MP_TAC o ISPEC `\v:real^1. Cx(drop v)` o MATCH_MP
        (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN ANTS_TAC THENL
       [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL];
        SIMP_TAC[]];
      X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(E:real^1->complex) x - Cx(&1) =
                    (E x - Cx(&1)) - ((E:real^1->complex)(vec 0) - Cx(&1))`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
      MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
      ASM_REWRITE_TAC[DROP_VEC] THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(--ii * Cx(&n)) * (E:real^1->complex) y =
                    (--ii * Cx(&n)) * E y - vec 0` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[WANL_PE_EXP_DERIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO;
                  COMPLEX_SUB_RZERO; REAL_SUB_REFL] THEN
  ABBREV_TAC `s = interval[vec 0:real^1,lift(&2 * pi)]` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. Cx((phi:real->real)(drop x)) * (E:real^1->complex) x) integrable_on s /\
    (E:real^1->complex) integrable_on s /\
    (\x. Cx((phi':real->real)(drop x))) integrable_on s /\
    (\x. Cx((phi':real->real)(drop x)) * (E:real^1->complex) x) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[integrable_on] THEN EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\x. Cx((phi':real->real)(drop x)) * (E:real^1->complex) x) =
        (\x. Cx(phi'(drop x)) * (E x - Cx(&1)) + Cx(phi'(drop x)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[integrable_on] THEN EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral s (E:real^1->complex) = Cx(&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN EXPAND_TAC "s" THEN
    MP_TAC(SPEC `n:num` WANL_PE_EXP_INTEGRAL) THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral s (\x. Cx((phi':real->real)(drop x))) = Cx(&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN EXPAND_TAC "s" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. Cx((phi:real->real)(drop x) - phi(&0)) * (--ii * Cx(&n)) *
                    (E:real^1->complex) x) =
    (--ii * Cx(&n)) * integral s (\x. Cx(phi(drop x)) * E x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s (\x. (--ii * Cx(&n)) * (Cx((phi:real->real)(drop x)) *
                                                  (E:real^1->complex) x) -
                                (--ii * Cx(&n) * Cx(phi(&0))) * E x)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; CX_SUB] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_COMPLEX_LMUL; INTEGRABLE_COMPLEX_LMUL; ETA_AX] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. Cx((phi':real->real)(drop x)) * ((E:real^1->complex) x - Cx(&1))) =
    integral s (\x. Cx(phi'(drop x)) * E x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s (\x. Cx((phi':real->real)(drop x)) * (E:real^1->complex) x -
                                Cx(phi'(drop x)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_SUB] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[wanl_pe_fc] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `integral s (\x. Cx((phi:real->real)(drop x) - phi(&0)) * (--ii * Cx(&n)) *
                    (E:real^1->complex) x) +
    integral s (\x. Cx((phi':real->real)(drop x)) * (E x - Cx(&1))) = Cx(&0)` THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `I1 = integral s (\x. Cx((phi:real->real)(drop x)) * (E:real^1->complex) x)` THEN
  ABBREV_TAC `I2 = integral s (\x. Cx((phi':real->real)(drop x)) * (E:real^1->complex) x)` THEN
  CONV_TAC COMPLEX_RING);;

(* Products of the data with continuous maps are integrable.                *)

let WANL_PE_PROD_INTEGRABLE = prove
 (`!(psi:real->real) (g:real^1->complex).
        (\s. lift(psi(drop s))) absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
        g continuous_on interval[vec 0,lift(&2 * pi)]
        ==> (\x. Cx(psi(drop x)) * g x) absolutely_integrable_on
            interval[vec 0,lift(&2 * pi)] /\
            (\x. Cx(psi(drop x)) * g x) integrable_on interval[vec 0,lift(&2 * pi)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `g:real^1->complex`;
                 `\x. Cx((psi:real->real)(drop x))`; `interval[vec 0:real^1,lift(&2 * pi)]`]
         ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL];
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_INTERVAL];
      SUBGOAL_THEN `(\x. Cx((psi:real->real)(drop x))) =
                    (\v. Cx(drop v)) o (\s. lift(psi(drop s)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; COMPLEX_MUL_SYM]]);;

(* The square of a trigonometric polynomial without constant term has      *)
(* integral 0.                                                              *)

let WANL_PE_SQ_INTEGRAL_ZERO = prove
 (`!(c:num->complex) N.
        ((\x. vsum(1..N) (\n. c n * cexp(ii * Cx(drop x)) pow n) *
              vsum(1..N) (\n. c n * cexp(ii * Cx(drop x)) pow n)) has_integral Cx(&0))
        (interval[vec 0,lift(&2 * pi)])`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC `\x. vsum(1..N) (\n. vsum(1..N) (\m. ((c:num->complex) n * c m) *
                                   cexp(ii * Cx(drop x)) pow (n + m)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_COMPLEX_RMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_COMPLEX_LMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&0) = vsum(1..N) (\n. vsum(1..N) (\m:num. Cx(&0)))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Cx(&0) = ((c:num->complex) n * c m) * Cx(&0)` SUBST1_TAC THENL
   [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
  MP_TAC(SPEC `n + m:num` WANL_ANGLE_POW_INTEGRAL) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n + m = 0)`]);;

let WANL_PE_RE_SQ = prove
 (`!z. Re z pow 2 = (norm z pow 2 + Re(z * z)) / &2`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_SQNORM; complex_mul; RE] THEN REAL_ARITH_TAC);;

(* The conjugate coefficient. *)

let WANL_PE_CONJ_COEF = prove
 (`!(psi:real->real) n.
        (\s. lift(psi(drop s))) absolutely_integrable_on interval[vec 0,lift(&2 * pi)]
        ==> ((\x. Cx(psi(drop x)) * cexp(ii * Cx(drop x)) pow n) has_integral
             cnj(wanl_pe_fc psi n)) (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real->real`; `\x. cnj(cexp(ii * Cx(drop x)) pow n)`]
         WANL_PE_PROD_INTEGRABLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[WANL_PE_CNJ_POW] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `x:real^1` THEN
    DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % ((--ii * Cx(&n)) * cexp(--ii * Cx(&n) * Cx(drop x)))` THEN
    REWRITE_TAC[GSYM has_vector_derivative; WANL_PE_EXP_DERIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
  REWRITE_TAC[GSYM wanl_pe_fc] THEN
  DISCH_THEN(MP_TAC o ISPEC `cnj` o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  REWRITE_TAC[LINEAR_CNJ; o_DEF; CNJ_MUL; CNJ_CX; CNJ_CNJ]);;

let WANL_PE_CEXP_CONT = prove
 (`!s. (\x:real^1. cexp(ii * Cx(drop x))) continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^1. cexp(ii * Cx(drop x))) = cexp o (\x. ii * Cx(drop x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
  REWRITE_TAC[CONTINUOUS_ON_ID]);;

(* Bessel's inequality for the coefficients n >= 1.                          *)

let WANL_PE_BESSEL = prove
 (`!(psi:real->real) N.
        (\s. lift(psi(drop s))) absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
        (\s. lift(psi(drop s) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)]
        ==> sum(1..N) (\n. norm(wanl_pe_fc psi n) pow 2) <=
            pi * drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(psi(drop s) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  ABBREV_TAC `c = \n. wanl_pe_fc psi n / Cx pi` THEN
  ABBREV_TAC `p = \x. vsum(1..N) (\n. (c:num->complex) n * cexp(ii * Cx(drop x)) pow n)` THEN
  ABBREV_TAC `S = sum(1..N) (\n. norm((c:num->complex) n) pow 2)` THEN
  SUBGOAL_THEN `!n. norm(wanl_pe_fc psi n) pow 2 = pi pow 2 * norm((c:num->complex) n) pow 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_POW_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_POW_LT; REAL_LT_IMP_NZ;
                 REAL_DIV_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..N) (\n. norm(wanl_pe_fc psi n) pow 2) = pi pow 2 * S` SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[SUM_LMUL]; ALL_TAC] THEN
  ABBREV_TAC `s0 = interval[vec 0:real^1,lift(&2 * pi)]` THEN
  SUBGOAL_THEN `(p:real^1->complex) continuous_on s0` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN REWRITE_TAC[WANL_PE_CEXP_CONT];
    ALL_TAC] THEN
  (* Parseval for p and the integral of p^2 *)
  SUBGOAL_THEN `((\x. lift(norm((p:real^1->complex) x) pow 2)) has_integral
                 lift(&2 * pi * S)) s0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "s0"; "S"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WANL_FINITE_PARSEVAL THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift(Re((p:real^1->complex) x * p x))) has_integral vec 0) s0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:num->complex`; `N:num`] WANL_PE_SQ_INTEGRAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `\z:complex. lift(Re z)` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; RE_CX; LIFT_NUM] THEN ANTS_TAC THENL
     [REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
    EXPAND_TAC "p" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* the integral of (Re p)^2 *)
  SUBGOAL_THEN `((\x. lift(Re((p:real^1->complex) x) pow 2)) has_integral lift(pi * S)) s0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. inv(&2) % (lift(norm((p:real^1->complex) x) pow 2) +
                               lift(Re(p x * p x)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[WANL_PE_RE_SQ] THEN
      REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lift(pi * S) = inv(&2) % (lift(&2 * pi * S) + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the integral of psi Re p *)
  SUBGOAL_THEN `((\x. Cx(psi(drop x)) * (p:real^1->complex) x) has_integral Cx(pi * S)) s0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. vsum(1..N) (\n. (c:num->complex) n *
                                   (Cx(psi(drop x)) * cexp(ii * Cx(drop x)) pow n))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN EXPAND_TAC "p" THEN REWRITE_TAC[] THEN
      SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_COMPLEX_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `Cx(pi * S) = vsum(1..N) (\n. (c:num->complex) n * cnj(wanl_pe_fc psi n))`
    SUBST1_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `wanl_pe_fc psi n = Cx pi * (c:num->complex) n` SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(Cx pi = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      REWRITE_TAC[CNJ_MUL; CNJ_CX] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * (a * c)`] THEN
      REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; GSYM CX_MUL];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN EXPAND_TAC "s0" THEN
    MATCH_MP_TAC WANL_PE_CONJ_COEF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift(psi(drop x) * Re((p:real^1->complex) x))) has_integral
                 lift(pi * S)) s0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o ISPEC `\z:complex. lift(Re z)` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; RE_CX; RE_MUL_CX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  (* positivity of the integral of (psi - Re p)^2 *)
  ABBREV_TAC `Ip = drop(integral s0 (\x. lift(psi(drop x) pow 2)))` THEN
  SUBGOAL_THEN `((\x. lift(psi(drop x) pow 2)) has_integral lift Ip) s0` ASSUME_TAC THENL
   [EXPAND_TAC "Ip" THEN REWRITE_TAC[LIFT_DROP; GSYM HAS_INTEGRAL_INTEGRAL] THEN
    EXPAND_TAC "s0" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift((psi(drop x) - Re((p:real^1->complex) x)) pow 2)) has_integral
                 lift(Ip - pi * S)) s0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. (lift(psi(drop x) pow 2) -
                     &2 % lift(psi(drop x) * Re((p:real^1->complex) x))) +
                    lift(Re(p x) pow 2)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lift(Ip - pi * S) = (lift Ip - &2 % lift(pi * S)) + lift(pi * S)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_SIMP_TAC[HAS_INTEGRAL_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Ip - pi * S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift((psi(drop x) - Re((p:real^1->complex) x)) pow 2)`;
                   `s0:real^1->bool`; `lift(Ip - pi * S)`] HAS_INTEGRAL_DROP_POS) THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Truncation of the Poisson kernel,                                        *)
(* P(w,s) = Re((1+q)/(1-q)) = 1 + 2 sum_n Re(q^n) with q = w e^(-is), and    *)
(* the harmonic polynomials u_N built from the Fourier coefficients: they    *)
(* are within 2 M s^(N+1)/(1-s) of the Poisson integral where |w| <= s.     *)
(* ========================================================================= *)

let WANL_PE_KERNEL_TRUNC = prove
 (`!w s N. norm w < &1
           ==> abs(wanl_poisson_kernel w s -
                   (&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx s))) pow n)))) <=
               &2 * norm w pow (N + 1) / (&1 - norm w)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WANL_POISSON_KERNEL_RE_FORM] THEN
  ABBREV_TAC `u = cexp(ii * Cx s)` THEN
  SUBGOAL_THEN `norm(u:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  ABBREV_TAC `q = w * cnj(u:complex)` THEN
  SUBGOAL_THEN `norm(q:complex) = norm(w:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `u * cnj(u:complex) = Cx(&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&1) - q = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(q:complex) = norm(w:complex)` THEN
    SUBGOAL_THEN `q = Cx(&1)` SUBST1_TAC THENL
     [UNDISCH_TAC `Cx(&1) - q = Cx(&0)` THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u / (u - w) = Cx(&1) / (Cx(&1) - q)` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN `~(u = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(u:complex) = &1` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~(Cx(&1) - q = Cx(&0))` THEN EXPAND_TAC "q" THEN
    UNDISCH_TAC `u * cnj(u:complex) = Cx(&1)` THEN UNDISCH_TAC `~(u = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&1) / (Cx(&1) - q) = vsum(0..N) (\n. q pow n) + q pow (N + 1) / (Cx(&1) - q)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`q:complex`; `N:num`] VSUM_GP_BASIC) THEN
    REWRITE_TAC[ADD1] THEN
    ABBREV_TAC `V = vsum(0..N) (\n. (q:complex) pow n)` THEN
    UNDISCH_TAC `~(Cx(&1) - q = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[RE_ADD; RE_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; complex_pow; RE_CX; ADD_CLAUSES] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= b ==> abs(&2 * ((&1 + s) + x) - &1 - (&1 + &2 * s)) <= &2 * b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(q pow (N + 1) / (Cx(&1) - q))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(NORM_ARITH `norm(Cx(&1)) - norm(q:complex) <= norm(Cx(&1) - q)`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC);;

let WANL_PE_RE_INTEGRAL = prove
 (`!(Fz:real^1->complex) s.
        Fz integrable_on s ==> Re(integral s Fz) = drop(integral s (\x. lift(Re(Fz x))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fz:real^1->complex`; `s:real^1->bool`; `\z:complex. lift(Re z)`]
         INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]]);;

(* The harmonic polynomial u_N of the data phi. *)

let wanl_pe_poly = new_definition
 `wanl_pe_poly (phi:real->real) N (a:real^2) r (x:real^2) =
    Re(Cx(inv(&2 * pi)) * wanl_pe_fc phi 0 +
       vsum(1..N) (\n. Cx(inv pi) * wanl_pe_fc phi n * (inv r % (x - a)) pow n))`;;

let WANL_PE_POLY_INTEGRAL = prove
 (`!(phi:real->real) N (a:real^2) r x.
        (\s. lift(phi(drop s))) continuous_on interval[vec 0,lift(&2 * pi)]
        ==> wanl_pe_poly phi N a r x =
            inv(&2 * pi) *
            drop(integral (interval[vec 0,lift(&2 * pi)])
                   (\s. lift((&1 + &2 * sum(1..N)
                                (\n. Re((inv r % (x - a) * cnj(cexp(ii * Cx(drop s))))
                                        pow n))) * phi(drop s))))`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `w:complex = inv r % (x - a)` THEN
  ABBREV_TAC `s0 = interval[vec 0:real^1,lift(&2 * pi)]` THEN
  SUBGOAL_THEN
   `!n. ((\s. Cx((phi:real->real)(drop s)) * cnj(cexp(ii * Cx(drop s)) pow n))
         has_integral wanl_pe_fc phi n) s0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wanl_pe_fc] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    EXPAND_TAC "s0" THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[LINEAR_CNJ] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN REWRITE_TAC[WANL_PE_CEXP_CONT];
    ALL_TAC] THEN
  ABBREV_TAC
   `Kf = \s. Cx((phi:real->real)(drop s)) * cnj(cexp(ii * Cx(drop s)) pow 0) +
             vsum(1..N) (\n. (Cx(&2) * w pow n) *
                             (Cx(phi(drop s)) * cnj(cexp(ii * Cx(drop s)) pow n)))` THEN
  SUBGOAL_THEN
   `((Kf:real^1->complex) has_integral
     (wanl_pe_fc phi 0 + vsum(1..N) (\n. (Cx(&2) * w pow n) * wanl_pe_fc phi n))) s0`
  ASSUME_TAC THENL
   [EXPAND_TAC "Kf" THEN MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. lift((&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n))) *
              (phi:real->real)(drop s))) =
    (\s. lift(Re((Kf:real^1->complex) s)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Kf" THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real^1` THEN AP_TERM_TAC THEN
    REWRITE_TAC[complex_pow; RE_ADD; COMPLEX_MUL_RID; CNJ_CX] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN REWRITE_TAC[RE_CX; CNJ_POW] THEN
    SUBGOAL_THEN
     `!k. Re((Cx(&2) * w pow k) * Cx((phi:real->real)(drop t)) *
             cnj(cexp(ii * Cx(drop t))) pow k) =
          (&2 * phi(drop t)) * Re((w * cnj(cexp(ii * Cx(drop t)))) pow k)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[COMPLEX_POW_MUL] THEN
      REWRITE_TAC[COMPLEX_RING `(Cx(&2) * a) * Cx p * b = Cx(&2) * (Cx p * (a * b))`;
                  RE_MUL_CX] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN
    ABBREV_TAC `SR = sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop t)))) pow n))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Kf:real^1->complex`; `s0:real^1->bool`] WANL_PE_RE_INTEGRAL) THEN
  ANTS_TAC THENL [REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[wanl_pe_poly] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM RE_MUL_CX] THEN AP_TERM_TAC THEN
  SIMP_TAC[COMPLEX_ADD_LDISTRIB; FINITE_NUMSEG; GSYM VSUM_COMPLEX_LMUL] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[CX_INV; CX_MUL] THEN
  SUBGOAL_THEN `~(Cx pi = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC; CONV_TAC COMPLEX_FIELD]);;

(* The truncated kernel is continuous. *)

let WANL_PE_PN_CONT = prove
 (`!(w:complex) N.
        (\s. lift(&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n))))
        continuous_on (:real^1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[RE_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[LINEAR_CNJ; WANL_PE_CEXP_CONT]);;

(* The components of the Poisson integral of the circle data, as real       *)
(* integrals.                                                               *)

let WANL_PE_DSOL_INTEGRAL = prove
 (`!(a:real^2) r (f:real->real^K) f' x j.
        &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
        (!t. t IN real_interval[&0,&2 * pi]
             ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
        x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
        ==> (wanl_dsol a r (\x. f(Arg(x - a))) x)$j =
            inv(&2 * pi) *
            drop(integral (interval[vec 0,lift(&2 * pi)])
                   (\s. lift(wanl_poisson_kernel (inv r % (x - a)) (drop s) * f(drop s)$j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`]
         WANL_PE_BOUNDARY)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(inv r % (x - a):complex) < &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `r:real`; `x:real^2`] WANL_UNIT_SCALE) THEN
    ASM_REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w:complex = inv r % (x - a)` THEN
  ASM_SIMP_TAC[wanl_dsol; LAMBDA_BETA; wanl_poisson_integral; RE_MUL_CX] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)])
                (\s. lift(Re(Cx(wanl_poisson_kernel w (drop s)) *
                             Cx((f:real->real^K)(drop s)$j)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_PE_RE_INTEGRAL THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      ASM_SIMP_TAC[WANL_POISSON_KERNEL_CONTINUOUS; SUBSET_UNIV];
      REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
      MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`] WANL_PE_DATA_CONT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o INST [`j:num`,`i:num`] o MATCH_MP CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE) THEN
      REWRITE_TAC[o_THM]];
    REWRITE_TAC[RE_CX; GSYM CX_MUL]]);;

(* A bound for integrals of products on [0,2pi]. *)

let WANL_PE_INT_BOUND = prove
 (`!(g:real^1->real) h B M.
        (\s. lift(g s)) continuous_on interval[vec 0,lift(&2 * pi)] /\
        (\s. lift(h s)) continuous_on interval[vec 0,lift(&2 * pi)] /\
        (!s. s IN interval[vec 0,lift(&2 * pi)] ==> abs(g s) <= B /\ abs(h s) <= M)
        ==> abs(drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(g s * h s))))
            <= &2 * pi * (B * M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)]) (\s:real^1. lift(B * M)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REWRITE_TAC[INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]];
    REWRITE_TAC[INTEGRAL_CONST] THEN
    ASM_SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; DROP_CMUL] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN REAL_ARITH_TAC]);;

(* The harmonic polynomials approximate the Poisson integral inside.        *)

let WANL_PE_APPROX = prove
 (`!(a:real^2) r (f:real->real^K) f' x j N s0 M.
        &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
        (!t. t IN real_interval[&0,&2 * pi]
             ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
        x IN ball(a,r) /\ norm(inv r % (x - a)) <= s0 /\ s0 < &1 /\
        1 <= j /\ j <= dimindex(:K) /\
        (!t. t IN real_interval[&0,&2 * pi] ==> abs(f t$j) <= M)
        ==> abs((wanl_dsol a r (\x. f(Arg(x - a))) x)$j - wanl_pe_poly (\t. f t$j) N a r x)
            <= M * &2 * s0 pow (N + 1) / (&1 - s0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(\s. lift((f:real->real^K)(drop s)$j)) continuous_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`] WANL_PE_DATA_CONT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o INST [`j:num`,`i:num`] o MATCH_MP CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE) THEN
    REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (f:real->real^K) t$j`; `N:num`; `a:real^2`; `r:real`; `x:real^2`]
         WANL_PE_POLY_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`; `x:real^2`;
                 `j:num`] WANL_PE_DSOL_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `norm(inv r % (x - a):complex) < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w:complex = inv r % (x - a)` THEN
  SUBGOAL_THEN `(\s. lift(wanl_poisson_kernel w (drop s))) continuous_on
                interval[vec 0,lift(&2 * pi)] /\
                (\s. lift(&1 + &2 * sum(1..N)
                       (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))) continuous_on
                interval[vec 0,lift(&2 * pi)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV; WANL_PE_PN_CONT] THEN
    REWRITE_TAC[GSYM CONTINUOUS_ON_CX_LIFT] THEN
    ASM_SIMP_TAC[WANL_POISSON_KERNEL_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM DROP_SUB] THEN
  W(fun (asl,w) -> let t = find_term (fun u -> is_comb u &&
      (try fst(dest_const(rator(rator u))) = "vector_sub" with _ -> false) &&
      (try fst(dest_const(fst(strip_comb(rand(rator u))))) = "integral" with _ -> false)) w in
      SUBGOAL_THEN (mk_eq(t, `integral (interval[vec 0,lift(&2 * pi)])
         (\s. lift((wanl_poisson_kernel w (drop s) -
                    (&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))) *
                   (f:real->real^K)(drop s)$j))`)) SUBST1_TAC) THENL
   [REWRITE_TAC[REAL_SUB_RDISTRIB; LIFT_SUB] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:real->real^K)(&0)$j)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bw = &2 * norm(w:complex) pow (N + 1) / (&1 - norm w)` THEN
  SUBGOAL_THEN `Bw <= &2 * s0 pow (N + 1) / (&1 - s0)` ASSUME_TAC THENL
   [EXPAND_TAC "Bw" THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. wanl_poisson_kernel w (drop s) -
         (&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))`;
    `\s. (f:real->real^K)(drop s)$j`; `Bw:real`; `M:real`] WANL_PE_INT_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [EXPAND_TAC "Bw" THEN MATCH_MP_TAC WANL_PE_KERNEL_TRUNC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(inv(&2 * pi)) = inv(&2 * pi) /\ &0 < &2 * pi` STRIP_ASSUME_TAC THENL
   [MP_TAC PI_POS THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN MATCH_MP_TAC REAL_LE_INV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * pi) * (&2 * pi * (Bw * M))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * pi) * (&2 * pi * (Bw * M)) = M * Bw` SUBST1_TAC THENL
   [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The energy of the harmonic polynomials u_N.  By polar                    *)
(* coordinates (FUBINI_POLAR) and finite Parseval on circles,               *)
(* int_{B(0,rho)} |sum_n d_n y^(n-1)|^2 = pi sum_n |d_n|^2 rho^(2n) / n,     *)
(* so E_rho(u_N) <= (1/pi) sum_n n |fc phi n|^2 for rho <= r.                *)
(* ========================================================================= *)

let WANL_PE_POW_INTEGRAL = prove
 (`!m R. &0 <= R
         ==> ((\t. lift(drop t pow m)) has_integral lift(R pow (m + 1) / &(m + 1)))
             (interval[vec 0,lift R])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. t pow (m + 1) / &(m + 1)`; `\t:real. t pow m`; `&0`; `R:real`]
         REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    REAL_DIFF_TAC THEN REWRITE_TAC[ADD_SUB] THEN
    SUBGOAL_THEN `~(&(m + 1) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL; o_DEF; LIFT_NUM] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH_RULE `~(m + 1 = 0)`; real_div; REAL_MUL_LZERO;
              REAL_SUB_RZERO] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP]);;

let WANL_PE_DISC_PARSEVAL = prove
 (`!(d:num->complex) N rho.
        &0 < rho
        ==> drop(integral (ball(Cx(&0),rho))
                   (\y. lift(norm(vsum(1..N) (\n. d n * y pow (n - 1))) pow 2))) =
            pi * sum(1..N) (\n. norm(d n) pow 2 * rho pow (2 * n) / &n)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = \y:complex. vsum(1..N) (\n. (d:num->complex) n * y pow (n - 1))` THEN
  SUBGOAL_THEN
   `(\y. lift(norm(vsum(1..N) (\n. (d:num->complex) n * y pow (n - 1))) pow 2)) =
    (\y. lift(norm((P:complex->complex) y) pow 2))`
  SUBST1_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:complex->complex) continuous_on (:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN REWRITE_TAC[CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(norm((P:complex->complex) y) pow 2)) continuous_on (:complex)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(norm((P:complex->complex) y) pow 2)) absolutely_integrable_on
                ball(Cx(&0),rho)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y. lift(norm((P:complex->complex) y) pow 2)`; `Cx(&0)`; `rho:real`]
           WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\y. if y IN ball(Cx(&0),rho) then lift(norm((P:complex->complex) y) pow 2)
                    else vec 0` FUBINI_POLAR) THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
  ABBREV_TAC `Fp = \t. &2 * pi * sum(1..N) (\n. norm((d:num->complex) n) pow 2 *
                                               t pow (2 * n - 1))` THEN
  (* the inner integrals *)
  SUBGOAL_THEN
   `!r. r IN {r | &0 <= drop r}
        ==> integral (interval[vec 0,lift(&2 * pi)])
              (\t. drop r % (if Cx(drop r) * cexp(ii * Cx(drop t)) IN ball(Cx(&0),rho)
                             then lift(norm((P:complex->complex)
                                              (Cx(drop r) * cexp(ii * Cx(drop t)))) pow 2)
                             else vec 0)) =
            (\r. if r IN {r | drop r < rho} then lift((Fp:real->real)(drop r)) else vec 0) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ABBREV_TAC `t = drop r` THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_BALL_0; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_CASES_TAC `t < rho` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; INTEGRAL_0] THEN
    SUBGOAL_THEN
     `!th. norm((P:complex->complex)(Cx t * cexp(ii * Cx th))) pow 2 =
           norm(vsum(1..N) (\n. ((d:num->complex) n * Cx t pow (n - 1)) *
                                cexp(ii * Cx th) pow n)) pow 2`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "P" THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `norm(cexp(ii * Cx th) *
                       vsum(1..N) (\n. (d:num->complex) n * (Cx t * cexp(ii * Cx th)) pow (n - 1)))` THEN
      CONJ_TAC THENL [REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID]; ALL_TAC] THEN
      AP_TERM_TAC THEN SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_COMPLEX_LMUL] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
      STRIP_TAC THEN REWRITE_TAC[COMPLEX_POW_MUL] THEN
      SUBGOAL_THEN `cexp(ii * Cx th) pow n = cexp(ii * Cx th) pow (n - 1) * cexp(ii * Cx th)`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`cexp(ii * Cx th)`; `n - 1`; `1`] COMPLEX_POW_ADD) THEN
        ASM_SIMP_TAC[SUB_ADD; COMPLEX_POW_1];
        CONV_TAC COMPLEX_RING];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `lift((Fp:real->real) t) =
      t % lift(&2 * pi * sum(1..N) (\n. norm((d:num->complex) n * Cx t pow (n - 1)) pow 2))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fp" THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      SUBGOAL_THEN `2 * n - 1 = (n - 1) * 2 + 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_POW; REAL_POW_1; REAL_POW_MUL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL [`\n. (d:num->complex) n * Cx t pow (n - 1)`; `1..N`]
                                    WANL_FINITE_PARSEVAL)) THEN
      REWRITE_TAC[FINITE_NUMSEG]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRAL_EQ) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
  MATCH_MP_TAC(MESON[LIFT_DROP] `integral s (f:real^1->real^1) = lift y ==> drop(integral s f) = y`) THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET THEN EXISTS_TAC `interval[vec 0:real^1,lift rho]` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{lift rho}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC;
                LIFT_DROP; IN_SING] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. lift((Fp:real->real)(drop r))) =
    (\r. vsum(1..N) (\n. (&2 * pi * norm((d:num->complex) n) pow 2) %
                         lift(drop r pow (2 * n - 1))))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fp" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL; LIFT_DROP] THEN
    SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[GSYM SUM_LMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lift(pi * sum(1..N) (\n. norm((d:num->complex) n) pow 2 * rho pow (2 * n) / &n)) =
    vsum(1..N) (\n. (&2 * pi * norm(d n) pow 2) %
                    lift(rho pow ((2 * n - 1) + 1) / &((2 * n - 1) + 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(2 * n - 1) + 1 = 2 * n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN MATCH_MP_TAC WANL_PE_POW_INTEGRAL THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The energy of the harmonic polynomials.  With                            *)
(* u_N = Re Q_N and Q_N(z) = c_0 + sum_n c_n (z - a)^n / r^n, the partials *)
(* of u_N are Re Q_N' and -Im Q_N', so the energy on ball(a,rho) is the     *)
(* integral of |Q_N'|^2, computed by WANL_PE_DISC_PARSEVAL.  With           *)
(* n |c_n|^2 <= n^2 |c_n|^2 = |c_n(phi')|^2 / pi^2 and Bessel the energy is *)
(* at most the integral of phi'^2 (WANL_PE_POLY_ENERGY).                    *)
(* ========================================================================= *)

let WANL_PE_RE_DPART = prove
 (`!(Q:complex->complex) c x.
     (Q has_complex_derivative c) (at x)
     ==> wan_dpart 1 (\y. Re(Q y)) x = Re c /\
         wan_dpart 2 (\y. Re(Q y)) x = --Im c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(Re((Q:complex->complex) y))) has_derivative (\h. lift(Re(c * h)))) (at x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift(Re((Q:complex->complex) y))) = (\z. lift(Re z)) o Q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h. lift(Re(c * h))) = (\z. lift(Re z)) o (\h. c * h)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[wan_dpart] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP; COMPLEX_BASIS; COMPLEX_MUL_RID; RE_MUL_II]);;

let WANL_PE_POLY_DERIV = prove
 (`!(phi:real->real) N (a:complex) r z.
     ((\x. Cx(inv(&2 * pi)) * wanl_pe_fc phi 0 +
           vsum(1..N) (\n. Cx(inv pi) * wanl_pe_fc phi n * (inv r % (x - a)) pow n))
      has_complex_derivative
      vsum(1..N) (\n. (Cx(&n) * Cx(inv pi) * wanl_pe_fc phi n * Cx(inv r) pow n) *
                      (z - a) pow (n - 1))) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_CMUL] THEN
  MATCH_MP_TAC(MESON[COMPLEX_ADD_LID]
   `(f has_complex_derivative (Cx(&0) + d)) net ==> (f has_complex_derivative d) net`) THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  COMPLEX_DIFF_TAC THEN
  SUBGOAL_THEN `!w:complex. w pow n = w pow (n - 1) * w` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `n = SUC(n - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[complex_pow; COMPLEX_MUL_SYM]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_POW_MUL] THEN CONV_TAC COMPLEX_RING);;

let WANL_PE_POLY_SMOOTH = prove
 (`!(phi:real->real) N (a:real^2) r.
     smooth_map_on (:real^2) (\x. lift(wanl_pe_poly phi N a r x)) /\
     (!x. llap (\y:real^2. mat 1) (wanl_pe_poly phi N a r) x = &0)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Q = \x:complex. Cx(inv(&2 * pi)) * wanl_pe_fc phi 0 +
                   vsum(1..N) (\n. Cx(inv pi) * wanl_pe_fc phi n * (inv r % (x - a)) pow n)` THEN
  SUBGOAL_THEN `wanl_pe_poly phi N a r = (\y. Re((Q:complex->complex) y))` SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[FUN_EQ_THM; wanl_pe_poly]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:complex->complex) holomorphic_on (:complex)` ASSUME_TAC THENL
   [SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `z:complex` THEN
    EXPAND_TAC "Q" THEN
    EXISTS_TAC `vsum(1..N) (\n. (Cx(&n) * Cx(inv pi) * wanl_pe_fc phi n * Cx(inv r) pow n) *
                                (z - a) pow (n - 1))` THEN
    REWRITE_TAC[WANL_PE_POLY_DERIV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. lift((\y. Re((Q:complex->complex) y)) x)) = (\z. lift(Re z)) o Q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[OPEN_UNIV; WANL_HOLOMORPHIC_SMOOTH] THEN
    REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    GEN_TAC THEN MATCH_MP_TAC WANL_RE_HOLOMORPHIC_HARMONIC THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]]);;

let WANL_PE_POLY_ENERGY_EQ = prove
 (`!(phi:real->real) N (a:real^2) r rho.
     &0 < rho
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(wan_dpart i (wanl_pe_poly phi N a r) x pow 2)))) =
         pi * sum(1..N) (\n. norm(Cx(&n) * Cx(inv pi) * wanl_pe_fc phi n * Cx(inv r) pow n)
                             pow 2 * rho pow (2 * n) / &n)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = \x:complex. Cx(inv(&2 * pi)) * wanl_pe_fc phi 0 +
                   vsum(1..N) (\n. Cx(inv pi) * wanl_pe_fc phi n * (inv r % (x - a)) pow n)` THEN
  ABBREV_TAC `dd = \n. Cx(&n) * Cx(inv pi) * wanl_pe_fc phi n * Cx(inv r) pow n` THEN
  ABBREV_TAC `D = \z:complex. vsum(1..N) (\n. (dd:num->complex) n * (z - a) pow (n - 1))` THEN
  SUBGOAL_THEN `wanl_pe_poly phi N a r = (\y. Re((Q:complex->complex) y))` SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[FUN_EQ_THM; wanl_pe_poly]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. ((Q:complex->complex) has_complex_derivative (D:complex->complex) x) (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["Q"; "D"; "dd"] THEN REWRITE_TAC[WANL_PE_POLY_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. wan_dpart 1 (\y. Re((Q:complex->complex) y)) x = Re((D:complex->complex) x) /\
        wan_dpart 2 (\y. Re(Q y)) x = --Im(D x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WANL_PE_RE_DPART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_2; SUM_2; REAL_POW_NEG; ARITH] THEN
  SUBGOAL_THEN `(D:complex->complex) continuous_on (:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(Re((D:complex->complex) x) pow 2)) integrable_on ball(a,rho) /\
    (\x. lift(Im((D:complex->complex) x) pow 2)) integrable_on ball(a,rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
     `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[RE_DEF; IM_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_ADD] THEN ASM_SIMP_TAC[GSYM INTEGRAL_ADD] THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM COMPLEX_SQNORM] THEN
  SUBGOAL_THEN `ball(a:complex,rho) = IMAGE (\x. a + x) (ball(Cx(&0),rho))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM BALL_TRANSLATION; COMPLEX_ADD_RID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INTEGRAL_TRANSLATION] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((D:complex->complex)(a + x)) pow 2)) =
    (\y. lift(norm(vsum(1..N) (\n. (dd:num->complex) n * y pow (n - 1))) pow 2))`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[FUN_EQ_THM; COMPLEX_RING `(a + x) - a:complex = x`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WANL_PE_DISC_PARSEVAL] THEN EXPAND_TAC "dd" THEN REWRITE_TAC[]);;

let WANL_PE_POLY_ENERGY = prove
 (`!(phi:real->real) phi' N (a:real^2) r rho.
     (!t. phi(t + &2 * pi) = phi t) /\
     (\s. lift(phi'(drop s))) absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
     (\s. lift(phi'(drop s) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. lift(phi'(drop s))) has_integral lift(phi t - phi(&0)))
              (interval[vec 0,lift t])) /\
     &0 < rho /\ rho <= r
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(wan_dpart i (wanl_pe_poly phi N a r) x pow 2)))) <=
         drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(phi'(drop s) pow 2)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WANL_PE_POLY_ENERGY_EQ] THEN
  MP_TAC(ISPECL [`phi':real->real`; `N:num`] WANL_PE_BESSEL) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Ip = drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(phi'(drop s) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r /\ &0 < pi` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv pi * sum(1..N) (\n. norm(wanl_pe_fc phi' n) pow 2)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv pi * (pi * Ip)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL]]] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:real->real`; `phi':real->real`; `n:num`] WANL_PE_FC_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX; COMPLEX_NORM_POW;
              REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `rho pow (2 * n) = (rho pow n) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv r pow n * rho pow n /\ inv r pow n * rho pow n <= &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_1_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `Xr = inv r pow n` THEN ABBREV_TAC `Yr = rho pow n` THEN
  ABBREV_TAC `Fn = norm(wanl_pe_fc phi n)` THEN
  SUBGOAL_THEN `~(pi = &0) /\ ~(&n = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `pi * ((&n * inv pi * Fn * Xr) pow 2 * Yr pow 2 / &n) =
    (inv pi * Fn pow 2) * (&n * (Xr * Yr) pow 2) /\
    inv pi * (&1 * &n * Fn) pow 2 = (inv pi * Fn pow 2) * &n pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [UNDISCH_TAC `~(pi = &0)` THEN UNDISCH_TAC `~(&n = &0)` THEN
                    CONV_TAC REAL_FIELD; CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Xr * Yr) pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_PE_DATA_COMPONENT = prove
 (`!(f:real->real^K) f' j.
     (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     1 <= j /\ j <= dimindex(:K)
     ==> (!t. f(t + &2 * pi)$j = f t$j) /\
         (\s. lift(f'(drop s)$j)) absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
         (\s. lift(f'(drop s)$j pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
         (!t. t IN real_interval[&0,&2 * pi]
              ==> ((\s. lift(f'(drop s)$j)) has_integral lift(f t$j - f(&0)$j))
                  (interval[vec 0,lift t]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&2 * pi]
        ==> ((\s. lift((f':real->real^K)(drop s)$j)) has_integral lift((f:real->real^K) t$j - f(&0)$j))
            (interval[vec 0,lift t])`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o ONCE_REWRITE_RULE[HAS_INTEGRAL_COMPONENTWISE]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\s. lift((f':real->real^K)(drop s)$j)) measurable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `lift((f:real->real^K)(&2 * pi)$j - f(&0)$j)` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\t. lift(&1) + lift(norm((f':real->real^K)(drop t)) pow 2)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_ADD; LIFT_DROP] THEN
      MP_TAC(ISPECL [`(f':real->real^K)(drop s)`; `j:num`] COMPONENT_LE_NORM) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `norm((f':real->real^K)(drop s))` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `norm((f':real->real^K)(drop s)) - &1` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t. lift(norm((f':real->real^K)(drop t)) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS; COMPONENT_LE_NORM]);;

let WANL_PE_INTEGRAL_SUM = prove
 (`!(g:num->real^N->real) k s.
     FINITE k /\ (!j. j IN k ==> (\x. lift(g j x)) integrable_on s)
     ==> drop(integral s (\x. lift(sum k (\j. g j x)))) =
         sum k (\j. drop(integral s (\x. lift(g j x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  ASM_SIMP_TAC[INTEGRAL_VSUM; DROP_VSUM; o_DEF]);;

let wanl_pe_vpoly = new_definition
 `wanl_pe_vpoly (f:real->real^K) N (a:real^2) r (x:real^2) =
    (lambda j. wanl_pe_poly (\t. f t$j) N a r x):real^K`;;

let WANL_PE_VPOLY_COMPONENT = prove
 (`!(f:real->real^K) N (a:real^2) r j.
     1 <= j /\ j <= dimindex(:K)
     ==> (\y. wanl_pe_vpoly f N a r y$j) = wanl_pe_poly (\t. f t$j) N a r`,
  SIMP_TAC[FUN_EQ_THM; wanl_pe_vpoly; LAMBDA_BETA]);;

let WANL_PE_VPOLY_SMOOTH = prove
 (`!(f:real->real^K) N (a:real^2) r.
     smooth_map_on (:real^2) (wanl_pe_vpoly f N a r) /\
     (!x j. 1 <= j /\ j <= dimindex(:K)
            ==> llap (\y:real^2. mat 1) (\y. wanl_pe_vpoly f N a r y$j) x = &0)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `wanl_pe_vpoly (f:real->real^K) N a r`]
           SMOOTH_MAP_ON_COMPONENTWISE) THEN
    REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[wanl_pe_vpoly; LAMBDA_BETA; WANL_PE_POLY_SMOOTH];
    SIMP_TAC[WANL_PE_VPOLY_COMPONENT; WANL_PE_POLY_SMOOTH]]);;

let WANL_PE_VPOLY_ENERGY = prove
 (`!(f:real->real^K) f' N (a:real^2) r rho.
     (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     &0 < rho /\ rho <= r
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (wanl_pe_vpoly f N a r) x) pow 2)))) <=
         drop(integral (interval[vec 0,lift(&2 * pi)]) (\t. lift(norm(f'(drop t)) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real^K`; `N:num`; `a:real^2`; `r:real`] WANL_PE_VPOLY_SMOOTH) THEN
  ABBREV_TAC `V = wanl_pe_vpoly (f:real->real^K) N a r` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i x. norm(partial_derivative i (V:real^2->real^K) x) pow 2 =
          sum(1..dimindex(:K))
             (\j. wan_dpart i (wanl_pe_poly (\t. (f:real->real^K) t$j) N a r) x pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`V:real^2->real^K`; `x:real^2`; `i:num`; `j:num`] WANL_DPART_COMPONENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "V" THEN ASM_SIMP_TAC[WANL_PE_VPOLY_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:2)
          ==> (\x. lift(wan_dpart i (wanl_pe_poly (\t. (f:real->real^K) t$j) N a r) x pow 2))
              integrable_on ball(a,rho)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
     `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`(:real^2)`; `wanl_pe_poly (\t. (f:real->real^K) t$j) N a r`; `i:num`;
                   `vec 0:real^2`] WANL_DPART_HARMONIC) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; WANL_PE_POLY_SMOOTH] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:K))
      (\j. drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\s. lift((f':real->real^K)(drop s)$j pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a b c:real. a = b /\ b <= c ==> a <= c`) THEN
    EXISTS_TAC
     `sum(1..dimindex(:2))
        (\i. sum(1..dimindex(:K))
           (\j. drop(integral (ball(a,rho))
                  (\x. lift(wan_dpart i (wanl_pe_poly (\t. (f:real->real^K) t$j) N a r) x
                            pow 2)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC WANL_PE_INTEGRAL_SUM THEN ASM_SIMP_TAC[FINITE_NUMSEG];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`; `j:num`] WANL_PE_DATA_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\t. (f:real->real^K) t$j`; `\t. (f':real->real^K) t$j`; `N:num`;
                             `a:real^2`; `r:real`; `rho:real`] WANL_PE_POLY_ENERGY)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN
   `(\t. lift(norm((f':real->real^K)(drop t)) pow 2)) =
    (\t. lift(sum(1..dimindex(:K)) (\j. f'(drop t)$j pow 2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; NORM_POW_2; dot; REAL_POW_2]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WANL_PE_INTEGRAL_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`; `j:num`] WANL_PE_DATA_COMPONENT) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The energy of the Poisson integral of the boundary data on               *)
(* the smaller discs ball(a,rho), rho < r.  The polynomials V_N approximate *)
(* h uniformly near cball(a,rho), so their gradients converge uniformly on  *)
(* ball(a,rho) (WANL_DD_GRAD_CLOSE); the energy of V_N is at most the       *)
(* integral of |f'|^2, and an epsilon argument gives the same bound for h.  *)
(* ========================================================================= *)

let WANL_PE_SQ_PERTURB1 = prove
 (`!x y d. abs(x - y) <= d ==> x pow 2 <= (&1 + d) * y pow 2 + (d + d pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d /\ abs x <= abs y + d` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 <= (abs y + d) pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * abs y <= y pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `abs y - &1` REAL_LE_POW_2) THEN MP_TAC(SPEC `y:real` REAL_POW2_ABS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d * (&2 * abs y) <= d * (y pow 2 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `y:real` REAL_POW2_ABS) THEN
  UNDISCH_TAC `x pow 2 <= (abs y + d) pow 2` THEN UNDISCH_TAC `d * (&2 * abs y) <= d * (y pow 2 + &1)` THEN
  REAL_ARITH_TAC);;

let WANL_PE_SQ_PERTURB = prove
 (`!(u:real^K) v delta.
     (!j. 1 <= j /\ j <= dimindex(:K) ==> abs((u - v)$j) <= delta)
     ==> norm(u) pow 2 <=
         (&1 + delta) * norm(v) pow 2 + &(dimindex(:K)) * (delta + delta pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBGOAL_THEN
   `&(dimindex(:K)) * (delta + delta pow 2) =
    sum(1..dimindex(:K)) (\j. delta + delta pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
  MATCH_MP_TAC WANL_PE_SQ_PERTURB1 THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT]);;

let WANL_PE_EPS_LE = prove
 (`!S E A. (!e. &0 < e /\ e <= &1 ==> S <= E + e * A) ==> S <= E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `A <= &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e = min (&1) ((S - E) / (&2 * A))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 /\ e * A <= (S - E) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(S - E) / (&2 * A) * A` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let WANL_PE_INT_PERTURB = prove
 (`!(s:real^N->bool) (p:real^N->real) q A B.
     measurable s /\ (\x. lift(p x)) integrable_on s /\ (\x. lift(q x)) integrable_on s /\
     (!x. x IN s ==> p x <= A * q x + B)
     ==> drop(integral s (\x. lift(p x))) <=
         A * drop(integral s (\x. lift(q x))) + B * measure s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(A * (q:real^N->real) x + B)) integrable_on s /\
    A * drop(integral s (\x. lift(q x))) + B * measure s =
    drop(integral s (\x. lift(A * (q:real^N->real) x + B)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    SUBGOAL_THEN `(\x:real^N. A % lift((q:real^N->real) x)) integrable_on s /\
                  (\x:real^N. lift B) integrable_on s`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ON_CONST]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRAL_CONST_GEN] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let WANL_PE_DATA_BOUND = prove
 (`!(f:real->real^K) f'.
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t]))
     ==> ?Mf. &0 < Mf /\ !t. t IN real_interval[&0,&2 * pi] ==> norm(f t) <= Mf`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`] WANL_PE_DATA_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:real->real^K) o drop`; `interval[vec 0:real^1,lift(&2 * pi)]`]
         COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let WANL_PE_VPOLY_APPROX = prove
 (`!(a:real^2) r (f:real->real^K) f' N s0 Mf z j.
     &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     dist(a,z) <= s0 * r /\ s0 < &1 /\
     (!t. t IN real_interval[&0,&2 * pi] ==> norm(f t) <= Mf) /\
     1 <= j /\ j <= dimindex(:K)
     ==> abs(wanl_dsol a r (\x. f(Arg(x - a))) z$j - wanl_pe_vpoly f N a r z$j) <=
         Mf * &2 * s0 pow (N + 1) / (&1 - s0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[wanl_pe_vpoly; LAMBDA_BETA] THEN
  MATCH_MP_TAC WANL_PE_APPROX THEN EXISTS_TAC `f':real->real^K` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `s0 * r < &1 * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `dist(a:real^2,z) <= s0 * r` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[dist] THEN MESON_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((f:real->real^K) t)` THEN ASM_SIMP_TAC[COMPONENT_LE_NORM]]);;

let WANL_PE_GRAD_APPROX = prove
 (`!(a:real^2) r (f:real->real^K) f' rho e.
     &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     &0 < rho /\ rho < r /\ &0 < e
     ==> ?N. !y i j. y IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:2) /\
                     1 <= j /\ j <= dimindex(:K)
                     ==> abs((partial_derivative i (wanl_dsol a r (\x. f(Arg(x - a)))) y -
                              partial_derivative i (wanl_pe_vpoly f N a r) y)$j) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`] WANL_PE_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x. (f:real->real^K)(Arg(x - a))`] WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`] WANL_PE_DATA_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Mf:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gc"))
    (INST_TYPE [`:2`,`:N`] WANL_DD_GRAD_CLOSE) THEN
  ABBREV_TAC `s0 = (r + rho) / (&2 * r)` THEN
  ABBREV_TAC `d = (r - rho) / &4` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 < &1 /\ &0 < d /\ s0 * r = (r + rho) / &2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s0"; "d"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < r ==> &0 < &2 * r`] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `tgt = e * d * (&1 - s0) / (&2 * C * Mf)` THEN
  SUBGOAL_THEN `&0 < tgt` ASSUME_TAC THENL
   [EXPAND_TAC "tgt" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s0:real`; `tgt:real`] REAL_ARCH_POW_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`y:real^2`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * (Mf * &2 * s0 pow (N + 1) / (&1 - s0)) / d` THEN CONJ_TAC THENL
   [USE_THEN "gc" MATCH_MP_TAC THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; WANL_PE_VPOLY_SMOOTH];
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[WANL_PE_VPOLY_SMOOTH];
      UNDISCH_TAC `(y:real^2) IN ball(a,rho)` THEN
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN DISCH_TAC THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `y:real^2`; `z:real^2`] DIST_TRIANGLE) THEN
      EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      MATCH_MP_TAC WANL_PE_VPOLY_APPROX THEN EXISTS_TAC `f':real->real^K` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^2) IN ball(a,rho)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `y:real^2`; `z:real^2`] DIST_TRIANGLE) THEN
      EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 pow (N + 1) <= tgt` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s0 pow N` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 - s0 = &0) /\ ~(d = &0) /\ ~(C = &0) /\ ~(Mf = &0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `pw = s0 pow (N + 1)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * C * Mf / ((&1 - s0) * d)) * tgt` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `C * (Mf * &2 * pw / (&1 - s0)) / d = (&2 * C * Mf / ((&1 - s0) * d)) * pw`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(&1 - s0 = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "tgt" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MAP_EVERY UNDISCH_TAC [`~(&1 - s0 = &0)`; `~(d = &0)`; `~(C = &0)`; `~(Mf = &0)`] THEN
    CONV_TAC REAL_FIELD]);;

let WANL_PE_ENERGY_STEP = prove
 (`!(a:real^2) r (f:real->real^K) f' rho N delta.
     &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     &0 < rho /\ rho < r /\ &0 <= delta /\
     (!y i j. y IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:2) /\
              1 <= j /\ j <= dimindex(:K)
              ==> abs((partial_derivative i (wanl_dsol a r (\x. f(Arg(x - a)))) y -
                       partial_derivative i (wanl_pe_vpoly f N a r) y)$j) <= delta)
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (wanl_dsol a r (\x. f(Arg(x - a)))) x)
                            pow 2)))) <=
         (&1 + delta) *
         drop(integral (interval[vec 0,lift(&2 * pi)]) (\t. lift(norm(f'(drop t)) pow 2))) +
         &2 * &(dimindex(:K)) * (delta + delta pow 2) * measure(ball(a:real^2,rho))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`] WANL_PE_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x. (f:real->real^K)(Arg(x - a))`] WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = wanl_dsol a r (\x. (f:real->real^K)(Arg(x - a)))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real^K`; `f':real->real^K`; `N:num`; `a:real^2`; `r:real`; `rho:real`]
         WANL_PE_VPOLY_ENERGY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real^K`; `N:num`; `a:real^2`; `r:real`] WANL_PE_VPOLY_SMOOTH) THEN
  ABBREV_TAC `V = wanl_pe_vpoly (f:real->real^K) N a r` THEN STRIP_TAC THEN
  ABBREV_TAC `E = drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(norm((f':real->real^K)(drop t)) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)) integrable_on
        ball(a,rho) /\
        (\x. lift(norm(partial_derivative i (V:real^2->real^K) x) pow 2)) integrable_on
        ball(a,rho)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
     `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    MATCH_MP_TAC(TAUT `a ==> a /\ a`) THEN REWRITE_TAC[ETA_AX] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
        REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:2))
      (\i. (&1 + delta) *
           drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (V:real^2->real^K) x) pow 2))) +
           (&(dimindex(:K)) * (delta + delta pow 2)) * measure(ball(a:real^2,rho)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC WANL_PE_INT_PERTURB THEN ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC WANL_PE_SQ_PERTURB THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `sum(1..dimindex(:2))
      (\i. drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (V:real^2->real^K) x) pow 2)))) <= E` THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
  ABBREV_TAC
   `SV = sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (V:real^2->real^K) x) pow 2))))` THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!x y c c':real. x <= y /\ c = c' ==> x + c <= y + c'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let WANL_PE_LOCAL_BOUND = prove
 (`!(a:real^2) r (f:real->real^K) f' rho.
     &0 < r /\ (!t. f(t + &2 * pi) = f t) /\
     (!t. t IN real_interval[&0,&2 * pi]
          ==> ((\s. f'(drop s)) has_integral (f t - f(&0))) (interval[vec 0,lift t])) /\
     (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     &0 < rho /\ rho < r
     ==> sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,rho))
                  (\x. lift(norm(partial_derivative i (wanl_dsol a r (\x. f(Arg(x - a)))) x)
                            pow 2)))) <=
         drop(integral (interval[vec 0,lift(&2 * pi)]) (\t. lift(norm(f'(drop t)) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(norm((f':real->real^K)(drop t)) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `mu = measure(ball(a:real^2,rho))` THEN
  ABBREV_TAC `Kd = &(dimindex(:K))` THEN
  SUBGOAL_THEN `&0 <= mu /\ &0 <= Kd` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["mu"; "Kd"] THEN
    SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC WANL_PE_EPS_LE THEN EXISTS_TAC `E + &4 * Kd * mu` THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`; `rho:real`;
                 `e:real`] WANL_PE_GRAD_APPROX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`; `rho:real`;
                 `N:num`; `e:real`] WANL_PE_ENERGY_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Kd * mu) * e pow 2 <= (Kd * mu) * e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Monotone convergence from the discs ball(a,rho), rho < r,                *)
(* to ball(a,r), and the main theorem WAN_POISSON_ENERGY.                   *)
(* ========================================================================= *)

let WANL_PE_MONO_LIMIT = prove
 (`!(a:real^N) r (Fq:real^N->real^1) B.
     &0 < r /\ Fq continuous_on ball(a,r) /\ (!x. x IN ball(a,r) ==> &0 <= drop(Fq x)) /\
     (!rho. &0 < rho /\ rho < r ==> drop(integral (ball(a,rho)) Fq) <= B)
     ==> Fq integrable_on ball(a,r) /\
         ((\k. integral (ball(a,r * (&1 - inv(&k + &2)))) Fq) --> integral (ball(a,r)) Fq)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t = \k. r * (&1 - inv(&k + &2))` THEN
  SUBGOAL_THEN `!k. r * (&1 - inv(&k + &2)) = (t:num->real) k` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 < (t:num->real) k /\ (t:num->real) k < r /\ (t:num->real) k <= (t:num->real)(SUC k)`
  (LABEL_TAC "t") THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    SUBGOAL_THEN
     `&0 < inv(&k + &2) /\ inv(&k + &2) < &1 /\ inv((&k + &1) + &2) <= inv(&k + &2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < r * e ==> r * (&1 - e) < r`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ball(a:real^N,(t:num->real) k) SUBSET ball(a,r) /\
                    cball(a:real^N,(t:num->real) k) SUBSET ball(a,r)`
  (LABEL_TAC "sub") THENL
   [GEN_TAC THEN USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (Fq:real^N->real^1) integrable_on ball(a,(t:num->real) k)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`Fq:real^N->real^1`; `a:real^N`; `(t:num->real) k`]
           WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k x. if x IN ball(a:real^N,(t:num->real) k) then (Fq:real^N->real^1) x
                        else vec 0`;
                 `Fq:real^N->real^1`; `ball(a:real^N,r)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`Fq:real^N->real^1`; `ball(a:real^N,(t:num->real) k)`; `ball(a:real^N,r)`]
             INTEGRABLE_RESTRICT) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^N`] THEN DISCH_TAC THEN
      USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= drop((Fq:real^N->real^1) x)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_LE_REFL] THEN
      TRY(ASM_REAL_ARITH_TAC) THEN
      UNDISCH_TAC `(x:real^N) IN ball(a,(t:num->real) k)` THEN
      UNDISCH_TAC `~((x:real^N) IN ball(a,(t:num->real)(SUC k)))` THEN
      REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      SUBGOAL_THEN `?N. r / (r - dist(a:real^N,x)) < &N` (X_CHOOSE_TAC `N:num`) THENL
       [REWRITE_TAC[REAL_ARCH_LT]; ALL_TAC] THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN ball(a,(t:num->real) k)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(x:real^N) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      EXPAND_TAC "t" THEN
      SUBGOAL_THEN `r * inv(&k + &2) < r - dist(a:real^N,x)` MP_TAC THENL
       [ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &k + &2`] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `(r - dist(a:real^N,x)) * &N` THEN CONJ_TAC THENL
         [UNDISCH_TAC `r / (r - dist(a:real^N,x)) < &N` THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC `N <= k:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `abs B` THEN X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`Fq:real^N->real^1`; `ball(a:real^N,(t:num->real) k)`; `ball(a:real^N,r)`]
             INTEGRAL_RESTRICT) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= drop(integral (ball(a:real^N,(t:num->real) k)) (Fq:real^N->real^1)) /\
                    drop(integral (ball(a:real^N,(t:num->real) k)) (Fq:real^N->real^1)) <= B`
      MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_MESON_TAC[SUBSET];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[NORM_1] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN MATCH_MP_TAC INTEGRAL_RESTRICT THEN ASM_MESON_TAC[]);;

let WANL_PE_ENERGY_LIMIT = prove
 (`!(a:real^2) r (h:real^2->real^K) E.
     &0 < r /\ smooth_map_on (ball(a,r)) h /\
     (!rho. &0 < rho /\ rho < r
            ==> sum(1..dimindex(:2))
                  (\i. drop(integral (ball(a,rho))
                         (\x. lift(norm(partial_derivative i h x) pow 2)))) <= E)
     ==> (!i. 1 <= i /\ i <= dimindex(:2)
              ==> (\x. partial_derivative i h x) IN lspace (ball(a,r)) (&2)) /\
         sum(1..dimindex(:2))
           (\i. drop(integral (ball(a,r))
                  (\x. lift(norm(partial_derivative i h x) pow 2)))) <= E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)) continuous_on
        ball(a,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    MATCH_MP_TAC(TAUT `a ==> a /\ a`) THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i rho. &0 < rho /\ rho < r
            ==> (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))
                integrable_on ball(a,rho)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
     `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))
            integrable_on ball(a,r) /\
            ((\k. integral (ball(a,r * (&1 - inv(&k + &2))))
                    (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))) -->
             integral (ball(a,r)) (\x. lift(norm(partial_derivative i h x) pow 2)))
            sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC WANL_PE_MONO_LIMIT THEN
    EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:2))
                  (\i. drop(integral (ball(a,rho))
                         (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))))` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`\i. drop(integral (ball(a:real^2,rho))
                         (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)))`;
                   `sum(1..dimindex(:2))
                      (\i. drop(integral (ball(a:real^2,rho))
                         (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))))`;
                   `1..dimindex(:2)`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_LE_POW_2];
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < r * (&1 - inv(&k + &2)) /\ r * (&1 - inv(&k + &2)) < r`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&0 < inv(&k + &2) /\ inv(&k + &2) < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < r * e ==> r * (&1 - e) < r`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\i k. integral (ball(a:real^2,r * (&1 - inv(&k + &2))))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))`;
                 `\i. integral (ball(a:real^2,r))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))`;
                 `1..dimindex(:2)`] LIM_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\k. vsum(1..dimindex(:2))
                        (\i. integral (ball(a:real^2,r * (&1 - inv(&k + &2))))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)))`;
                 `vsum(1..dimindex(:2))
                    (\i. integral (ball(a:real^2,r))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)))`;
                 `E:real`] LIM_DROP_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r * (&1 - inv(&k + &2))`) THEN ASM_REWRITE_TAC[]);;

let WAN_POISSON_ENERGY = prove
 (`!kk:K->bool. WAN_POISSON_ENERGY_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_POISSON_ENERGY_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `f:real->real^K`; `f':real->real^K`]
         WANL_PE_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x. (f:real->real^K)(Arg(x - a))`]
         WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x. (f:real->real^K)(Arg(x - a))`]
         WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `wanl_dsol a r (\x. (f:real->real^K)(Arg(x - a)))`;
                 `drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(norm((f':real->real^K)(drop t)) pow 2)))`]
         WANL_PE_ENERGY_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC WANL_PE_LOCAL_BOUND THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `h = wanl_dsol a r (\x. (f:real->real^K)(Arg(x - a)))` THEN
  EXISTS_TAC `h:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. wan_circ a r t IN sphere(a:real^2,r)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[WANL_WAN_CIRC; IN_SPHERE; dist;
                             VECTOR_ARITH `a - (a + x):real^N = --x`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL; NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (h:real^2->real^K)(wan_circ a r t) = f t` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:real^2->real^K) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(INST_TYPE [`:1`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `\x:real^2. lift B` THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC LSPACE_CONST THEN REWRITE_TAC[MEASURABLE_BALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `h:real^2->real^K`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN
    UNDISCH_TAC `smooth_map_on (ball(a,r)) (h:real^2->real^K)` THEN SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

