(* ========================================================================= *)
(* pc_smt_germ: positive definite linear germs (S4b').                       *)
(*                                                                           *)
(* The statement SMT_POSDEF_GERM_STATEMENT and its proof SMT_POSDEF_GERM. It *)
(* is used in place of SMT_LINEAR_GERM_STATEMENT (S4b of pc_smt_defs) in S7  *)
(* and in M3, where the orthogonal factor of the polar decomposition is      *)
(* absorbed by an orthogonal map. Route: the diagonal case by the complete   *)
(* flow of the compactly supported autonomous field                          *)
(* smooth_bump 1 2 y % (l_i y_i)_i, reparametrized by smooth_step; the       *)
(* general case by orthogonal diagonalization.                               *)
(* ========================================================================= *)

needs "src/pc_smt_sphere.ml";;
needs "src/pc_ode_vf.ml";;

prioritize_real();;
type_invention_error := true;;

(* S4b'. For linear P with positive definite matrix there is a compactly    *)
(* supported isotopy from the identity to a diffeomorphism equal to P near  *)
(* the origin.                                                              *)

let SMT_POSDEF_GERM_STATEMENT = new_definition
 `SMT_POSDEF_GERM_STATEMENT (n:N->bool) <=>
    !P:real^N->real^N.
        linear P /\ positive_definite(matrix P)
        ==> ?H K e. diffeo_isotopy H K /\ &0 < e /\
                    (!t x. t <= &0 ==> H t x = x) /\
                    (!t x. &1 <= t ==> H t x = H (&1) x) /\
                    (!x. norm x <= e ==> H (&1) x = P x) /\
                    (?R. !t x. R <= norm x ==> H t x = x)`;;

(* ------------------------------------------------------------------------- *)
(* The diagonal case.  For l in real^N the field                             *)
(*   X y = smooth_bump 1 2 y % (l_i y_i)_i                                   *)
(* is smooth and vanishes off cball(0,2), so its flow is complete and a      *)
(* diffeomorphism at each time (ODE_VF_COMPLETE, ODE_VF_FLOW_SMOOTH).  On    *)
(* cball(0,1) the field is linear, and by ODE_VF_UNIQUE the time-1 flow is   *)
(* (exp(l_i) x_i)_i for small x.  Time is reparametrized by smooth_step.     *)
(* ------------------------------------------------------------------------- *)

let SMT_GERM_DIAG_LINEAR = prove
 (`!l:real^N. linear (\y:real^N. (lambda i. l$i * y$i):real^N)`,
  GEN_TAC THEN
  SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let SMT_GERM_FIELD_SMOOTH = prove
 (`!l:real^N. smooth_map_on (:real^N)
        (\y. smooth_bump (&1) (&2) y % (lambda i. l$i * y$i):real^N)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(smooth_bump (&1) (&2) y)`;
                 `\y:real^N. (lambda i. (l:real^N)$i * y$i):real^N`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`;
                   `\y:real^N. (lambda i. (l:real^N)$i * y$i):real^N`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMT_GERM_DIAG_LINEAR; o_DEF]]);;

let SMT_GERM_EXP_DERIV = prove
 (`!a b s. ((\s. lift(exp(drop s * a) * b)) has_vector_derivative
            lift(a * exp(drop s * a) * b)) (at s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV
    `((\t. exp(t * a) * b) has_real_derivative f) (atreal (drop s))`) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_ASSOC]);;

let SMT_GERM_DIAG_DERIV = prove
 (`!(l:real^N) (x:real^N) s.
     ((\s. (lambda i. exp(drop s * l$i) * x$i):real^N) has_vector_derivative
      (lambda i. l$i * (exp(drop s * l$i) * x$i))) (at s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  SIMP_TAC[LAMBDA_BETA; SMT_GERM_EXP_DERIV]);;

(* The explicit solution stays in the unit ball for times in [0,1].         *)

let SMT_GERM_DIAG_SMALL = prove
 (`!(l:real^N) (x:real^N) s.
     norm x <= exp(--norm l) /\ &0 <= drop s /\ drop s <= &1
     ==> norm((lambda i. exp(drop s * l$i) * x$i):real^N) <= &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(exp(norm(l:real^N)) % (x:real^N))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; REAL_ABS_MUL; REAL_ABS_EXP] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(drop s) * abs((l:real^N)$i)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm(l:real^N)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS; COMPONENT_LE_NORM] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    REWRITE_TAC[NORM_MUL; REAL_ABS_EXP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(norm(l:real^N)) * exp(--norm l)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_EXP_NEG_MUL; REAL_LE_REFL]]]);;

let SMT_GERM_DIAG = prove
 (`!l:real^N.
     ?(H:real->real^N->real^N) K e. diffeo_isotopy H K /\ &0 < e /\
             (!t x. t <= &0 ==> H t x = x) /\
             (!t x. &1 <= t ==> H t x = H (&1) x) /\
             (!x. norm x <= e ==> H (&1) x = (lambda i. exp(l$i) * x$i)) /\
             (!t x. &3 <= norm x ==> H t x = x)`,
  GEN_TAC THEN
  ABBREV_TAC
   `X = \y:real^N. smooth_bump (&1) (&2) y % (lambda i. (l:real^N)$i * y$i):real^N` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (X:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[SMT_GERM_FIELD_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (X:real^N->real^N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`; `cball(vec 0:real^N,&2)`]
    ODE_VF_COMPLETE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV; IN_UNIV;
                    IN_CBALL_0; REAL_NOT_LE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "X" THEN
    SUBGOAL_THEN `smooth_bump (&1) (&2) (y:real^N) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV; IN_CBALL_0; REAL_NOT_LE; UNIV_PCROSS_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "max")
    (CONJUNCTS_THEN2 (LABEL_TAC "dom")
    (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (CONJUNCTS_THEN2 (LABEL_TAC "off") (LABEL_TAC "inK"))))) THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`] ODE_VF_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. ode_vf_flow X (:real^N) (vec 0) x = x`
  (LABEL_TAC "zero") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`; `x:real^N`] ODE_VF_MAXIMAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\t (x:real^N). ode_vf_flow X (:real^N) (lift(smooth_step t)) x`;
    `\t (y:real^N). ode_vf_flow X (:real^N) (--lift(smooth_step t)) y`;
    `exp(--norm(l:real^N))`] THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[diffeo_isotopy] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`;
                     `\t (x:real^N). ode_vf_flow X (:real^N) (lift t) x`;
                     `smooth_step`] SMT_FAMILY_REPARAM) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV; LIFT_DROP];
      MP_TAC(ISPECL [`(:real^N)`;
                     `\t (x:real^N). ode_vf_flow X (:real^N) (--lift t) x`;
                     `smooth_step`] SMT_FAMILY_REPARAM) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV; LIFT_DROP] THEN
      SUBGOAL_THEN
       `(\z:real^(1,N)finite_sum. ode_vf_flow X (:real^N) (--fstcart z) (sndcart z)) =
        (\w:real^(1,N)finite_sum. ode_vf_flow X (:real^N) (fstcart w) (sndcart w)) o
        (\z:real^(1,N)finite_sum. pastecart (--fstcart z) (sndcart z))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                     `\z:real^(1,N)finite_sum. pastecart (--fstcart z) (sndcart z)`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_SNDCART] THEN
      MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN REWRITE_TAC[LINEAR_FSTCART];
      GEN_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SMOOTH_STEP_0; LIFT_NUM];
    SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`;
                   `interval[vec 0:real^1,lift(&1)]`;
                   `\s:real^1. (lambda i. exp(drop s * (l:real^N)$i) *
                                          (x:real^N)$i):real^N`;
                   `vec 0:real^1`] ODE_VF_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_INTERVAL; IN_UNIV; IN_INTERVAL_1;
                      DROP_VEC; LIFT_DROP; REAL_POS; REAL_LE_REFL] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN
       `(X:real^N->real^N) ((lambda i. exp(drop s * (l:real^N)$i) *
                                        (x:real^N)$i):real^N) =
        (lambda i. l$i * (exp(drop s * l$i) * x$i))`
      SUBST1_TAC THENL
       [EXPAND_TAC "X" THEN
        SUBGOAL_THEN
         `smooth_bump (&1) (&2) ((lambda i. exp(drop s * (l:real^N)$i) *
                                            (x:real^N)$i):real^N) = &1`
        SUBST1_TAC THENL
         [MATCH_MP_TAC SMOOTH_BUMP_1 THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC SMT_GERM_DIAG_SMALL THEN ASM_REWRITE_TAC[];
          SIMP_TAC[VECTOR_MUL_LID; CART_EQ; LAMBDA_BETA]];
        REWRITE_TAC[SMT_GERM_DIAG_DERIV]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_EXP_0;
                LAMBDA_ETA] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "off" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The general case.  P = U D U^T with U orthogonal and D                    *)
(* diagonal with positive entries d_i (SYMMETRIC_MATRIX_DIAGONALIZABLE_      *)
(* EXPLICIT, POSITIVE_DEFINITE_SIMILAR, POSITIVE_DEFINITE_DIAGONAL_MATRIX_   *)
(* EQ); the diagonal isotopy for l_i = log d_i is conjugated by U.           *)
(* ------------------------------------------------------------------------- *)

let SMT_DIAGONAL_MATRIX_VECTOR_MUL = prove
 (`!(d:num->real) (y:real^N).
        ((lambda i j. if i = j then d i else &0):real^N^N) ** y =
        (lambda i. d i * y$i)`,
  REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  W(fun (asl,w) -> SUBGOAL_THEN
    (mk_eq(lhand w,
      `sum(1..dimindex(:N)) (\j. if j = i then (d:num->real) i * (y:real^N)$i
                                 else &0)`)) SUBST1_TAC) THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `j:num = i` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

(* Linear maps with linear inverses are diffeomorphisms of R^N.             *)

let SMT_LINEAR_INVERSES_DIFFEO = prove
 (`!(A:real^N->real^N) A'.
        linear A /\ linear A' /\ (!x. A'(A x) = x) /\ (!y. A(A' y) = y)
        ==> diffeomorphism_on (:real^N) (:real^N) A A'`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `A:real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    REWRITE_TAC[o_DEF; ETA_AX];
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `A':real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    REWRITE_TAC[o_DEF; ETA_AX]]);;

(* Conjugating a smooth family of maps of R^N by linear maps.               *)

let SMT_FAMILY_LINEAR_CONJ = prove
 (`!(H:real->real^N->real^N) (A:real^N->real^N) (A':real^N->real^N).
        smooth_family (:real^N) H /\ linear A /\ linear A'
        ==> smooth_family (:real^N) (\t x. A(H t (A' x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (A:real^N->real^N)
        ((H:real->real^N->real^N) (drop(fstcart z))
                                  ((A':real^N->real^N)(sndcart z)))) =
    A o (\z. H (drop(fstcart z)) (sndcart z)) o
        (\z:real^(1,N)finite_sum. pastecart (fstcart z) (A'(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MP_TAC(ISPECL
   [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
    `\z:real^(1,N)finite_sum. pastecart (fstcart z) ((A':real^N->real^N)(sndcart z))`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_FSTCART] THEN
  MP_TAC(ISPECL [`sndcart:real^(1,N)finite_sum->real^N`; `A':real^N->real^N`]
    LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[LINEAR_SNDCART; o_DEF]);;

let SMT_DIFFEO_ISOTOPY_LINEAR_CONJ = prove
 (`!(H:real->real^N->real^N) K (A:real^N->real^N) (A':real^N->real^N).
        diffeo_isotopy H K /\ linear A /\ linear A' /\
        (!x. A'(A x) = x) /\ (!y. A(A' y) = y)
        ==> diffeo_isotopy (\t x. A(H t (A' x))) (\t y. A(K t (A' y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeo_isotopy] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SMT_FAMILY_LINEAR_CONJ] THEN X_GEN_TAC `t:real` THEN
  SUBGOAL_THEN
   `diffeomorphism_on (:real^N) (:real^N) A A' /\
    diffeomorphism_on (:real^N) (:real^N) A' A`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMT_LINEAR_INVERSES_DIFFEO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N)`; `(:real^N)`; `(:real^N)`;
                 `A':real^N->real^N`; `A:real^N->real^N`;
                 `(H:real->real^N->real^N) t`; `(K:real->real^N->real^N) t`]
    DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `(:real^N)`; `(:real^N)`;
                 `(H:real->real^N->real^N) t o (A':real^N->real^N)`;
                 `(A:real^N->real^N) o (K:real->real^N->real^N) t`;
                 `A:real^N->real^N`; `A':real^N->real^N`]
    DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF]);;

(* S4b'. *)

let SMT_POSDEF_GERM = prove
 (`!n:N->bool. SMT_POSDEF_GERM_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[SMT_POSDEF_GERM_STATEMENT] THEN
  X_GEN_TAC `P:real^N->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `matrix(P:real^N->real^N)`
    SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N^N`; `d:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "diag")) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < (d:num->real) i`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `invertible(U:real^N^N)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_MATRIX_IMP_INVERTIBLE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`matrix(P:real^N->real^N)`; `U:real^N^N`]
      POSITIVE_DEFINITE_SIMILAR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(lambda i j. if i = j then (d:num->real) i else &0):real^N^N`
      POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ) THEN
    ANTS_TAC THENL [SIMP_TAC[diagonal_matrix; LAMBDA_BETA]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. transp(U:real^N^N) ** U ** x = x /\ U ** transp U ** x = x`
  (LABEL_TAC "inv") THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_LMUL;
                 ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(lambda i. log((d:num->real) i)):real^N` SMT_GERM_DIAG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`H0:real->real^N->real^N`; `K0:real->real^N->real^N`; `e:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "neg") (CONJUNCTS_THEN2 (LABEL_TAC "one")
   (CONJUNCTS_THEN2 (LABEL_TAC "near") (LABEL_TAC "far")))))) THEN
  MAP_EVERY EXISTS_TAC
   [`\t (x:real^N). (U:real^N^N) ** (H0:real->real^N->real^N) t (transp U ** x)`;
    `\t (y:real^N). (U:real^N^N) ** (K0:real->real^N->real^N) t (transp U ** y)`;
    `e:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`H0:real->real^N->real^N`; `K0:real->real^N->real^N`;
                   `\x:real^N. (U:real^N^N) ** x`;
                   `\x:real^N. transp(U:real^N^N) ** x`]
      SMT_DIFFEO_ISOTOPY_LINEAR_CONJ) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REPEAT STRIP_TAC THEN USE_THEN "neg" (fun th -> ASM_SIMP_TAC[th]);
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN USE_THEN "one" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(transp(U:real^N^N) ** (x:real^N)) <= e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP]; ALL_TAC] THEN
    USE_THEN "near" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `norm(transp(U:real^N^N) ** (x:real^N)) <= e`)]) THEN
    SUBGOAL_THEN
     `(lambda i. exp((lambda i. log((d:num->real) i)):real^N$i) *
                 (transp(U:real^N^N) ** (x:real^N))$i):real^N =
      (lambda i j. if i = j then d i else &0) ** (transp U ** x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[SMT_DIAGONAL_MATRIX_VECTOR_MUL] THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_SIMP_TAC[EXP_LOG];
      ALL_TAC] THEN
    USE_THEN "diag" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIX_WORKS];
    EXISTS_TAC `&3` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(H0:real->real^N->real^N) t (transp(U:real^N^N) ** (x:real^N)) =
      transp U ** x`
    SUBST1_TAC THENL
     [USE_THEN "far" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP];
      ASM_REWRITE_TAC[]]]);;

