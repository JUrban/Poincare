(* ========================================================================= *)
(* pc_smt_planar: S3 (SMT_PLANAR_ISOTOPY_STATEMENT), compactly supported     *)
(* diffeomorphisms of R^2 are isotopic to the identity.                      *)
(*                                                                           *)
(* S3 from S3a (smooth angle), S3c (straightening) and S3d                   *)
(* (end correction).  For a compactly supported diffeomorphism f the field   *)
(* Y = f_* e_1 is rho (cos theta, sin theta); the family                     *)
(*   V s = ((1 - b s) + b s rho) (cos(b s theta), sin(b s theta)),           *)
(* b = smooth_step, joins e_1 to Y; its straightening isotopy Psi joins I    *)
(* (s = 0) to f (s = 1) by the uniqueness clause of S3c, and S3d makes it    *)
(* compactly supported.                                                      *)
(* ========================================================================= *)

needs "src/pc_smt_rn.ml";;
needs "src/pc_smt_cover.ml";;
needs "src/pc_smt_pole.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_DIFFEO_DERIV_INJ = prove
 (`!(f:real^N->real^N) g x h.
        diffeomorphism_on (:real^N) (:real^N) f g /\
        frechet_derivative f (at x) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(f has_derivative frechet_derivative (f:real^N->real^N) (at x)) (at x) /\
    (g has_derivative frechet_derivative (g:real^N->real^N) (at (f x))) (at (f x))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `f:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    MP_TAC(ISPECL [`(:real^N)`; `g:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^N->real^N) o (f:real^N->real^N) has_derivative
     frechet_derivative g (at (f x)) o frechet_derivative f (at x)) (at x)`
  MP_TAC THENL [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) o (f:real^N->real^N) = (\x. x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (g:real^N->real^N) (at (f x)) o
    frechet_derivative (f:real^N->real^N) (at x) = (\h. h)`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `x:real^N`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN ASM_REWRITE_TAC[o_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (g:real^N->real^N) (at ((f:real^N->real^N) x))`
    LINEAR_0) THEN
  UNDISCH_TAC `(g has_derivative frechet_derivative (g:real^N->real^N) (at (f x)))
               (at ((f:real^N->real^N) x))` THEN
  SIMP_TAC[has_derivative]);;

let SMT_DERIV_ID_FAR = prove
 (`!(f:real^N->real^N) r x.
        (!y. r <= norm y ==> f y = y) /\ r < norm x
        ==> frechet_derivative f (at x) = (\h. h)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `norm(x:real^N) - r`] THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(NORM_ARITH `dist(y:real^N,x) < norm(x) - r ==> r <= norm y`) THEN
  ASM_REWRITE_TAC[]);;

(* Smooth scalar functions of (s,y) built from smooth_step and functions of y. *)

let SMT_LIFT_STEP_FST_SMOOTH = prove
 (`smooth_map_on (:real^(1,N)finite_sum)
     (\z. lift(smooth_step(drop(fstcart z))))`,
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. lift(smooth_step(drop(fstcart z)))) =
    (lift o smooth_step o drop) o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_STEP_SMOOTH] THEN
  MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                 `fstcart:real^(1,N)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX]);;

let SMT_SND_COMPOSE_SMOOTH = prove
 (`!(u:real^N->real^P).
        smooth_map_on (:real^N) u
        ==> smooth_map_on (:real^(1,N)finite_sum) (\z. u(sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (u:real^N->real^P)(sndcart z)) = u o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                 `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX]);;

(* The interpolating family of fields.                                       *)

let SMT_INTERP_POS = prove
 (`!b p. &0 <= b /\ b <= &1 /\ &0 < p ==> &0 < (&1 - b) + b * p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b = &1` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < &1 - b /\ &0 <= c ==> &0 < (&1 - b) + c`) THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let SMT_ANGLE_FAMILY = prove
 (`!theta rho:real^2->real r.
        smooth_map_on (:real^2) (\x. lift(theta x)) /\
        smooth_map_on (:real^2) (\x. lift(rho x)) /\
        (!x. &0 < rho x) /\
        (!x. r <= norm x ==> theta x = &0 /\ rho x = &1)
        ==> smooth_family (:real^2)
              (\s x. ((&1 - smooth_step s) + smooth_step s * rho x) %
                     vector[cos(smooth_step s * theta x);
                            sin(smooth_step s * theta x)]:real^2) /\
            (!s x. ~(((&1 - smooth_step s) + smooth_step s * rho x) %
                     vector[cos(smooth_step s * theta x);
                            sin(smooth_step s * theta x)]:real^2 = vec 0)) /\
            (!s x. r <= norm x
                   ==> ((&1 - smooth_step s) + smooth_step s * rho x) %
                       vector[cos(smooth_step s * theta x);
                              sin(smooth_step s * theta x)]:real^2 = basis 1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "far")))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^(1,2)finite_sum)
        (\z. lift(smooth_step(drop(fstcart z)))) /\
      smooth_map_on (:real^(1,2)finite_sum) (\z. lift(theta(sndcart z))) /\
      smooth_map_on (:real^(1,2)finite_sum) (\z. lift(rho(sndcart z)))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SMT_LIFT_STEP_FST_SMOOTH] THEN CONJ_TAC THEN
      MATCH_MP_TAC SMT_SND_COMPOSE_SMOOTH THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^(1,2)finite_sum)
        (\z. lift(smooth_step(drop(fstcart z)) * theta(sndcart z)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                     `\z:real^(1,2)finite_sum. lift(smooth_step(drop(fstcart z)))`;
                     `\z:real^(1,2)finite_sum. lift(theta(sndcart z))`]
        SMOOTH_MAP_ON_LIFT_MUL) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`(:real^(1,2)finite_sum)`;
      `\z:real^(1,2)finite_sum.
          lift((&1 - smooth_step(drop(fstcart z))) +
               smooth_step(drop(fstcart z)) * rho(sndcart z))`;
      `\z:real^(1,2)finite_sum.
          vector[cos(smooth_step(drop(fstcart z)) * theta(sndcart z));
                 sin(smooth_step(drop(fstcart z)) * theta(sndcart z))]:real^2`]
      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
        MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                       `\z:real^(1,2)finite_sum. lift(smooth_step(drop(fstcart z)))`;
                       `\z:real^(1,2)finite_sum. lift(rho(sndcart z))`]
          SMOOTH_MAP_ON_LIFT_MUL) THEN
        ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]];
      MP_TAC(ISPECL
       [`(:real^(1,2)finite_sum)`;
        `\z:real^(1,2)finite_sum.
          vector[cos(smooth_step(drop(fstcart z)) * theta(sndcart z));
                 sin(smooth_step(drop(fstcart z)) * theta(sndcart z))]:real^2`]
        SMOOTH_MAP_ON_COMPONENTWISE) THEN
      REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                       `\z:real^(1,2)finite_sum.
                          lift(smooth_step(drop(fstcart z)) * theta(sndcart z))`]
          SMOOTH_MAP_ON_LIFT_COS);
        MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                       `\z:real^(1,2)finite_sum.
                          lift(smooth_step(drop(fstcart z)) * theta(sndcart z))`]
          SMOOTH_MAP_ON_LIFT_SIN)] THEN
      ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]];
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a ==> ~(a = &0)`) THEN
      MATCH_MP_TAC SMT_INTERP_POS THEN ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS];
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      STRIP_TAC THEN MP_TAC(SPEC `smooth_step s * theta(x:real^2)` SIN_CIRCLE) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN USE_THEN "far" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; COS_0; SIN_0; REAL_MUL_RID; REAL_SUB_ADD] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* S3 from S3a, S3c and S3d.                                                 *)
(* ------------------------------------------------------------------------- *)

let SMT_FRECHET_DERIVATIVE_ID = prove
 (`!x:real^N. frechet_derivative (\x. x) (at x) = (\h. h)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID]);;

let SMT_PLANAR_FROM_PARTS = prove
 (`SMT_SMOOTH_ANGLE_STATEMENT /\ SMT_STRAIGHTENING_STATEMENT /\
   SMT_END_CORRECTION_STATEMENT ==> SMT_PLANAR_ISOTOPY_STATEMENT`,
  REWRITE_TAC[SMT_SMOOTH_ANGLE_STATEMENT; SMT_STRAIGHTENING_STATEMENT;
              SMT_END_CORRECTION_STATEMENT; SMT_PLANAR_ISOTOPY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S3a")
    (CONJUNCTS_THEN2 (LABEL_TAC "S3c") (LABEL_TAC "S3d"))) THEN
  MAP_EVERY X_GEN_TAC [`f:real^2->real^2`; `g:real^2->real^2`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ffar")) THEN
  ABBREV_TAC `r1 = abs r + &1` THEN
  SUBGOAL_THEN `&0 < r1 /\ r < r1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^2) (f:real^2->real^2) /\
    smooth_map_on (:real^2) (g:real^2->real^2) /\
    (!x. g(f x) = x) /\ (!y. f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^2) (:real^2) f g` THEN
    SIMP_TAC[diffeomorphism_on; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. r <= norm x ==> (g:real^2->real^2) x = x`
  (LABEL_TAC "gfar") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^2) x = x`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [USE_THEN "ffar" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the push-forward field Y = f_* e_1 *)
  SUBGOAL_THEN
   `smooth_map_on (:real^2)
      (\y. frechet_derivative (f:real^2->real^2) (at ((g:real^2->real^2) y))
                              (basis 1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. frechet_derivative (f:real^2->real^2) (at ((g:real^2->real^2) y))
                              (basis 1)) =
      (\x. frechet_derivative f (at x) (basis 1)) o g`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  USE_THEN "S3a" (MP_TAC o SPECL
   [`\y. frechet_derivative (f:real^2->real^2) (at ((g:real^2->real^2) y))
                            (basis 1)`; `r1:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`;
                     `(g:real^2->real^2) y`; `basis 1:real^2`]
        SMT_DIFFEO_DERIV_INJ) THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^2->real^2) y = y` SUBST1_TAC THENL
       [USE_THEN "gfar" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^2->real^2`; `r:real`; `y:real^2`] SMT_DERIV_ID_FAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:real^2->real` (X_CHOOSE_THEN `rho:real^2->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "polar"))))))) THEN
  MP_TAC(ISPECL [`theta:real^2->real`; `rho:real^2->real`; `r1:real`]
    SMT_ANGLE_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "S3c" (MP_TAC o SPECL
   [`\s x. ((&1 - smooth_step s) + smooth_step s * (rho:real^2->real) x) %
           vector[cos(smooth_step s * (theta:real^2->real) x);
                  sin(smooth_step s * theta x)]:real^2`; `r1:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_STEP_0; SMOOTH_STEP_1; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Psi:real->real^2->real^2`
    (X_CHOOSE_THEN `Psi':real->real^2->real^2` (X_CHOOSE_THEN `tau:real->real->real`
    (X_CHOOSE_THEN `sigma:real->real->real` (X_CHOOSE_THEN `R:real`
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "strip")
    (CONJUNCTS_THEN2 (LABEL_TAC "right") (LABEL_TAC "uniq")))))))))))) THEN
  (* Psi 0 = I and Psi 1 = f *)
  SUBGOAL_THEN `!x:real^2. (Psi:real->real^2->real^2) (&0) x = x` ASSUME_TAC THENL
   [USE_THEN "uniq" (MP_TAC o SPECL [`&0`; `\x:real^2. x`]) THEN
    REWRITE_TAC[DIFFERENTIABLE_ID; SMT_FRECHET_DERIVATIVE_ID] THEN
    SIMP_TAC[SMOOTH_STEP_0; REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO;
                REAL_ADD_RID; COS_0; SIN_0; VECTOR_MUL_LID] THEN
    ANTS_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; BASIS_COMPONENT; ARITH];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. (Psi:real->real^2->real^2) (&1) x = f x` ASSUME_TAC THENL
   [USE_THEN "uniq" (MP_TAC o SPECL [`&1`; `f:real^2->real^2`]) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN USE_THEN "ffar" MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ADD_LID; REAL_MUL_LID] THEN
      USE_THEN "polar" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* S3d *)
  USE_THEN "S3d" (MP_TAC o SPECL
   [`Psi:real->real^2->real^2`; `Psi':real->real^2->real^2`;
    `tau:real->real->real`; `sigma:real->real->real`; `f:real^2->real^2`;
    `r1:real`; `max R r1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "right" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "ffar" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Smooth inverses.  A smooth bijection of R^N with invertible               *)
(* derivative has a smooth inverse (SMT_OPEN_INVERSE_SMOOTH, pc_smt_cover);   *)
(* a smooth family of such bijections has a smooth inverse family (apply it  *)
(* to (t,x) |-> (t, H t x), whose derivative is block triangular).           *)
(* ------------------------------------------------------------------------- *)

let SMT_GLOBAL_INVERSE_SMOOTH = prove
 (`!(f:real^N->real^N) g.
        smooth_map_on (:real^N) f /\ (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
        (!x. ~(det(matrix(frechet_derivative f (at x))) = &0))
        ==> smooth_map_on (:real^N) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_OPEN_INVERSE_SMOOTH THEN
  EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let SMT_FAMILY_INVERSE_SMOOTH = prove
 (`!(H:real->real^N->real^N) K.
        smooth_family (:real^N) H /\
        (!t x. K t (H t x) = x) /\ (!t y. H t (K t y) = y) /\
        (!t x h. frechet_derivative (H t) (at x) h = vec 0 ==> h = vec 0)
        ==> diffeo_isotopy H K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Hj = \z:real^(1,N)finite_sum.
                     (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)` THEN
  ABBREV_TAC `Phi = \z:real^(1,N)finite_sum.
                      pastecart (fstcart z) ((Hj:real^(1,N)finite_sum->real^N) z)` THEN
  ABBREV_TAC `Psi = \z:real^(1,N)finite_sum.
                      pastecart (fstcart z)
                        ((K:real->real^N->real^N) (drop(fstcart z)) (sndcart z))` THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (Hj:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL [EXPAND_TAC "Hj" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,N)finite_sum)
      (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\z:real^(1,N)finite_sum. z`;
                   `fstcart:real^(1,N)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z. (Psi:real^(1,N)finite_sum->real^(1,N)finite_sum)
           ((Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) z) = z) /\
    (!z. Phi(Psi z) = z)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"; "Psi"; "Hj"] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(det(matrix(frechet_derivative
            (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) (at w))) = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    SUBGOAL_THEN `((Hj:real^(1,N)finite_sum->real^N) has_derivative
                   frechet_derivative Hj (at w)) (at w)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `Hj:real^(1,N)finite_sum->real^N`]
        SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `w:real^(1,N)finite_sum`);
      ALL_TAC] THEN
    ABBREV_TAC `DH = frechet_derivative (Hj:real^(1,N)finite_sum->real^N) (at w)` THEN
    SUBGOAL_THEN `linear (DH:real^(1,N)finite_sum->real^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `((Hj:real^(1,N)finite_sum->real^N) has_derivative DH) (at w)` THEN
      SIMP_TAC[has_derivative];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) has_derivative
       (\h. pastecart (fstcart h) ((DH:real^(1,N)finite_sum->real^N) h))) (at w)`
    ASSUME_TAC THENL
     [EXPAND_TAC "Phi" THEN MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_FSTCART];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    SUBGOAL_THEN
     `linear (\h:real^(1,N)finite_sum.
                pastecart (fstcart h) ((DH:real^(1,N)finite_sum->real^N) h))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_PASTECART THEN
      ASM_REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_FSTCART];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_DET_NONZERO_INJECTIVE] THEN
    X_GEN_TAC `h:real^(1,N)finite_sum` THEN
    REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_INJ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^(1,N)finite_sum) = pastecart (vec 0) (sndcart h)`
    SUBST_ALL_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `k = sndcart(h:real^(1,N)finite_sum)` THEN
    REWRITE_TAC[PASTECART_INJ] THEN
    (* the x-derivative of Hj is the derivative of the slice *)
    SUBGOAL_THEN
     `(H:real->real^N->real^N) (drop(fstcart(w:real^(1,N)finite_sum))) =
      (Hj:real^(1,N)finite_sum->real^N) o (\x. pastecart (fstcart w) x)`
    ASSUME_TAC THENL
     [EXPAND_TAC "Hj" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((H:real->real^N->real^N) (drop(fstcart(w:real^(1,N)finite_sum)))
       has_derivative
       (DH:real^(1,N)finite_sum->real^N) o (\x. pastecart (vec 0) x))
      (at (sndcart w))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
        REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
        REWRITE_TAC[PASTECART_FST_SND] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                        `sndcart(w:real^(1,N)finite_sum)`]) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,N)finite_sum)
      (Psi:real^(1,N)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_GLOBAL_INVERSE_SMOOTH THEN
    EXISTS_TAC `Phi:real^(1,N)finite_sum->real^(1,N)finite_sum` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,N)finite_sum)
      (\z. (K:real->real^N->real^N) (drop(fstcart z)) (sndcart z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. (K:real->real^N->real^N) (drop(fstcart z)) (sndcart z)) =
      sndcart o (Psi:real^(1,N)finite_sum->real^(1,N)finite_sum)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Psi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; SNDCART_PASTECART];
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[diffeo_isotopy; smooth_family; UNIV_PCROSS_UNIV] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `(K:real->real^N->real^N) t y` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `(H:real->real^N->real^N) t y` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `H:real->real^N->real^N`; `t:real`]
      SMT_FAMILY_SLICE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; smooth_family; UNIV_PCROSS_UNIV];
    MP_TAC(ISPECL [`(:real^N)`; `K:real->real^N->real^N`; `t:real`]
      SMT_FAMILY_SLICE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; smooth_family; UNIV_PCROSS_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the end correction S3d.  smooth_step is Lipschitz;              *)
(* directional difference quotients; maps of R^2 preserving one coordinate   *)
(* whose other coordinate increases along the fibre have injective           *)
(* derivative; increasing fibre maps equal to a translation at both ends are *)
(* onto.                                                                     *)
(* ------------------------------------------------------------------------- *)

let SMT_STEP_LIPSCHITZ = prove
 (`?L. &0 < L /\ !a b. abs(smooth_step a - smooth_step b) <= L * abs(a - b)`,
  MP_TAC(ISPECL [`\t:real^1. lift(smooth_step(drop t) * smooth_step(&2 - drop t))`;
                 `interval[vec 0:real^1,lift(&2)]`] SMT_SMOOTH_COMPACT_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`; `\t:real^1. lift(smooth_step(drop t))`;
                     `\t:real^1. lift(smooth_step(&2 - drop t))`]
        SMOOTH_MAP_ON_LIFT_MUL) THEN
      REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MP_TAC SMOOTH_STEP_SMOOTH THEN REWRITE_TAC[o_DEF];
        MP_TAC(ISPECL [`(:real^1)`; `\t:real^1. lift(&2 - drop t)`]
          SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
        REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP; SMOOTH_MAP_ON_ID;
                    ETA_AX]];
      X_GEN_TAC `t:real^1` THEN REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[SMOOTH_STEP_0; REAL_LT_IMP_LE; REAL_MUL_LZERO; LIFT_NUM];
        SUBGOAL_THEN `smooth_step(&2 - drop t) = &0` SUBST1_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_MUL_RZERO; LIFT_NUM]]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a b. a <= &1 /\ b <= &1
          ==> abs(smooth_step a - smooth_step b) <= L * abs(a - b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`lift a`; `lift b`]) THEN
    REWRITE_TAC[LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
    SUBGOAL_THEN `smooth_step(&2 - a) = &1 /\ smooth_step(&2 - b) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[REAL_LE_TOTAL]
   `(!a b. P a b ==> P b a) /\ (!a b. a <= b ==> P a b) ==> !a b. P a b`) THEN
  CONJ_TAC THENL [MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b <= &1` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= a` THENL
   [ASM_SIMP_TAC[SMOOTH_STEP_1; REAL_ARITH `~(b <= &1) ==> &1 <= b`] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_step b = smooth_step(&1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL; REAL_ARITH `~(b <= &1) ==> &1 <= b`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * abs(a - &1)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* Difference quotients along a direction.                                  *)

let SMT_DERIV_DIRECTION = prove
 (`!(f:real^M->real^N) f' x e.
        (f has_derivative f') (at x)
        ==> !eps. &0 < eps
                  ==> ?d. &0 < d /\
                          !t. &0 < t /\ t < d
                              ==> norm(f(x + t % e) - f x - t % f' e) <= eps * t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `e:real^M = vec 0` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_REFL; NORM_0; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(e:real^M)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  USE_THEN "d" (MP_TAC o SPEC `eps / norm(e:real^M)`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / norm(e:real^M)` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + t % e:real^M`) THEN
  REWRITE_TAC[VECTOR_ADD_SUB; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  UNDISCH_TAC `&0 < norm(e:real^M)` THEN CONV_TAC REAL_FIELD);;

(* Maps of R^2 that preserve one coordinate.                                *)

let SMT_TRIANG_DERIV_INJ = prove
 (`!(f:real^2->real^2) f' x i j c d.
        (f has_derivative f') (at x) /\
        ((i = 1 /\ j = 2) \/ (i = 2 /\ j = 1)) /\
        (!y. (f y)$i = y$i) /\ &0 < c /\ &0 < d /\
        (!t. &0 < t /\ t < d ==> c * t <= (f(x + t % basis j) - f x)$j)
        ==> !h. f' h = vec 0 ==> h = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ij") STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `linear(f':real^2->real^2)` ASSUME_TAC THENL
    [ASM_MESON_TAC[has_derivative]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!h:real^2. (f' h:real^2)$i = h$i` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`f:real^2->real^2`; `f':real^2->real^2`; `x:real^2`]
       HAS_DERIVATIVE_COMPONENTWISE_AT) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
     ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_2] THEN ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `((\y:real^2. lift(y$i)) has_derivative (\h. lift(h$i))) (at x)`
     ASSUME_TAC THENL
      [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
       MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN
       REWRITE_TAC[DIMINDEX_2] THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     X_GEN_TAC `h:real^2` THEN
     MP_TAC(ISPECL [`\y:real^2. lift(y$i)`; `\h:real^2. lift((f':real^2->real^2) h$i)`;
                    `\h:real^2. lift(h$i)`; `x:real^2`]
       FRECHET_DERIVATIVE_UNIQUE_AT) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^2`) THEN
     REWRITE_TAC[LIFT_EQ];
     ALL_TAC]) THEN
  X_GEN_TAC `h:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^2)$i = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `h:real^2`) THEN ASM_REWRITE_TAC[VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2) = h$j % basis j` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT] THEN
    USE_THEN "ij" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(h:real^2)$j = &0` THENL
   [UNDISCH_TAC `(h:real^2) = h$j % basis j` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `(f':real^2->real^2) (basis j) = vec 0` ASSUME_TAC THENL
   [UNDISCH_TAC `(h:real^2) = h$j % basis j` THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(f':real^2->real^2) h = vec 0` THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `f':real^2->real^2`; `x:real^2`;
                 `basis j:real^2`] SMT_DERIV_DIRECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < min d d' / &2 /\ min d d' / &2 < d /\ min d d' / &2 < d'`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t0 = min d d' / &2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:real^2->real^2)(x + t0 % basis j) - f x`; `j:num`]
    COMPONENT_LE_NORM) THEN
  SUBGOAL_THEN `&0 < c * t0` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Onto: a continuous increasing fibre map equal to a translation at both   *)
(* ends.                                                                     *)

let SMT_FIBRE_ONTO = prove
 (`!(f:real^1->real^2) k a b c.
        f continuous_on (:real^1) /\ (k = 1 \/ k = 2) /\
        (!u. drop u <= a ==> (f u)$k = drop u) /\
        (!u. b <= drop u ==> (f u)$k = drop u + c)
        ==> !y. ?u. (f u)$k = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lo") (LABEL_TAC "hi")))) THEN
  X_GEN_TAC `y:real` THEN
  MP_TAC(ISPECL [`f:real^1->real^2`; `lift(min (min a b) y)`;
                 `lift(max (max a b) (y - c))`; `y:real`; `k:num`]
    IVT_INCREASING_COMPONENT_ON_1) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_DROP; DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      USE_THEN "lo" (MP_TAC o SPEC `lift(min (min a b) y)`) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      USE_THEN "hi" (MP_TAC o SPEC `lift(max (max a b) (y - c))`) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The data of S3d.  The right-end shear (x1 + tau s x2,                     *)
(* sigma s x2) of the straightening isotopy: tau, sigma are read off Psi on  *)
(* the line x1 = R, trivial for |x2| >= r and at s = 0, 1; sigma s is a      *)
(* strictly increasing bijection of R with positive lower difference         *)
(* quotients near each point; tau is bounded for s in [0,1].                 *)
(* ------------------------------------------------------------------------- *)

let SMT_SMOOTH_VECTOR2 = prove
 (`!s (a:real^M->real) b.
        open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
        ==> smooth_map_on s (\x. vector[a x; b x]:real^2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. vector[a x; b x]:real^2`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[DIMINDEX_2; FORALL_2; VECTOR_2]);;

let SMT_LINE_SMOOTH = prove
 (`!R. smooth_map_on (:real^1) (\u. vector[R; drop u]:real^2)`,
  GEN_TAC THEN MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP; SMOOTH_MAP_ON_ID]);;

let SMT_END_DATA = prove
 (`!Psi Psi':real->real^2->real^2 tau sigma:real->real->real h r R.
        diffeo_isotopy Psi Psi' /\
        (!x. Psi (&0) x = x) /\ (!x. Psi (&1) x = h x) /\
        (!s x. x$1 <= --r \/ r <= abs(x$2) ==> Psi s x = x) /\
        (!s x. R <= x$1
               ==> Psi s x = vector[x$1 + tau s (x$2); sigma s (x$2)]) /\
        (!x. R <= norm x ==> h x = x)
        ==> (!s y. tau s y = (Psi s (vector[R; y]))$1 - R /\
                   sigma s y = (Psi s (vector[R; y]))$2) /\
            (!s y. r <= abs y ==> tau s y = &0 /\ sigma s y = y) /\
            (!y. tau (&0) y = &0 /\ sigma (&0) y = y) /\
            (!y. tau (&1) y = &0 /\ sigma (&1) y = y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "P0")
   (CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "strip")
   (CONJUNCTS_THEN2 (LABEL_TAC "right") (LABEL_TAC "hfar")))))) THEN
  SUBGOAL_THEN
   `!s y x1. R <= x1
             ==> (Psi:real->real^2->real^2) s (vector[x1; y]) =
                 vector[x1 + tau s y; sigma s y]`
  (LABEL_TAC "R1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "right" (MP_TAC o SPECL
     [`s:real`; `vector[x1; y]:real^2`]) THEN
    REWRITE_TAC[VECTOR_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN USE_THEN "R1" (fun th ->
      REWRITE_TAC[MATCH_MP th (SPEC `R:real` REAL_LE_REFL)]) THEN
    REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "R1" (MP_TAC o SPECL [`s:real`; `y:real`; `R:real`]) THEN
    USE_THEN "strip" (MP_TAC o SPECL [`s:real`; `vector[R; y]:real^2`]) THEN
    REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    USE_THEN "R1" (MP_TAC o SPECL [`&0`; `y:real`; `R:real`]) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    GEN_TAC THEN
    USE_THEN "R1" (MP_TAC o SPECL [`&1`; `y:real`; `abs R + &1`]) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h:real^2->real^2) (vector[abs R + &1; y]) = vector[abs R + &1; y]`
    SUBST1_TAC THENL
     [USE_THEN "hfar" MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`vector[abs R + &1; y]:real^2`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC]]);;

(* sigma s is a strictly increasing bijection of R, with positive lower      *)
(* difference quotients near each point.                                     *)

let SMT_END_SIGMA = prove
 (`!Psi Psi':real->real^2->real^2 tau sigma:real->real->real r R s.
        diffeo_isotopy Psi Psi' /\
        (!s y x1. R <= x1
                  ==> Psi s (vector[x1; y]) = vector[x1 + tau s y; sigma s y]) /\
        (!s y. r <= abs y ==> tau s y = &0 /\ sigma s y = y) /\
        (!s y. sigma s y = (Psi s (vector[R; y]))$2)
        ==> (!u v. u < v ==> sigma s u < sigma s v) /\
            (!y. ?u. sigma s u = y) /\
            (!v. ?c d. &0 < c /\ &0 < d /\
                       !t. &0 < t /\ t < d ==> c * t <= sigma s (v + t) - sigma s v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "R1")
    (CONJUNCTS_THEN2 (LABEL_TAC "far") (LABEL_TAC "sdef")))) THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^2) ((Psi:real->real^2->real^2) s) /\
    (!x. (Psi':real->real^2->real^2) s (Psi s x) = x) /\
    (!y. Psi s (Psi' s y) = y) /\
    diffeomorphism_on (:real^2) (:real^2) (Psi s) (Psi' s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeo_isotopy (Psi:real->real^2->real^2) Psi'` THEN
    REWRITE_TAC[diffeo_isotopy] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    SIMP_TAC[diffeomorphism_on; IN_UNIV];
    ALL_TAC] THEN
  (* smoothness and continuity *)
  SUBGOAL_THEN `smooth_map_on (:real^1) (\u. lift((sigma:real->real->real) s (drop u)))`
  ASSUME_TAC THENL
   [USE_THEN "sdef" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN `(\u:real^1. (Psi:real->real^2->real^2) s (vector[R; drop u])) =
                  Psi s o (\u. vector[R; drop u])` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMT_LINE_SMOOTH];
    ALL_TAC] THEN
  REMOVE_THEN "sdef" (K ALL_TAC) THEN
  SUBGOAL_THEN `(\u. lift((sigma:real->real->real) s (drop u))) continuous_on (:real^1)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  (* injectivity *)
  SUBGOAL_THEN `!u v. (sigma:real->real->real) s u = sigma s v ==> u = v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ABBREV_TAC `a = R + abs((tau:real->real->real) s u) + abs(tau s v)` THEN
    SUBGOAL_THEN
     `(Psi:real->real^2->real^2) s (vector[a - tau s u; u]) =
      Psi s (vector[a - (tau:real->real->real) s v; v])`
    MP_TAC THENL
     [USE_THEN "R1" (fun th -> W(fun (asl,w) ->
        MP_TAC(SPECL [`s:real`; `u:real`; `a - (tau:real->real->real) s u`] th) THEN
        MP_TAC(SPECL [`s:real`; `v:real`; `a - (tau:real->real->real) s v`] th))) THEN
      REPEAT(ANTS_TAC THENL [EXPAND_TAC "a" THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD];
      DISCH_THEN(MP_TAC o AP_TERM `(Psi':real->real^2->real^2) s`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN REWRITE_TAC[VECTOR_2]];
    ALL_TAC] THEN
  (* monotone increasing *)
  SUBGOAL_THEN `!u v. u < v ==> (sigma:real->real->real) s u < sigma s v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\u. lift((sigma:real->real->real) s (drop u))`; `(:real^1)`]
      CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
    REWRITE_TAC[IS_INTERVAL_UNIV; IN_UNIV; LIFT_DROP; LIFT_EQ] THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[DROP_EQ]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [FIRST_X_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`abs r`; `abs r + &1`]) THEN
      USE_THEN "far" (fun th -> MP_TAC(SPECL [`s:real`; `abs r`] th) THEN
                                MP_TAC(SPECL [`s:real`; `abs r + &1`] th)) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* onto *)
    MP_TAC(ISPECL [`\u. vector[drop u; (sigma:real->real->real) s (drop u)]:real^2`;
                   `2`; `--abs r`; `abs r`; `&0`] SMT_FIBRE_ONTO) THEN
    REWRITE_TAC[VECTOR_2; FORALL_LIFT; LIFT_DROP; REAL_ADD_RID] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
        ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMOOTH_MAP_ON_ID];
        X_GEN_TAC `u:real` THEN DISCH_TAC THEN
        USE_THEN "far" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `u:real` THEN DISCH_TAC THEN
        USE_THEN "far" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* local lower bound *)
  X_GEN_TAC `v:real` THEN
  ABBREV_TAC `p:real^2 = vector[R + &1; v]` THEN
  SUBGOAL_THEN `((Psi:real->real^2->real^2) s has_derivative
                 frechet_derivative (Psi s) (at p)) (at p)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `(Psi:real->real^2->real^2) s`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `p:real^2`);
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative ((Psi:real->real^2->real^2) s) (at p)` THEN
  SUBGOAL_THEN `linear(D:real^2->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t
        ==> ((Psi:real->real^2->real^2) s (p + t % basis 2))$2 =
            (sigma:real->real->real) s (v + t) /\
            Psi s (p + t % basis 1) = Psi s p + t % basis 1`
  (LABEL_TAC "moves") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "p" THEN
    SUBGOAL_THEN `vector[R + &1; v] + t % basis 2 = vector[R + &1; v + t]:real^2 /\
                  vector[R + &1; v] + t % basis 1 = vector[R + &1 + t; v]:real^2`
    (fun th -> REWRITE_TAC[th]) THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "R1" (fun th ->
      MP_TAC(SPECL [`s:real`; `v + t:real`; `R + &1`] th) THEN
      MP_TAC(SPECL [`s:real`; `v:real`; `R + &1 + t`] th) THEN
      MP_TAC(SPECL [`s:real`; `v:real`; `R + &1`] th)) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((Psi:real->real^2->real^2) s p)$2 = (sigma:real->real->real) s v`
  ASSUME_TAC THENL
   [USE_THEN "moves" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_LE_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* D e1 = e1 *)
  SUBGOAL_THEN `(D:real^2->real^2) (basis 1) = basis 1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(Psi:real->real^2->real^2) s`; `D:real^2->real^2`; `p:real^2`;
                   `basis 1:real^2`] SMT_DERIV_DIRECTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; NORM_POS_LE] THEN
    MATCH_MP_TAC SMT_REAL_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "moves" (MP_TAC o SPEC `d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - a - c:real^2 = b - c`] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    SUBGOAL_THEN `abs(d / &2) = d / &2 /\ &0 < d / &2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    MP_TAC(ISPECL [`(D:real^2->real^2)(basis 1)`; `basis 1:real^2`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* D is injective *)
  SUBGOAL_THEN `!h. (D:real^2->real^2) h = vec 0 ==> h = vec 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEO_DERIV_INJ THEN
    MAP_EVERY EXISTS_TAC [`(Psi:real->real^2->real^2) s`;
                          `(Psi':real->real^2->real^2) s`; `p:real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = ((D:real^2->real^2) (basis 2))$2` THEN
  SUBGOAL_THEN `~(a = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis 2 - ((D:real^2->real^2) (basis 2))$1 % basis 1`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th; MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; VEC_COMPONENT; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Psi:real->real^2->real^2) s`; `D:real^2->real^2`; `p:real^2`;
                 `basis 2:real^2`] SMT_DERIV_DIRECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `abs a / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < d
        ==> abs((sigma:real->real->real) s (v + t) - sigma s v - t * a)
            <= abs a / &2 * t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= n ==> n <= b ==> x <= b`) THEN
    MP_TAC(ISPECL [`(Psi:real->real^2->real^2) s (p + t % basis 2) - Psi s p -
                    t % (D:real^2->real^2) (basis 2)`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    USE_THEN "moves" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real`; `v + d / &2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs a = --a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < --a * (d / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a / &2`; `d:real`] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs a = a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* tau is bounded for s in [0,1].                                            *)

let SMT_END_TAU_BOUND = prove
 (`!Psi Psi':real->real^2->real^2 tau:real->real->real r R.
        diffeo_isotopy Psi Psi' /\
        (!s y. tau s y = (Psi s (vector[R; y]))$1 - R) /\
        (!s y. r <= abs y ==> tau s y = &0)
        ==> ?M. &0 < M /\ !s y. &0 <= s /\ s <= &1 ==> abs(tau s y) <= M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tdef")
    (LABEL_TAC "far"))) THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,2)finite_sum)
      (\z. (Psi:real->real^2->real^2) (drop(fstcart z)) (sndcart z))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeo_isotopy (Psi:real->real^2->real^2) Psi'` THEN
    SIMP_TAC[diffeo_isotopy; smooth_family; UNIV_PCROSS_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,1)finite_sum)
      (\w. lift(((Psi:real->real^2->real^2) (drop(fstcart w))
                   (vector[R; drop(sndcart w)]))$1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN
     `(\w:real^(1,1)finite_sum. (Psi:real->real^2->real^2) (drop(fstcart w))
                                   (vector[R; drop(sndcart w)])) =
      (\z. Psi (drop(fstcart z)) (sndcart z)) o
      (\w:real^(1,1)finite_sum. pastecart (fstcart w)
                                  (vector[R; drop(sndcart w)]:real^2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(1,2)finite_sum)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^(1,1)finite_sum)`; `\z:real^(1,1)finite_sum. z`;
                     `fstcart:real^(1,1)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX];
      MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP] THEN
      MP_TAC(ISPECL [`(:real^(1,1)finite_sum)`; `\z:real^(1,1)finite_sum. z`;
                     `sndcart:real^(1,1)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w:real^(1,1)finite_sum. lift(((Psi:real->real^2->real^2) (drop(fstcart w))
                                     (vector[R; drop(sndcart w)]))$1)`;
    `(:real^(1,1)finite_sum)`;
    `interval[vec 0:real^1,lift(&1)] PCROSS interval[lift(--abs r),lift(abs r)]`]
    ODE_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV; COMPACT_PCROSS;
                 COMPACT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + abs R + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= abs y` THENL
   [SUBGOAL_THEN `(tau:real->real->real) s y = &0` SUBST1_TAC THENL
     [USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (lift y):real^(1,1)finite_sum`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC; LIFT_DROP;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "tdef" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two fibrewise maps of S3d.                                            *)
(*   B x = (x1 + beta(x1) c(x2), x2),   beta u = smooth_step((u - a0)/L),     *)
(*   A z = (z1, (1 - g z1) z2 + g z1 sig(z2)),   g u = smooth_step(u - a0),   *)
(* are bijections of R^2 with injective derivative, B for |c| <= M and L    *)
(* large, A for sig a strictly increasing bijection equal to I far out.      *)
(* ------------------------------------------------------------------------- *)

let SMT_SHEAR_B = prove
 (`!(c:real->real) a0 L Ls M.
        smooth_map_on (:real^1) (\u. lift(c(drop u))) /\
        &0 < L /\ &0 < Ls /\ &0 <= M /\ &2 * Ls * (M + &1) <= L /\
        (!a b. abs(smooth_step a - smooth_step b) <= Ls * abs(a - b)) /\
        (!y. abs(c y) <= M)
        ==> smooth_map_on (:real^2)
              (\x. vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2) /\
            (!u v y. u < v
                     ==> (v - u) / &2 <=
                         (v + smooth_step((v - a0) / L) * c y) -
                         (u + smooth_step((u - a0) / L) * c y)) /\
            (!(x:real^2) (x':real^2).
                    vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2 =
                    vector[x'$1 + smooth_step((x'$1 - a0) / L) * c(x'$2); x'$2]
                    ==> x = x') /\
            (!y. ?x:real^2. vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2 = y) /\
            (!(x:real^2) (h:real^2). frechet_derivative
                     (\x:real^2. vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2)
                     (at x) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip")
   (LABEL_TAC "cb"))))))) THEN
  ABBREV_TAC `B = \x:real^2. vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2` THEN
  SUBGOAL_THEN `!x:real^2. ((B:real^2->real^2) x)$1 = x$1 + smooth_step((x$1 - a0) / L) * c(x$2) /\
                           (B x)$2 = x$2`
  (LABEL_TAC "Bc") THENL [EXPAND_TAC "B" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]:real^2 =
                           (B:real^2->real^2) x`
  (LABEL_TAC "Bfold") THENL [EXPAND_TAC "B" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (B:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
    REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^2) (\x:real^2. lift(x$1)) /\
      smooth_map_on (:real^2) (\x:real^2. lift(x$2))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC(ISPECL [`(:real^2)`;
                   `\x:real^2. lift(smooth_step((x$1 - a0) / L))`;
                   `\x:real^2. lift(c((x:real^2)$2))`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift((x$1 - a0) / L)`]
        SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
      REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `(\x:real^2. lift((x$1 - a0) / L)) =
                    (\x. lift(inv L * drop(lift(x$1) - lift a0)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; DROP_SUB; LIFT_DROP] THEN GEN_TAC THEN
        AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(:real^2)`; `inv L`; `\x:real^2. lift(x$1) - lift a0`]
        SMOOTH_MAP_ON_LIFT_CMUL) THEN
      REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
      SUBGOAL_THEN `(\x:real^2. lift(c((x:real^2)$2))) =
                    (\u. lift(c(drop u))) o (\x:real^2. lift(x$2))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]];
    ALL_TAC] THEN
  (* the fibre map is increasing with slope at least 1/2 *)
  SUBGOAL_THEN `(Ls * M) / L <= &1 / &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v y. u < v
            ==> (v - u) / &2 <=
                (v + smooth_step((v - a0) / L) * (c:real->real) y) -
                (u + smooth_step((u - a0) / L) * (c:real->real) y)`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `abs(smooth_step((v - a0) / L) - smooth_step((u - a0) / L)) <= Ls * ((v - u) / L)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Ls * abs((v - a0) / L - (u - a0) / L)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(v - a0) / L - (u - a0) / L = (v - u) / L` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs((smooth_step((v - a0) / L) - smooth_step((u - a0) / L)) * (c:real->real) y)
      <= (v - u) * ((Ls * M) / L)`
    MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(Ls * ((v - u) / L)) * M` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v - u) * ((Ls * M) / L) <= (v - u) * (&1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "Bfold" (fun th -> REWRITE_TAC[th]) THEN
  (* injective *)
  SUBGOAL_THEN `!x x':real^2. (B:real^2->real^2) x = B x' ==> x = x'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2)$2 = (x':real^2)$2` ASSUME_TAC THENL
     [MP_TAC(AP_TERM `\v:real^2. v$2` (ASSUME `(B:real^2->real^2) x = B x'`)) THEN
      USE_THEN "Bc" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2)$1 = (x':real^2)$1` ASSUME_TAC THENL
     [MP_TAC(AP_TERM `\v:real^2. v$1` (ASSUME `(B:real^2->real^2) x = B x'`)) THEN
      USE_THEN "Bc" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (REAL_ARITH `(x:real^2)$1 < (x':real^2)$1 \/ x$1 = x'$1 \/ x'$1 < x$1`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "mono" (fun mth -> FIRST_ASSUM(fun th ->
        MP_TAC(SPEC `(x':real^2)$2` (MATCH_MP mth th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* onto *)
    X_GEN_TAC `y:real^2` THEN
    MP_TAC(ISPECL [`\w:real^1. (B:real^2->real^2) (vector[drop w; (y:real^2)$2])`;
                   `1`; `a0:real`; `a0 + L`; `c((y:real^2)$2):real`] SMT_FIBRE_ONTO) THEN
    USE_THEN "Bc" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[VECTOR_2] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        SUBGOAL_THEN
         `(\w:real^1. (B:real^2->real^2) (vector[drop w; (y:real^2)$2])) =
          B o (\w. vector[drop w; y$2])` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
        REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
        X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
        SUBGOAL_THEN `smooth_step((drop w - a0) / L) = &0` SUBST1_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_0 THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
        SUBGOAL_THEN `smooth_step((drop w - a0) / L) = &1` SUBST1_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_1 THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      DISCH_THEN(X_CHOOSE_TAC `w:real^1` o SPEC `(y:real^2)$1`) THEN
      EXISTS_TAC `vector[drop w; (y:real^2)$2]:real^2` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
      USE_THEN "Bc" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[VECTOR_2]];
    ALL_TAC] THEN
  (* derivative injective *)
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`B:real^2->real^2`; `frechet_derivative (B:real^2->real^2) (at x)`;
                 `x:real^2`; `2`; `1`; `&1 / &2`; `&1`] SMT_TRIANG_DERIV_INJ) THEN
  ANTS_TAC THENL [ALL_TAC; EXPAND_TAC "B" THEN SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `B:real^2->real^2`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `x:real^2`);
    ARITH_TAC;
    USE_THEN "Bc" (fun th -> REWRITE_TAC[th]);
    REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    USE_THEN "Bc" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_2; ARITH; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    USE_THEN "mono" (MP_TAC o SPECL [`(x:real^2)$1`; `(x:real^2)$1 + t`;
                                     `(x:real^2)$2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC]);;

let SMT_SHEAR_A = prove
 (`!(sig:real->real) a0 r0.
        smooth_map_on (:real^1) (\u. lift(sig(drop u))) /\
        (!u v. u < v ==> sig u < sig v) /\
        (!v. ?c d. &0 < c /\ &0 < d /\
                   !t. &0 < t /\ t < d ==> c * t <= sig(v + t) - sig v) /\
        (!y. r0 <= abs y ==> sig y = y)
        ==> smooth_map_on (:real^2)
              (\z. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                smooth_step(z$1 - a0) * sig(z$2)]:real^2) /\
            (!(z:real^2) (z':real^2).
                vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                            smooth_step(z$1 - a0) * sig(z$2)]:real^2 =
                vector[z'$1; (&1 - smooth_step(z'$1 - a0)) * z'$2 +
                             smooth_step(z'$1 - a0) * sig(z'$2)]
                ==> z = z') /\
            (!y. ?z:real^2. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                        smooth_step(z$1 - a0) * sig(z$2)]:real^2 = y) /\
            (!(z:real^2) (h:real^2).
                frechet_derivative
                  (\z:real^2. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                          smooth_step(z$1 - a0) * sig(z$2)]:real^2)
                  (at z) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inc")
   (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "far")))) THEN
  ABBREV_TAC `A = \z:real^2. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                          smooth_step(z$1 - a0) * sig(z$2)]:real^2` THEN
  SUBGOAL_THEN
   `!z:real^2. ((A:real^2->real^2) z)$1 = z$1 /\
               (A z)$2 = (&1 - smooth_step(z$1 - a0)) * z$2 +
                         smooth_step(z$1 - a0) * sig(z$2)`
  (LABEL_TAC "Ac") THENL [EXPAND_TAC "A" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                           smooth_step(z$1 - a0) * sig(z$2)]:real^2 = (A:real^2->real^2) z`
  (LABEL_TAC "Afold") THENL [EXPAND_TAC "A" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (A:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
    REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^2) (\x:real^2. lift(x$1)) /\
      smooth_map_on (:real^2) (\x:real^2. lift(x$2)) /\
      smooth_map_on (:real^2) (\x:real^2. lift(smooth_step(x$1 - a0))) /\
      smooth_map_on (:real^2) (\x:real^2. lift(sig(x$2)))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
        MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(x$1 - a0)`]
          SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
        REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
        SUBGOAL_THEN `(\x:real^2. lift(sig((x:real^2)$2))) =
                      (\u. lift(sig(drop u))) o (\x:real^2. lift(x$2))`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^2)`;
                     `\x:real^2. lift(&1 - smooth_step(x$1 - a0))`;
                     `\x:real^2. lift(x$2)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
      MP_TAC(ISPECL [`(:real^2)`;
                     `\x:real^2. lift(smooth_step(x$1 - a0))`;
                     `\x:real^2. lift(sig((x:real^2)$2))`] SMOOTH_MAP_ON_LIFT_MUL) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]];
    ALL_TAC] THEN
  (* the fibre maps are strictly increasing *)
  SUBGOAL_THEN
   `!w v v'. v < v'
             ==> (&1 - smooth_step(w - a0)) * v + smooth_step(w - a0) * sig v <
                 (&1 - smooth_step(w - a0)) * v' + smooth_step(w - a0) * sig v'`
  (LABEL_TAC "fmono") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(sig:real->real) v < sig v'` ASSUME_TAC THENL
     [USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `w - a0:real` SMOOTH_STEP_BOUNDS) THEN
    ABBREV_TAC `g = smooth_step(w - a0)` THEN STRIP_TAC THEN
    ABBREV_TAC `m = min (v' - v) ((sig:real->real) v' - sig v)` THEN
    SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - g) * ((v' - v) - m) /\
                  &0 <= g * (((sig:real->real) v' - sig v) - m)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN EXPAND_TAC "m" THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "Afold" (fun th -> REWRITE_TAC[th]) THEN
  (* injective *)
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2)$1 = (z':real^2)$1` ASSUME_TAC THENL
     [MP_TAC(AP_TERM `\v:real^2. v$1` (ASSUME `(A:real^2->real^2) z = A z'`)) THEN
      USE_THEN "Ac" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2)$2 = (z':real^2)$2` ASSUME_TAC THENL
     [MP_TAC(AP_TERM `\v:real^2. v$2` (ASSUME `(A:real^2->real^2) z = A z'`)) THEN
      USE_THEN "Ac" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (REAL_ARITH `(z:real^2)$2 < (z':real^2)$2 \/ z$2 = z'$2 \/ z'$2 < z$2`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "fmono" (fun mth -> FIRST_ASSUM(fun th ->
        MP_TAC(MATCH_MP (SPEC `(z':real^2)$1` mth) th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* onto *)
    X_GEN_TAC `y:real^2` THEN
    MP_TAC(ISPECL [`\w:real^1. (A:real^2->real^2) (vector[(y:real^2)$1; drop w])`;
                   `2`; `--abs r0`; `abs r0`; `&0`] SMT_FIBRE_ONTO) THEN
    USE_THEN "Ac" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[VECTOR_2] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        SUBGOAL_THEN
         `(\w:real^1. (A:real^2->real^2) (vector[(y:real^2)$1; drop w])) =
          A o (\w. vector[y$1; drop w])` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
        REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
        X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
        USE_THEN "far" (MP_TAC o SPEC `drop w`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
        USE_THEN "far" (MP_TAC o SPEC `drop w`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_TAC `w:real^1` o SPEC `(y:real^2)$2`) THEN
      EXISTS_TAC `vector[(y:real^2)$1; drop w]:real^2` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
      USE_THEN "Ac" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[VECTOR_2]];
    ALL_TAC] THEN
  (* derivative injective *)
  MAP_EVERY X_GEN_TAC [`z:real^2`; `h:real^2`] THEN
  USE_THEN "loc" (X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) o
    SPEC `(z:real^2)$2`) THEN
  MP_TAC(ISPECL [`A:real^2->real^2`; `frechet_derivative (A:real^2->real^2) (at z)`;
                 `z:real^2`; `1`; `2`; `min (&1) c0`; `d0:real`] SMT_TRIANG_DERIV_INJ) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `A:real^2->real^2`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `z:real^2`);
    ARITH_TAC;
    USE_THEN "Ac" (fun th -> REWRITE_TAC[th]);
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    USE_THEN "Ac" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_2; ARITH; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(z:real^2)$1 - a0` SMOOTH_STEP_BOUNDS) THEN
    ABBREV_TAC `g = smooth_step((z:real^2)$1 - a0)` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (&1 - g) * ((&1 - min (&1) c0) * t) /\
                  &0 <= g * ((sig:real->real) ((z:real^2)$2 + t) - sig(z$2) -
                             min (&1) c0 * t)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `m * t <= c0 * t /\ c0 * t <= x ==> &0 <= x - m * t`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* S3d, the end correction.  With s = smooth_step(1 - t) and                 *)
(* the two fibrewise maps (B s for tau s, A s for sigma s), the family       *)
(*   K t = A s o B s o (Psi s)^-1                                            *)
(* is smooth, each K t is a bijection with injective derivative, K t is      *)
(* h^-1 for t <= 0 and I for t >= 1, and K t = I far out (A s o B s agrees   *)
(* with Psi s for large x1, both are I off the strip).  H t = (K t)^-1.      *)
(* ------------------------------------------------------------------------- *)

let SMT_FAMILY_COMPOSE = prove
 (`!(FF:real->real^N->real^P) (GG:real->real^M->real^N).
        smooth_family (:real^N) FF /\ smooth_family (:real^M) GG
        ==> smooth_family (:real^M) (\t x. FF t (GG t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^(1,M)finite_sum. (FF:real->real^N->real^P) (drop(fstcart z))
        ((GG:real->real^M->real^N) (drop(fstcart z)) (sndcart z))) =
    (\w:real^(1,N)finite_sum. FF (drop(fstcart w)) (sndcart w)) o
    (\z:real^(1,M)finite_sum. pastecart (fstcart z) (GG (drop(fstcart z)) (sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:real^(1,M)finite_sum)`; `\z:real^(1,M)finite_sum. z`;
                 `fstcart:real^(1,M)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX]);;

let SMT_DIFFEO_ISOTOPY_SYM = prove
 (`!(H:real->real^N->real^N) K. diffeo_isotopy H K ==> diffeo_isotopy K H`,
  REWRITE_TAC[diffeo_isotopy] THEN MESON_TAC[DIFFEOMORPHISM_ON_SYM]);;

let SMT_COMPOSE_DERIV_INJ = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
        (f has_derivative frechet_derivative f (at x)) (at x) /\
        (g has_derivative frechet_derivative g (at (f x))) (at (f x)) /\
        (!h. frechet_derivative f (at x) h = vec 0 ==> h = vec 0) /\
        (!k. frechet_derivative g (at (f x)) k = vec 0 ==> k = vec 0)
        ==> (g o f has_derivative frechet_derivative (g o f) (at x)) (at x) /\
            (!h. frechet_derivative (g o f) (at x) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((g:real^N->real^P) o (f:real^M->real^N) has_derivative
     frechet_derivative g (at (f x)) o frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

let SMT_SNDCART_COMPONENT_SMOOTH = prove
 (`!k. smooth_map_on (:real^(1,N)finite_sum) (\w. lift((sndcart w)$k))`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\z:real^(1,N)finite_sum. z`;
                 `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX]);;

(* The data on the line x1 = R are jointly smooth in (s, x2).                *)

let SMT_END_LINE_SMOOTH = prove
 (`!(Psi:real->real^2->real^2) R k.
        smooth_family (:real^2) Psi
        ==> smooth_map_on (:real^(1,2)finite_sum)
              (\w. lift((Psi (drop(fstcart w)) (vector[R; (sndcart w)$2]))$k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN REWRITE_TAC[OPEN_UNIV] THEN
  SUBGOAL_THEN
   `(\w:real^(1,2)finite_sum. (Psi:real->real^2->real^2) (drop(fstcart w))
                                 (vector[R; (sndcart w)$2])) =
    (\z. Psi (drop(fstcart z)) (sndcart z)) o
    (\w:real^(1,2)finite_sum. pastecart (fstcart w) (vector[R; (sndcart w)$2]:real^2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^(1,2)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`; `\z:real^(1,2)finite_sum. z`;
                   `fstcart:real^(1,2)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX];
    MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMT_SNDCART_COMPONENT_SMOOTH]]);;

let SMT_END_LINE_SMOOTH1 = prove
 (`!(Psi:real->real^2->real^2) Psi' R s k.
        diffeo_isotopy Psi Psi'
        ==> smooth_map_on (:real^1) (\u. lift((Psi s (vector[R; drop u]))$k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  REWRITE_TAC[OPEN_UNIV] THEN
  SUBGOAL_THEN `(\u:real^1. (Psi:real->real^2->real^2) s (vector[R; drop u])) =
                Psi s o (\u. vector[R; drop u])` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMT_LINE_SMOOTH] THEN
  MATCH_MP_TAC SMT_FAMILY_SLICE THEN REWRITE_TAC[OPEN_UNIV] THEN
  UNDISCH_TAC `diffeo_isotopy (Psi:real->real^2->real^2) Psi'` THEN
  SIMP_TAC[diffeo_isotopy]);;

(* The two shear families are smooth in (s, x).                              *)

let SMT_END_B_FAMILY = prove
 (`!(c:real->real->real) a0 L.
        smooth_map_on (:real^(1,2)finite_sum)
          (\w. lift(c (drop(fstcart w)) ((sndcart w)$2)))
        ==> smooth_family (:real^2)
              (\s (x:real^2). vector[x$1 + smooth_step((x$1 - a0) / L) * c s (x$2);
                                     x$2]:real^2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
  MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
  REWRITE_TAC[OPEN_UNIV; SMT_SNDCART_COMPONENT_SMOOTH; LIFT_ADD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMT_SNDCART_COMPONENT_SMOOTH] THEN
  MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                 `\w:real^(1,2)finite_sum. lift(smooth_step(((sndcart w)$1 - a0) / L))`;
                 `\w:real^(1,2)finite_sum. lift(c (drop(fstcart w)) ((sndcart w)$2))`]
    SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                 `\w:real^(1,2)finite_sum. lift(((sndcart w)$1 - a0) / L)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `(\w:real^(1,2)finite_sum. lift(((sndcart w)$1 - a0) / L)) =
                (\w. lift(inv L * drop(lift((sndcart w)$1) - lift a0)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DROP_SUB; LIFT_DROP] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`; `inv L`;
                 `\w:real^(1,2)finite_sum. lift((sndcart w)$1) - lift a0`]
    SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMT_SNDCART_COMPONENT_SMOOTH]);;

let SMT_END_A_FAMILY = prove
 (`!(sig:real->real->real) a0.
        smooth_map_on (:real^(1,2)finite_sum)
          (\w. lift(sig (drop(fstcart w)) ((sndcart w)$2)))
        ==> smooth_family (:real^2)
              (\s (z:real^2). vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                          smooth_step(z$1 - a0) * sig s (z$2)]:real^2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,2)finite_sum) (\w. lift(smooth_step((sndcart w)$1 - a0)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                   `\w:real^(1,2)finite_sum. lift((sndcart w)$1 - a0)`]
      SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMT_SNDCART_COMPONENT_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
  MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
  REWRITE_TAC[OPEN_UNIV; SMT_SNDCART_COMPONENT_SMOOTH; LIFT_ADD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                   `\w:real^(1,2)finite_sum. lift(&1 - smooth_step((sndcart w)$1 - a0))`;
                   `\w:real^(1,2)finite_sum. lift((sndcart w)$2)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMT_SNDCART_COMPONENT_SMOOTH] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    MP_TAC(ISPECL [`(:real^(1,2)finite_sum)`;
                   `\w:real^(1,2)finite_sum. lift(smooth_step((sndcart w)$1 - a0))`;
                   `\w:real^(1,2)finite_sum. lift(sig (drop(fstcart w)) ((sndcart w)$2))`]
      SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]]);;

(* The family K is smooth.                                                   *)

let SMT_END_K_SMOOTH = prove
 (`!(Psi:real->real^2->real^2) (Psi':real->real^2->real^2) tau sigma
    (A:real->real^2->real^2) (B:real->real^2->real^2) R a0 L.
        smooth_family (:real^2) Psi /\ smooth_family (:real^2) Psi' /\
        (!s y. tau s y = (Psi s (vector[R; y]))$1 - R /\
               sigma s y = (Psi s (vector[R; y]))$2) /\
        (!s x. B s x = vector[x$1 + smooth_step((x$1 - a0) / L) * tau s (x$2); x$2]) /\
        (!s z. A s z = vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                   smooth_step(z$1 - a0) * sigma s (z$2)])
        ==> smooth_family (:real^2)
              (\t y. A (smooth_step(&1 - t)) (B (smooth_step(&1 - t))
                         (Psi' (smooth_step(&1 - t)) y)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "def") (CONJUNCTS_THEN2 (LABEL_TAC "Bdef")
   (LABEL_TAC "Adef"))))) THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,2)finite_sum)
      (\w. lift((tau:real->real->real) (drop(fstcart w)) ((sndcart w)$2))) /\
    smooth_map_on (:real^(1,2)finite_sum)
      (\w. lift((sigma:real->real->real) (drop(fstcart w)) ((sndcart w)$2)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "def" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMT_END_LINE_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMT_END_LINE_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_family (:real^2) (B:real->real^2->real^2)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(B:real->real^2->real^2) =
      (\s x. vector[x$1 + smooth_step((x$1 - a0) / L) * (tau:real->real->real) s (x$2);
                    x$2])`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]);
      MATCH_MP_TAC SMT_END_B_FAMILY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_family (:real^2) (A:real->real^2->real^2)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(A:real->real^2->real^2) =
      (\s z. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                         smooth_step(z$1 - a0) * (sigma:real->real->real) s (z$2)])`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN USE_THEN "Adef" (fun th -> REWRITE_TAC[th]);
      MATCH_MP_TAC SMT_END_A_FAMILY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "def" (K ALL_TAC) THEN REMOVE_THEN "Bdef" (K ALL_TAC) THEN
  REMOVE_THEN "Adef" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `smooth_family (:real^2)
      (\s y. (A:real->real^2->real^2) s ((B:real->real^2->real^2) s
               ((Psi':real->real^2->real^2) s y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^2->real^2`;
                   `\s y. (B:real->real^2->real^2) s ((Psi':real->real^2->real^2) s y)`]
      SMT_FAMILY_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`B:real->real^2->real^2`; `Psi':real->real^2->real^2`]
      SMT_FAMILY_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`;
                 `\s y. (A:real->real^2->real^2) s ((B:real->real^2->real^2) s
                          ((Psi':real->real^2->real^2) s y))`;
                 `\t. smooth_step(&1 - t)`] SMT_FAMILY_REPARAM) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lift o (\t. smooth_step(&1 - t)) o drop =
                lift o (\t. smooth_step(--(&1) * t - --(&1))) o drop`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SMOOTH_STEP_AFFINE_SMOOTH]]);;

(* For fixed s, A o B o P is a bijection with injective derivative.          *)

let SMT_END_KSLICE = prove
 (`!(A:real^2->real^2) B P Q.
        smooth_map_on (:real^2) A /\ smooth_map_on (:real^2) B /\
        diffeomorphism_on (:real^2) (:real^2) P Q /\
        (!z z'. A z = A z' ==> z = z') /\ (!y. ?z. A z = y) /\
        (!x x'. B x = B x' ==> x = x') /\ (!y. ?x. B x = y) /\
        (!z h. frechet_derivative A (at z) h = vec 0 ==> h = vec 0) /\
        (!x h. frechet_derivative B (at x) h = vec 0 ==> h = vec 0)
        ==> (!y y'. A(B(P y)) = A(B(P y')) ==> y = y') /\
            (!x. ?y. A(B(P y)) = x) /\
            (!y h. frechet_derivative (\y. A(B(P y))) (at y) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Ai")
   (CONJUNCTS_THEN2 (LABEL_TAC "Ao") (CONJUNCTS_THEN2 (LABEL_TAC "Bi")
   (CONJUNCTS_THEN2 (LABEL_TAC "Bo") (CONJUNCTS_THEN2 (LABEL_TAC "Ad")
   (LABEL_TAC "Bd"))))))))) THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^2) (P:real^2->real^2) /\ (!y. (Q:real^2->real^2) (P y) = y) /\
    (!x. P (Q x) = x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^2) (:real^2) (P:real^2->real^2) Q` THEN
    SIMP_TAC[diffeomorphism_on; IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^2->real^2) y = P y'` MP_TAC THENL
     [USE_THEN "Bi" MATCH_MP_TAC THEN USE_THEN "Ai" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `Q:real^2->real^2`) THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^2` THEN
    USE_THEN "Ao" (X_CHOOSE_TAC `z:real^2` o SPEC `x:real^2`) THEN
    USE_THEN "Bo" (X_CHOOSE_TAC `w:real^2` o SPEC `z:real^2`) THEN
    EXISTS_TAC `(Q:real^2->real^2) w` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\y. (A:real^2->real^2) (B ((P:real^2->real^2) y))) = A o (B o P)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `!(f:real^2->real^2) x. smooth_map_on (:real^2) f
                    ==> (f has_derivative frechet_derivative f (at x)) (at x)`
    (LABEL_TAC "hd") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`(:real^2)`; `f:real^2->real^2`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!k. frechet_derivative (P:real^2->real^2) (at y) k = vec 0 ==> k = vec 0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEO_DERIV_INJ THEN
      MAP_EVERY EXISTS_TAC [`P:real^2->real^2`; `Q:real^2->real^2`; `y:real^2`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`P:real^2->real^2`; `B:real^2->real^2`; `y:real^2`]
      SMT_COMPOSE_DERIV_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "hd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "hd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "Bd" (fun th -> REWRITE_TAC[th])];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`(B:real^2->real^2) o (P:real^2->real^2)`; `A:real^2->real^2`;
                   `y:real^2`] SMT_COMPOSE_DERIV_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[o_THM] THEN USE_THEN "hd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "Ad" (fun th -> REWRITE_TAC[th])];
      DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2)]]);;

(* For fixed s, A o B o (Psi s)^-1 is the identity far out.                  *)

let SMT_END_KFAR = prove
 (`!(P:real^2->real^2) (Q:real^2->real^2) (A:real^2->real^2) (B:real^2->real^2)
    (c:real->real) (sig:real->real) r R a0 L M.
        (!x. P (Q x) = x) /\
        (!x. x$1 <= --r \/ r <= abs(x$2) ==> Q x = x) /\
        (!y x1. R <= x1 ==> Q (vector[x1; y]) = vector[x1 + c y; sig y]) /\
        (!y. r <= abs y ==> c y = &0 /\ sig y = y) /\
        (!y. ?v. sig v = y) /\ (!y. abs(c y) <= M) /\
        (!x. B x = vector[x$1 + smooth_step((x$1 - a0) / L) * c(x$2); x$2]) /\
        (!z. A z = vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                               smooth_step(z$1 - a0) * sig(z$2)]) /\
        abs R + abs r + &1 <= a0 /\ &1 <= L /\ &0 <= M
        ==> !y. a0 + L + M + abs r <= norm y ==> A(B(P y)) = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PQ") (CONJUNCTS_THEN2 (LABEL_TAC "strip")
   (CONJUNCTS_THEN2 (LABEL_TAC "right") (CONJUNCTS_THEN2 (LABEL_TAC "far")
   (CONJUNCTS_THEN2 (LABEL_TAC "onto") (CONJUNCTS_THEN2 (LABEL_TAC "cb")
   (CONJUNCTS_THEN2 (LABEL_TAC "Bdef") (CONJUNCTS_THEN2 (LABEL_TAC "Adef")
   STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `!x:real^2. Q x = x ==> P x = x` (LABEL_TAC "fixP") THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    USE_THEN "PQ" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* off the strip *)
  SUBGOAL_THEN `!x:real^2. r <= abs(x$2) ==> (A:real^2->real^2)((B:real^2->real^2)((P:real^2->real^2) x)) = x`
  (LABEL_TAC "c1") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^2->real^2) x = x` SUBST1_TAC THENL
     [USE_THEN "fixP" MATCH_MP_TAC THEN USE_THEN "strip" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "far" (MP_TAC o SPEC `(x:real^2)$2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Adef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* left of the strip *)
  SUBGOAL_THEN `!x:real^2. x$1 <= --r ==> (A:real^2->real^2)((B:real^2->real^2)((P:real^2->real^2) x)) = x`
  (LABEL_TAC "c2") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^2->real^2) x = x` SUBST1_TAC THENL
     [USE_THEN "fixP" MATCH_MP_TAC THEN USE_THEN "strip" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step(((x:real^2)$1 - a0) / L) = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step((x:real^2)$1 - a0) = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Adef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO;
                    REAL_MUL_LID] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
    ALL_TAC] THEN
  (* far right: A o B agrees with Q there *)
  SUBGOAL_THEN `!x:real^2. a0 + L + M <= x$1 ==> (A:real^2->real^2)((B:real^2->real^2)((P:real^2->real^2) x)) = x`
  (LABEL_TAC "c3") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "onto" (X_CHOOSE_TAC `v:real` o SPEC `(x:real^2)$2`) THEN
    USE_THEN "cb" (ASSUME_TAC o SPEC `v:real`) THEN
    SUBGOAL_THEN `(Q:real^2->real^2) (vector[(x:real^2)$1 - (c:real->real) v; v]) = x`
    ASSUME_TAC THENL
     [USE_THEN "right" (MP_TAC o SPECL [`v:real`; `(x:real^2)$1 - (c:real->real) v`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(P:real^2->real^2) x = vector[(x:real^2)$1 - (c:real->real) v; v]`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      USE_THEN "PQ" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step((((x:real^2)$1 - (c:real->real) v) - a0) / L) = &1`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step((x:real^2)$1 - a0) = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Adef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_MUL_LID; REAL_SUB_ADD; REAL_SUB_REFL;
                    REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `r <= abs((y:real^2)$2)` THENL
   [USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^2)$1 <= --r` THENL
   [USE_THEN "c2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "c3" MATCH_MP_TAC THEN
  MP_TAC(ISPEC `y:real^2` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN ASM_REAL_ARITH_TAC);;

(* The inverse family of such a K is the required isotopy.                   *)

let SMT_END_FROM_FAMILY = prove
 (`!(K:real->real^N->real^N) (h:real^N->real^N) R'.
        smooth_family (:real^N) K /\
        (!t y y'. K t y = K t y' ==> y = y') /\ (!t x. ?y. K t y = x) /\
        (!t y k. frechet_derivative (K t) (at y) k = vec 0 ==> k = vec 0) /\
        (!t y. t <= &0 ==> K t (h y) = y) /\
        (!t y. &1 <= t ==> K t y = y) /\
        (!t y. R' <= norm y ==> K t y = y)
        ==> ?H K'. diffeo_isotopy H K' /\
                   (!t x. t <= &0 ==> H t x = h x) /\
                   (!t x. &1 <= t ==> H t x = x) /\
                   (?R'. !t x. R' <= norm x ==> H t x = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "onto") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "K0") (CONJUNCTS_THEN2 (LABEL_TAC "K1")
   (LABEL_TAC "Kfar"))))))) THEN
  ABBREV_TAC `H = \t x. @y. (K:real->real^N->real^N) t y = x` THEN
  SUBGOAL_THEN `!t x. (K:real->real^N->real^N) t ((H:real->real^N->real^N) t x) = x`
  (LABEL_TAC "KH") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "H" THEN CONV_TAC SELECT_CONV THEN
    USE_THEN "onto" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!t y. (H:real->real^N->real^N) t ((K:real->real^N->real^N) t y) = y`
  (LABEL_TAC "HK") THENL
   [REPEAT GEN_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN
    USE_THEN "KH" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x y. (K:real->real^N->real^N) t y = x ==> (H:real->real^N->real^N) t x = y`
  (LABEL_TAC "uniq") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "HK" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`H:real->real^N->real^N`; `K:real->real^N->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEO_ISOTOPY_SYM THEN MATCH_MP_TAC SMT_FAMILY_INVERSE_SMOOTH THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "uniq" MATCH_MP_TAC THEN
    USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "uniq" MATCH_MP_TAC THEN
    USE_THEN "K1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `R':real` THEN REPEAT STRIP_TAC THEN USE_THEN "uniq" MATCH_MP_TAC THEN
    USE_THEN "Kfar" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* S3d.                                                                      *)

let SMT_END_CORRECTION = prove
 (`SMT_END_CORRECTION_STATEMENT`,
  REWRITE_TAC[SMT_END_CORRECTION_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`Psi:real->real^2->real^2`; `Psi':real->real^2->real^2`;
                       `tau:real->real->real`; `sigma:real->real->real`;
                       `h:real^2->real^2`; `r:real`; `R:real`] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SMT_END_DATA th) THEN
    CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "P0")
     (CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "strip")
     (CONJUNCTS_THEN2 (LABEL_TAC "right") (LABEL_TAC "hfar"))))) th) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "def") (CONJUNCTS_THEN2 (LABEL_TAC "far")
   (CONJUNCTS_THEN2 (LABEL_TAC "d0") (LABEL_TAC "d1")))) THEN
  SUBGOAL_THEN
   `!s y x1. R <= x1
             ==> (Psi:real->real^2->real^2) s (vector[x1; y]) =
                 vector[x1 + (tau:real->real->real) s y; (sigma:real->real->real) s y]`
  (LABEL_TAC "R1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "right" (MP_TAC o SPECL
     [`s:real`; `vector[x1; y]:real^2`]) THEN
    REWRITE_TAC[VECTOR_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_family (:real^2) (Psi:real->real^2->real^2) /\
    smooth_family (:real^2) (Psi':real->real^2->real^2) /\
    (!s. diffeomorphism_on (:real^2) (:real^2) (Psi' s) (Psi s)) /\
    (!s x. Psi' s (Psi s x) = x)`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "PP")))) THENL
   [UNDISCH_TAC `diffeo_isotopy (Psi:real->real^2->real^2) Psi'` THEN
    REWRITE_TAC[diffeo_isotopy] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real` THENL
     [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN SIMP_TAC[diffeomorphism_on; IN_UNIV]];
    ALL_TAC] THEN
  (* constants *)
  MP_TAC(ISPECL [`Psi:real->real^2->real^2`; `Psi':real->real^2->real^2`;
                 `tau:real->real->real`; `r:real`; `R:real`] SMT_END_TAU_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "def" (fun th -> REWRITE_TAC[th]);
      REPEAT STRIP_TAC THEN USE_THEN "far" (MP_TAC o SPECL [`s:real`; `y:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Mb")))] THEN
  X_CHOOSE_THEN `Ls:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip"))
    SMT_STEP_LIPSCHITZ THEN
  ABBREV_TAC `a0 = abs R + abs r + &1` THEN
  ABBREV_TAC `L = &2 * Ls * (M + &1) + M + &1` THEN
  SUBGOAL_THEN `&0 <= M /\ &0 < L /\ &1 <= L /\ &2 * Ls * (M + &1) <= L /\
                abs R + abs r + &1 <= a0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &2 * Ls * (M + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "L" THEN EXPAND_TAC "a0" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the shear families *)
  ABBREV_TAC `B = \s (x:real^2). vector[x$1 + smooth_step((x$1 - a0) / L) *
                                         (tau:real->real->real) s (x$2); x$2]:real^2` THEN
  ABBREV_TAC `A = \s (z:real^2). vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                                         smooth_step(z$1 - a0) *
                                         (sigma:real->real->real) s (z$2)]:real^2` THEN
  SUBGOAL_THEN
   `!s x. (B:real->real^2->real^2) s x =
          vector[x$1 + smooth_step((x$1 - a0) / L) * (tau:real->real->real) s (x$2); x$2]`
  (LABEL_TAC "Bdef") THENL [EXPAND_TAC "B" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z. (A:real->real^2->real^2) s z =
          vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                      smooth_step(z$1 - a0) * (sigma:real->real->real) s (z$2)]`
  (LABEL_TAC "Adef") THENL [EXPAND_TAC "A" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_family (:real^2)
      (\t y. (A:real->real^2->real^2) (smooth_step(&1 - t))
               ((B:real->real^2->real^2) (smooth_step(&1 - t))
                  ((Psi':real->real^2->real^2) (smooth_step(&1 - t)) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_END_K_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`Psi:real->real^2->real^2`; `tau:real->real->real`;
                          `sigma:real->real->real`; `R:real`; `a0:real`; `L:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "def" ACCEPT_TAC;
      USE_THEN "Bdef" ACCEPT_TAC;
      USE_THEN "Adef" ACCEPT_TAC];
    ALL_TAC] THEN
  (* sigma s *)
  SUBGOAL_THEN
   `!s. (!u v. u < v ==> (sigma:real->real->real) s u < sigma s v) /\
        (!y. ?u. sigma s u = y) /\
        (!v. ?c d. &0 < c /\ &0 < d /\
                   !t. &0 < t /\ t < d ==> c * t <= sigma s (v + t) - sigma s v)`
  (LABEL_TAC "sig") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMT_END_SIGMA THEN
    MAP_EVERY EXISTS_TAC [`Psi:real->real^2->real^2`; `Psi':real->real^2->real^2`;
                          `tau:real->real->real`; `r:real`; `R:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "R1" ACCEPT_TAC;
      USE_THEN "far" ACCEPT_TAC;
      USE_THEN "def" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  (* each slice *)
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> (!y y'. (A:real->real^2->real^2) s ((B:real->real^2->real^2) s
                      ((Psi':real->real^2->real^2) s y)) = A s (B s (Psi' s y'))
                    ==> y = y') /\
            (!x. ?y. A s (B s (Psi' s y)) = x) /\
            (!y k. frechet_derivative (\y. A s (B s (Psi' s y))) (at y) k = vec 0
                   ==> k = vec 0)`
  (LABEL_TAC "slice") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(tau:real->real->real) s`; `a0:real`; `L:real`; `Ls:real`; `M:real`]
      SMT_SHEAR_B) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "def" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[LIFT_SUB] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMT_END_LINE_SMOOTH1 THEN EXISTS_TAC `Psi':real->real^2->real^2` THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        USE_THEN "lip" ACCEPT_TAC;
        GEN_TAC THEN USE_THEN "Mb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        STRIP_ASSUME_TAC))] THEN
    MP_TAC(ISPECL [`(sigma:real->real->real) s`; `a0:real`; `r:real`] SMT_SHEAR_A) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "def" (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC SMT_END_LINE_SMOOTH1 THEN EXISTS_TAC `Psi':real->real^2->real^2` THEN
        ASM_REWRITE_TAC[];
        USE_THEN "sig" (fun th -> REWRITE_TAC[th]);
        USE_THEN "sig" (fun th -> REWRITE_TAC[th]);
        REPEAT STRIP_TAC THEN USE_THEN "far" (MP_TAC o SPECL [`s:real`; `y:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      STRIP_TAC] THEN
    MATCH_MP_TAC SMT_END_KSLICE THEN EXISTS_TAC `(Psi:real->real^2->real^2) s` THEN
    SUBGOAL_THEN
     `(B:real->real^2->real^2) s =
        (\x. vector[x$1 + smooth_step((x$1 - a0) / L) * (tau:real->real->real) s (x$2);
                    x$2]) /\
      (A:real->real^2->real^2) s =
        (\z. vector[z$1; (&1 - smooth_step(z$1 - a0)) * z$2 +
                         smooth_step(z$1 - a0) * (sigma:real->real->real) s (z$2)])`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "Adef" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REMOVE_THEN "def" (K ALL_TAC) THEN
    REMOVE_THEN "Bdef" (K ALL_TAC) THEN REMOVE_THEN "Adef" (K ALL_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the inverse family *)
  MATCH_MP_TAC SMT_END_FROM_FAMILY THEN
  MAP_EVERY EXISTS_TAC
   [`\t y. (A:real->real^2->real^2) (smooth_step(&1 - t))
             ((B:real->real^2->real^2) (smooth_step(&1 - t))
                ((Psi':real->real^2->real^2) (smooth_step(&1 - t)) y))`;
    `a0 + L + M + abs r`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN USE_THEN "slice" (MP_TAC o SPEC `smooth_step(&1 - t)`) THEN
    REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT1);
    X_GEN_TAC `t:real` THEN USE_THEN "slice" (MP_TAC o SPEC `smooth_step(&1 - t)`) THEN
    REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    X_GEN_TAC `t:real` THEN USE_THEN "slice" (MP_TAC o SPEC `smooth_step(&1 - t)`) THEN
    REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2 o CONJUNCT2);
    (* t <= 0: K t = h^-1 *)
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step(&1 - t) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Psi':real->real^2->real^2) (&1) (h y) = y` SUBST1_TAC THENL
     [USE_THEN "P1" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "PP" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Adef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "d1" (fun th -> REWRITE_TAC[th; VECTOR_2; REAL_MUL_RZERO; REAL_ADD_RID]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    (* t >= 1: K t = I *)
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step(&1 - t) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Psi':real->real^2->real^2) (&0) y = y` SUBST1_TAC THENL
     [USE_THEN "PP" (MP_TAC o SPECL [`&0`; `y:real^2`]) THEN
      USE_THEN "P0" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "Bdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Adef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "d0" (fun th -> REWRITE_TAC[th; VECTOR_2; REAL_MUL_RZERO; REAL_ADD_RID]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    (* far out: K t = I *)
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^2`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(Psi':real->real^2->real^2) (smooth_step(&1 - t))`;
                   `(Psi:real->real^2->real^2) (smooth_step(&1 - t))`;
                   `(A:real->real^2->real^2) (smooth_step(&1 - t))`;
                   `(B:real->real^2->real^2) (smooth_step(&1 - t))`;
                   `(tau:real->real->real) (smooth_step(&1 - t))`;
                   `(sigma:real->real->real) (smooth_step(&1 - t))`;
                   `r:real`; `R:real`; `a0:real`; `L:real`; `M:real`] SMT_END_KFAR) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "PP" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        USE_THEN "strip" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        USE_THEN "R1" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        USE_THEN "far" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        USE_THEN "sig" (fun th ->
          MATCH_ACCEPT_TAC(CONJUNCT1(CONJUNCT2(SPEC `smooth_step(&1 - t)` th))));
        GEN_TAC THEN USE_THEN "Mb" MATCH_MP_TAC THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS];
        USE_THEN "Bdef" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        USE_THEN "Adef" (fun th -> MATCH_ACCEPT_TAC(SPEC `smooth_step(&1 - t)` th));
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

