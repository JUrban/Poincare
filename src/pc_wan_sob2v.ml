(* ========================================================================= *)
(* Unit pc_wan_sob2v: W^(1,2) under C^1 diffeomorphisms.  The chain         *)
(* rule for weak partials through a C^1 diffeomorphism (locally, without    *)
(* derivative bounds), WAN_W12_DIFFEO (bounded derivatives both ways give   *)
(* W^(1,2) of the composite), and the conformal invariance of the planar    *)
(* Dirichlet integral, WAN_DIR_CONFORMAL_2D.  Statement constants:          *)
(* pc_wan_p4defs.  Tools: the library change of variables                   *)
(* (HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) and the local smooth         *)
(* approximation WAN_W12_LOCAL_APPROX of pc_wan_sob2.  Source: Ziemer,      *)
(* Weakly Differentiable Functions, Thm 2.2.2; Evans PDE 5.3.               *)
(* ========================================================================= *)

needs "src/pc_wan_sob2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* C^1 maps on open sets, continuity and integrability helpers, and the     *)
(* change of variables through a map with a left inverse.                    *)
(* ------------------------------------------------------------------------- *)

let WAN_C1_OPEN_FACTS = prove
 (`!(t:real^N->bool) (Phi:real^N->real^M).
     open t /\ continuously_differentiable 1 t Phi
     ==> (!x. x IN t ==> (Phi has_derivative frechet_derivative Phi (at x)) (at x)) /\
         (!h. (\x. frechet_derivative Phi (at x) h) continuous_on t) /\
         Phi continuous_on t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUSLY_DIFFERENTIABLE_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN t ==> ((Phi:real^N->real^M) has_derivative f' x) (at x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[HAS_DERIVATIVE_WITHIN_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN t ==> frechet_derivative (Phi:real^N->real^M) (at x) = f' x`
  ASSUME_TAC THENL [ASM_MESON_TAC[FRECHET_DERIVATIVE_AT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    X_GEN_TAC `h:real^N` THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (f':real^N->real^N->real^M) x h` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; differentiable]]);;

let WAN_CONT_OPEN_SUPPORT_UNIV = prove
 (`!(f:real^N->real^K) t k.
     open t /\ compact k /\ k SUBSET t /\ f continuous_on t /\
     (!x. ~(x IN k) ==> f x = vec 0)
     ==> f continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `t:real^N->bool`; `k:real^N->bool`]
                WAN_NT_ZERO_EXTENSION_CONTINUOUS) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let WAN_CONT_COMPACT_ABS_INT = prove
 (`!(f:real^N->real^K) k.
     f continuous_on k /\ compact k ==> f absolutely_integrable_on k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^N. lift B` THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
               LEBESGUE_MEASURABLE_COMPACT; LIFT_DROP; INTEGRABLE_ON_CONST;
               MEASURABLE_COMPACT]);;

let WAN_DET_JACOBIAN_CONT = prove
 (`!(s:real^N->bool) (Psi:real^N->real^N).
     open s /\ continuously_differentiable 1 s Psi
     ==> (\y. lift(det(jacobian Psi (at y)))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[jacobian; MATRIX_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[]);;

let WAN_COV_COMPOSE = prove
 (`!(S:real^N->bool) (Psi:real^N->real^N) (Phi:real^N->real^N) (q:real^N->real^K).
     lebesgue_measurable S /\
     (!y. y IN S ==> (Psi has_derivative frechet_derivative Psi (at y)) (at y)) /\
     (!y. y IN S ==> Phi(Psi y) = y)
     ==> ((\x. q(Phi x)) absolutely_integrable_on (IMAGE Psi S) <=>
          (\y. abs(det(jacobian Psi (at y))) % q y) absolutely_integrable_on S) /\
         ((\x. q(Phi x)) absolutely_integrable_on (IMAGE Psi S)
          ==> integral (IMAGE Psi S) (\x. q(Phi x)) =
              integral S (\y. abs(det(jacobian Psi (at y))) % q y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y z. y IN S /\ z IN S /\ (Psi:real^N->real^N) y = Psi z ==> y = z`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> ((Psi:real^N->real^N) has_derivative frechet_derivative Psi (at y))
            (at y within S)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> abs(det(jacobian (Psi:real^N->real^N) (at y))) %
            (q:real^N->real^K)((Phi:real^N->real^N)(Psi y)) =
            abs(det(jacobian Psi (at y))) % q y`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (q:real^N->real^K)((Phi:real^N->real^N) x)`; `Psi:real^N->real^N`;
                 `\y. frechet_derivative (Psi:real^N->real^N) (at y)`; `S:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES) THEN
  MP_TAC(ISPECL [`\x. (q:real^N->real^K)((Phi:real^N->real^N) x)`; `Psi:real^N->real^N`;
                 `\y. frechet_derivative (Psi:real^N->real^N) (at y)`; `S:real^N->bool`]
                INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ASM_REWRITE_TAC[GSYM jacobian] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. abs(det(jacobian (Psi:real^N->real^N) (at x))) %
         (q:real^N->real^K)((Phi:real^N->real^N)(Psi x))) absolutely_integrable_on S <=>
    (\y. abs(det(jacobian Psi (at y))) % q y) absolutely_integrable_on S`
  ASSUME_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THENL
     [EXISTS_TAC `\x. abs(det(jacobian (Psi:real^N->real^N) (at x))) %
                      (q:real^N->real^K)((Phi:real^N->real^N)(Psi x))`;
      EXISTS_TAC `\y. abs(det(jacobian (Psi:real^N->real^N) (at y))) %
                      (q:real^N->real^K) y`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral S (\x. abs(det(jacobian (Psi:real^N->real^N) (at x))) %
                    (q:real^N->real^K)((Phi:real^N->real^N)(Psi x))) =
    integral S (\y. abs(det(jacobian Psi (at y))) % q y)`
  ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let WAN_WEIGHT_ABS_INT = prove
 (`!(w:real^N->real) (q:real^N->real^K) S C.
     (\y. lift(w y)) continuous_on S /\ lebesgue_measurable S /\
     (!y. y IN S ==> abs(w y) <= C) /\ q absolutely_integrable_on S
     ==> (\y. w y % q y) absolutely_integrable_on S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y:real^K. drop x % y`; `\y. lift((w:real^N->real) y)`;
                 `q:real^N->real^K`; `S:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  EXISTS_TAC `abs C + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_DIFFEO_LOCAL_L1 = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi k.
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     compact k /\ k SUBSET t
     ==> compact(IMAGE Phi k) /\ IMAGE Phi k SUBSET s /\
         ?C. &0 <= C /\
             !q:real^N->real^K.
               q absolutely_integrable_on (IMAGE Phi k)
               ==> (\x. q(Phi x)) absolutely_integrable_on k /\
                   drop(integral k (\x. lift(norm(q(Phi x))))) <=
                   C * drop(integral (IMAGE Phi k) (\y. lift(norm(q y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (Phi:real^N->real^N) k) /\ IMAGE Phi k SUBSET s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (Psi:real^N->real^N) (IMAGE Phi k) = k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^N`] WAN_DET_JACOBIAN_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(abs(det(jacobian (Psi:real^N->real^N) (at y))))) continuous_on
    IMAGE (Phi:real^N->real^N) k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?C. &0 <= C /\
        !y. y IN IMAGE (Phi:real^N->real^N) k
            ==> abs(abs(det(jacobian (Psi:real^N->real^N) (at y)))) <= C`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\y. lift(abs(det(jacobian (Psi:real^N->real^N) (at y)))))
                        (IMAGE (Phi:real^N->real^N) k)` COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:real^N->real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(IMAGE (Phi:real^N->real^N) k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (Phi:real^N->real^N) k
        ==> ((Psi:real^N->real^N) has_derivative frechet_derivative Psi (at y)) (at y) /\
            Phi(Psi y) = y`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (Phi:real^N->real^N) k`; `Psi:real^N->real^N`; `Phi:real^N->real^N`;
                 `q:real^N->real^K`] WAN_COV_COMPOSE) THEN
  MP_TAC(ISPECL [`IMAGE (Phi:real^N->real^N) k`; `Psi:real^N->real^N`; `Phi:real^N->real^N`;
                 `\y. lift(norm((q:real^N->real^K) y))`] WAN_COV_COMPOSE) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `(\y. abs(det(jacobian (Psi:real^N->real^N) (at y))) % (q:real^N->real^K) y)
      absolutely_integrable_on IMAGE (Phi:real^N->real^N) k /\
    (\y. abs(det(jacobian (Psi:real^N->real^N) (at y))) % lift(norm((q:real^N->real^K) y)))
      absolutely_integrable_on IMAGE (Phi:real^N->real^N) k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_WEIGHT_ABS_INT THEN EXISTS_TAC `C:real` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MP (CONJUNCT2 th) (CONJUNCT1 th))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  SUBGOAL_THEN
   `C % integral (IMAGE (Phi:real^N->real^N) k) (\y. lift(norm((q:real^N->real^K) y))) =
    integral (IMAGE Phi k) (\y. C % lift(norm(q y)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term ((=) `C:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of the local change of variables: local integrability and   *)
(* L^1 convergence pass to composites; the classical chain rule for smooth  *)
(* maps composed with a C^1 map.                                             *)
(* ------------------------------------------------------------------------- *)

let WAN_DIFFEO_LLOC = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi (q:real^N->real^K).
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     wan_lloc s q
     ==> wan_lloc t (\x. q(Phi x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                 `Psi:real^N->real^N`; `k:real^N->bool`] WAN_DIFFEO_LOCAL_L1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o ISPEC `q:real^N->real^K`))))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[wan_lloc]; SIMP_TAC[]]);;

let WAN_DIFFEO_L1_CONV = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi k (q:num->real^N->real^K) q0.
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     compact k /\ k SUBSET t /\
     (!n. q n absolutely_integrable_on (IMAGE Phi k)) /\
     q0 absolutely_integrable_on (IMAGE Phi k) /\
     ((\n. drop(integral (IMAGE Phi k) (\y. lift(norm(q n y - q0 y))))) ---> &0)
       sequentially
     ==> (!n. (\x. q n (Phi x)) absolutely_integrable_on k) /\
         (\x. q0 (Phi x)) absolutely_integrable_on k /\
         ((\n. drop(integral k (\x. lift(norm(q n (Phi x) - q0 (Phi x)))))) ---> &0)
           sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                 `Psi:real^N->real^N`; `k:real^N->bool`] WAN_DIFFEO_LOCAL_L1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cv"))))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "cv" (fun th -> MP_TAC(ISPEC `(q:num->real^N->real^K) n` th)) THEN
    ASM_SIMP_TAC[];
    USE_THEN "cv" (fun th -> MP_TAC(ISPEC `q0:real^N->real^K` th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. C * drop(integral (IMAGE (Phi:real^N->real^N) k)
                     (\y. lift(norm((q:num->real^N->real^K) n y - q0 y))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    USE_THEN "cv" (fun th ->
      MP_TAC(ISPEC `\y. (q:num->real^N->real^K) n y - q0 y` th)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_LINEAR_BASIS_EXPAND = prove
 (`!(f:real^N->real^K) v.
     linear f ==> f v = vsum(1..dimindex(:N)) (\j. v$j % f(basis j))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let WAN_SMOOTH_DIFFEO_CHAIN = prove
 (`!(t:real^N->bool) (Phi:real^N->real^N) (w:real^N->real^K).
     open t /\ continuously_differentiable 1 t Phi /\ smooth_map_on (:real^N) w
     ==> continuously_differentiable 1 t (\x. w(Phi x)) /\
         !i x. x IN t
               ==> partial_derivative i (\x. w(Phi x)) x =
                   vsum(1..dimindex(:N))
                     (\j. (frechet_derivative Phi (at x) (basis i))$j %
                          partial_derivative j w (Phi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (w:real^N->real^K)((Phi:real^N->real^N) x)) = w o Phi` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (w:real^N->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative ((w:real^N->real^K) o (Phi:real^N->real^N)) (at x) =
    frechet_derivative w (at (Phi x)) o frechet_derivative Phi (at x)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[partial_derivative; o_THM] THEN
  MATCH_MP_TAC WAN_LINEAR_BASIS_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Weighted limits of composites: the integrals of c(x) q_n(Phi x) converge *)
(* when q_n -> q0 in L^2 of the compact image and c is a bounded continuous *)
(* weight supported in a compact subset of t.                                *)
(* ------------------------------------------------------------------------- *)

let WAN_CONT_COMPACT_BOUND = prove
 (`!(c:real^N->real) k.
     (\x. lift(c x)) continuous_on k /\ compact k ==> ?C. !x. x IN k ==> abs(c x) <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((c:real^N->real) x)`; `k:real^N->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[]);;

let WAN_CONT_COMPACT_LSPACE2 = prove
 (`!(f:real^N->real^K) k. f continuous_on k /\ compact k ==> f IN lspace k (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
                 LEBESGUE_MEASURABLE_COMPACT];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_CMUL; REAL_POW_2] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE]]);;

let WAN_DIFFEO_COEFF = prove
 (`!(t:real^N->bool) (Phi:real^N->real^N) (phi:real^N->real) k i j.
     open t /\ continuously_differentiable 1 t Phi /\ compact k /\ k SUBSET t /\
     (\x. lift(phi x)) continuous_on (:real^N) /\ (!x. ~(x IN k) ==> phi x = &0)
     ==> (\x. lift(phi x * (frechet_derivative Phi (at x) (basis i))$j))
            continuous_on (:real^N) /\
         (!x. ~(x IN k) ==> phi x * (frechet_derivative Phi (at x) (basis i))$j = &0) /\
         ?M. !x. abs(phi x * (frechet_derivative Phi (at x) (basis i))$j) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^N->real) x *
              (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j))
      continuous_on (:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_OPEN_SUPPORT_UNIV THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `k:real^N->bool`] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
  MP_TAC(ISPECL [`\x. lift((phi:real^N->real) x *
                         (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j)`;
                 `k:real^N->bool`] WAN_CONT_SUPPORT_BOUNDED) THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM; NORM_LIFT]);;

let WAN_DIFFEO_WEIGHTED_LIMIT = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi k (c:real^N->real) M
    (q:num->real^N->real^K) q0.
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     compact k /\ k SUBSET t /\
     (\x. lift(c x)) continuous_on (:real^N) /\ (!x. ~(x IN k) ==> c x = &0) /\
     (!x. abs(c x) <= M) /\
     (!n. q n IN lspace (IMAGE Phi k) (&2)) /\ q0 IN lspace (IMAGE Phi k) (&2) /\
     ((\n. drop(integral (IMAGE Phi k) (\y. lift(norm(q n y - q0 y) pow 2))))
      ---> &0) sequentially
     ==> (!n. (\x. c x % q n (Phi x)) absolutely_integrable_on t) /\
         (\x. c x % q0 (Phi x)) absolutely_integrable_on t /\
         ((\n. integral t (\x. c x % q n (Phi x))) --> integral t (\x. c x % q0 (Phi x)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                 `Psi:real^N->real^N`; `k:real^N->bool`] WAN_DIFFEO_LOCAL_L1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `(!n. (q:num->real^N->real^K) n absolutely_integrable_on (IMAGE (Phi:real^N->real^N) k)) /\
    (q0:real^N->real^K) absolutely_integrable_on (IMAGE Phi k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[wan_lloc; RIGHT_IMP_FORALL_THM; IMP_IMP]
                   WAN_LSPACE2_IMP_LLOC) THEN
    EXISTS_TAC `IMAGE (Phi:real^N->real^N) k` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. drop(integral (IMAGE (Phi:real^N->real^N) k)
            (\y. lift(norm((q:num->real^N->real^K) n y - q0 y))))) ---> &0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\n y. (q:num->real^N->real^K) n y - q0 y`;
                   `IMAGE (Phi:real^N->real^N) k`] WAN_L2_TO_L1_CONV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN GEN_TAC THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                 `Psi:real^N->real^N`; `k:real^N->bool`; `q:num->real^N->real^K`;
                 `q0:real^N->real^K`] WAN_DIFFEO_L1_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!G:real^N->real^K.
      G absolutely_integrable_on k
      ==> (\x. (c:real^N->real) x % G x) absolutely_integrable_on t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. (c:real^N->real) x % (G:real^N->real^K) x`; `k:real^N->bool`;
                   `k:real^N->bool`; `t:real^N->bool`] WAN_ABS_INTEGRABLE_SUPPORT_SUBSET) THEN
    ASM_SIMP_TAC[SUBSET_REFL; VECTOR_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC WAN_WEIGHT_ABS_INT THEN EXISTS_TAC `M:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_WEIGHTED_L1_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `M:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]]);;

(* ------------------------------------------------------------------------- *)
(* The chain rule for weak partials through a C^1 diffeomorphism (local:    *)
(* no bounds on the derivatives are needed).  Approximate u by test maps on *)
(* the compact image of the support of the test function, use the classical *)
(* chain rule and the local change of variables to pass to the limit.       *)
(* ------------------------------------------------------------------------- *)

let WAN_DIFFEO_WPD = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi (u:real^N->real^K)
    (g:num->real^N->real^K) i.
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     wan_l2loc s u /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_l2loc s (g j) /\ wan_wpd s j u (g j)) /\
     1 <= i /\ i <= dimindex(:N)
     ==> wan_wpd t i (\x. u(Phi x))
           (\x. vsum(1..dimindex(:N))
                  (\j. (frechet_derivative Phi (at x) (basis i))$j % g j (Phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[wan_wpd] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_DIFFEO_LLOC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `Psi:real^N->real^N`] THEN
    ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC];
    REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j`;
                   `k:real^N->bool`] WAN_CONT_COMPACT_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      DISCH_THEN(X_CHOOSE_TAC `C:real` o BETA_RULE)] THEN
    MATCH_MP_TAC WAN_WEIGHT_ABS_INT THEN EXISTS_TAC `C:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      SUBGOAL_THEN `wan_lloc t (\x. (g:num->real^N->real^K) j ((Phi:real^N->real^N) x))`
      MP_TAC THENL
       [MATCH_MP_TAC WAN_DIFFEO_LLOC THEN
        MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `Psi:real^N->real^N`] THEN
        ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC];
        REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                 `Psi:real^N->real^N`; `k:real^N->bool`] WAN_DIFFEO_LOCAL_L1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `g:num->real^N->real^K`;
                 `IMAGE (Phi:real^N->real^N) k`] WAN_W12_LOCAL_APPROX) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^N) ((w:num->real^N->real^K) n) /\
        w n continuous_on (:real^N) /\
        (!j. partial_derivative j (w n) continuous_on (:real^N))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest] o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `kn:real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(w:num->real^N->real^K) n`; `kn:real^N->bool`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (w:num->real^N->real^K) n IN lspace (IMAGE (Phi:real^N->real^N) k) (&2)) /\
    (!n j. partial_derivative j ((w:num->real^N->real^K) n) IN
           lspace (IMAGE (Phi:real^N->real^N) k) (&2)) /\
    (u:real^N->real^K) IN lspace (IMAGE Phi k) (&2) /\
    (!j. 1 <= j /\ j <= dimindex(:N)
         ==> (g:num->real^N->real^K) j IN lspace (IMAGE Phi k) (&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_MESON_TAC[wan_l2loc];
      ASM_MESON_TAC[wan_l2loc]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral t (\x. wan_dpart i phi x %
                        (w:num->real^N->real^K) n ((Phi:real^N->real^N) x)) =
        --(integral t (\x. phi x %
              vsum(1..dimindex(:N))
                (\j. (frechet_derivative Phi (at x) (basis i))$j %
                     partial_derivative j (w n) (Phi x))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`; `(w:num->real^N->real^K) n`]
                  WAN_SMOOTH_DIFFEO_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^N->bool`;
                   `\x. (w:num->real^N->real^K) n ((Phi:real^N->real^N) x)`; `i:num`]
                  WAN_WPD_C1) THEN
    ASM_REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. integral t (\x. wan_dpart i phi x %
                                  (w:num->real^N->real^K) n ((Phi:real^N->real^N) x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                   `Psi:real^N->real^N`; `k:real^N->bool`; `wan_dpart i (phi:real^N->real)`; `B:real`;
                   `w:num->real^N->real^K`; `u:real^N->real^K`]
                  WAN_DIFFEO_WEIGHTED_LIMIT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_NEG THEN
  REWRITE_TAC[GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> (!n. (\x. ((phi:real^N->real) x *
                       (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j) %
                      partial_derivative j ((w:num->real^N->real^K) n) (Phi x))
                 absolutely_integrable_on t) /\
            (\x. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                 (g:num->real^N->real^K) j (Phi x)) absolutely_integrable_on t /\
            ((\n. integral t (\x. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                                  partial_derivative j (w n) (Phi x))) -->
             integral t (\x. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                             g j (Phi x)))
            sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`; `phi:real^N->real`;
                   `k:real^N->bool`; `i:num`; `j:num`] WAN_DIFFEO_COEFF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `Mj:real`))) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                   `Psi:real^N->real^N`; `k:real^N->bool`;
                   `\x. (phi:real^N->real) x *
                        (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j`;
                   `Mj:real`; `\n. partial_derivative j ((w:num->real^N->real^K) n)`;
                   `(g:num->real^N->real^K) j`] WAN_DIFFEO_WEIGHTED_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(G:num->real^N->real^K).
      (!j. 1 <= j /\ j <= dimindex(:N)
           ==> (\x. ((phi:real^N->real) x *
                     (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j) %
                    G j (Phi x)) absolutely_integrable_on t)
      ==> integral t (\x. vsum(1..dimindex(:N))
                          (\j. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                               G j (Phi x))) =
          vsum(1..dimindex(:N))
            (\j. integral t (\x. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                                 G j (Phi x)))`
  (LABEL_TAC "split") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\j x. ((phi:real^N->real) x *
                           (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j) %
                          (G:num->real^N->real^K) j (Phi x)`;
                   `t:real^N->bool`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  USE_THEN "split" (fun th -> MP_TAC(ISPEC `g:num->real^N->real^K` th)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!n. integral t (\x. vsum(1..dimindex(:N))
                       (\j. ((phi:real^N->real) x *
                             (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j) %
                            partial_derivative j ((w:num->real^N->real^K) n) (Phi x))) =
        vsum(1..dimindex(:N))
          (\j. integral t (\x. (phi x * (frechet_derivative Phi (at x) (basis i))$j) %
                               partial_derivative j (w n) (Phi x)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "split" (fun th ->
      MP_TAC(ISPEC `\j. partial_derivative j ((w:num->real^N->real^K) n)` th)) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Global L^2 bounds under a diffeomorphism with bounded derivatives, and   *)
(* WAN_W12_DIFFEO.                                                           *)
(* ------------------------------------------------------------------------- *)

let WAN_DET_ONORM_BOUND = prove
 (`!f:real^N->real^N. linear f ==> abs(det(matrix f)) <= onorm f pow dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `matrix(f:real^N->real^N)` DET_LE_ONORM_POW) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX]);;

let WAN_DIFFEO_LSPACE2 = prove
 (`!(s:real^N->bool) t (Phi:real^N->real^N) Psi B (q:real^N->real^K).
     open s /\ open t /\
     continuously_differentiable 1 t Phi /\ continuously_differentiable 1 s Psi /\
     (!x. x IN t ==> Phi x IN s /\ Psi(Phi x) = x) /\
     (!y. y IN s ==> Psi y IN t /\ Phi(Psi y) = y) /\
     (!y. y IN s ==> onorm(frechet_derivative Psi (at y)) <= B) /\
     q IN lspace s (&2)
     ==> (\x. q(Phi x)) IN lspace t (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (Psi:real^N->real^N) s = t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MEASURABLE_ON_DIFFERENTIABLE_IMAGE THEN
    ASM_SIMP_TAC[LE_REFL; LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable_on] THEN
      ASM_MESON_TAC[differentiable; HAS_DERIVATIVE_AT_WITHIN];
      MATCH_MP_TAC MEASURABLE_ON_EQ THEN EXISTS_TAC `q:real^N->real^K` THEN
      ASM_SIMP_TAC[o_THM] THEN
      UNDISCH_TAC `(q:real^N->real^K) IN lspace s (&2)` THEN
      SIMP_TAC[lspace; IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^N`; `Phi:real^N->real^N`;
                 `\y. lift(norm((q:real^N->real^K) y) pow 2)`] WAN_COV_COMPOSE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC WAN_WEIGHT_ABS_INT THEN
  EXISTS_TAC `B pow dimindex(:N)` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    MATCH_MP_TAC WAN_DET_JACOBIAN_CONT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_ABS; jacobian] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(frechet_derivative (Psi:real^N->real^N) (at y)) pow dimindex(:N)` THEN
    SUBGOAL_THEN `linear(frechet_derivative (Psi:real^N->real^N) (at y))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WAN_DET_ONORM_BOUND] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[ONORM_POS_LE];
    MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; WAN_LSPACE2_SQNORM_INTEGRABLE]]);;

let WAN_W12_DIFFEO = prove
 (`!(n:N->bool) (kk:K->bool). WAN_W12_DIFFEO_STATEMENT n kk`,
  REWRITE_TAC[WAN_W12_DIFFEO_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `Phi:real^N->real^N`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd t i (\x. (u:real^N->real^K)((Phi:real^N->real^N) x))
              (\x. vsum(1..dimindex(:N))
                     (\j. (frechet_derivative Phi (at x) (basis i))$j %
                          wan_wd s j u (Phi x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `Phi:real^N->real^N`;
                   `Psi:real^N->real^N`; `u:real^N->real^K`;
                   `\j. wan_wd s j (u:real^N->real^K)`; `i:num`] WAN_DIFFEO_WPD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_WD_WORKS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_DIFFEO_LSPACE2 THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `Psi:real^N->real^N`; `B':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N))
                    (\j. (frechet_derivative (Phi:real^N->real^N) (at x) (basis i))$j %
                         wan_wd s j (u:real^N->real^K) (Phi x))` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC LSPACE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN
  EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(frechet_derivative (Phi:real^N->real^N) (at x) (basis i))` THEN
    REWRITE_TAC[COMPONENT_LE_NORM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(frechet_derivative (Phi:real^N->real^N) (at x)) * norm(basis i:real^N)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `frechet_derivative (Phi:real^N->real^N) (at x)` ONORM) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable];
        SIMP_TAC[]];
      ASM_SIMP_TAC[NORM_BASIS; REAL_MUL_RID]];
    MATCH_MP_TAC WAN_DIFFEO_LSPACE2 THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `Psi:real^N->real^N`; `B':real`] THEN
    ASM_SIMP_TAC[WAN_WD_WORKS]]);;

(* ------------------------------------------------------------------------- *)
(* Conformal matrices: transp(J) J = c I gives J transp(J) = c I, in the    *)
(* plane abs(det J) = c, and the sum of the squared norms of the columns of *)
(* the chain rule expression is c times the sum of the squared norms.       *)
(* ------------------------------------------------------------------------- *)

let WAN_CONFORMAL_TRANSP = prove
 (`!(J:real^N^N) c. transp J ** J = c %% mat 1 ==> J ** transp J = c %% mat 1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN
     `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> (J:real^N^N)$a$b = &0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `\A:real^N^N. A$b$b`) THEN
      ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT; MATRIX_CMUL_COMPONENT;
                   REAL_MUL_LZERO] THEN
      MP_TAC(ISPECL [`\k. (J:real^N^N)$k$b * J$k$b`; `1`; `dimindex(:N)`]
                    SUM_POS_EQ_0_NUMSEG) THEN
      REWRITE_TAC[REAL_LE_SQUARE] THEN DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[REAL_ENTIRE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_CMUL_LZERO] THEN
    SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA; MAT_0_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp (J:real^N^N) ** (inv c %% J) = mat 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_LEFT_RIGHT_INVERSE]) THEN
  REWRITE_TAC[MATRIX_MUL_LMUL] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\A:real^N^N. c %% A`) THEN
  ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_RINV; MATRIX_CMUL_LID]);;

let WAN_CONFORMAL_DET_2D = prove
 (`!(J:real^2^2) c. transp J ** J = c %% mat 1 ==> abs(det J) = c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `\A:real^2^2. A$1$1`) THEN
    SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT; MATRIX_CMUL_COMPONENT;
             MAT_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_LE_SQUARE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `det:real^2^2->real`) THEN
  REWRITE_TAC[DET_MUL; DET_TRANSP; DET_CMUL; DET_I; DIMINDEX_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN `det(J:real^2^2) pow 2 = c pow 2` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

let WAN_CONFORMAL_SUM_SQ = prove
 (`!(J:real^N^N) c (G:num->real^K).
     J ** transp J = c %% mat 1
     ==> sum(1..dimindex(:N))
            (\i. norm(vsum(1..dimindex(:N)) (\j. J$j$i % G j)) pow 2) =
         c * sum(1..dimindex(:N)) (\j. norm(G j) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j l. 1 <= j /\ j <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
          ==> sum(1..dimindex(:N)) (\i. (J:real^N^N)$j$i * J$l$i) =
              if j = l then c else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\A:real^N^N. A$j$l`) THEN
    ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT; MATRIX_CMUL_COMPONENT;
                 MAT_COMPONENT] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(1..dimindex(:N)) (\j. sum(1..dimindex(:N)) (\l.
       sum(1..dimindex(:N)) (\i. (J:real^N^N)$j$i * J$l$i) *
       ((G:num->real^K) j dot G l)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_POW_2] THEN
    SIMP_TAC[DOT_LSUM; DOT_RSUM; FINITE_NUMSEG; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `sum(1..dimindex(:N)) (\j. c * ((G:num->real^K) j dot G j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N)) (\l. if l = j then c * ((G:num->real^K) j dot G l) else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN ASM_CASES_TAC `l:num = j` THENL
       [ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~(j:num = l)` (fun th -> ASM_REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
        ASM_MESON_TAC[]];
      ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]];
    REWRITE_TAC[SUM_LMUL; NORM_POW_2]]);;

(* ------------------------------------------------------------------------- *)
(* Conformal invariance of the planar Dirichlet integral.                    *)
(* ------------------------------------------------------------------------- *)

let WAN_SUM_DROP_INTEGRAL = prove
 (`!(s:real^N->bool) (f:num->real^N->real) n.
     (!i. 1 <= i /\ i <= n ==> (\x. lift(f i x)) integrable_on s)
     ==> sum(1..n) (\i. drop(integral s (\x. lift(f i x)))) =
         drop(integral s (\x. lift(sum(1..n) (\i. f i x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\i x. lift((f:num->real^N->real) i x)`; `s:real^N->bool`; `1..n`]
                INTEGRAL_VSUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let WAN_CONFORMAL_CHAIN_POINT = prove
 (`!(f:real^2->real^2) c (G:num->real^K).
     transp(matrix f) ** matrix f = c %% mat 1
     ==> sum(1..dimindex(:2))
            (\i. norm(vsum(1..dimindex(:2)) (\j. (f(basis i))$j % G j)) pow 2) =
         abs(det(matrix f)) * sum(1..dimindex(:2)) (\j. norm(G j) pow 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WAN_CONFORMAL_DET_2D) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_CONFORMAL_TRANSP) THEN
  DISCH_THEN(MP_TAC o ISPEC `G:num->real^K` o MATCH_MP WAN_CONFORMAL_SUM_SQ) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT]);;

let WAN_DIR_CONFORMAL_2D = prove
 (`!(kk:K->bool). WAN_DIR_CONFORMAL_2D_STATEMENT kk`,
  REWRITE_TAC[WAN_DIR_CONFORMAL_2D_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `Phi:real^2->real^2`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> wan_wpd t i (\x. (u:real^2->real^K)((Phi:real^2->real^2) x))
              (\x. vsum(1..dimindex(:2))
                     (\j. (frechet_derivative Phi (at x) (basis i))$j %
                          wan_wd s j u (Phi x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `Phi:real^2->real^2`;
                   `Psi:real^2->real^2`; `u:real^2->real^K`;
                   `\j. wan_wd s j (u:real^2->real^K)`; `i:num`] WAN_DIFFEO_WPD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_WD_WORKS; WAN_W12_IMP_LSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> (\x. lift(norm(vsum(1..dimindex(:2))
                  (\j. (frechet_derivative (Phi:real^2->real^2) (at x) (basis i))$j %
                       wan_wd s j (u:real^2->real^K) (Phi x))) pow 2)) integrable_on t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\x. lift(norm(wan_wd t i
                  (\x. (u:real^2->real^K)((Phi:real^2->real^2) x)) x) pow 2)` THEN
    EXISTS_TAC
     `{x | x IN t /\
           ~(wan_wd t i (\x. (u:real^2->real^K)((Phi:real^2->real^2) x)) x =
             vsum(1..dimindex(:2))
               (\j. (frechet_derivative Phi (at x) (basis i))$j % wan_wd s j u (Phi x)))}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `\x. (u:real^2->real^K)((Phi:real^2->real^2) x)`;
                 `\i x. vsum(1..dimindex(:2))
                          (\j. (frechet_derivative (Phi:real^2->real^2) (at x) (basis i))$j %
                               wan_wd s j (u:real^2->real^K) (Phi x))`] WAN_DIR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir] THEN
  MP_TAC(ISPECL [`t:real^2->bool`;
                 `\i x. norm(vsum(1..dimindex(:2))
                          (\j. (frechet_derivative (Phi:real^2->real^2) (at x) (basis i))$j %
                               wan_wd s j (u:real^2->real^K) (Phi x))) pow 2`;
                 `dimindex(:2)`] WAN_SUM_DROP_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\j y. norm(wan_wd s j (u:real^2->real^K) y) pow 2`;
                 `dimindex(:2)`] WAN_SUM_DROP_INTEGRAL) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `integral t (\x. abs(det(matrix(frechet_derivative (Phi:real^2->real^2) (at x)))) %
                    lift(sum(1..dimindex(:2))
                           (\j. norm(wan_wd s j (u:real^2->real^K) (Phi x)) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `?c. transp(matrix(frechet_derivative (Phi:real^2->real^2) (at x))) **
          matrix(frechet_derivative Phi (at x)) = c %% mat 1`
    (X_CHOOSE_TAC `c:real`) THENL
     [REWRITE_TAC[GSYM jacobian] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`frechet_derivative (Phi:real^2->real^2) (at x)`; `c:real`;
                   `\j. wan_wd s j (u:real^2->real^K) ((Phi:real^2->real^2) x)`]
                  WAN_CONFORMAL_CHAIN_POINT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. lift(sum(1..dimindex(:2))
                             (\j. norm(wan_wd s j (u:real^2->real^K) y) pow 2))`;
                 `Phi:real^2->real^2`; `\x. frechet_derivative (Phi:real^2->real^2) (at x)`;
                 `t:real^2->bool`] INTEGRAL_CHANGE_OF_VARIABLES) THEN
  SUBGOAL_THEN `IMAGE (Phi:real^2->real^2) t = s` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; HAS_DERIVATIVE_AT_WITHIN] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN
      SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2] THEN
      REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

