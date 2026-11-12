(* ========================================================================= *)
(* pc_ode_c1: C^1 dependence of the flow on initial data and parameters and  *)
(* the variational equation.                                                 *)
(* ========================================================================= *)

needs "src/pc_ode_cont.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic analysis lemmas.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Gronwall with an inhomogeneous term, in derivative form.                 *)

let ODE_GRONWALL_INHOM = prove
 (`!(r:real^1->real^N) r' J t0 M K.
        is_interval J /\ t0 IN J /\ &0 < M /\ &0 <= K /\
        (!t. t IN J ==> (r has_vector_derivative r' t) (at t within J) /\
                        norm(r' t) <= M * norm(r t) + K)
        ==> !t. t IN J
                ==> norm(r t) <= (norm(r t0) + K / M) *
                                 exp(&3 * M * abs(drop t - drop t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = K / M` THEN
  SUBGOAL_THEN `&0 <= c /\ K = M * c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. (r:real^1->real^N) t dot r t + c * c`;
    `\t. &2 * ((r:real^1->real^N) t dot r' t)`;
    `&3 * M`; `J:real^1->bool`; `t0:real^1`] ODE_GRONWALL_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\t. lift((r:real^1->real^N) t dot r t + c * c)) =
        (\t. lift(r t dot r t) + lift(c * c))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD]; ALL_TAC] THEN
      SUBGOAL_THEN
       `lift(&2 * ((r:real^1->real^N) t dot r' t)) =
        lift(&2 * (r t dot r' t)) + vec 0`
      SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      MP_TAC(ISPECL
       [`\x y:real^N. lift(x dot y)`; `r:real^1->real^N`; `r:real^1->real^N`;
        `(r':real^1->real^N) t`; `(r':real^1->real^N) t`;
        `t:real^1`; `J:real^1->bool`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
      ASM_REWRITE_TAC[BILINEAR_DOT] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ; DOT_SYM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((r:real^1->real^N) t dot r' t) <= norm(r t) * norm(r' t)`
    ASSUME_TAC THENL [REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((r:real^1->real^N) t) * norm((r':real^1->real^N) t) <=
      norm(r t) * (M * norm(r t) + M * c)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * (norm((r:real^1->real^N) t) - c) pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * c * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^1->real^N) t dot r t = norm(r t) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `abs((r:real^1->real^N) t dot r' t) <= norm(r t) * norm(r' t)` THEN
    UNDISCH_TAC
     `norm((r:real^1->real^N) t) * norm((r':real^1->real^N) t) <=
      norm(r t) * (M * norm(r t) + M * c)` THEN
    UNDISCH_TAC `&0 <= M * (norm((r:real^1->real^N) t) - c) pow 2` THEN
    UNDISCH_TAC `&0 <= M * c * c` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  ABBREV_TAC `E = exp(&3 * M * abs(drop t - drop t0))` THEN
  SUBGOAL_THEN `exp((&3 * M) * abs(drop t - drop t0)) = E` SUBST1_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MP_TAC(SPEC `&3 * M * abs(drop t - drop t0)` REAL_EXP_LE_X) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 + x <= y ==> &1 <= y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `(r:real^1->real^N) t0` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(norm((r:real^1->real^N) t0) pow 2 + c * c) * E <=
    (norm(r t0) + c) pow 2 * (E * E)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&0 <= norm((r:real^1->real^N) t0) * c` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * c` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  UNDISCH_TAC
   `norm((r:real^1->real^N) t) pow 2 + c * c <= (norm(r t0) pow 2 + c * c) * E` THEN
  UNDISCH_TAC
   `(norm((r:real^1->real^N) t0) pow 2 + c * c) * E <=
    (norm(r t0) + c) pow 2 * (E * E)` THEN
  UNDISCH_TAC `&0 <= c * c` THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* Basic facts on C^1 maps on open sets.                                     *)

let ODE_C1_FRECHET = prove
 (`!(f:real^M->real^N) s.
        open s /\ continuously_differentiable 1 s f
        ==> f continuous_on s /\
            (!x. x IN s ==> (f has_derivative frechet_derivative f (at x)) (at x)) /\
            (!h. (\x. frechet_derivative f (at x) h) continuous_on s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable (SUC 0) s (f:real^M->real^N)` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[GSYM ONE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    SUBGOAL_THEN `(f:real^M->real^N) differentiable_on s` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT]];
    GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `s:real^M->bool`; `f:real^M->real^N`]
           CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ASM_REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* Entries of a matrix-valued map from continuity of its vectorization.    *)

let ODE_VECTORIZE_CONTINUOUS_ENTRIES = prove
 (`!(A:real^P->real^N^M) s.
        (\a. vectorize(A a)) continuous_on s
        ==> !i j. (\a. lift(A a$i$j)) continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  MP_TAC(SPEC `i:num` (INST_TYPE [`:real^N`,`:A`; `:M`,`:N`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `j:num` (INST_TYPE [`:real`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The matrix of the partial derivative in the state variable.              *)

let ode_dxmat = new_definition
 `ode_dxmat (f:real^(1,N)finite_sum->real^N) w =
    matrix(\k. frechet_derivative f (at w) (pastecart (vec 0:real^1) k))`;;

let ODE_DXMAT_PROPS = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
        open D /\ continuously_differentiable 1 D f
        ==> (!w k. w IN D
                   ==> ode_dxmat f w ** k =
                       frechet_derivative f (at w) (pastecart (vec 0) k)) /\
            (\w. vectorize(ode_dxmat f w)) continuous_on D`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ODE_C1_FRECHET) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ode_dxmat] THEN
    SUBGOAL_THEN
     `linear (\k:real^N. frechet_derivative (f:real^(1,N)finite_sum->real^N) (at w)
                           (pastecart (vec 0:real^1) k))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\k:real^N. frechet_derivative (f:real^(1,N)finite_sum->real^N) (at w)
                      (pastecart (vec 0:real^1) k)) =
        frechet_derivative f (at w) o (\k. pastecart (vec 0) k)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_PASTECART_VEC0_R] THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[MATRIX_WORKS]];
    REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ode_dxmat; MATRIX_COMPONENT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (vec 0:real^1) (basis j:real^N)`) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o
      GEN_REWRITE_RULE I [CONTINUOUS_ON_COMPONENTWISE_LIFT]) THEN
    ASM_REWRITE_TAC[]]);;

(* Uniform continuity of the partial derivative matrix near a compact set. *)

let ODE_DXMAT_UNIFORM = prove
 (`!(f:real^(1,N)finite_sum->real^N) D K.
        open D /\ continuously_differentiable 1 D f /\ compact K /\ K SUBSET D
        ==> ?R. &0 < R /\
                (!w w'. w IN K /\ norm(w' - w) <= R ==> w' IN D) /\
                !e. &0 < e
                    ==> ?d. &0 < d /\ d <= R /\
                            !w w'. w IN K /\ norm(w' - w) <= d
                                   ==> norm(vectorize(ode_dxmat f w') -
                                            vectorize(ode_dxmat f w)) <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_DXMAT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^(1,N)finite_sum->bool`; `D:real^(1,N)finite_sum->bool`]
         ODE_COMPACT_THICKEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` MP_TAC) THEN
  ABBREV_TAC
   `K' = {x + y | x IN K /\ y IN cball(vec 0:real^(1,N)finite_sum,R)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!w w':real^(1,N)finite_sum. w IN K /\ norm(w' - w) <= R ==> w' IN K'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`w:real^(1,N)finite_sum`; `w' - w:real^(1,N)finite_sum`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\w. vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N) w))
    uniformly_continuous_on K'`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d1 / &2) R` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(w:real^(1,N)finite_sum) IN K' /\ (w':real^(1,N)finite_sum) IN K'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `w:real^(1,N)finite_sum` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC);;

(* Uniform differentiability in the state variable near a compact set.     *)

let ODE_DX_UNIFORM_DIFF = prove
 (`!(f:real^(1,N)finite_sum->real^N) D K.
        open D /\ continuously_differentiable 1 D f /\ compact K /\ K SUBSET D
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !t x y. pastecart t x IN K /\ norm(y - x) <= d
                                ==> pastecart t y IN D /\
                                    norm(f(pastecart t y) - f(pastecart t x) -
                                         ode_dxmat f (pastecart t x) ** (y - x))
                                    <= e * norm(y - x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_DXMAT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_DXMAT_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "unif" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!y'. y' IN cball(x:real^N,d)
         ==> pastecart (t:real^1) y' IN D /\
             norm(vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart t y')) -
                  vectorize(ode_dxmat f (pastecart t x))) <= e`
  ASSUME_TAC THENL
   [X_GEN_TAC `y':real^N` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `norm(pastecart (t:real^1) (y':real^N) - pastecart t x) <= d`
    ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `pastecart (t:real^1) (x:real^N)` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y':real^N. (f:real^(1,N)finite_sum->real^N)(pastecart t y') -
                 ode_dxmat f (pastecart t x) ** y'`;
    `\y':real^N k:real^N.
        ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart t y') ** k -
        ode_dxmat f (pastecart t x) ** k`;
    `cball(x:real^N,d)`; `e:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_CBALL] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y':real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y':real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\k. ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart t y') ** k) =
          frechet_derivative f (at (pastecart t y')) o (\k. pastecart (vec 0) k)`
        SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `(\y'. (f:real^(1,N)finite_sum->real^N)(pastecart t y')) =
          f o (\y'. pastecart t y')`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
          REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
          ASM_SIMP_TAC[]];
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `norm(vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart t y')) -
             vectorize(ode_dxmat f (pastecart t x)))` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC
       `\k:real^N. ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart t y') ** k -
                   ode_dxmat f (pastecart t x) ** k` ONORM) THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LINEAR] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[GSYM VECTORIZE_SUB; COMPATIBLE_NORM_VECTORIZE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `x:real^N`]) THEN
  REWRITE_TAC[IN_CBALL; DIST_REFL] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Solutions of the variational equation at a fixed initial time, as        *)
(* solutions of a linear system along the solution curve.                   *)
(* ------------------------------------------------------------------------- *)

let ODE_HAS_VECTOR_DERIVATIVE_IMP_CONTINUOUS_AT = prove
 (`!(u:real^1->real^N) u' t.
        (u has_vector_derivative u') (at t) ==> u continuous (at t)`,
  REWRITE_TAC[has_vector_derivative] THEN
  MESON_TAC[differentiable; DIFFERENTIABLE_IMP_CONTINUOUS_AT]);;

(* An interval inside an open interval J containing t0 and a neighbourhood  *)
(* of t1.                                                                    *)

let ODE_INTERVAL_AROUND = prove
 (`!J (t0:real^1) t1.
        open J /\ is_interval J /\ t0 IN J /\ t1 IN J
        ==> ?a b d. &0 < d /\ interval[a,b] SUBSET J /\ t0 IN interval[a,b] /\
                    !t. dist(t,t1) < d ==> t IN interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t0:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t1:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min e1 e2` THEN
  SUBGOAL_THEN `&0 < e /\ e <= e1 /\ e <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = lift(min (drop t0) (drop t1) - e / &2)` THEN
  ABBREV_TAC `b = lift(max (drop t0) (drop t1) + e / &2)` THEN
  SUBGOAL_THEN `(a:real^1) IN J /\ (b:real^1) IN J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_CASES_TAC `drop t0 <= drop t1` THENL
     [UNDISCH_TAC `ball(t0:real^1,e1) SUBSET J`;
      UNDISCH_TAC `ball(t1:real^1,e2) SUBSET J`;
      UNDISCH_TAC `ball(t1:real^1,e2) SUBSET J`;
      UNDISCH_TAC `ball(t0:real^1,e1) SUBSET J`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`; `e / &2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[IN_INTERVAL_1; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* The variational solution: the solution at time t of the linear system   *)
(* v' = D_x f(s, flow s) v with v(t0) = h, along the solution through       *)
(* (t0,x).                                                                   *)

let ode_varsol = new_definition
 `ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x t h =
    ode_flow (\z:real^(1,N)finite_sum.
                ode_dxmat f (pastecart (fstcart z)
                                (ode_flow f D (fstcart z) (pastecart t0 x))) **
                sndcart z)
             (ode_maxint f D (pastecart t0 x) PCROSS (:real^N))
             t (pastecart t0 h)`;;

let ODE_VARSOL_LINFIELD = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x.
        open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D
        ==> (\t. vectorize(ode_dxmat f (pastecart t (ode_flow f D t (pastecart t0 x)))))
            continuous_on ode_maxint f D (pastecart t0 x) /\
            (\z:real^(1,N)finite_sum.
                ode_dxmat f (pastecart (fstcart z)
                                (ode_flow f D (fstcart z) (pastecart t0 x))) **
                sndcart z)
            continuous_on (ode_maxint f D (pastecart t0 x) PCROSS (:real^N)) /\
            ode_locally_lipschitz
              (\z:real^(1,N)finite_sum.
                ode_dxmat f (pastecart (fstcart z)
                                (ode_flow f D (fstcart z) (pastecart t0 x))) **
                sndcart z)
              (ode_maxint f D (pastecart t0 x) PCROSS (:real^N)) /\
            open(ode_maxint f D (pastecart t0 x) PCROSS (:real^N)) /\
            (!h. ode_maxint
                   (\z:real^(1,N)finite_sum.
                      ode_dxmat f (pastecart (fstcart z)
                                      (ode_flow f D (fstcart z) (pastecart t0 x))) **
                      sndcart z)
                   (ode_maxint f D (pastecart t0 x) PCROSS (:real^N))
                   (pastecart t0 h) =
                 ode_maxint f D (pastecart t0 x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_DXMAT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N)
                     (pastecart t (ode_flow f D t (pastecart t0 x)))))
    continuous_on ode_maxint f D (pastecart t0 x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\t. vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N)
                       (pastecart t (ode_flow f D t (pastecart t0 x))))) =
      (\w. vectorize(ode_dxmat f w)) o
      (\t. pastecart t (ode_flow f D t (pastecart t0 x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ODE_SOLUTION_CONTINUOUS) THEN REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o BETA_RULE o MATCH_MP ODE_VECTORIZE_CONTINUOUS_ENTRIES) THEN
  MP_TAC(ISPECL
   [`\t. ode_dxmat (f:real^(1,N)finite_sum->real^N)
           (pastecart t (ode_flow f D t (pastecart t0 x)))`;
    `\t:real^1. vec 0:real^N`;
    `ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x)`]
   ODE_LINEAR_FIELD_PROPS) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; VECTOR_ADD_RID] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`\t. ode_dxmat (f:real^(1,N)finite_sum->real^N)
           (pastecart t (ode_flow f D t (pastecart t0 x)))`;
    `\t:real^1. vec 0:real^N`;
    `ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x)`;
    `t0:real^1`; `h:real^N`] ODE_LINEAR_GLOBAL) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; VECTOR_ADD_RID]);;

let ODE_VARSOL_BASIC = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D
    ==> (!h. ode_varsol f D t0 x t0 h = h) /\
        (!t h. t IN ode_maxint f D (pastecart t0 x)
               ==> ((\s. ode_varsol f D t0 x s h) has_vector_derivative
                    ode_dxmat f (pastecart t (ode_flow f D t (pastecart t0 x))) **
                    ode_varsol f D t0 x t h) (at t)) /\
        (!J v h. is_interval J /\ J SUBSET ode_maxint f D (pastecart t0 x) /\
                 t0 IN J /\ v t0 = h /\
                 (!t. t IN J
                      ==> (v has_vector_derivative
                           ode_dxmat f (pastecart t (ode_flow f D t (pastecart t0 x))) **
                           v t) (at t within J))
                 ==> !t. t IN J ==> v t = ode_varsol f D t0 x t h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x:real^N`] ODE_VARSOL_LINFIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  ABBREV_TAC
   `lf = \z:real^(1,N)finite_sum.
           ode_dxmat (f:real^(1,N)finite_sum->real^N)
             (pastecart (fstcart z) (ode_flow f D (fstcart z) (pastecart t0 x))) **
           sndcart z` THEN
  ABBREV_TAC `J0 = ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x)` THEN
  SUBGOAL_THEN
   `!t v. (lf:real^(1,N)finite_sum->real^N) (pastecart t v) =
          ode_dxmat (f:real^(1,N)finite_sum->real^N)
            (pastecart t (ode_flow f D t (pastecart t0 x))) ** v`
  ASSUME_TAC THENL
   [EXPAND_TAC "lf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t h. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x t h =
          ode_flow lf (J0 PCROSS (:real^N)) t (pastecart t0 h)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lf"; "J0"] THEN REWRITE_TAC[ode_varsol]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!h. ode_flow (lf:real^(1,N)finite_sum->real^N) (J0 PCROSS (:real^N)) t0
          (pastecart t0 h) = h /\
        !t. t IN J0
            ==> ((\s. ode_flow lf (J0 PCROSS (:real^N)) s (pastecart t0 h))
                 has_vector_derivative
                 lf(pastecart t (ode_flow lf (J0 PCROSS (:real^N)) t
                                  (pastecart t0 h)))) (at t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`lf:real^(1,N)finite_sum->real^N`; `(J0:real^1->bool) PCROSS (:real^N)`;
                   `pastecart (t0:real^1) (h:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART;
                    SNDCART_PASTECART] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPEC `h:real^N`) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`lf:real^(1,N)finite_sum->real^N`; `(J0:real^1->bool) PCROSS (:real^N)`;
                   `pastecart (t0:real^1) (h:real^N)`; `J:real^1->bool`;
                   `v:real^1->real^N`] ODE_MAXIMAL_UNIQUE) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ode_solution] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]]]);;

(* The first two clauses only (safe for simplification: the uniqueness     *)
(* clause has a variable-headed conclusion).                                 *)

let ODE_VARSOL_DERIV = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D
    ==> (!h. ode_varsol f D t0 x t0 h = h) /\
        (!t h. t IN ode_maxint f D (pastecart t0 x)
               ==> ((\s. ode_varsol f D t0 x s h) has_vector_derivative
                    ode_dxmat f (pastecart t (ode_flow f D t (pastecart t0 x))) **
                    ode_varsol f D t0 x t h) (at t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP ODE_VARSOL_BASIC) THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let ODE_VARSOL_LINEAR = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x t.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D /\
    t IN ode_maxint f D (pastecart t0 x)
    ==> linear (\h. ode_varsol f D t0 x t h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x:real^N`] ODE_VARSOL_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "uniq"))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h1:real^N`; `h2:real^N`] THEN
    CONV_TAC SYM_CONV THEN
    USE_THEN "uniq" (MP_TAC o SPECL
     [`ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x)`;
      `\s. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h1 +
           ode_varsol f D t0 x s h2`;
      `h1 + h2:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`c:real`; `h:real^N`] THEN
    CONV_TAC SYM_CONV THEN
    USE_THEN "uniq" (MP_TAC o SPECL
     [`ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x)`;
      `\s. c % ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h`;
      `c % h:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[]]]);;

let ODE_VARSOL_MATRIX = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D
    ==> (!t h. t IN ode_maxint f D (pastecart t0 x)
               ==> ode_varsol f D t0 x t h =
                   matrix(\h. ode_varsol f D t0 x t h) ** h) /\
        (\t. vectorize(matrix(\h. ode_varsol f D t0 x t h))) continuous_on
        ode_maxint f D (pastecart t0 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x:real^N`; `t:real^1`] ODE_VARSOL_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^N` o MATCH_MP MATRIX_WORKS) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x:real^N`] ODE_VARSOL_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  SUBGOAL_THEN
   `(\t. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x t (basis j))
    continuous_on ode_maxint f D (pastecart t0 x)`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_IMP_CONTINUOUS_AT THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o
    GEN_REWRITE_RULE I [CONTINUOUS_ON_COMPONENTWISE_LIFT]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The first order remainder estimate in the initial value and the          *)
(* continuous dependence of the variational solutions on it.                *)
(* ------------------------------------------------------------------------- *)

(* Uniform estimates along a compact piece of a solution curve.             *)

let ODE_C1_TUBE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x1 a b.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x1 IN D /\
    t0 IN interval[a,b] /\ interval[a,b] SUBSET ode_maxint f D (pastecart t0 x1)
    ==> ?R C M.
          &0 < R /\ &0 < C /\ &0 < M /\
          (!x. norm(x - x1) <= R
               ==> pastecart t0 x IN D /\
                   interval[a,b] SUBSET ode_maxint f D (pastecart t0 x) /\
                   !t. t IN interval[a,b]
                       ==> norm(ode_flow f D t (pastecart t0 x) -
                                ode_flow f D t (pastecart t0 x1))
                           <= C * norm(x - x1)) /\
          (!t. t IN interval[a,b]
               ==> norm(vectorize(ode_dxmat f
                          (pastecart t (ode_flow f D t (pastecart t0 x1))))) <= M) /\
          (!e. &0 < e
               ==> ?d. &0 < d /\
                       !t y. t IN interval[a,b] /\
                             norm(y - ode_flow f D t (pastecart t0 x1)) <= d
                             ==> norm(f(pastecart t y) -
                                      f(pastecart t (ode_flow f D t (pastecart t0 x1))) -
                                      ode_dxmat f (pastecart t
                                         (ode_flow f D t (pastecart t0 x1))) **
                                      (y - ode_flow f D t (pastecart t0 x1)))
                                 <= e * norm(y - ode_flow f D t (pastecart t0 x1)) /\
                                 norm(vectorize(ode_dxmat f (pastecart t y)) -
                                      vectorize(ode_dxmat f (pastecart t
                                         (ode_flow f D t (pastecart t0 x1))))) <= e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x1:real^N)`; `a:real^1`; `b:real^1`]
         ODE_FLOW_STABILITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))))) THEN
  ABBREV_TAC
   `K = IMAGE (\t. pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t
                                  (pastecart t0 x1))) (interval[a,b])` THEN
  SUBGOAL_THEN `compact(K:real^(1,N)finite_sum->bool) /\ K SUBSET D`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x1)` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ODE_SOLUTION_CONTINUOUS) THEN REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[a,b]
        ==> pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t
                           (pastecart t0 x1)) IN K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_DXMAT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\w. vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N) w)`;
                 `D:real^(1,N)finite_sum->bool`; `K:real^(1,N)finite_sum->bool`]
         ODE_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bnd"))) THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `C:real`; `M:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "stab" (MP_TAC o SPEC `pastecart (t0:real^1) (x:real^N)`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "bnd" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_DX_UNIFORM_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ud"))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_DXMAT_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc")))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart t0 x1)) IN K`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "ud" (MP_TAC o SPECL
     [`t:real^1`; `ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart t0 x1)`;
      `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REMOVE_THEN "uc" (MP_TAC o SPECL
     [`pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart t0 x1))`;
      `pastecart (t:real^1) (y:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Exponential factor bound on an interval.                                 *)

let ODE_EXP_INTERVAL_BOUND = prove
 (`!a b t t0 M.
        t IN interval[a,b] /\ t0 IN interval[a,b] /\ &0 <= M
        ==> &1 <= exp(&3 * M * (drop b - drop a)) /\
            exp(&3 * M * abs(drop t - drop t0)) <= exp(&3 * M * (drop b - drop a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= drop b - drop a /\ abs(drop t - drop t0) <= drop b - drop a`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `&3 * M * (drop b - drop a)` REAL_EXP_LE_X) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 + x <= y ==> &1 <= y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]]);;

(* The remainder of the first order expansion in the initial value.         *)

let ODE_FLOW_REMAINDER = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x1 a b.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x1 IN D /\
    t0 IN interval[a,b] /\ interval[a,b] SUBSET ode_maxint f D (pastecart t0 x1)
    ==> ?R. &0 < R /\
            (!x. norm(x - x1) <= R
                 ==> pastecart t0 x IN D /\
                     interval[a,b] SUBSET ode_maxint f D (pastecart t0 x)) /\
            (!e. &0 < e
                 ==> ?d. &0 < d /\ d <= R /\
                         !x t. norm(x - x1) <= d /\ t IN interval[a,b]
                               ==> norm(ode_flow f D t (pastecart t0 x) -
                                        ode_flow f D t (pastecart t0 x1) -
                                        ode_varsol f D t0 x1 t (x - x1))
                                   <= e * norm(x - x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x1:real^N`; `a:real^1`; `b:real^1`] ODE_C1_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `M:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "stab")
       (CONJUNCTS_THEN2 (LABEL_TAC "bnd") (LABEL_TAC "unif"))))))))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "stab" (MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `E = exp(&3 * M * (drop b - drop a))` THEN
  SUBGOAL_THEN `&1 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `t0:real^1`; `t0:real^1`; `M:real`]
           ODE_EXP_INTERVAL_BOUND) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = e * M / (C * E)` THEN
  SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPEC `e1:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ud"))) THEN
  EXISTS_TAC `min R (d1 / C)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(x - x1:real^N) <= R /\ C * norm(x - x1) <= d1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * d1 / C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REMOVE_THEN "stab" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip"))) THEN
  SUBGOAL_THEN
   `ode_flow (f:real^(1,N)finite_sum->real^N) D t0 (pastecart t0 x) = x /\
    ode_flow f D t0 (pastecart t0 x1) = x1 /\
    ode_varsol f D t0 x1 t0 (x - x1) = x - x1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `pastecart (t0:real^1) (x1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x1:real^N`] ODE_VARSOL_BASIC) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN interval[a,b]
        ==> pastecart s (ode_flow (f:real^(1,N)finite_sum->real^N) D s
                           (pastecart t0 x)) IN D /\
            ((\s. ode_flow f D s (pastecart t0 x)) has_vector_derivative
             f(pastecart s (ode_flow f D s (pastecart t0 x)))) (at s) /\
            ((\s. ode_flow f D s (pastecart t0 x1)) has_vector_derivative
             f(pastecart s (ode_flow f D s (pastecart t0 x1)))) (at s) /\
            ((\s. ode_varsol f D t0 x1 s (x - x1)) has_vector_derivative
             ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1))) **
             ode_varsol f D t0 x1 s (x - x1)) (at s)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s IN ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x) /\
      s IN ode_maxint f D (pastecart t0 x1)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^1` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `pastecart (t0:real^1) (x1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^1` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x1:real^N`] ODE_VARSOL_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `x - x1:real^N`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x) -
         ode_flow f D s (pastecart t0 x1) - ode_varsol f D t0 x1 s (x - x1)`;
    `\s. (f:real^(1,N)finite_sum->real^N)(pastecart s (ode_flow f D s (pastecart t0 x))) -
         f(pastecart s (ode_flow f D s (pastecart t0 x1))) -
         ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1))) **
         ode_varsol f D t0 x1 s (x - x1)`;
    `interval[a:real^1,b]`; `t0:real^1`; `M:real`;
    `e1 * C * norm(x - x1:real^N)`] ODE_GRONWALL_INHOM) THEN
  REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      ALL_TAC] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "der" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "lip" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REMOVE_THEN "ud" (MP_TAC o SPECL
     [`s:real^1`; `ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x)`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    REMOVE_THEN "bnd" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    ABBREV_TAC `u1 = ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x1)` THEN
    ABBREV_TAC `u = ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x)` THEN
    ABBREV_TAC `v = ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 s (x - x1)` THEN
    ABBREV_TAC `A = ode_dxmat (f:real^(1,N)finite_sum->real^N) (pastecart s u1)` THEN
    SUBGOAL_THEN
     `(f:real^(1,N)finite_sum->real^N)(pastecart s u) - f(pastecart s u1) - A ** v =
      (f(pastecart s u) - f(pastecart s u1) - A ** (u - u1)) + A ** (u - u1 - v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN
    MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> a + b <= b' + a'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e1 * norm(u - u1:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize(A:real^N^N)) * norm(u - u1 - v:real^N)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_ADD_LID] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `t:real^1`; `t0:real^1`; `M:real`]
         ODE_EXP_INTERVAL_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(e1 * C * norm(x - x1:real^N)) / M * E` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "e1" THEN
  MAP_EVERY UNDISCH_TAC [`&0 < M`; `&0 < C`; `&1 <= E`] THEN
  CONV_TAC REAL_FIELD);;

(* Continuous dependence of the variational solutions on the initial value, *)
(* uniformly in time on a compact interval and in the direction.            *)

let ODE_VARSOL_NEAR = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x1 a b.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x1 IN D /\
    t0 IN interval[a,b] /\ interval[a,b] SUBSET ode_maxint f D (pastecart t0 x1)
    ==> !e. &0 < e
            ==> ?d. &0 < d /\
                    !x t h. norm(x - x1) <= d /\ t IN interval[a,b]
                            ==> norm(ode_varsol f D t0 x t h -
                                     ode_varsol f D t0 x1 t h) <= e * norm h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x1:real^N`; `a:real^1`; `b:real^1`] ODE_C1_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `M:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "stab")
       (CONJUNCTS_THEN2 (LABEL_TAC "bnd") (LABEL_TAC "unif"))))))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `E0 = exp(&3 * M * (drop b - drop a))` THEN
  ABBREV_TAC `E1 = exp(&3 * (M + &1) * (drop b - drop a))` THEN
  SUBGOAL_THEN `&1 <= E0 /\ &1 <= E1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E0"; "E1"] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `t0:real^1`; `t0:real^1`; `M:real`]
             ODE_EXP_INTERVAL_BOUND);
      MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `t0:real^1`; `t0:real^1`; `M + &1`]
             ODE_EXP_INTERVAL_BOUND)] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = min (&1) (e * M / (E1 * E0))` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= &1 /\ e1 <= e * M / (E1 * E0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPEC `e1:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ud"))) THEN
  EXISTS_TAC `min R (d1 / C)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`; `h:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(x - x1:real^N) <= R /\ C * norm(x - x1) <= d1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * d1 / C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REMOVE_THEN "stab" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip"))) THEN
  SUBGOAL_THEN
   `!s. s IN interval[a,b]
        ==> norm(vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N)
                             (pastecart s (ode_flow f D s (pastecart t0 x)))) -
                 vectorize(ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1)))))
            <= e1 /\
            norm(vectorize(ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1)))))
            <= M`
  (LABEL_TAC "coef") THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REMOVE_THEN "lip" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      REMOVE_THEN "ud" (MP_TAC o SPECL
       [`s:real^1`; `ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x)`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REMOVE_THEN "bnd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN interval[a,b]
        ==> ((\s. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h)
             has_vector_derivative
             ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x))) **
             ode_varsol f D t0 x s h) (at s) /\
            ((\s. ode_varsol f D t0 x1 s h) has_vector_derivative
             ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1))) **
             ode_varsol f D t0 x1 s h) (at s)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s IN ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x) /\
      s IN ode_maxint f D (pastecart t0 x1)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x:real^N`] ODE_VARSOL_DERIV) THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x1:real^N`] ODE_VARSOL_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x t0 h = h /\
    ode_varsol f D t0 x1 t0 h = h`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x:real^N`] ODE_VARSOL_DERIV) THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x1:real^N`] ODE_VARSOL_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* A priori bound on the perturbed variational solution. *)
  SUBGOAL_THEN
   `!s. s IN interval[a,b]
        ==> norm(ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h)
            <= norm(h:real^N) * E1`
  (LABEL_TAC "vb") THENL
   [MP_TAC(ISPECL
     [`\s. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h`;
      `\s. ode_dxmat (f:real^(1,N)finite_sum->real^N)
             (pastecart s (ode_flow f D s (pastecart t0 x))) **
           ode_varsol f D t0 x s h`;
      `interval[a:real^1,b]`; `t0:real^1`; `M + &1`; `&0`] ODE_GRONWALL_INHOM) THEN
    REWRITE_TAC[IS_INTERVAL_INTERVAL; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `norm(vectorize(ode_dxmat (f:real^(1,N)finite_sum->real^N)
                         (pastecart s (ode_flow f D s (pastecart t0 x))))) *
        norm(ode_varsol f D t0 x s h)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      REMOVE_THEN "coef" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(NORM_ARITH
       `e1 <= &1 ==> norm(a - b:real^M) <= e1 /\ norm b <= M ==> norm a <= M + &1`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `s:real^1`; `t0:real^1`; `M + &1`]
           ODE_EXP_INTERVAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h -
         ode_varsol f D t0 x1 s h`;
    `\s. ode_dxmat (f:real^(1,N)finite_sum->real^N)
           (pastecart s (ode_flow f D s (pastecart t0 x))) **
         ode_varsol f D t0 x s h -
         ode_dxmat f (pastecart s (ode_flow f D s (pastecart t0 x1))) **
         ode_varsol f D t0 x1 s h`;
    `interval[a:real^1,b]`; `t0:real^1`; `M:real`;
    `e1 * norm(h:real^N) * E1`] ODE_GRONWALL_INHOM) THEN
  REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "coef" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REMOVE_THEN "vb" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    ABBREV_TAC `v = ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h` THEN
    ABBREV_TAC `v1 = ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 s h` THEN
    ABBREV_TAC `A = ode_dxmat (f:real^(1,N)finite_sum->real^N)
                      (pastecart s (ode_flow f D s (pastecart t0 x)))` THEN
    ABBREV_TAC `A1 = ode_dxmat (f:real^(1,N)finite_sum->real^N)
                       (pastecart s (ode_flow f D s (pastecart t0 x1)))` THEN
    SUBGOAL_THEN
     `(A:real^N^N) ** (v:real^N) - (A1:real^N^N) ** (v1:real^N) =
      A1 ** (v - v1) + (A - A1) ** v`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN
    MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> a + b <= a' + b'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize(A1:real^N^N)) * norm(v - v1:real^N)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize(A - A1:real^N^N)) * norm(v:real^N)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; VECTORIZE_SUB]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_ADD_LID] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(ISPECL [`a:real^1`; `b:real^1`; `t:real^1`; `t0:real^1`; `M:real`]
         ODE_EXP_INTERVAL_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(e1 * norm(h:real^N) * E1) / M * E0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e1 * norm(h:real^N) * E1) / M * E0 = (e1 * (E1 * E0 / M)) * norm h`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < M`; `&1 <= E0`; `&1 <= E1`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(e * M / (E1 * E0)) * (E1 * E0 / M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MAP_EVERY UNDISCH_TAC [`&0 < M`; `&1 <= E0`; `&1 <= E1`] THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Joint differentiability of the flow at a fixed initial time and the C^1  *)
(* core (ODE_FLOW_C1_FIXED_TIME, ODE_FLOW_VARIATIONAL_FIXED_TIME).          *)
(* ------------------------------------------------------------------------- *)

let ODE_DIST_FSTCART_SNDCART = prove
 (`!(w:real^(M,N)finite_sum) t x.
        dist(fstcart w,t) <= dist(w,pastecart t x) /\
        dist(sndcart w,x) <= dist(w,pastecart t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `w - pastecart (t:real^M) (x:real^N)` NORM_FSTCART) THEN
  MP_TAC(ISPEC `w - pastecart (t:real^M) (x:real^N)` NORM_SNDCART) THEN
  REWRITE_TAC[FSTCART_SUB; SNDCART_SUB; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REAL_ARITH_TAC);;

let ODE_FIXED_TIME_DOMAIN = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 w.
        w IN {pastecart t x | pastecart t0 x IN D /\
                              t IN ode_maxint f D (pastecart t0 x)} <=>
        pastecart t0 (sndcart w) IN D /\
        fstcart w IN ode_maxint f D (pastecart t0 (sndcart w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`fstcart(w:real^(1,N)finite_sum)`;
                          `sndcart(w:real^(1,N)finite_sum)`] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND]]);;

(* Joint derivative at a point, at a fixed initial time t0.                 *)

let ODE_FLOW_FIXED_TIME_DERIVATIVE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 t1 x1.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x1 IN D /\
    t1 IN ode_maxint f D (pastecart t0 x1)
    ==> ((\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w))) has_derivative
         (\v. drop(fstcart v) % f(pastecart t1 (ode_flow f D t1 (pastecart t0 x1))) +
              ode_varsol f D t0 x1 t1 (sndcart v)))
        (at (pastecart t1 x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sol")))))) THEN
  MP_TAC(ISPECL [`ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x1)`;
                 `t0:real^1`; `t1:real^1`] ODE_INTERVAL_AROUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1`
    (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x1:real^N`; `a:real^1`; `b:real^1`]
         ODE_FLOW_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rem")))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x1:real^N`] ODE_VARSOL_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mat") ASSUME_TAC) THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_FSTCART];
      SUBGOAL_THEN
       `(\v. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t1 (sndcart v)) =
        (\h. ode_varsol f D t0 x1 t1 h) o (sndcart:real^(1,N)finite_sum->real^N)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_SNDCART] THEN
      MATCH_MP_TAC ODE_VARSOL_LINEAR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "rem" (MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))) THEN
  SUBGOAL_THEN
   `(\t. vectorize(matrix(\h. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t h)))
    continuous (at t1)`
  MP_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2"))) THEN
  SUBGOAL_THEN
   `((\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t0 x1)) has_derivative
     (\s. drop s % f(pastecart t1 (ode_flow f D t1 (pastecart t0 x1))))) (at t1)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM has_vector_derivative] THEN
    REMOVE_THEN "sol" (MP_TAC o SPEC `t1:real^1`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r3"))) THEN
  EXISTS_TAC `min d0 (min d1 (min d2 d3))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `y:real^(1,N)finite_sum` THEN
  ABBREV_TAC `t = fstcart(y:real^(1,N)finite_sum)` THEN
  ABBREV_TAC `x = sndcart(y:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `y = pastecart (t:real^1) (x:real^N)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t"; "x"] THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_SUB] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t - t1:real^1`; `x - x1:real^N`] NORM_LE_PASTECART) THEN
  ABBREV_TAC `n = norm(pastecart (t - t1:real^1) (x - x1:real^N))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `norm(t - t1:real^1) < d0 /\ norm(t - t1) < d2 /\ norm(t - t1) < d3 /\
    norm(x - x1:real^N) <= d1`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_MIN]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^1) IN interval[a,b]` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x1)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "r1" (MP_TAC o SPECL [`x:real^N`; `t:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "r2" (MP_TAC o SPEC `t:real^1`) THEN
  ASM_REWRITE_TAC[dist] THEN DISCH_TAC THEN
  REMOVE_THEN "r3" (MP_TAC o SPEC `t:real^1`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t (x - x1) -
         ode_varsol f D t0 x1 t1 (x - x1)) <= e / &3 * norm(x - x1)`
  ASSUME_TAC THENL
   [USE_THEN "mat" (fun th -> ONCE_REWRITE_TAC[MATCH_MP th
      (ASSUME `(t:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D
                 (pastecart t0 x1)`)]) THEN
    USE_THEN "mat" (fun th -> ONCE_REWRITE_TAC[MATCH_MP th
      (ASSUME `(t1:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D
                 (pastecart t0 x1)`)]) THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `norm(vectorize(matrix(\h. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t h) -
                     matrix(\h. ode_varsol f D t0 x1 t1 h))) * norm(x - x1:real^N)` THEN
    REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE; VECTORIZE_SUB] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `u = ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart t0 x)` THEN
  ABBREV_TAC `u1 = ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart t0 x1)` THEN
  ABBREV_TAC `u0 = ode_flow (f:real^(1,N)finite_sum->real^N) D t1 (pastecart t0 x1)` THEN
  ABBREV_TAC `c = (f:real^(1,N)finite_sum->real^N)(pastecart t1 u0)` THEN
  ABBREV_TAC `V = ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t (x - x1)` THEN
  ABBREV_TAC `V1 = ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t1 (x - x1)` THEN
  SUBGOAL_THEN
   `u - u0 - (drop(t - t1) % c + V1) =
    (u - u1 - V) + (V - V1) + (u1 - u0 - drop(t - t1) % (c:real^N))`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `e / &3 * norm(x - x1:real^N) + e / &3 * norm(x - x1) +
              e / &3 * norm(t - t1:real^1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(p:real^N) <= a /\ norm(q) <= b /\ norm(r) <= c
      ==> norm(p + q + r) <= a + b + c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `e / &3 * norm(x - x1:real^N) <= e / &3 * n /\
    e / &3 * norm(t - t1:real^1) <= e / &3 * n`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Joint continuity of the variational solutions.                           *)

let ODE_VARSOL_JOINT_CONTINUOUS = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 t1 x1 h.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x1 IN D /\
    t1 IN ode_maxint f D (pastecart t0 x1)
    ==> (\w. ode_varsol f D t0 (sndcart w) (fstcart w) h) continuous
        (at (pastecart t1 x1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart t0 x1)`;
                 `t0:real^1`; `t1:real^1`] ODE_INTERVAL_AROUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1`
    (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[continuous_at; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x1:real^N`; `a:real^1`; `b:real^1`] ODE_VARSOL_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / (norm(h:real^N) + &1)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC(ISPEC `h:real^N` NORM_POS_LE) THEN UNDISCH_TAC `&0 < e` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  SUBGOAL_THEN
   `(\t. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1 t h) continuous (at t1)`
  MP_TAC THENL
   [MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_IMP_CONTINUOUS_AT THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `x1:real^N`] ODE_VARSOL_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:real^1`; `h:real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  EXISTS_TAC `min d0 (min d1 d2)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:real^(1,N)finite_sum`; `t1:real^1`; `x1:real^N`]
         ODE_DIST_FSTCART_SNDCART) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(w:real^(1,N)finite_sum) IN interval[a,b]` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(w:real^(1,N)finite_sum,pastecart t1 x1) < min d0 (min d1 d2)` THEN
    UNDISCH_TAC `dist(fstcart(w:real^(1,N)finite_sum),t1) <= dist(w,pastecart t1 x1)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "n1" (MP_TAC o SPECL
   [`sndcart(w:real^(1,N)finite_sum)`; `fstcart(w:real^(1,N)finite_sum)`; `h:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM dist] THEN
    UNDISCH_TAC `dist(w:real^(1,N)finite_sum,pastecart t1 x1) < min d0 (min d1 d2)` THEN
    UNDISCH_TAC `dist(sndcart(w:real^(1,N)finite_sum),x1) <= dist(w,pastecart t1 x1)` THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  REMOVE_THEN "n2" (MP_TAC o SPEC `fstcart(w:real^(1,N)finite_sum)`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `dist(w:real^(1,N)finite_sum,pastecart t1 x1) < min d0 (min d1 d2)` THEN
    UNDISCH_TAC `dist(fstcart(w:real^(1,N)finite_sum),t1) <= dist(w,pastecart t1 x1)` THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `e / &2 / (norm(h:real^N) + &1) * norm h <= e / &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `h:real^N` NORM_POS_LE) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2 / (norm(h:real^N) + &1) * (norm h + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN
        UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 <= norm(h:real^N)` THEN
        REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= norm(h:real^N)` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b c:real^N k. norm(a - b) <= k /\ dist(b,c) < e / &2 /\ k <= e / &2
                     ==> dist(a,c) < e`) THEN
  EXISTS_TAC `ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x1
                (fstcart(w:real^(1,N)finite_sum)) h` THEN
  EXISTS_TAC `e / &2 / (norm(h:real^N) + &1) * norm h` THEN
  ASM_REWRITE_TAC[]);;

(* The C^1 core: the flow at a fixed initial time is C^1 in (t,x0).         *)

let ODE_FLOW_C1_FIXED_TIME = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0.
    open D /\ continuously_differentiable 1 D f
    ==> open {pastecart t x | pastecart t0 x IN D /\
                              t IN ode_maxint f D (pastecart t0 x)} /\
        continuously_differentiable 1
          {pastecart t x | pastecart t0 x IN D /\
                           t IN ode_maxint f D (pastecart t0 x)}
          (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `W = {pastecart t x | pastecart t0 x IN D /\
                         t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D
                                (pastecart t0 x)}` THEN
  SUBGOAL_THEN
   `!w. w IN W <=>
        pastecart (fstcart w) (pastecart t0 (sndcart w)) IN
        ode_domain (f:real^(1,N)finite_sum->real^N) D`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[ODE_FIXED_TIME_DOMAIN; ODE_IN_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(W:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `W = {w | pastecart (fstcart w) (pastecart (t0:real^1) (sndcart w)) IN
               ode_domain (f:real^(1,N)finite_sum->real^N) D}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    SIMP_TAC[CONTINUOUS_CONST; LINEAR_CONTINUOUS_AT; LINEAR_SNDCART; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
           (pastecart t0 (sndcart w))) continuous_on W`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
             (pastecart t0 (sndcart w))) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o
      (\w. pastecart (fstcart w) (pastecart (t0:real^1) (sndcart w)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_PASTECART THEN
      SIMP_TAC[CONTINUOUS_CONST; LINEAR_CONTINUOUS_AT; LINEAR_SNDCART; ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ode_domain (f:real^(1,N)finite_sum->real^N) D` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `W:real^(1,N)finite_sum->bool`;
                 `\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
                        (pastecart t0 (sndcart w))`]
         CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ONE] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC
   `\w v. drop(fstcart v) %
          (f:real^(1,N)finite_sum->real^N)
            (pastecart (fstcart w)
               (ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))) +
          ode_varsol f D t0 (sndcart w) (fstcart w) (sndcart v)` THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `fstcart(w:real^(1,N)finite_sum)`;
                   `sndcart(w:real^(1,N)finite_sum)`]
           ODE_FLOW_FIXED_TIME_DERIVATIVE) THEN
    UNDISCH_TAC `(w:real^(1,N)finite_sum) IN W` THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[ODE_FIXED_TIME_DOMAIN] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^(1,N)finite_sum` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    SUBGOAL_THEN
     `(\w. (f:real^(1,N)finite_sum->real^N)
             (pastecart (fstcart w)
               (ode_flow f D (fstcart w) (pastecart t0 (sndcart w))))) =
      f o (\w. pastecart (fstcart w)
                 (ode_flow f D (fstcart w) (pastecart t0 (sndcart w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      EXPAND_TAC "W" THEN REWRITE_TAC[ODE_FIXED_TIME_DOMAIN] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                     `pastecart (t0:real^1) (sndcart(w:real^(1,N)finite_sum))`]
             ODE_MAXIMAL_SOLUTION) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[ODE_FIXED_TIME_DOMAIN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `t0:real^1`; `fstcart(w:real^(1,N)finite_sum)`;
                   `sndcart(w:real^(1,N)finite_sum)`;
                   `sndcart(v:real^(1,N)finite_sum)`]
           ODE_VARSOL_JOINT_CONTINUOUS) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND]]);;

(* The variational equation at a fixed initial time.                        *)

let ODE_FLOW_FIXED_TIME_FRECHET = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x s h.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D /\
    s IN ode_maxint f D (pastecart t0 x)
    ==> frechet_derivative (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))
          (at (pastecart s x)) (pastecart (vec 0) h) =
        ode_varsol f D t0 x s h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `s:real^1`; `x:real^N`]
         ODE_FLOW_FIXED_TIME_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; VECTOR_MUL_LZERO;
              VECTOR_ADD_LID]);;

let ODE_FLOW_VARIATIONAL_FIXED_TIME = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t0 x h.
    open D /\ continuously_differentiable 1 D f /\ pastecart t0 x IN D
    ==> frechet_derivative (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))
          (at (pastecart t0 x)) (pastecart (vec 0) h) = h /\
        !t. t IN ode_maxint f D (pastecart t0 x)
            ==> ((\s. frechet_derivative
                        (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))
                        (at (pastecart s x)) (pastecart (vec 0) h))
                 has_vector_derivative
                 frechet_derivative f
                   (at (pastecart t (ode_flow f D t (pastecart t0 x))))
                   (pastecart (vec 0)
                      (frechet_derivative
                         (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))
                         (at (pastecart t x)) (pastecart (vec 0) h)))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sol")))))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x:real^N`] ODE_VARSOL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vd")) THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[ODE_FLOW_FIXED_TIME_FRECHET]; ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ODE_FLOW_FIXED_TIME_FRECHET] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_DXMAT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REMOVE_THEN "sol" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t
                            (pastecart t0 x)) IN D`))]) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. ode_varsol (f:real^(1,N)finite_sum->real^N) D t0 x s h` THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC ODE_FLOW_FIXED_TIME_FRECHET THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "vd" (MP_TAC o SPECL [`t:real^1`; `h:real^N`]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Parametric problems by augmentation (ODE_PARAM_C1,                        *)
(* ODE_PARAM_VARIATIONAL), used by pc_ode_ck for C^k dependence.             *)
(* ------------------------------------------------------------------------- *)

let ODE_IN_UNIV_PCROSS = prove
 (`!(w:real^(M,N)finite_sum) s. w IN (:real^M) PCROSS s <=> sndcart w IN s`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV]);;

let ODE_PARAM_DOM_IN = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H w.
        w IN ode_param_dom g h D H <=>
        sndcart w IN H /\
        fstcart w IN ode_maxint (ode_param_field g) D
                       (pastecart (vec 0) (pastecart (h(sndcart w)) (sndcart w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ode_param_dom; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`fstcart(w:real^(1,Q)finite_sum)`;
                          `sndcart(w:real^(1,Q)finite_sum)`] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND]]);;

let ODE_PARAM_FIELD_C1 = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) D.
        open D /\ continuously_differentiable 1 D g
        ==> continuously_differentiable 1 D (ode_param_field g) /\
            !y k. y IN D
                  ==> frechet_derivative (ode_param_field g) (at y) k =
                      pastecart (frechet_derivative g (at y) k) (vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ode_param_field] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; ETA_AX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. pastecart ((g:real^(1,(N,Q)finite_sum)finite_sum->real^N) y) (vec 0:real^Q))
     has_derivative
     (\k. pastecart (frechet_derivative g (at y) k) (vec 0))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]));;

(* The solution map as a composition with the fixed time flow of the       *)
(* augmented field.                                                          *)

let ODE_PARAM_SOL_COMPOSE = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D.
        ode_param_sol g h D =
        (fstcart:real^(N,Q)finite_sum->real^N) o
        ((\w. ode_flow (ode_param_field g) D (fstcart w) (pastecart (vec 0) (sndcart w))) o
         (\w:real^(1,Q)finite_sum.
            pastecart (fstcart w) (pastecart (h(sndcart w)) (sndcart w))))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; ode_param_sol; FSTCART_PASTECART;
              SNDCART_PASTECART]);;

let ODE_PARAM_DOM_EQ = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H.
        (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
        ==> !w. w IN ode_param_dom g h D H <=>
                sndcart w IN H /\
                pastecart (fstcart w) (pastecart (h(sndcart w)) (sndcart w)) IN
                {pastecart t x | pastecart (vec 0) x IN D /\
                                 t IN ode_maxint (ode_param_field g) D
                                        (pastecart (vec 0) x)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[ODE_PARAM_DOM_IN; ODE_FIXED_TIME_DOMAIN; FSTCART_PASTECART;
              SNDCART_PASTECART] THEN
  ASM_MESON_TAC[]);;

let ODE_PARAM_C1 = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H.
    open D /\ open H /\
    continuously_differentiable 1 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
    ==> open(ode_param_dom g h D H) /\
        continuously_differentiable 1 (ode_param_dom g h D H)
          (ode_param_sol g h D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`]
         ODE_FLOW_C1_FIXED_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_DOM_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `W = {pastecart t x | pastecart (vec 0) x IN D /\
                         t IN ode_maxint
                                (ode_param_field
                                   (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
                                D (pastecart (vec 0) x)}` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^Q->real^N) continuous_on H` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `open(ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H =
      {w | w IN (:real^1) PCROSS H /\
           pastecart (fstcart w) (pastecart ((h:real^Q->real^N)(sndcart w)) (sndcart w))
           IN W}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; ODE_IN_UNIV_PCROSS]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX] THEN
    SUBGOAL_THEN
     `(\w. (h:real^Q->real^N)(sndcart w)) = h o (sndcart:real^(1,Q)finite_sum->real^Q)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `H:real^Q->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_UNIV_PCROSS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ODE_PARAM_SOL_COMPOSE] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `W:real^(1,(N,Q)finite_sum)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_FSTCART; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART; ETA_AX] THEN
  SUBGOAL_THEN
   `(\w. (h:real^Q->real^N)(sndcart w)) = h o (sndcart:real^(1,Q)finite_sum->real^Q)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `H:real^Q->bool` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* Derivative of the solution map by the chain rule.                        *)

let ODE_PARAM_SOL_FRECHET = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H s q v.
    open D /\ open H /\
    continuously_differentiable 1 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D) /\
    pastecart s q IN ode_param_dom g h D H
    ==> frechet_derivative (ode_param_sol g h D) (at (pastecart s q)) v =
        fstcart(frechet_derivative
                  (\w. ode_flow (ode_param_field g) D (fstcart w)
                         (pastecart (vec 0) (sndcart w)))
                  (at (pastecart s (pastecart (h q) q)))
                  (pastecart (fstcart v)
                     (pastecart (frechet_derivative h (at q) (sndcart v))
                                (sndcart v))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`]
         ODE_FLOW_C1_FIXED_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `W = {pastecart t x | pastecart (vec 0) x IN D /\
                         t IN ode_maxint
                                (ode_param_field
                                   (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
                                D (pastecart (vec 0) x)}` THEN
  ABBREV_TAC
   `Psi = \w. ode_flow (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
                D (fstcart w) (pastecart (vec 0) (sndcart w))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_DOM_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (s:real^1) (q:real^Q)`) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum`;
                 `W:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^Q->real^N`; `H:real^Q->bool`] ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\w:real^(1,Q)finite_sum.
        pastecart (fstcart w) (pastecart ((h:real^Q->real^N)(sndcart w)) (sndcart w)))
     has_derivative
     (\v. pastecart (fstcart v)
            (pastecart (frechet_derivative h (at q) (sndcart v)) (sndcart v))))
    (at (pastecart s q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LINEAR_FSTCART];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LINEAR_SNDCART]] THEN
    SUBGOAL_THEN
     `(\w. (h:real^Q->real^N)(sndcart w)) = h o (sndcart:real^(1,Q)finite_sum->real^Q) /\
      (\v. frechet_derivative (h:real^Q->real^N) (at q) (sndcart v)) =
      frechet_derivative h (at q) o (sndcart:real^(1,Q)finite_sum->real^Q)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    REWRITE_TAC[SNDCART_PASTECART] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum) has_derivative
     frechet_derivative Psi (at (pastecart s (pastecart ((h:real^Q->real^N) q) q))))
    (at (pastecart s (pastecart (h q) q)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w:real^(1,Q)finite_sum.
       pastecart (fstcart w) (pastecart ((h:real^Q->real^N)(sndcart w)) (sndcart w))`;
    `Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum`;
    `\v:real^(1,Q)finite_sum.
       pastecart (fstcart v)
         (pastecart (frechet_derivative (h:real^Q->real^N) (at q) (sndcart v))
                    (sndcart v))`;
    `frechet_derivative (Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum)
       (at (pastecart s (pastecart ((h:real^Q->real^N) q) q)))`;
    `pastecart (s:real^1) (q:real^Q)`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum) o
     (\w:real^(1,Q)finite_sum.
       pastecart (fstcart w) (pastecart ((h:real^Q->real^N)(sndcart w)) (sndcart w)))`;
    `fstcart:real^(N,Q)finite_sum->real^N`;
    `frechet_derivative (Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum)
       (at (pastecart s (pastecart ((h:real^Q->real^N) q) q))) o
     (\v:real^(1,Q)finite_sum.
       pastecart (fstcart v)
         (pastecart (frechet_derivative (h:real^Q->real^N) (at q) (sndcart v))
                    (sndcart v)))`;
    `fstcart:real^(N,Q)finite_sum->real^N`;
    `pastecart (s:real^1) (q:real^Q)`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_FSTCART] THEN
  REWRITE_TAC[ODE_PARAM_SOL_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

(* The variational equation for parametric problems.                       *)

let ODE_PARAM_VARIATIONAL = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H q
   (e:real^Q).
    open D /\ open H /\
    continuously_differentiable 1 D g /\ continuously_differentiable 1 H h /\
    (!q'. q' IN H ==> pastecart (vec 0) (pastecart (h q') q') IN D) /\
    q IN H
    ==> frechet_derivative (ode_param_sol g h D) (at (pastecart (vec 0) q))
          (pastecart (vec 0) e) = frechet_derivative h (at q) e /\
        !t. pastecart t q IN ode_param_dom g h D H
            ==> ((\s. frechet_derivative (ode_param_sol g h D)
                        (at (pastecart s q)) (pastecart (vec 0) e))
                 has_vector_derivative
                 frechet_derivative g
                   (at (pastecart t (pastecart (ode_param_sol g h D (pastecart t q)) q)))
                   (pastecart (vec 0)
                      (pastecart (frechet_derivative (ode_param_sol g h D)
                                    (at (pastecart t q)) (pastecart (vec 0) e))
                                 e))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dG")) THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q) IN D`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. pastecart s q IN
        ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H <=>
        s IN ode_maxint (ode_param_field g) D
               (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ODE_PARAM_DOM_IN; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN ode_maxint (ode_param_field g) D
               (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q))
        ==> frechet_derivative
              (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D)
              (at (pastecart s q)) (pastecart (vec 0) e) =
            fstcart(frechet_derivative
                      (\w. ode_flow (ode_param_field g) D (fstcart w)
                             (pastecart (vec 0) (sndcart w)))
                      (at (pastecart s (pastecart (h q) q)))
                      (pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) e)))`
  (LABEL_TAC "chain") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                   `s:real^1`; `q:real^Q`; `pastecart (vec 0:real^1) (e:real^Q)`]
           ODE_PARAM_SOL_FRECHET) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`;
                 `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q)`]
         ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sol")))))) THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`;
                 `pastecart ((h:real^Q->real^N) q) q`;
                 `pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) e`]
         ODE_FLOW_VARIATIONAL_FIXED_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "var")) THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`;
                 `(h:real^Q->real^N) q`; `q:real^Q`] ODE_FLOW_PARAM_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ps") THEN
  ABBREV_TAC
   `J = ode_maxint (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)) D
          (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q))` THEN
  ABBREV_TAC
   `Psi = \w. ode_flow (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
                D (fstcart w) (pastecart (vec 0) (sndcart w))` THEN
  ABBREV_TAC
   `u = \s. ode_flow (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
              D s (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q))` THEN
  SUBGOAL_THEN
   `!s. ode_flow (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N))
          D s (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q)) =
        (u:real^1->real^(N,Q)finite_sum) s`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             ASSUME_TAC th) THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Z = \s. frechet_derivative
              (Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum)
              (at (pastecart s (pastecart ((h:real^Q->real^N) q) q)))
              (pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) e))` THEN
  SUBGOAL_THEN
   `!s. frechet_derivative
          (Psi:real^(1,(N,Q)finite_sum)finite_sum->real^(N,Q)finite_sum)
          (at (pastecart s (pastecart ((h:real^Q->real^N) q) q)))
          (pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) e)) =
        (Z:real^1->real^(N,Q)finite_sum) s`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             ASSUME_TAC th) THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN J
        ==> ((Z:real^1->real^(N,Q)finite_sum) has_vector_derivative
             pastecart (frechet_derivative (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                          (at (pastecart s ((u:real^1->real^(N,Q)finite_sum) s)))
                          (pastecart (vec 0) (Z s)))
                       (vec 0)) (at s)`
  (LABEL_TAC "dZ") THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "sol" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    USE_THEN "dG" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `pastecart s ((u:real^1->real^(N,Q)finite_sum) s) IN D`))]) THEN
    REMOVE_THEN "var" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN J ==> sndcart((Z:real^1->real^(N,Q)finite_sum) s) = e`
  (LABEL_TAC "sndZ") THENL
   [MP_TAC(ISPECL [`\s. sndcart((Z:real^1->real^(N,Q)finite_sum) s)`; `J:real^1->bool`]
           HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[IS_INTERVAL_CONVEX_1]; ALL_TAC] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(\x:real^1. vec 0:real^Q) = (\x. drop x % vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_RZERO]; ALL_TAC] THEN
      REWRITE_TAC[GSYM has_vector_derivative] THEN
      MP_TAC(ISPECL [`sndcart:real^(N,Q)finite_sum->real^Q`;
                     `Z:real^1->real^(N,Q)finite_sum`;
                     `pastecart (frechet_derivative
                                   (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                                   (at (pastecart s ((u:real^1->real^(N,Q)finite_sum) s)))
                                   (pastecart (vec 0) ((Z:real^1->real^(N,Q)finite_sum) s)))
                                (vec 0:real^Q)`;
                     `s:real^1`] ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT) THEN
      REWRITE_TAC[LINEAR_SNDCART; SNDCART_PASTECART] THEN
      DISCH_THEN MATCH_MP_TAC THEN REMOVE_THEN "dZ" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real^Q`) THEN
    SUBGOAL_THEN `c:real^Q = e` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `(Z:real^1->real^(N,Q)finite_sum) (vec 0) =
      pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) e` THEN
    SIMP_TAC[SNDCART_PASTECART];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "chain" (MP_TAC o SPEC `vec 0:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s. s IN J
        ==> frechet_derivative
              (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D)
              (at (pastecart s q)) (pastecart (vec 0) e) =
            fstcart((Z:real^1->real^(N,Q)finite_sum) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REMOVE_THEN "chain" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^1->real^(N,Q)finite_sum) t =
    pastecart (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D
                 (pastecart t q)) q`
  ASSUME_TAC THENL
   [REWRITE_TAC[ode_param_sol; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ps" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MESON_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Z:real^1->real^(N,Q)finite_sum) t =
    pastecart (frechet_derivative
                 (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D)
                 (at (pastecart t q)) (pastecart (vec 0) e)) e`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN REMOVE_THEN "sndZ" (MP_TAC o SPEC `t:real^1`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\s. fstcart((Z:real^1->real^(N,Q)finite_sum) s)` THEN
  EXISTS_TAC `J:real^1->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fstcart:real^(N,Q)finite_sum->real^N`;
                 `Z:real^1->real^(N,Q)finite_sum`;
                 `pastecart (frechet_derivative
                               (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                               (at (pastecart t ((u:real^1->real^(N,Q)finite_sum) t)))
                               (pastecart (vec 0) ((Z:real^1->real^(N,Q)finite_sum) t)))
                            (vec 0:real^Q)`;
                 `t:real^1`] ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT) THEN
  REWRITE_TAC[LINEAR_FSTCART; FSTCART_PASTECART] THEN
  ANTS_TAC THENL [REMOVE_THEN "dZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The flow with variable initial time as a parametric problem by           *)
(* translation in time (ODE_FLOW_AS_PARAM).                                 *)
(* ------------------------------------------------------------------------- *)

let ODE_HAS_VECTOR_DERIVATIVE_SHIFT = prove
 (`!(u:real^1->real^N) u' t c.
        (u has_vector_derivative u') (at (t + c))
        ==> ((\s. u(s + c)) has_vector_derivative u') (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. s + c`; `u:real^1->real^N`; `vec 1 + vec 0:real^1`;
                 `u':real^N`; `t:real^1`] VECTOR_DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF; DROP_ADD; DROP_VEC; REAL_ADD_RID; VECTOR_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST]);;

let ODE_HAS_VECTOR_DERIVATIVE_SHIFT_SUB = prove
 (`!(u:real^1->real^N) u' t c.
        (u has_vector_derivative u') (at (t - c))
        ==> ((\s. u(s - c)) has_vector_derivative u') (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. s - c`; `u:real^1->real^N`; `vec 1 - vec 0:real^1`;
                 `u':real^N`; `t:real^1`] VECTOR_DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF; DROP_SUB; DROP_VEC; REAL_SUB_RZERO; VECTOR_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST]);;

let ODE_HAS_VECTOR_DERIVATIVE_PASTECART_CONST = prove
 (`!(u:real^1->real^N) u' (c:real^P) t s.
        (u has_vector_derivative u') (at t within s)
        ==> ((\x. pastecart (u x) c) has_vector_derivative pastecart u' (vec 0))
            (at t within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. drop x % pastecart (u':real^N) (vec 0:real^P)) =
    (\x. pastecart (drop x % u') (vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST]);;

let ODE_IS_INTERVAL_SHIFT = prove
 (`!J (c:real^1).
        is_interval J
        ==> is_interval {t | t + c IN J} /\ is_interval {t | t - c IN J}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [IS_INTERVAL_1]) THENL
   [MAP_EVERY EXISTS_TAC [`a + c:real^1`; `b + c:real^1`];
    MAP_EVERY EXISTS_TAC [`a - c:real^1`; `b - c:real^1`]] THEN
  ASM_REWRITE_TAC[DROP_ADD; DROP_SUB] THEN ASM_REAL_ARITH_TAC);;

(* The translated field and its domain.                                     *)

let ODE_TRANSLATE_SETUP = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable 1 D f
    ==> open {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
                pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                          (fstcart(sndcart w)) IN D} /\
        continuously_differentiable 1
          {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
                pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                          (fstcart(sndcart w)) IN D}
          (\w. f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                           (fstcart(sndcart w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `L = \w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
          pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w))` THEN
  SUBGOAL_THEN
   `linear(L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
       pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)) IN D} =
    {w | (L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^(1,N)finite_sum) w
         IN D} /\
    (\w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
       (f:real^(1,N)finite_sum->real^N)
         (pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))) =
    f o L`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open {w | (L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->
                            real^(1,N)finite_sum) w IN D}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]);;

(* Forward: solutions of the original problem give solutions of the        *)
(* translated parametric problem.                                           *)

let ODE_TRANSLATE_FORWARD = prove
 (`!(f:real^(1,N)finite_sum->real^N) D
    (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N) D' z.
    open D /\ continuously_differentiable 1 D f /\
    open D' /\ continuously_differentiable 1 D' g /\
    (!w. w IN D' <=>
         pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)) IN D) /\
    (!w. g w = f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))) /\
    z IN D
    ==> !t. t IN ode_maxint f D z
            ==> t - fstcart z IN
                ode_maxint (ode_param_field g) D' (pastecart (vec 0) (pastecart (sndcart z) z)) /\
                ode_flow (ode_param_field g) D' (t - fstcart z)
                  (pastecart (vec 0) (pastecart (sndcart z) z)) =
                pastecart (ode_flow f D t z) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`]
         ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`ode_param_field
                    (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fs")))))) THEN
  MP_TAC(ISPECL
   [`ode_param_field (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)`;
    `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
    `pastecart (vec 0:real^1) (pastecart (sndcart(z:real^(1,N)finite_sum)) z)`;
    `{tau | tau + fstcart(z:real^(1,N)finite_sum) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z}`;
    `\tau. pastecart (ode_flow (f:real^(1,N)finite_sum->real^N) D (tau + fstcart(z:real^(1,N)finite_sum)) z)
                     (z:real^(1,N)finite_sum)`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM;
                    VECTOR_ADD_LID] THEN
    REWRITE_TAC[ode_solution] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ode_maxint (f:real^(1,N)finite_sum->real^N) D z`;
                     `fstcart(z:real^(1,N)finite_sum)`] ODE_IS_INTERVAL_SHIFT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `tau:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REMOVE_THEN "fs" (MP_TAC o SPEC `tau + fstcart(z:real^(1,N)finite_sum)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ode_param_field; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) + tau = tau + fstcart(z:real^(1,N)finite_sum)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_PASTECART_CONST THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC(REWRITE_RULE[]
     (ISPECL [`\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z`]
             ODE_HAS_VECTOR_DERIVATIVE_SHIFT)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "eq")) THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t - fstcart(z:real^(1,N)finite_sum)) + fstcart(z:real^(1,N)finite_sum) = t:real^1` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "eq" (MP_TAC o SPEC `t - fstcart(z:real^(1,N)finite_sum)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)]);;

(* Backward: solutions of the translated problem give solutions of the     *)
(* original one.                                                             *)

let ODE_TRANSLATE_BACKWARD = prove
 (`!(f:real^(1,N)finite_sum->real^N) D
    (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N) D' z.
    open D /\ continuously_differentiable 1 D f /\
    open D' /\ continuously_differentiable 1 D' g /\
    (!w. w IN D' <=>
         pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)) IN D) /\
    (!w. g w = f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))) /\
    z IN D
    ==> !tau. tau IN ode_maxint (ode_param_field g) D'
                       (pastecart (vec 0) (pastecart (sndcart z) z))
              ==> tau + fstcart z IN ode_maxint f D z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`]
         ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`ode_param_field
                    (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart (vec 0:real^1) (pastecart (sndcart(z:real^(1,N)finite_sum)) z) IN D'`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_ADD_RID;
                    PASTECART_FST_SND];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ode_param_field (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)`;
    `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
    `pastecart (vec 0:real^1) (pastecart (sndcart(z:real^(1,N)finite_sum)) z)`]
   ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gs")))))) THEN
  MP_TAC(ISPECL [`g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `vec 0:real^1`; `sndcart(z:real^(1,N)finite_sum)`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_PARAM_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ps") THEN
  ABBREV_TAC
   `J = ode_maxint (ode_param_field
                      (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)) D'
          (pastecart (vec 0) (pastecart (sndcart(z:real^(1,N)finite_sum)) z))` THEN
  ABBREV_TAC
   `V = \s. ode_flow (ode_param_field
                        (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)) D' s
              (pastecart (vec 0) (pastecart (sndcart(z:real^(1,N)finite_sum)) z))` THEN
  SUBGOAL_THEN
   `!s. ode_flow (ode_param_field
                    (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)) D' s
          (pastecart (vec 0) (pastecart (sndcart(z:real^(1,N)finite_sum)) z)) =
        (V:real^1->real^(N,(1,N)finite_sum)finite_sum) s`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             ASSUME_TAC th) THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
    `z:real^(1,N)finite_sum`; `{t | t - fstcart(z:real^(1,N)finite_sum) IN J}`;
    `\t. fstcart((V:real^1->real^(N,(1,N)finite_sum)finite_sum)
                   (t - fstcart(z:real^(1,N)finite_sum)))`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_SUB_REFL; FSTCART_PASTECART] THEN
    REWRITE_TAC[ode_solution] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`J:real^1->bool`; `fstcart(z:real^(1,N)finite_sum)`]
             ODE_IS_INTERVAL_SHIFT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) + (t - fstcart z) = t:real^1`
    ASSUME_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "ps" (MP_TAC o SPEC `t - fstcart(z:real^(1,N)finite_sum)`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
    REMOVE_THEN "gs" (MP_TAC o SPEC `t - fstcart(z:real^(1,N)finite_sum)`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC(REWRITE_RULE[]
     (ISPECL [`\s. fstcart((V:real^1->real^(N,(1,N)finite_sum)finite_sum) s)`]
             ODE_HAS_VECTOR_DERIVATIVE_SHIFT_SUB)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  X_GEN_TAC `tau:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(tau + c) - c:real^1 = tau`]);;

let ODE_FLOW_AS_PARAM = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable 1 D f
    ==> !t z. z IN D
              ==> (t IN ode_maxint f D z <=>
                   pastecart (t - fstcart z) z IN
                   ode_param_dom
                     (\w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
                        f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                                    (fstcart(sndcart w))))
                     sndcart
                     {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
                        pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                                  (fstcart(sndcart w)) IN D}
                     D) /\
                  (t IN ode_maxint f D z
                   ==> ode_flow f D t z =
                       ode_param_sol
                         (\w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
                            f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                                        (fstcart(sndcart w))))
                         sndcart
                         {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
                            pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                                      (fstcart(sndcart w)) IN D}
                         (pastecart (t - fstcart z) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_TRANSLATE_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `D' = {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
            pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                      (fstcart(sndcart w)) IN D}` THEN
  ABBREV_TAC
   `g = \w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
          (f:real^(1,N)finite_sum->real^N)
            (pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum. w IN D' <=>
         pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)) IN D) /\
    (!w. (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N) w =
         f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w))))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D'"; "g"] THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
  REWRITE_TAC[ODE_PARAM_DOM_IN; ode_param_sol; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_TRANSLATE_FORWARD) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_TRANSLATE_BACKWARD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t - fstcart(z:real^(1,N)finite_sum)`) THEN
  REWRITE_TAC[VECTOR_ARITH `(t - c) + c:real^1 = t`] THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
  ASM_CASES_TAC `(t:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C^1 dependence on (t, t0, x0) and the derivatives of the flow map        *)
(* (ODE_FLOW_C1, ODE_FLOW_DERIVATIVE_TIME,                                  *)
(* ODE_FLOW_DERIVATIVE_INITIAL_TIME, ODE_FLOW_VARIATIONAL).                 *)
(* ------------------------------------------------------------------------- *)

let ODE_FLOW_C1 = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable 1 D f
    ==> open(ode_domain f D) /\
        continuously_differentiable 1 (ode_domain f D)
          (\w. ode_flow f D (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_TRANSLATE_SETUP) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_AS_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `D' = {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
            pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                      (fstcart(sndcart w)) IN D}` THEN
  ABBREV_TAC
   `g = \w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
          (f:real^(1,N)finite_sum->real^N)
            (pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))` THEN
  DISCH_THEN(LABEL_TAC "ap") THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `sndcart:real^(1,N)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `D:real^(1,N)finite_sum->bool`] ODE_PARAM_C1) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
    X_GEN_TAC `q:real^(1,N)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "D'" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                    VECTOR_ADD_RID; PASTECART_FST_SND];
    STRIP_TAC] THEN
  ABBREV_TAC
   `T0 = \w:real^(1,(1,N)finite_sum)finite_sum.
           pastecart (fstcart w - fstcart(sndcart w)) (sndcart w)` THEN
  SUBGOAL_THEN
   `linear(T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ode_domain (f:real^(1,N)finite_sum->real^N) D
        ==> (T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum) w
            IN ode_param_dom g sndcart D' D /\
            ode_flow f D (fstcart w) (sndcart w) = ode_param_sol g sndcart D' (T0 w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN
    REWRITE_TAC[ODE_IN_DOMAIN_ALT] THEN STRIP_TAC THEN EXPAND_TAC "T0" THEN
    REWRITE_TAC[] THEN
    REMOVE_THEN "ap" (MP_TAC o SPECL [`fstcart(w:real^(1,(1,N)finite_sum)finite_sum)`;
                                      `sndcart(w:real^(1,(1,N)finite_sum)finite_sum)`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC
   `ode_param_sol (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N) sndcart D' o
    (T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum)` THEN
  ASM_SIMP_TAC[o_THM] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC
   `ode_param_dom (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)
                  sndcart D' D` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

(* The flow map is differentiable at each point of the (open) domain.       *)

let ODE_FLOW_HAS_DERIVATIVE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D w.
    open D /\ continuously_differentiable 1 D f /\ w IN ode_domain f D
    ==> ((\w. ode_flow f D (fstcart w) (sndcart w)) has_derivative
         frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w)) (at w)) (at w) /\
        linear(frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w)) (at w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP ODE_C1_FRECHET) THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^(1,(1,N)finite_sum)finite_sum` o CONJUNCT1 o
             CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]);;

let ODE_FLOW_DERIVATIVE_TIME = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t z a.
    open D /\ continuously_differentiable 1 D f /\
    pastecart t z IN ode_domain f D
    ==> frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w))
          (at (pastecart t z)) (pastecart a (vec 0)) =
        drop a % f(pastecart t (ode_flow f D t z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t:real^1) (z:real^(1,N)finite_sum)`]
         ODE_FLOW_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `DF = frechet_derivative
           (\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w) (sndcart w))
           (at (pastecart (t:real^1) (z:real^(1,N)finite_sum)))` THEN
  UNDISCH_TAC `pastecart (t:real^1) (z:real^(1,N)finite_sum) IN
               ode_domain (f:real^(1,N)finite_sum->real^N) D` THEN
  REWRITE_TAC[ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s:real^1. pastecart s (z:real^(1,N)finite_sum)`;
    `\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w) (sndcart w)`;
    `\s:real^1. pastecart s (vec 0:real^(1,N)finite_sum)`;
    `DF:real^(1,(1,N)finite_sum)finite_sum->real^N`; `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z`;
    `\s:real^1. DF(pastecart s (vec 0:real^(1,N)finite_sum)):real^N`;
    `\x:real^1. drop x % (f:real^(1,N)finite_sum->real^N)
                           (pastecart t (ode_flow f D t z))`;
    `t:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `a:real^1`) THEN
  REWRITE_TAC[]);;

let ODE_FLOW_DERIVATIVE_INITIAL_TIME = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t z a.
    open D /\ continuously_differentiable 1 D f /\
    pastecart t z IN ode_domain f D
    ==> frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w))
          (at (pastecart t z)) (pastecart (vec 0) (pastecart a (vec 0))) =
        frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w))
          (at (pastecart t z))
          (pastecart (vec 0) (pastecart (vec 0) (--(drop a % f z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (t:real^1) (z:real^(1,N)finite_sum)`]
         ODE_FLOW_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `DF = frechet_derivative
           (\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w) (sndcart w))
           (at (pastecart (t:real^1) (z:real^(1,N)finite_sum)))` THEN
  UNDISCH_TAC `pastecart (t:real^1) (z:real^(1,N)finite_sum) IN
               ode_domain (f:real^(1,N)finite_sum->real^N) D` THEN
  REWRITE_TAC[ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sol")))))) THEN
  ABBREV_TAC `t0 = fstcart(z:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `pastecart (t0:real^1) (sndcart(z:real^(1,N)finite_sum)) = z`
  ASSUME_TAC THENL [EXPAND_TAC "t0" THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z) has_derivative
     (\x. drop x % f z)) (at t0)`
  ASSUME_TAC THENL
   [REMOVE_THEN "sol" (MP_TAC o SPEC `t0:real^1`) THEN
    ASM_REWRITE_TAC[has_vector_derivative] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart(pastecart t (pastecart s
                    (ode_flow f D s z))))
              (sndcart(pastecart t (pastecart s (ode_flow f D s z))))) has_derivative
     (\x. vec 0)) (at t0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\s:real^1. ode_flow (f:real^(1,N)finite_sum->real^N) D t z` THEN
    EXISTS_TAC `ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `z:real^(1,N)finite_sum`; `s:real^1`] ODE_FLOW_COCYCLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s:real^1. pastecart (t:real^1)
                  (pastecart s (ode_flow (f:real^(1,N)finite_sum->real^N) D s z))`;
    `\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w) (sndcart w)`;
    `\x:real^1. pastecart (vec 0:real^1)
                  (pastecart x (drop x % (f:real^(1,N)finite_sum->real^N) z))`;
    `DF:real^(1,(1,N)finite_sum)finite_sum->real^N`; `t0:real^1`] DIFF_CHAIN_AT) THEN
  SUBGOAL_THEN
   `pastecart (t:real^1) (pastecart t0 (ode_flow (f:real^(1,N)finite_sum->real^N) D t0 z)) =
    pastecart t z`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s. ode_flow (f:real^(1,N)finite_sum->real^N) D
           (fstcart(pastecart t (pastecart s (ode_flow f D s z))))
           (sndcart(pastecart t (pastecart s (ode_flow f D s z))))`;
    `\x:real^1. (DF:real^(1,(1,N)finite_sum)finite_sum->real^N)
                  (pastecart (vec 0) (pastecart x (drop x % (f:real^(1,N)finite_sum->real^N) z)))`;
    `\x:real^1. vec 0:real^N`; `t0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `a:real^1`) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pastecart (vec 0:real^1) (pastecart (a:real^1) (drop a % (f:real^(1,N)finite_sum->real^N) z)) =
    pastecart (vec 0) (pastecart a (vec 0)) +
    pastecart (vec 0) (pastecart (vec 0) (drop a % f z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD] THEN
  SUBGOAL_THEN
   `pastecart (vec 0:real^1) (pastecart (vec 0:real^1) (--(drop a % (f:real^(1,N)finite_sum->real^N) z))) =
    --(pastecart (vec 0) (pastecart (vec 0) (drop a % f z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_NEG; VECTOR_NEG_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN VECTOR_ARITH_TAC);;

(* The variational equation for the flow with variable initial time.       *)

let ODE_FLOW_VARIATIONAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z (e:real^(1,N)finite_sum).
    open D /\ continuously_differentiable 1 D f /\ z IN D
    ==> frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w))
          (at (pastecart (fstcart z) z)) (pastecart (vec 0) e) =
        sndcart e - drop(fstcart e) % f z /\
        !t. t IN ode_maxint f D z
            ==> ((\s. frechet_derivative
                        (\w. ode_flow f D (fstcart w) (sndcart w))
                        (at (pastecart s z)) (pastecart (vec 0) e))
                 has_vector_derivative
                 frechet_derivative f (at (pastecart t (ode_flow f D t z)))
                   (pastecart (vec 0)
                      (frechet_derivative
                         (\w. ode_flow f D (fstcart w) (sndcart w))
                         (at (pastecart t z)) (pastecart (vec 0) e)))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t0 = fstcart(z:real^(1,N)finite_sum)` THEN
  ABBREV_TAC `x0 = sndcart(z:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `pastecart (t0:real^1) (x0:real^N) = z` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t0"; "x0"] THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  ABBREV_TAC
   `k = sndcart(e:real^(1,N)finite_sum) - drop(fstcart e) %
        (f:real^(1,N)finite_sum->real^N) z` THEN
  SUBGOAL_THEN
   `!s. s IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z
        ==> frechet_derivative (\w. ode_flow f D (fstcart w) (sndcart w))
              (at (pastecart s z)) (pastecart (vec 0) e) =
            frechet_derivative
              (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))
              (at (pastecart s x0)) (pastecart (vec 0) k)`
  (LABEL_TAC "I") THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (s:real^1) (z:real^(1,N)finite_sum) IN
                  ode_domain (f:real^(1,N)finite_sum->real^N) D`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[ODE_IN_DOMAIN]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `pastecart (s:real^1) (z:real^(1,N)finite_sum)`]
           ODE_FLOW_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `s:real^1`; `z:real^(1,N)finite_sum`;
                   `fstcart(e:real^(1,N)finite_sum)`]
           ODE_FLOW_DERIVATIVE_INITIAL_TIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC
     `DF = frechet_derivative
             (\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w) (sndcart w))
             (at (pastecart (s:real^1) (z:real^(1,N)finite_sum)))` THEN
    SUBGOAL_THEN
     `frechet_derivative
        (\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
               (pastecart t0 (sndcart w)))
        (at (pastecart s x0)) =
      (DF:real^(1,(1,N)finite_sum)finite_sum->real^N) o
      (\v:real^(1,N)finite_sum.
         pastecart (fstcart v) (pastecart (vec 0:real^1) (sndcart v)))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      SUBGOAL_THEN
       `(\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
               (pastecart t0 (sndcart w))) =
        (\w. ode_flow f D (fstcart w) (sndcart w)) o
        (\w:real^(1,N)finite_sum. pastecart (fstcart w) (pastecart (t0:real^1) (sndcart w)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
        ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
        REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART]];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN
     `pastecart (vec 0:real^1) (e:real^(1,N)finite_sum) =
      pastecart (vec 0) (pastecart (fstcart e) (vec 0)) +
      pastecart (vec 0) (pastecart (vec 0) (sndcart e))`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID; PASTECART_FST_SND];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(DF:real^(1,(1,N)finite_sum)finite_sum->real^N)
        (pastecart (vec 0) (pastecart (vec 0)
           (--(drop(fstcart(e:real^(1,N)finite_sum)) %
               (f:real^(1,N)finite_sum->real^N) z)))) +
      DF(pastecart (vec 0) (pastecart (vec 0) (sndcart e)))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM LINEAR_ADD] THEN AP_TERM_TAC THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; PASTECART_INJ] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `t0:real^1`; `x0:real^N`; `k:real^N`]
         ODE_FLOW_VARIATIONAL_FIXED_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fv")) THEN
  CONJ_TAC THENL
   [USE_THEN "I" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(t0:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  USE_THEN "I" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(t:real^1) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)]) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC
   `\s. frechet_derivative
          (\w. ode_flow (f:real^(1,N)finite_sum->real^N) D (fstcart w)
                 (pastecart t0 (sndcart w)))
          (at (pastecart s x0)) (pastecart (vec 0) k)` THEN
  EXISTS_TAC `ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN REMOVE_THEN "I" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "fv" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[]]);;

