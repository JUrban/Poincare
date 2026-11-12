(* Vendored copy of the library file src/ns_smooth.ml from the Navier_Stokes
   development (github.com/hol-light-family/Navier_Stokes).
   Code unchanged except that its needs lines point to the vendored copies. *)

(* ========================================================================= *)
(* Smooth calculus on real^N, part 0: the C^k predicate and its closure      *)
(* properties, Schwarz symmetry for C^2 maps, and the smooth inverse         *)
(* function theorem.                                                         *)
(*                                                                           *)
(* Ported unchanged (88 top-level blocks, with their local dependencies)     *)
(* from a HOL Light prototype of differential geometry by the project's      *)
(* initiator, which also supplies the C^k predicate                          *)
(* continuously_differentiable.  Only the blocks needed here were taken.     *)
(* ========================================================================= *)

type_invention_error := true;;

let HAS_DERIVATIVE_LINE_PARAM = prove
 (`!a (v:real^N) (t:real^1).
    ((\t. a + drop t % v) has_derivative (\d. drop d % v)) (at t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\d:real^1. drop d % v:real^N) = (\d. vec 0 + drop d % v)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID]);;

let HAS_DERIVATIVE_TRANSLATION = prove
 (`!(f:real^N->real^M) f' c (y:real^N).
    (f has_derivative f') (at (y + c))
    ==> ((\z. f(z + c)) has_derivative f') (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[o_DEF] (ISPECL
    [`\z:real^N. z + c`; `f:real^N->real^M`;
     `\h:real^N. h`; `f':real^N->real^M`; `y:real^N`] DIFF_CHAIN_AT)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(\h:real^N. h:real^N) = (\h. h + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
   MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
   REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX]);;

let DIFFERENTIABLE_TRANSLATION = prove
 (`!(f:real^N->real^M) c y.
    f differentiable at (y + c) ==> (\z. f(z + c)) differentiable at y`,
  REWRITE_TAC[differentiable] THEN MESON_TAC[HAS_DERIVATIVE_TRANSLATION]);;

let DIFFERENTIABLE_TRANSLATION_DIFF = prove
 (`!(f:real^N->real^M) c y.
    f differentiable at y /\ f differentiable at (y + c)
    ==> (\z. f(z + c) - f(z)) differentiable at y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_SUB THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_TRANSLATION]);;

let FRECHET_DERIVATIVE_TRANSLATION_DIFF = prove
 (`!(f:real^N->real^M) c y v.
    f differentiable at y /\ f differentiable at (y + c)
    ==> frechet_derivative (\z. f(z + c) - f(z)) (at y) v =
        frechet_derivative f (at (y + c)) v - frechet_derivative f (at y) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `frechet_derivative (\z:real^N. (f:real^N->real^M)(z + c) - f z) (at y) =
     (\v. frechet_derivative f (at (y + c)) v - frechet_derivative f (at y) v)`
    (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
  [MATCH_MP_TAC HAS_DERIVATIVE_TRANSLATION THEN
   ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
   ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let MVT_ALONG_LINE = prove
 (`!(f:real^N->real^1) a (v:real^N) h.
    &0 <= h /\
    (!t. &0 <= t /\ t <= h ==> f differentiable at (a + t % v))
    ==> ?c. &0 <= c /\ c <= h /\
            f(a + h % v) - f a =
            h % frechet_derivative f (at (a + c % v)) v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h = &0` THENL
  [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID;
    VECTOR_SUB_REFL; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^N->real^1) o (\t:real^1. a + drop t % v)`;
                  `\u:real^1. frechet_derivative (f:real^N->real^1)
                    (at (a + drop u % v)) o (\d:real^1. drop d % v)`;
                  `vec 0:real^1`; `lift h`] MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   X_GEN_TAC `u:real^1` THEN
   REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
   MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
   MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_LINE_PARAM]; ALL_TAC] THEN
   REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[o_DEF; DROP_VEC; LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
              IN_INTERVAL_1; DROP_SUB] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop(w:real^1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h - &0 = h` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `linear(frechet_derivative (f:real^N->real^1) (at (a + drop w % v)))`
    MP_TAC THENL
  [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
   SIMP_TAC[linear] THEN MESON_TAC[]]);;

let MVT_SECOND_DIFFERENCE = prove
 (`!(f:real^N->real^1) (x:real^N) (ei:real^N) (ej:real^N) h.
    &0 < h /\
    (!s t. &0 <= s /\ s <= h /\ &0 <= t /\ t <= h
           ==> f differentiable at (x + s % ei + t % ej)) /\
    (!s t. &0 <= s /\ s <= h /\ &0 <= t /\ t <= h
           ==> (\z. frechet_derivative f (at z) ei)
                differentiable at (x + s % ei + t % ej))
    ==> ?c1 c2. &0 <= c1 /\ c1 <= h /\ &0 <= c2 /\ c2 <= h /\
                f(x + h % ei + h % ej) - f(x + h % ei) -
                f(x + h % ej) + f(x) =
                (h * h) %
                frechet_derivative
                  (\z. frechet_derivative f (at z) ei)
                  (at (x + c1 % ei + c2 % ej)) ej`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= h` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* First MVT: apply to g(t) = f(x+t%ei+h%ej) - f(x+t%ei) along ei *)
  MP_TAC(ISPECL [`\y:real^N. (f:real^N->real^1)(y + h % ej) - f y`;
                  `x:real^N`; `ei:real^N`; `h:real`] MVT_ALONG_LINE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
   MATCH_MP_TAC DIFFERENTIABLE_TRANSLATION_DIFF THEN
   SUBGOAL_THEN `!s' t'. &0 <= s' /\ s' <= h /\ &0 <= t' /\ t' <= h
     ==> (f:real^N->real^1) differentiable at (x + s' % ei + t' % ej)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `x + t % ei = x + t % ei + &0 % ej:real^N` SUBST1_TAC THENL
    [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(x + t % ei) + h % ej = x + t % ei + h % ej:real^N`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
    `(x + h % ei) + h % ej = x + h % ei + h % ej:real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC) THEN
  (* Establish f differentiable at key points for FRECHET_DERIVATIVE *)
  SUBGOAL_THEN
    `(f:real^N->real^1) differentiable at (x + c1 % ei) /\
     f differentiable at (x + c1 % ei + h % ej)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [SUBGOAL_THEN `x + c1 % ei = x + c1 % ei + &0 % ej:real^N`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Compute g'(c1) using FRECHET_DERIVATIVE_TRANSLATION_DIFF *)
  SUBGOAL_THEN
    `frechet_derivative (\y:real^N. (f:real^N->real^1)(y + h % ej) - f y)
       (at (x + c1 % ei)) ei =
     frechet_derivative f (at (x + c1 % ei + h % ej)) ei -
     frechet_derivative f (at (x + c1 % ei)) ei`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:real^N->real^1`; `h % ej:real^N`;
                   `x + c1 % ei:real^N`; `ei:real^N`]
    FRECHET_DERIVATIVE_TRANSLATION_DIFF) THEN
   REWRITE_TAC[VECTOR_ARITH
     `(x + c % ei) + h % ej = x + c % ei + h % ej:real^N`] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Second MVT: apply to Di(z) = frechet_derivative f (at z) ei along ej *)
  MP_TAC(ISPECL [`\z:real^N. frechet_derivative (f:real^N->real^1) (at z) ei`;
                  `x + c1 % ei:real^N`; `ej:real^N`; `h:real`]
    MVT_ALONG_LINE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
   REWRITE_TAC[VECTOR_ARITH
     `(x + c % ei) + t % ej = x + c % ei + t % ej:real^N`] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
    `(x + c1 % ei) + c2 % ej = x + c1 % ei + c2 % ej:real^N`;
    VECTOR_ARITH
    `(x + c1 % ei) + h % ej = x + c1 % ei + h % ej:real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c1:real` THEN EXISTS_TAC `c2:real` THEN
  ASM_REWRITE_TAC[] THEN
  (* Combine: second_diff = h%(Di(x+c1%ei+h%ej) - Di(x+c1%ei))
                          = h%(h % frechet_derivative Di (at ...) ej)
                          = (h*h) % ... *)
  SUBGOAL_THEN
    `(f:real^N->real^1) (x + h % ei + h % ej) - f (x + h % ei) -
     f (x + h % ej) + f x =
     f (x + h % ei + h % ej) - f (x + h % ei) - (f (x + h % ej) - f x)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC]);;

let SCHWARZ_PARTIAL_DERIVATIVES = prove
 (`!f:real^N->real^1 s x i j.
    open s /\ x IN s /\
    i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N) /\
    (!y. y IN s ==> f differentiable at y) /\
    (!y. y IN s
         ==> (\z. frechet_derivative f (at z) (basis i)) differentiable at y /\
             (\z. frechet_derivative f (at z) (basis j)) differentiable at y) /\
    (\y. frechet_derivative
           (\z. frechet_derivative f (at z) (basis i)) (at y) (basis j))
      continuous at x /\
    (\y. frechet_derivative
           (\z. frechet_derivative f (at z) (basis j)) (at y) (basis i))
      continuous at x
    ==> frechet_derivative (\z. frechet_derivative f (at z) (basis i))
          (at x) (basis j) =
        frechet_derivative (\z. frechet_derivative f (at z) (basis j))
          (at x) (basis i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Di = \y:real^N. frechet_derivative (f:real^N->real^1)
                                (at y) (basis i)` THEN
  ABBREV_TAC `Dj = \y:real^N. frechet_derivative (f:real^N->real^1)
                                (at y) (basis j)` THEN
  REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0; GSYM REAL_LE_ANTISYM;
              NORM_POS_LE] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = norm(frechet_derivative (Di:real^N->real^1) (at x)
                         (basis j) -
                       frechet_derivative Dj (at x) (basis i))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Get ball(x,r) inside s *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  (* Get d1 from continuity of frechet_derivative Dj (...) (basis i) *)
  UNDISCH_TAC
    `(\y. frechet_derivative (Dj:real^N->real^1)
            (at y) (basis i)) continuous at (x:real^N)` THEN
  ASM_REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  (* Get d2 from continuity of frechet_derivative Di (...) (basis j) *)
  UNDISCH_TAC
    `(\y. frechet_derivative (Di:real^N->real^1)
            (at y) (basis j)) continuous at (x:real^N)` THEN
  ASM_REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  (* Choose h *)
  ABBREV_TAC `h = min r (min d1 d2) / &3` THEN
  SUBGOAL_THEN `&0 < h /\ h < r /\ h < d1 /\ h < d2` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* NORM_BASIS simplification *)
  SUBGOAL_THEN `norm(basis i:real^N) = &1 /\ norm(basis j:real^N) = &1`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC NORM_BASIS THEN
   ASM_REWRITE_TAC[GSYM IN_NUMSEG]; ALL_TAC] THEN
  (* Key norm bound: 2h < r, d1, d2 *)
  SUBGOAL_THEN `&2 * h < r /\ &2 * h < d1 /\ &2 * h < d2`
    STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Norm bound for points in the box *)
  SUBGOAL_THEN
    `!s' t'. &0 <= s' /\ s' <= h /\ &0 <= t' /\ t' <= h
             ==> norm(s' % basis i + t' % basis j:real^N) < r /\
                 norm(s' % basis i + t' % basis j:real^N) < d1 /\
                 norm(s' % basis i + t' % basis j:real^N) < d2`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * h` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `norm(s' % basis i:real^N) + norm(t' % basis j:real^N)` THEN
   REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Membership in s *)
  SUBGOAL_THEN
    `!s' t'. &0 <= s' /\ s' <= h /\ &0 <= t' /\ t' <= h
             ==> (x + s' % basis i + t' % basis j:real^N) IN s`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
   REWRITE_TAC[IN_BALL; dist;
     VECTOR_ARITH `x - (x + a):real^N = --a`; NORM_NEG] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`s':real`; `t':real`]) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* First MVT_SECOND_DIFFERENCE: with basis i, basis j *)
  MP_TAC(ISPECL [`f:real^N->real^1`; `x:real^N`; `basis i:real^N`;
                 `basis j:real^N`; `h:real`] MVT_SECOND_DIFFERENCE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(x + s' % basis i + t % basis j:real^N) IN s`
      ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `(x + s' % basis i + t % basis j:real^N) IN s`
      ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real`
    (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)) THEN
  (* Second MVT_SECOND_DIFFERENCE: with basis j, basis i *)
  MP_TAC(ISPECL [`f:real^N->real^1`; `x:real^N`; `basis j:real^N`;
                 `basis i:real^N`; `h:real`] MVT_SECOND_DIFFERENCE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(x + s' % basis j + t % basis i:real^N) IN s`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `x + s' % basis j + t % basis i =
                    x + t % basis i + s' % basis j:real^N` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
     ASM_MESON_TAC[]];
    SUBGOAL_THEN `(x + s' % basis j + t % basis i:real^N) IN s`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `x + s' % basis j + t % basis i =
                    x + t % basis i + s' % basis j:real^N` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
     ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1':real`
    (X_CHOOSE_THEN `d2':real` STRIP_ASSUME_TAC)) THEN
  (* Abbreviate the two second derivative values *)
  ABBREV_TAC `A = frechet_derivative
    (\z. frechet_derivative (f:real^N->real^1) (at z) (basis i))
    (at (x + c1 % basis i + c2 % basis j)) (basis j)` THEN
  ABBREV_TAC `B = frechet_derivative
    (\z. frechet_derivative (f:real^N->real^1) (at z) (basis j))
    (at (x + d1' % basis j + d2' % basis i)) (basis i)` THEN
  (* Prove h*h <> 0 *)
  SUBGOAL_THEN `~(h * h = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Prove A = B from the two MVT equations *)
  SUBGOAL_THEN `A:real^1 = B` ASSUME_TAC THENL
  [SUBGOAL_THEN `(h * h) % A = (h * h) % B:real^1` MP_TAC THENL
   [SUBGOAL_THEN `x + h % basis i + h % basis j =
                   x + h % basis j + h % basis i:real^N`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `f (x + h % basis j + h % basis i) -
        f (x + h % basis i:real^N) -
      f (x + h % basis j) + f x =
      f (x + h % basis j + h % basis i) -
        f (x + h % basis j) -
      f (x + h % basis i) + f x:real^1`
      MP_TAC THENL [VECTOR_ARITH_TAC; ASM_MESON_TAC[]];
    ASM_MESON_TAC[VECTOR_MUL_LCANCEL]];
   ALL_TAC] THEN
  (* Get distance bound for Di at c1,c2 *)
  SUBGOAL_THEN
    `dist(frechet_derivative (Di:real^N->real^1)
            (at (x + c1 % basis i + c2 % basis j)) (basis j),
          frechet_derivative Di (at x) (basis j)) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `x + c1 % basis i + c2 % basis j:real^N` o
     check (fun th -> free_in `d2:real` (concl th) &&
                      not(free_in `d1:real` (concl th)))) THEN
   REWRITE_TAC[dist; VECTOR_ARITH `(x + a) - x:real^N = a`] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   UNDISCH_TAC `!s' t'. &0 <= s' /\ s' <= h /\ &0 <= t' /\ t' <= h
     ==> norm (s' % basis i + t' % basis j:real^N) < r /\
         norm (s' % basis i + t' % basis j:real^N) < d1 /\
         norm (s' % basis i + t' % basis j:real^N) < d2` THEN
   DISCH_THEN(MP_TAC o SPECL [`c1:real`; `c2:real`]) THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC[];
   ALL_TAC] THEN
  (* Get distance bound for Dj at d1',d2' *)
  SUBGOAL_THEN
    `dist(frechet_derivative (Dj:real^N->real^1)
            (at (x + d1' % basis j + d2' % basis i)) (basis i),
          frechet_derivative Dj (at x) (basis i)) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `x + d1' % basis j + d2' % basis i:real^N` o
     check (fun th -> free_in `d1:real` (concl th) &&
                      not(free_in `d2:real` (concl th)))) THEN
   REWRITE_TAC[dist; VECTOR_ARITH `(x + a) - x:real^N = a`] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   SUBGOAL_THEN `d1' % basis j + d2' % basis i =
                  d2' % basis i + d1' % basis j:real^N`
     SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `!s' t'. &0 <= s' /\ s' <= h /\ &0 <= t' /\ t' <= h
     ==> norm (s' % basis i + t' % basis j:real^N) < r /\
         norm (s' % basis i + t' % basis j:real^N) < d1 /\
         norm (s' % basis i + t' % basis j:real^N) < d2` THEN
   DISCH_THEN(MP_TAC o SPECL [`d2':real`; `d1':real`]) THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC[];
   ALL_TAC] THEN
  (* Connect A, B with Di, Dj *)
  SUBGOAL_THEN
    `frechet_derivative (Di:real^N->real^1)
       (at (x + c1 % basis i + c2 % basis j)) (basis j) = A`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `Di = (\z:real^N. frechet_derivative (f:real^N->real^1)
                         (at z) (basis i))`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `frechet_derivative (Dj:real^N->real^1)
       (at (x + d1' % basis j + d2' % basis i)) (basis i) = B`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `Dj = (\z:real^N. frechet_derivative (f:real^N->real^1)
                         (at z) (basis j))`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Triangle inequality + contradiction *)
  MP_TAC(ASSUME
    `norm (frechet_derivative (Di:real^N->real^1) (at x) (basis j) -
          frechet_derivative (Dj:real^N->real^1) (at x) (basis i)) = e`) THEN
  SUBGOAL_THEN
    `norm(frechet_derivative (Di:real^N->real^1) (at x) (basis j) -
         frechet_derivative Dj (at x) (basis i)) <=
     dist(A, frechet_derivative Di (at x) (basis j)) +
     dist(A, frechet_derivative Dj (at x) (basis i))`
    MP_TAC THENL
  [REWRITE_TAC[dist] THEN NORM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `dist(A:real^1, frechet_derivative (Di:real^N->real^1) (at x) (basis j))
       < e / &2`
    ASSUME_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `dist(A:real^1, frechet_derivative (Dj:real^N->real^1) (at x) (basis i))
       < e / &2`
    ASSUME_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let continuously_differentiable = define
 `(continuously_differentiable 0 s (f:real^M->real^N) <=>
   f continuous_on s) /\
  (!n. continuously_differentiable (SUC n) s f <=>
       ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
            !h. continuously_differentiable n s (\x. f' x h))`;;

let CONTINUOUSLY_DIFFERENTIABLE_0 = prove
 (`!s f:real^M->real^N.
     continuously_differentiable 0 s f <=> f continuous_on s`,
  REWRITE_TAC[continuously_differentiable]);;

let CONTINUOUSLY_DIFFERENTIABLE_SUC = prove
 (`!n s f:real^M->real^N.
     continuously_differentiable (SUC n) s f <=>
     ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
          !h. continuously_differentiable n s (\x. f' x h)`,
  REWRITE_TAC[continuously_differentiable]);;

let CONTINUOUSLY_DIFFERENTIABLE_1 = prove
 (`!s f:real^M->real^N.
     continuously_differentiable 1 s f <=>
     ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
          !h. (\x. f' x h) continuous_on s`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; CONTINUOUSLY_DIFFERENTIABLE_SUC;
              CONTINUOUSLY_DIFFERENTIABLE_0]);;

let CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON = prove
 (`!n s f:real^M->real^N.
     continuously_differentiable (SUC n) s f ==> f differentiable_on s`,
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC; differentiable_on;
              differentiable] THEN
  MESON_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON = prove
 (`!n s f:real^M->real^N.
     continuously_differentiable n s f ==> f continuous_on s`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[differentiable_on; differentiable] THEN
  ASM_MESON_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_SUC_IMP = prove
 (`!n s f:real^M->real^N.
     continuously_differentiable (SUC n) s f
     ==> continuously_differentiable n s f`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0;
                CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[differentiable_on; differentiable] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `f':real^M->real^M->real^N` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^M`) THEN MESON_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_MONO = prove
 (`!m n s f:real^M->real^N.
     m <= n /\ continuously_differentiable n s f
     ==> continuously_differentiable m s f`,
  GEN_TAC THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d. n = m + d:num` MP_TAC THENL
   [EXISTS_TAC `n - m:num` THEN ASM_ARITH_TAC;
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC)] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUC_IMP THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN = prove
 (`!n s f:real^M->real^N.
     open s
     ==> (continuously_differentiable (SUC n) s f <=>
          ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x)) /\
               !h. continuously_differentiable n s (\x. f' x h))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  SUBGOAL_THEN
    `!(f':real^M->real^M->real^N) (x:real^M).
       x IN s
       ==> ((f has_derivative f' x) (at x within s) <=>
            (f has_derivative f' x) (at x))`
    (fun th -> SIMP_TAC[th]) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN]);;

let CONTINUOUSLY_DIFFERENTIABLE_UNIV = prove
 (`!n f:real^M->real^N.
     continuously_differentiable (SUC n) (:real^M) f <=>
     ?f'. (!x. (f has_derivative f' x) (at x)) /\
          !h. continuously_differentiable n (:real^M) (\x. f' x h)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `(:real^M)`; `f:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN = prove
 (`!n s f g:real^M->real^N.
     open s /\
     (!x. x IN s ==> f x = g x) /\
     continuously_differentiable n s f
     ==> continuously_differentiable n s g`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `f:real^M->real^N` THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^N) has_derivative f' x)
            (at x)) /\
           !h. continuously_differentiable n s (\x. f' x h)` MP_TAC THENL
     [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^M->real^M->real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`f:real^M->real^N`; `s:real^M->bool`] THEN
    ASM_SIMP_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_FRECHET = prove
 (`!n s f:real^M->real^N.
     open s /\ continuously_differentiable (SUC n) s f
     ==> !h. continuously_differentiable n s
               (\x. frechet_derivative f (at x) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^N) has_derivative f' x)
           (at x)) /\
          !h. continuously_differentiable n s (\x. f' x h)` MP_TAC THENL
    [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `h:real^M` THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `(\x:real^M. (f':real^M->real^M->real^N) x h):real^M->real^N` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
  ASM_SIMP_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_FRECHET_UNIV = prove
 (`!n f:real^M->real^N.
     continuously_differentiable (SUC n) (:real^M) f
     ==> !h. continuously_differentiable n (:real^M)
               (\x. frechet_derivative f (at x) h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `(:real^M)`; `f:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `h:real^M`) THEN REWRITE_TAC[]);;

let LINEAR_LIFT_DOLLAR_COMPONENT = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> linear((\x:real^N. lift(x$k)):real^N->real^1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear; CART_EQ] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           LIFT_ADD; LIFT_CMUL; LIFT_COMPONENT;
           DIMINDEX_1; FORALL_1]);;

let CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O = prove
 (`!n s (f:real^M->real^N) (g:real^N->real^P).
     open s /\ linear g /\ continuously_differentiable n s f
     ==> continuously_differentiable n s (g o f)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^N) has_derivative f' x)
            (at x)) /\
           !h. continuously_differentiable n s (\x. f' x h)` MP_TAC THENL
     [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x:real^M. (g:real^N->real^P) o
                (f':real^M->real^M->real^N) x):real^M->real^M->real^P` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `h:real^M` THEN REWRITE_TAC[o_DEF] THEN
      SUBGOAL_THEN
       `(\x:real^M. (g:real^N->real^P)
         ((f':real^M->real^M->real^N) x (h:real^M))) = g o (\x. f' x h)`
       SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let FRECHET_DERIVATIVE_LIFT_VECTOR_COMPONENT = prove
 (`!(f:real^M->real^N) x k.
     f differentiable at x /\ 1 <= k /\ k <= dimindex(:N)
     ==> frechet_derivative (\z. lift(f z$k)) (at x) =
         (\h. lift(frechet_derivative f (at x) h$k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
  SUBGOAL_THEN `(\z:real^M. lift((f:real^M->real^N) z$k)) =
                (\x:real^N. lift(x$k)) o f` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^M. lift(frechet_derivative (f:real^M->real^N)
                (at x) h$k)) =
                (\x:real^N. lift(x$k)) o frechet_derivative f (at x)`
   SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN
  ASM_REWRITE_TAC[]);;

let SCHWARZ_C2_SCALAR = prove
 (`!s (f:real^M->real^1) x i j.
     open s /\ x IN s /\
     i IN 1..dimindex(:M) /\ j IN 1..dimindex(:M) /\
     continuously_differentiable 2 s f
     ==> frechet_derivative
           (\z. frechet_derivative f (at z) (basis i)) (at x) (basis j) =
         frechet_derivative
           (\z. frechet_derivative f (at z) (basis j)) (at x) (basis i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHWARZ_PARTIAL_DERIVATIVES THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!h:real^M. continuously_differentiable 1 s
    (\z:real^M. frechet_derivative (f:real^M->real^1) (at z) h)`
    (LABEL_TAC "C1PART") THENL
   [MP_TAC(ISPECL [`1`; `s:real^M->bool`; `f:real^M->real^1`]
      CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^1) differentiable_on s` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
      REWRITE_TAC[differentiable_on] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
      MESON_TAC[differentiable]];
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
        `(\z:real^M. frechet_derivative (f:real^M->real^1) (at z) (basis i))
         differentiable_on s` MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
        EXISTS_TAC `0` THEN
        ASM_SIMP_TAC[ARITH_RULE `SUC 0 = 1`];
        REWRITE_TAC[differentiable_on] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
        MESON_TAC[differentiable]];
      SUBGOAL_THEN
        `(\z:real^M. frechet_derivative (f:real^M->real^1) (at z) (basis j))
         differentiable_on s` MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
        EXISTS_TAC `0` THEN
        ASM_SIMP_TAC[ARITH_RULE `SUC 0 = 1`];
        REWRITE_TAC[differentiable_on] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
        MESON_TAC[differentiable]]];
    SUBGOAL_THEN
      `(\y:real^M. frechet_derivative
         (\z. frechet_derivative (f:real^M->real^1) (at z) (basis i))
         (at y) (basis j)) continuous_on s` MP_TAC THENL
     [MP_TAC(ISPECL [`0`; `s:real^M->bool`;
        `(\z:real^M. frechet_derivative (f:real^M->real^1) (at z) (basis i))`]
        CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC 0 = 1`] THEN
      DISCH_THEN(MP_TAC o SPEC `basis j:real^M`) THEN
      REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0];
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]];
    SUBGOAL_THEN
      `(\y:real^M. frechet_derivative
         (\z. frechet_derivative (f:real^M->real^1) (at z) (basis j))
         (at y) (basis i)) continuous_on s` MP_TAC THENL
     [MP_TAC(ISPECL [`0`; `s:real^M->bool`;
        `(\z:real^M. frechet_derivative (f:real^M->real^1) (at z) (basis j))`]
        CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC 0 = 1`] THEN
      DISCH_THEN(MP_TAC o SPEC `basis i:real^M`) THEN
      REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0];
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]]]);;

let SCHWARZ_C2 = prove
 (`!s (f:real^M->real^N) x i j.
     open s /\ x IN s /\
     i IN 1..dimindex(:M) /\ j IN 1..dimindex(:M) /\
     continuously_differentiable 2 s f
     ==> frechet_derivative
           (\z. frechet_derivative f (at z) (basis i)) (at x) (basis j) =
         frechet_derivative
           (\z. frechet_derivative f (at z) (basis j)) (at x) (basis i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ABBREV_TAC `g = (\z:real^M. lift((f:real^M->real^N) z $ k))` THEN
  SUBGOAL_THEN `continuously_differentiable 2 s (g:real^M->real^1)`
    ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    SUBGOAL_THEN `(\z:real^M. lift((f:real^M->real^N) z $ k)) =
                  ((\x:real^N. lift(x$k)) o f)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) differentiable at x` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^M->real^N) differentiable_on s` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
      REWRITE_TAC[differentiable_on] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
      MESON_TAC[differentiable]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^M.
      (\z:real^M. frechet_derivative (f:real^M->real^N) (at z) h)
      differentiable at x`
   (LABEL_TAC "PARTDIFF") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
      `(\z:real^M. frechet_derivative (f:real^M->real^N) (at z) h)
       differentiable_on s` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
      MP_TAC(ISPECL [`1`; `s:real^M->bool`; `f:real^M->real^N`]
        CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[differentiable_on] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
      MESON_TAC[differentiable]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN s
    ==> (f:real^M->real^N) differentiable at y` (LABEL_TAC "FDIFF") THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) differentiable_on s` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
      REWRITE_TAC[differentiable_on] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
      MESON_TAC[differentiable]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y m. y IN s
    ==> frechet_derivative (g:real^M->real^1) (at y) (basis m) =
        lift(frechet_derivative (f:real^M->real^N) (at y) (basis m) $ k)`
   (LABEL_TAC "GCONN") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `frechet_derivative (g:real^M->real^1) (at y) =
       (\v:real^M. lift(frechet_derivative (f:real^M->real^N) (at y) v $ k))`
      (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "g" THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_LIFT_VECTOR_COMPONENT THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `g:real^M->real^1`; `x:real^M`;
                  `i:num`; `j:num`] SCHWARZ_C2_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN
  SUBGOAL_THEN
   `!h:real^M->real^N. h differentiable at x
    ==> !v:real^M. lift(frechet_derivative h (at x) v $ k) =
                   frechet_derivative (\z. lift(h z $ k)) (at x) v`
   (LABEL_TAC "INV") THENL
   [GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MP_TAC(ISPEC `h:real^M->real^N` FRECHET_DERIVATIVE_LIFT_VECTOR_COMPONENT) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> CONV_TAC(RAND_CONV(REWRITE_CONV[th])));
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!m. frechet_derivative (\z:real^M. frechet_derivative (g:real^M->real^1)
          (at z) (basis m)) (at x) =
        frechet_derivative (\z. lift(frechet_derivative (f:real^M->real^N)
          (at z) (basis m) $ k)) (at x)`
   (fun fd2 -> ONCE_REWRITE_TAC[GSYM fd2]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `((\z:real^M. lift(frechet_derivative (f:real^M->real^N)
          (at z) (basis m) $ k)) has_derivative
      frechet_derivative (\z. frechet_derivative (g:real^M->real^1)
          (at z) (basis m)) (at x)) (at x)`
     (fun th -> REWRITE_TAC[GSYM(MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th)]) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(\z:real^M. frechet_derivative (g:real^M->real^1)
                  (at z) (basis m))` THEN
    EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[BETA_THM] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    SUBGOAL_THEN
     `continuously_differentiable 1 s
       (\z:real^M. frechet_derivative (g:real^M->real^1)
         (at z) (basis m))`
     MP_TAC THENL
     [MP_TAC(ISPECL [`1`; `s:real^M->bool`; `g:real^M->real^1`]
       CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      DISCH_THEN(fun th ->
       MP_TAC(MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON
         (REWRITE_RULE[ARITH_RULE `1 = SUC 0`] th))) THEN
      REWRITE_TAC[differentiable_on] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN] THEN
      MESON_TAC[differentiable]];
    ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_CONST = prove
 (`!n (s:real^M->bool) (c:real^N).
    open s ==> continuously_differentiable n s (\x. c)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_CONST];
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
   EXISTS_TAC `\(x:real^M) (h:real^M). vec 0:real^N` THEN
   REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_ID = prove
 (`!n:num. continuously_differentiable n (:real^N) (\x:real^N. x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_ID];
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_UNIV] THEN
    EXISTS_TAC `\(x:real^N) (h:real^N). h` THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `(:real^N)`; `h:real^N`]
      CONTINUOUSLY_DIFFERENTIABLE_CONST) THEN
    REWRITE_TAC[OPEN_UNIV]]);;

let CONTINUOUSLY_DIFFERENTIABLE_ID_OPEN = prove
 (`!n s. open s ==> continuously_differentiable n s (\x:real^N. x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_ID];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    EXISTS_TAC `\(x:real^N) (h:real^N). h` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_WITHIN_OPEN];
      GEN_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN
      ASM_REWRITE_TAC[]]]);;

let smooth_map_on = new_definition
 `smooth_map_on M (f:real^M->real^N) <=>
    !n. continuously_differentiable n M f`;;

let SMOOTH_MAP_ON_ID = prove
 (`smooth_map_on M (\x:real^N. x)`,
  REWRITE_TAC[smooth_map_on] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_ID];
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    EXISTS_TAC `\(x:real^N) (h:real^N). h` THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    SUBGOAL_THEN `!n (M:real^N->bool) (c:real^N).
      continuously_differentiable n M (\x. c)` (fun th -> REWRITE_TAC[th]) THEN
    INDUCT_TAC THENL
     [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_CONST];
      REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN REPEAT GEN_TAC THEN
      EXISTS_TAC `\(x:real^N) (h:real^N). vec 0:real^N` THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ASM_REWRITE_TAC[]]]);;

let SMOOTH_MAP_ON_CONST = prove
 (`!M (c:real^P). smooth_map_on (M:real^N->bool) (\x. c)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!n (M:real^N->bool) (c:real^P).
    continuously_differentiable n M (\x. c)` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; CONTINUOUS_ON_CONST];
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN REPEAT GEN_TAC THEN
    EXISTS_TAC `\(x:real^N) (h:real^N). vec 0:real^P` THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ASM_REWRITE_TAC[]]);;

let SMOOTH_MAP_ON_CONTINUOUS = prove
 (`!M (f:real^N->real^P). smooth_map_on M f ==> f continuous_on M`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0]);;

let CONTINUOUSLY_DIFFERENTIABLE_SUBSET = prove
 (`!n (s:real^N->bool) (t:real^N->bool) (f:real^N->real^P).
     t SUBSET s /\ continuously_differentiable n s f
     ==> continuously_differentiable n t f`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N->real^P` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f':real^N->real^N->real^P` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let SMOOTH_MAP_ON_SUBSET = prove
 (`!M s (f:real^N->real^P).
     s SUBSET M /\ smooth_map_on M f ==> smooth_map_on s f`,
  REWRITE_TAC[smooth_map_on] THEN
  MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUBSET]);;

let CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN = prove
 (`!n s (f:real^M->real^N) g.
       open s /\
       continuously_differentiable n s f /\ continuously_differentiable n s g
       ==> continuously_differentiable n s (\x. f x + g x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^N) has_derivative f' x)
          (at x)) /\
         !h. continuously_differentiable n s (\x. f' x h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g'. (!x:real^M. x IN s ==> ((g:real^M->real^N) has_derivative g' x)
          (at x)) /\
         !h. continuously_differentiable n s (\x. g' x h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  EXISTS_TAC `(\x h:real^M.
    (f':real^M->real^M->real^N) x h + (g':real^M->real^M->real^N) x h)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `h:real^M` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN = prove
 (`!n s (f:A->real^M->real^N) (t:A->bool).
       open s /\ FINITE t /\
       (!a. a IN t ==> continuously_differentiable n s (f a))
       ==> continuously_differentiable n s (\x. vsum t (\a. f a x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t':A->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES] THEN
  SUBGOAL_THEN
    `(\x:real^M. (f:A->real^M->real^N) a x + vsum t' (\a. f a x)) =
     (\x. f a x + (\x. vsum t' (\a. f a x)) x)`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN = prove
 (`!n s (b:real^A->real^B->real^C) (f:real^M->real^A) (g:real^M->real^B).
       open s /\ bilinear b /\
       continuously_differentiable n s f /\
       continuously_differentiable n s g
       ==> continuously_differentiable n s (\x. b (f x) (g x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BILINEAR_CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^A) has_derivative f' x)
          (at x)) /\
         !h. continuously_differentiable n s (\x. f' x h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g'. (!x:real^M. x IN s ==> ((g:real^M->real^B) has_derivative g' x)
          (at x)) /\
         !h. continuously_differentiable n s (\x. g' x h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  EXISTS_TAC `(\x:real^M h:real^M.
    (b:real^A->real^B->real^C) ((f:real^M->real^A) x)
      ((g':real^M->real^M->real^B) x h) +
    b ((f':real^M->real^M->real^A) x h) ((g:real^M->real^B) x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_BILINEAR_AT THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^M` THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun ih ->
      MATCH_MP_TAC(BETA_RULE(SPECL
       [`s:real^M->bool`;
        `b:real^A->real^B->real^C`;
        `f:real^M->real^A`;
        `(\x:real^M. (g':real^M->real^M->real^B) x (h:real^M))`] ih)));
    FIRST_ASSUM(fun ih ->
      MATCH_MP_TAC(BETA_RULE(SPECL
       [`s:real^M->bool`;
        `b:real^A->real^B->real^C`;
        `(\x:real^M. (f':real^M->real^M->real^A) x (h:real^M))`;
        `g:real^M->real^B`] ih)))] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
  EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[LE; LE_REFL]);;

let LINEAR_LIFT_VECTOR_COMPONENT = prove
 (`!k. linear(\x:real^N. lift(x$k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    MP_TAC(ISPEC `basis j:real^N` LINEAR_LIFT_DOT) THEN
    ASM_SIMP_TAC[DOT_BASIS]]);;

let LINEAR_APPLY_EXPAND = prove
 (`!f:real^N->real^P v.
       linear f
       ==> f v = vsum(1..dimindex(:N)) (\k. v$k % f(basis k))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN = prove
 (`!n s t (f:real^M->real^N) (g:real^N->real^P).
       open s /\ open t /\ IMAGE f s SUBSET t /\
       continuously_differentiable n s f /\
       continuously_differentiable n t g
       ==> continuously_differentiable n s (g o f)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?f'. (!x:real^M. x IN s ==> ((f:real^M->real^N) has_derivative f' x)
          (at x)) /\
         !h. continuously_differentiable n s (\x. f' x h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g'. (!y:real^N. y IN t ==> ((g:real^N->real^P) has_derivative g' y)
          (at y)) /\
         !h. continuously_differentiable n t (\y. g' y h)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
  EXISTS_TAC `(\x:real^M.
    (g':real^N->real^N->real^P) ((f:real^M->real^N) x) o
    (f':real^M->real^M->real^N) x)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^M. x IN s ==> linear((g':real^N->real^N->real^P)
    ((f:real^M->real^N) x))` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative_at; SUBSET; IN_IMAGE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^M` THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `(\x:real^M. vsum (1..dimindex(:N))
    (\k. (f':real^M->real^M->real^N) x (h:real^M)$k %
         (g':real^N->real^N->real^P) ((f:real^M->real^N) x) (basis k)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. (f':real^M->real^M->real^N) x (h:real^M)$k %
                (g':real^N->real^N->real^P) ((f:real^M->real^N) x) (basis k)) =
    (\x. (\u:real^1 v:real^P. drop u % v)
      (((\y:real^N. lift(y$k)) o (\x. f' x h)) x)
      (((\y:real^N. g' y (basis k)) o f) x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_VECTOR_COMPONENT];
    FIRST_X_ASSUM(fun ih ->
      MATCH_MP_TAC(BETA_RULE(SPECL
       [`s:real^M->bool`; `t:real^N->bool`;
        `f:real^M->real^N`;
        `(\y:real^N. (g':real^N->real^N->real^P) y (basis k))`] ih))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[LE; LE_REFL]]);;

let CONTINUOUSLY_DIFFERENTIABLE_NEG_OPEN = prove
 (`!n s (f:real^M->real^N).
      open s /\ continuously_differentiable n s f
      ==> continuously_differentiable n s (\x. --(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. --((f:real^M->real^N) x)) = (--) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_NEGATION]);;

let CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN = prove
 (`!n s (f:real^M->real^N) g.
      open s /\
      continuously_differentiable n s f /\ continuously_differentiable n s g
      ==> continuously_differentiable n s (\x. f x - g x)`,
  REWRITE_TAC[VECTOR_SUB] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_NEG_OPEN]);;

let CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN = prove
 (`!n s c (f:real^M->real^N).
      open s /\ continuously_differentiable n s f
      ==> continuously_differentiable n s (\x. c % f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. c % (f:real^M->real^N) x) = (\v. c % v) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_SCALING]);;

let LINEAR_PASTECART_VEC0_L = prove
 (`linear(\v:real^N. pastecart v (vec 0:real^P))`,
  SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; pastecart; DIMINDEX_FINITE_SUM;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let LINEAR_PASTECART_VEC0_R = prove
 (`linear(\v:real^P. pastecart (vec 0:real^N) v)`,
  SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; pastecart; DIMINDEX_FINITE_SUM;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN = prove
 (`!n s (f:real^M->real^N) (g:real^M->real^P).
      open s /\
      continuously_differentiable n s f /\
      continuously_differentiable n s g
      ==> continuously_differentiable n s (\x. pastecart (f x) (g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x:real^M. pastecart ((f:real^M->real^N) x) ((g:real^M->real^P) x)) =
     (\x. (\v. pastecart v (vec 0:real^P)) (f x) +
          (\v. pastecart (vec 0:real^N) v) (g x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC(RAND_CONV(REWRITE_CONV[PASTECART_ADD; VECTOR_ADD_LID;
                                     VECTOR_ADD_RID])) THEN
    REFL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
      `(\x:real^M. pastecart ((f:real^M->real^N) x) (vec 0:real^P)) =
       (\v. pastecart v (vec 0)) o f` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_PASTECART_VEC0_L];
    SUBGOAL_THEN
      `(\x:real^M. pastecart (vec 0:real^N) ((g:real^M->real^P) x)) =
       (\v. pastecart (vec 0) v) o g` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_PASTECART_VEC0_R]]);;

let SMOOTH_MAP_ON_ADD_OPEN = prove
 (`!s (f:real^M->real^N) g.
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. f x + g x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_NEG_OPEN = prove
 (`!s (f:real^M->real^N).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. --(f x))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_NEG_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_SUB_OPEN = prove
 (`!s (f:real^M->real^N) g.
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. f x - g x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_CMUL_OPEN = prove
 (`!s c (f:real^M->real^N).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. c % f x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_COMPOSE_OPEN = prove
 (`!s t (f:real^M->real^N) (g:real^N->real^P).
      open s /\ open t /\ IMAGE f s SUBSET t /\
      smooth_map_on s f /\ smooth_map_on t g
      ==> smooth_map_on s (g o f)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_BILINEAR_OPEN = prove
 (`!s (b:real^A->real^B->real^C) (f:real^M->real^A) (g:real^M->real^B).
      open s /\ bilinear b /\
      smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. b (f x) (g x))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SMOOTH_MAP_ON_LINEAR_O = prove
 (`!s (f:real^M->real^N) (g:real^N->real^P).
      open s /\ linear g /\ smooth_map_on s f
      ==> smooth_map_on s (g o f)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_VSUM_OPEN = prove
 (`!s (f:A->real^M->real^N) (t:A->bool).
      open s /\ FINITE t /\
      (!a. a IN t ==> smooth_map_on s (f a))
      ==> smooth_map_on s (\x. vsum t (\a. f a x))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SMOOTH_MAP_ON_PASTECART_OPEN = prove
 (`!s (f:real^M->real^N) (g:real^M->real^P).
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. pastecart (f x) (g x))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_FSTCART_OPEN = prove
 (`!s (f:real^M->real^(N,P)finite_sum).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (fstcart o f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_FSTCART]);;

let SMOOTH_MAP_ON_SNDCART_OPEN = prove
 (`!s (f:real^M->real^(N,P)finite_sum).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (sndcart o f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_SNDCART]);;

let SMOOTH_MAP_ON_OPEN_UNIV = prove
 (`!f:real^M->real^N.
      smooth_map_on (:real^M) f <=>
      (!n. continuously_differentiable n (:real^M) f)`,
  REWRITE_TAC[smooth_map_on]);;

let CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN = prove
 (`!n s (f:real^M->real^1) (g:real^M->real^N).
      open s /\
      continuously_differentiable n s f /\ continuously_differentiable n s g
      ==> continuously_differentiable n s (\x. drop(f x) % g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
                  `\x:real^1 y:real^N. drop x % y`;
                  `f:real^M->real^1`; `g:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL]);;

let CONTINUOUSLY_DIFFERENTIABLE_DOT_OPEN = prove
 (`!n s (f:real^M->real^N) (g:real^M->real^N).
      open s /\
      continuously_differentiable n s f /\ continuously_differentiable n s g
      ==> continuously_differentiable n s (\x. lift(f x dot g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
                  `\x:real^N y:real^N. lift(x dot y)`;
                  `f:real^M->real^N`; `g:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT]);;

let CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN = prove
 (`!n s (f:real^M->real^1) (g:real^M->real^1).
      open s /\
      continuously_differentiable n s f /\ continuously_differentiable n s g
      ==> continuously_differentiable n s (\x. lift(drop(f x) * drop(g x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
                  `\x:real^1 y:real^1. lift(drop x * drop y)`;
                  `f:real^M->real^1`; `g:real^M->real^1`]
    CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_LIFT_MUL]);;

let CONTINUOUSLY_DIFFERENTIABLE_NORM_POW2_OPEN = prove
 (`!n s (f:real^M->real^N).
      open s /\ continuously_differentiable n s f
      ==> continuously_differentiable n s (\x. lift(norm(f x) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. lift(norm((f:real^M->real^N) x) pow 2)) =
                (\x. lift(f x dot f x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; NORM_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DOT_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_MUL_DROP_OPEN = prove
 (`!s (f:real^M->real^1) (g:real^M->real^N).
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. drop(f x) % g x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_DOT_OPEN = prove
 (`!s (f:real^M->real^N) (g:real^M->real^N).
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. lift(f x dot g x))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DOT_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_MUL_LIFT_OPEN = prove
 (`!s (f:real^M->real^1) (g:real^M->real^1).
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> smooth_map_on s (\x. lift(drop(f x) * drop(g x)))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_NORM_POW2_OPEN = prove
 (`!s (f:real^M->real^N).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. lift(norm(f x) pow 2))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_NORM_POW2_OPEN THEN
  ASM_REWRITE_TAC[]);;

let diffeomorphism_on = new_definition
 `diffeomorphism_on s t (f:real^M->real^N) (g:real^N->real^M) <=>
    open s /\ open t /\
    IMAGE f s = t /\ IMAGE g t = s /\
    (!x. x IN s ==> g(f x) = x) /\
    (!y. y IN t ==> f(g y) = y) /\
    smooth_map_on s f /\ smooth_map_on t g`;;

let DIFFEOMORPHISM_ON_ID = prove
 (`!s:real^N->bool.
      open s ==> diffeomorphism_on s s (\x. x) (\x. x)`,
  REWRITE_TAC[diffeomorphism_on; IMAGE_ID; SMOOTH_MAP_ON_ID]);;

let DIFFEOMORPHISM_ON_SYM = prove
 (`!s t (f:real^M->real^N) g.
      diffeomorphism_on s t f g ==> diffeomorphism_on t s g f`,
  REWRITE_TAC[diffeomorphism_on] THEN MESON_TAC[]);;

let DIFFEOMORPHISM_ON_COMPOSE = prove
 (`!s t u (f:real^M->real^N) g (h:real^N->real^P) k.
      diffeomorphism_on s t f g /\ diffeomorphism_on t u h k
      ==> diffeomorphism_on s u (h o f) (g o k)`,
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[IMAGE_o] THEN ASM_MESON_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[IN_IMAGE; EXTENSION];
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[IN_IMAGE; EXTENSION];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_REFL]]);;

let SMOOTH_MAP_ON_DIFFERENTIABLE = prove
 (`!s (f:real^M->real^N) x.
      open s /\ smooth_map_on s f /\ x IN s
      ==> f differentiable (at x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC 0`) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REWRITE_TAC[differentiable] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f':real^M->real^M->real^N) x` THEN
  ASM_SIMP_TAC[]);;

let SMOOTH_MAP_ON_HAS_DERIVATIVE = prove
 (`!s (f:real^M->real^N).
      open s /\ smooth_map_on s f
      ==> !x. x IN s
              ==> (f has_derivative frechet_derivative f (at x)) (at x)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC 0`) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REWRITE_TAC[differentiable] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f':real^M->real^M->real^N) x` THEN
  ASM_SIMP_TAC[]);;

let SMOOTH_MAP_ON_FRECHET_DERIVATIVE = prove
 (`!s (f:real^M->real^N) h.
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. frechet_derivative f (at x) h)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN s ==>
      (f':real^M->real^M->real^N) x = frechet_derivative (f:real^M->real^N) (at x)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[FRECHET_DERIVATIVE_AT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `\x:real^M. (f':real^M->real^M->real^N) x h` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let SMOOTH_MAP_ON_CONTINUOUS_ON = prove
 (`!s (f:real^M->real^N). smooth_map_on s f ==> f continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON) THEN
  REWRITE_TAC[]);;

let DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_AT = prove
 (`!(f:real^N->real^M) s (x:real^N). open s /\ f differentiable_on s /\ x IN s
           ==> f differentiable (at x)`,
  MESON_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT]);;

let CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_AT = prove
 (`!(f:real^N->real^M) s (x:real^N).
     open s /\ (!n. continuously_differentiable n s f) /\ x IN s
     ==> f differentiable (at x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON THEN
  EXISTS_TAC `0` THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC 0`) THEN
  REWRITE_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN = prove
 (`!n s (f:real^M->real^N). open s /\ linear f
    ==> continuously_differentiable n s f`,
  INDUCT_TAC THENL
   [SIMP_TAC[continuously_differentiable; LINEAR_CONTINUOUS_ON];
    REWRITE_TAC[continuously_differentiable] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\x:real^M. (f:real^M->real^N)):real^M->real^M->real^N` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; HAS_DERIVATIVE_WITHIN_OPEN];
      X_GEN_TAC `h:real^M` THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST]]]);;

let HAS_DERIVATIVE_LIFT_INV = prove
 (`!a:real^1. ~(drop a = &0)
    ==> ((lift o inv o drop) has_derivative
         (\h. --(inv(drop a pow 2)) % h)) (at a)`,
  X_GEN_TAC `a:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[has_derivative_at; LINEAR_SCALING] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[LIM_AT; DIST_0] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; DIST_1; NORM_1; DROP_SUB] THEN
  REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_ADD; GSYM LIFT_CMUL; GSYM LIFT_NEG;
              DROP_CMUL; NORM_1; LIFT_DROP; DROP_ADD; DROP_SUB] THEN
  SUBGOAL_THEN `!t r. &0 < abs t ==> abs(inv(abs t)) * abs r = inv(abs t) * abs r`
    (fun th -> SIMP_TAC[th]) THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_ABS]; ALL_TAC] THEN
  ABBREV_TAC `b = drop(a:real^1)` THEN
  EXISTS_TAC `min (abs b / &2) (e * abs b pow 3 / &2)` THEN
  SUBGOAL_THEN `&0 < abs b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs b pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(drop(x:real^1) = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = drop(x:real^1) - b` THEN
  SUBGOAL_THEN `drop(x:real^1) = b + h` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `inv(drop(x:real^1)) - (inv b + --inv(b pow 2) * h) =
     h pow 2 / (b pow 2 * drop x)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_FIELD
     `~(b = &0) /\ ~(b + h = &0)
      ==> inv(b + h) - (inv b + --inv(b pow 2) * h) =
          h pow 2 / (b pow 2 * (b + h))`) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_POW] THEN
  SUBGOAL_THEN `abs(drop(x:real^1)) > abs b / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs b pow 2 * abs(drop(x:real^1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(abs h) * abs h pow 2 / (abs b pow 2 * abs(drop(x:real^1))) =
                abs h / (abs b pow 2 * abs(drop x))` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
      `&0 < t /\ &0 < u ==> inv t * t pow 2 / u = t / u`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `e * abs b pow 3 / &2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e * abs b pow 3 / &2 = e * abs b pow 2 * (abs b / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2; ARITH_RULE `3 = SUC 2`; real_pow] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_MUL; REAL_POW_LT] THEN
  ASM_REAL_ARITH_TAC);;

let CONTINUOUSLY_DIFFERENTIABLE_LIFT_INV_OPEN = prove
 (`!n s (f:real^M->real^1).
    open s /\ (!x. x IN s ==> ~(drop(f x) = &0)) /\
    continuously_differentiable n s f
    ==> continuously_differentiable n s (\x. lift(inv(drop(f x))))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x:real^M. lift(inv(drop(f x:real^1)))) =
      (lift o inv o drop) o (f:real^M->real^1)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(lift o drop):real^1->real^1 = (\x. x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP];
        REWRITE_TAC[CONTINUOUS_ON_ID]];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `continuously_differentiable (SUC n) s (f:real^M->real^1)`) THEN
  ONCE_REWRITE_TAC[MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN
    (ASSUME `open(s:real^M->bool)`)] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^1` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\(x:real^M) (h:real^M). --inv(drop((f:real^M->real^1) x) pow 2) %
    (f':real^M->real^M->real^1) x h` THEN
  REWRITE_TAC[BETA_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x:real^M. lift(inv(drop((f:real^M->real^1) x)))) =
      (lift o inv o drop) o f` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^M. --inv(drop((f:real^M->real^1) x) pow 2) %
       (f':real^M->real^M->real^1) x h) =
      (\h. --inv(drop(f x) pow 2) % h) o f' x` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_LIFT_INV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  X_GEN_TAC `h:real^M` THEN
  SUBGOAL_THEN `(\x:real^M. --inv(drop((f:real^M->real^1) x) pow 2) %
    (f':real^M->real^M->real^1) x h) =
    (\x. drop(lift(--inv(drop(f x) pow 2))) % f' x h)`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `continuously_differentiable n s (f:real^M->real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUC_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^M. lift(--inv(drop((f:real^M->real^1) x) pow 2))) =
    (\x. --(lift(inv(drop(f x)) * inv(drop(f x)))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_NEG; LIFT_EQ] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_INV_POW; REAL_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:real^M. lift(inv(drop((f:real^M->real^1) x)) * inv(drop(f x)))) =
    (\x. lift(drop(lift(inv(drop(f x)))) * drop(lift(inv(drop(f x))))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^M->bool`; `f:real^M->real^1`]) THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_SUM_OPEN = prove
 (`!n s (f:A->real^M->real^N) k.
    open s /\ FINITE k /\
    (!i. i IN k ==> continuously_differentiable n s (f i))
    ==> continuously_differentiable n s (\x. vsum k (\i. f i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; VSUM_CLAUSES] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
  DISCH_TAC THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `(f:A->real^M->real^N) a`; `\x:real^M. vsum k (\i:A. (f:A->real^M->real^N) i x)`]
    CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN MATCH_MP_TAC THEN DISJ1_TAC THEN REFL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_INSERT]]);;

let CONTINUOUSLY_DIFFERENTIABLE_PRODUCT_OPEN = prove
 (`!n s (f:A->real^M->real^1) k.
    open s /\ FINITE k /\
    (!i. i IN k ==> continuously_differentiable n s (f i))
    ==> continuously_differentiable n s
        (\x. lift(product k (\i. drop(f i x))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
  DISCH_TAC THEN ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN
    `(\x:real^M. lift(drop((f:A->real^M->real^1) a x) *
        product k (\i. drop(f i x)))) =
     (\x. lift(drop(f a x) * drop(lift(product k (\i. drop(f i x))))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `(f:A->real^M->real^1) a`;
    `\x:real^M. lift(product k (\i:A. drop((f:A->real^M->real^1) i x)))`]
    CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN MATCH_MP_TAC THEN DISJ1_TAC THEN REFL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_INSERT]]);;

let CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN = prove
 (`!n s (A:real^M->real^N^N).
    open s /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> continuously_differentiable n s (\x. lift((A x)$i$j)))
    ==> continuously_differentiable n s (\x. lift(det(A x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x:real^M. lift(det((A:real^M->real^N^N) x))) =
     (\x. vsum {p | p permutes 1..dimindex(:N)}
               (\p. lift(sign p * product (1..dimindex(:N)) (\i. A x$i$p i))))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; det; LIFT_SUM; o_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`n:num`; `s:real^M->bool`;
     `\p (x:real^M). lift(sign p * product (1..dimindex(:N))
        (\i. (A:real^M->real^N^N) x$i$p i))`;
     `{p:num->num | p permutes 1..dimindex(:N)}`]
    CONTINUOUSLY_DIFFERENTIABLE_SUM_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PERMUTATIONS THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `(\x:real^M. lift(sign p * product (1..dimindex(:N))
        (\i. (A:real^M->real^N^N) x$i$(p:num->num) i))) =
     (\x. lift(drop(lift(sign p)) *
           drop(lift(product (1..dimindex(:N)) (\i. A x$i$p i)))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `\x:real^M. lift(sign(p:num->num))`;
    `\x:real^M. lift(product (1..dimindex(:N))
      (\i. (A:real^M->real^N^N) x$i$p i))`]
    CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real^M. lift(product (1..dimindex(:N))
        (\i. (A:real^M->real^N^N) x$i$(p:num->num) i))) =
     (\x. lift(product (1..dimindex(:N))
        (\i. drop((\x. lift(A x$i$p i)) x))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `\i (x:real^M). lift((A:real^M->real^N^N) x$i$(p:num->num) i)`;
    `1..dimindex(:N)`]
    CONTINUOUSLY_DIFFERENTIABLE_PRODUCT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`p:num->num`; `dimindex(:N)`; `i:num`] PERMUTES_IN_NUMSEG) THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

let CONTINUOUSLY_DIFFERENTIABLE_COFACTOR_ENTRY_OPEN = prove
 (`!n s (A:real^M->real^N^N) i j.
    open s /\
    1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> continuously_differentiable n s (\x. lift((A x)$i$j)))
    ==> continuously_differentiable n s (\x. lift(cofactor(A x)$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cofactor] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  ASM_CASES_TAC `i':num = i /\ j':num = j` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i':num = i \/ j':num = j` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CONTINUOUSLY_DIFFERENTIABLE_MATRIX_INV_ENTRY_OPEN = prove
 (`!n s (A:real^M->real^N^N) i j.
    open s /\
    1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
    (!x. x IN s ==> ~(det(A x) = &0)) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> continuously_differentiable n s (\x. lift((A x)$i$j)))
    ==> continuously_differentiable n s (\x. lift(matrix_inv(A x)$i$j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `\x:real^M. lift(inv(det((A:real^M->real^N^N) x)) * cofactor(A x)$j$i)`;
    `\x:real^M. lift(matrix_inv((A:real^M->real^N^N) x)$i$j)`]
    CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[MATRIX_INV_COFACTOR; MATRIX_CMUL_COMPONENT;
                 TRANSP_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real^M. lift(inv(det((A:real^M->real^N^N) x)) * cofactor(A x)$j$i)) =
     (\x. lift(drop(lift(inv(det(A x)))) * drop(lift(cofactor(A x)$j$i))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`;
    `\x:real^M. lift(inv(det((A:real^M->real^N^N) x)))`;
    `\x:real^M. lift(cofactor((A:real^M->real^N^N) x)$j$i)`]
    CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
      `(\x:real^M. lift(inv(det((A:real^M->real^N^N) x)))) =
       (\x. lift(inv(drop(lift(det(A x))))))`
      SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LIFT_INV_OPEN THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COFACTOR_ENTRY_OPEN THEN
    ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_FRECHET_ENTRY_COMPOSE = prove
 (`!n s t u (f:real^N->real^N) (g:real^N->real^N) i j.
    open s /\ open u /\ open t /\ t SUBSET s /\
    IMAGE g u SUBSET t /\
    smooth_map_on s f /\
    continuously_differentiable n u g /\
    1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
    ==> continuously_differentiable n u
        (\y. lift(frechet_derivative f (at (g y)) (basis j)$i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `continuously_differentiable n u
      (\y:real^N. frechet_derivative (f:real^N->real^N) (at ((g:real^N->real^N) y)) (basis j))`
    ASSUME_TAC THENL
   [SUBGOAL_THEN
      `(\y:real^N. frechet_derivative (f:real^N->real^N) (at (g y)) (basis j)) =
       (\x. frechet_derivative f (at x) (basis j)) o (g:real^N->real^N)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^N`; `basis j:real^N`]
      SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[smooth_map_on] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\y:real^N. lift(frechet_derivative (f:real^N->real^N)
        (at ((g:real^N->real^N) y)) (basis j)$i)) =
     ((\v:real^N. lift(v$i)) o (\y. frechet_derivative f (at (g y)) (basis j)))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; LIFT_ADD; VECTOR_MUL_COMPONENT; LIFT_CMUL]);;

let SMOOTH_INVERSE_FUNCTION_THEOREM = prove
 (`!(f:real^N->real^N) s a.
      open s /\ a IN s /\ smooth_map_on s f /\
      ~(det(matrix(frechet_derivative f (at a))) = &0)
      ==> ?t u g. open t /\ a IN t /\ t SUBSET s /\
                  open u /\ f a IN u /\ diffeomorphism_on t u f g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(!x:real^N. x IN s ==> (f has_derivative frechet_derivative f (at x)) (at x)) /\
     (!h:real^N. (\x. frechet_derivative (f:real^N->real^N) (at x) h) continuous at a)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
      GEN_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^N`; `h:real^N`]
        SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`;
    `\x:real^N. frechet_derivative (f:real^N->real^N) (at x)`;
    `s:real^N->bool`; `a:real^N`] INVERSE_FUNCTION_THEOREM_C1_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `g:real^N->real^N` (X_CHOOSE_THEN `g':real^N->real^N->real^N`
    STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `u:real^N->bool`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) t = u /\ IMAGE g u = t`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[smooth_map_on] THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `g':real^N->real^N->real^N` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `h:real^N` THEN
  SUBGOAL_THEN `!y:real^N. y IN u ==>
    ~(det(matrix(frechet_derivative (f:real^N->real^N) (at (g y)))) = &0)`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM INVERTIBLE_DET_NZ; INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `matrix((g':real^N->real^N->real^N) y)` THEN
    SUBGOAL_THEN `linear(g' (y:real^N) :real^N->real^N) /\
      linear(frechet_derivative (f:real^N->real^N) (at (g y)))`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_DERIVATIVE_LINEAR; has_derivative];
        SUBGOAL_THEN `(g:real^N->real^N) y IN t` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[HAS_DERIVATIVE_LINEAR; has_derivative]]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN `(g':real^N->real^N->real^N) y o
      frechet_derivative (f:real^N->real^N) (at (g y)) = I` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_I]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN u ==>
    g' y (h:real^N) =
      matrix_inv(matrix(frechet_derivative (f:real^N->real^N) (at (g y)))) ** h`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `linear(g' (y:real^N) :real^N->real^N) /\
      linear(frechet_derivative (f:real^N->real^N) (at (g y)))`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_DERIVATIVE_LINEAR; has_derivative];
        SUBGOAL_THEN `(g:real^N->real^N) y IN t` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[HAS_DERIVATIVE_LINEAR; has_derivative]]; ALL_TAC] THEN
    SUBGOAL_THEN
      `matrix_inv(matrix(frechet_derivative (f:real^N->real^N) (at (g y)))) =
       matrix((g':real^N->real^N->real^N) y)` SUBST1_TAC THENL
     [MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
      ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
      SUBGOAL_THEN `frechet_derivative (f:real^N->real^N) (at (g y)) o
        (g':real^N->real^N->real^N) y = I` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MATRIX_I]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `\y:real^N.
    matrix_inv(matrix(frechet_derivative (f:real^N->real^N) (at (g y)))) **
    (h:real^N)` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
    `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
    ==> continuously_differentiable n u
        (\y:real^N. lift(matrix_inv(matrix(frechet_derivative (f:real^N->real^N)
          (at (g y))))$i$j))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `u:real^N->bool`;
      `\y:real^N. matrix(frechet_derivative (f:real^N->real^N)
        (at (g y))) :real^N^N`;
      `i:num`; `j:num`] CONTINUOUSLY_DIFFERENTIABLE_MATRIX_INV_ENTRY_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `!y:real^N. matrix(frechet_derivative (f:real^N->real^N)
        (at (g y)))$i'$j' = frechet_derivative f (at (g y)) (basis j')$i'`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN ASM_SIMP_TAC[matrix; LAMBDA_BETA]; ALL_TAC] THEN
    MP_TAC(ISPECL [`n:num`; `s:real^N->bool`; `t:real^N->bool`;
      `u:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`;
      `i':num`; `j':num`]
      CONTINUOUSLY_DIFFERENTIABLE_FRECHET_ENTRY_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\y:real^N.
       matrix_inv(matrix(frechet_derivative (f:real^N->real^N)
         (at (g y)))) ** (h:real^N)) =
     (\y. vsum (1..dimindex(:N))
       (\j. h$j % vsum (1..dimindex(:N))
         (\i. drop(lift(matrix_inv(matrix(frechet_derivative f
           (at (g y))))$i$j)) % (basis i :real^N))))`
    SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_DROP; FUN_EQ_THM; MATRIX_VECTOR_COLUMN] THEN
    GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `j':num` THEN STRIP_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `i':num` THEN STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[transp; LAMBDA_BETA]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j':num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i':num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN = prove
 (`!n s (f:real^M->real^N). open s ==>
    (continuously_differentiable n s f <=>
     !x. x IN s ==> ?t. open t /\ x IN t /\ t SUBSET s /\
         continuously_differentiable n t f)`,
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
      EXISTS_TAC `t:real^M->bool` THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_OPEN]];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      DISCH_TAC THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
      EXISTS_TAC `\x. frechet_derivative (f:real^M->real^N) (at x)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(f:real^M->real^N) differentiable (at x)` MP_TAC THENL
         [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON;
                        DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_AT];
          REWRITE_TAC[FRECHET_DERIVATIVE_WORKS]];
        REPEAT GEN_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `?f'. (!y. y IN t ==> ((f:real^M->real^N) has_derivative f' y)
                (at y)) /\
               (!h:real^M. continuously_differentiable n t (\y. f' y h))`
        MP_TAC THENL
         [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN]; ALL_TAC] THEN
        STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
        EXISTS_TAC `\y:real^M. (f':real^M->real^M->real^N) y h` THEN
        ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN AP_THM_TAC THEN
        MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_MESON_TAC[]]]]);;


(* ========================================================================= *)
(* Smooth calculus on real^N, part 1: partial derivatives along the basis    *)
(* directions and their iterates along lists of indices (innermost last).   *)
(* ========================================================================= *)

let partial_derivative = new_definition
 `partial_derivative (i:num) (f:real^M->real^N) (x:real^M) =
    frechet_derivative f (at x) (basis i)`;;

let iterated_partial = define
 `(!f:real^M->real^N. iterated_partial [] f = f) /\
  (!i l (f:real^M->real^N).
      iterated_partial (CONS i l) f = partial_derivative i (iterated_partial l f))`;;

let PARTIAL_DERIVATIVE_ALT = prove
 (`!i (f:real^M->real^N).
      partial_derivative i f = \x. frechet_derivative f (at x) (basis i)`,
  REWRITE_TAC[FUN_EQ_THM; partial_derivative]);;

let SMOOTH_MAP_ON_PARTIAL_DERIVATIVE = prove
 (`!s (f:real^M->real^N) i.
      open s /\ smooth_map_on s f ==> smooth_map_on s (partial_derivative i f)`,
  SIMP_TAC[PARTIAL_DERIVATIVE_ALT; SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let SMOOTH_MAP_ON_ITERATED_PARTIAL = prove
 (`!l s (f:real^M->real^N).
      open s /\ smooth_map_on s f ==> smooth_map_on s (iterated_partial l f)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[iterated_partial; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let ITERATED_PARTIAL_APPEND = prove
 (`!l m (f:real^M->real^N).
      iterated_partial (APPEND l m) f = iterated_partial l (iterated_partial m f)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; iterated_partial]);;

(* Partial derivatives only depend on the function near the point.          *)
let FRECHET_DERIVATIVE_LOCAL = prove
 (`!(f:real^M->real^N) g x d.
      &0 < d /\ (!y. dist(y,x) < d ==> f y = g y)
      ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[DIST_SYM]);;

let PARTIAL_DERIVATIVE_LOCAL = prove
 (`!i (f:real^M->real^N) g x d.
      &0 < d /\ (!y. dist(y,x) < d ==> f y = g y)
      ==> partial_derivative i f x = partial_derivative i g x`,
  REWRITE_TAC[partial_derivative] THEN MESON_TAC[FRECHET_DERIVATIVE_LOCAL]);;

let PARTIAL_DERIVATIVE_LOCAL_OPEN = prove
 (`!i (f:real^M->real^N) g s x.
      open s /\ x IN s /\ (!y. y IN s ==> f y = g y)
      ==> partial_derivative i f x = partial_derivative i g x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[DIST_SYM]);;

let PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE = prove
 (`!i (f:real^M->real^N) f' x.
      (f has_derivative f') (at x) ==> partial_derivative i f x = f'(basis i)`,
  SIMP_TAC[partial_derivative; HAS_FRECHET_DERIVATIVE_UNIQUE_AT]);;

let PARTIAL_DERIVATIVE_CONST = prove
 (`!i (c:real^N) (x:real^M). partial_derivative i (\x. c) x = vec 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:real^N`; `at (x:real^M)`] HAS_DERIVATIVE_CONST) THEN
  DISCH_THEN(MP_TAC o MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  SIMP_TAC[]);;

let PARTIAL_DERIVATIVE_LINEAR = prove
 (`!i (f:real^M->real^N) x. linear f ==> partial_derivative i f x = f(basis i)`,
  MESON_TAC[PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE; HAS_DERIVATIVE_LINEAR]);;

let PARTIAL_DERIVATIVE_ID = prove
 (`!i (x:real^M). partial_derivative i (\x. x) x = basis i`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`i:num`; `\x:real^M. x`; `x:real^M`] PARTIAL_DERIVATIVE_LINEAR) THEN
  REWRITE_TAC[LINEAR_ID]);;

let PARTIAL_DERIVATIVE_ADD = prove
 (`!i (f:real^M->real^N) g x.
      f differentiable (at x) /\ g differentiable (at x)
      ==> partial_derivative i (\x. f x + g x) x =
          partial_derivative i f x + partial_derivative i g x`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_ADD o CONJ (ASSUME
   `((f:real^M->real^N) has_derivative frechet_derivative f (at x)) (at x)`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th]));;

let PARTIAL_DERIVATIVE_SUB = prove
 (`!i (f:real^M->real^N) g x.
      f differentiable (at x) /\ g differentiable (at x)
      ==> partial_derivative i (\x. f x - g x) x =
          partial_derivative i f x - partial_derivative i g x`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_SUB o CONJ (ASSUME
   `((f:real^M->real^N) has_derivative frechet_derivative f (at x)) (at x)`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th]));;

let PARTIAL_DERIVATIVE_NEG = prove
 (`!i (f:real^M->real^N) x.
      f differentiable (at x)
      ==> partial_derivative i (\x. --(f x)) x = --(partial_derivative i f x)`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_NEG) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th]));;

let PARTIAL_DERIVATIVE_CMUL = prove
 (`!i c (f:real^M->real^N) x.
      f differentiable (at x)
      ==> partial_derivative i (\x. c % f x) x = c % partial_derivative i f x`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th]));;

let PARTIAL_DERIVATIVE_VSUM = prove
 (`!i (f:A->real^M->real^N) k x.
      FINITE k /\ (!a. a IN k ==> f a differentiable (at x))
      ==> partial_derivative i (\x. vsum k (\a. f a x)) x =
          vsum k (\a. partial_derivative i (f a) x)`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. vsum k (\a. (f:A->real^M->real^N) a x)) has_derivative
     (\h. vsum k (\a. frechet_derivative (f a) (at x) h))) (at x)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th])]);;

let PARTIAL_DERIVATIVE_MUL = prove
 (`!i (a:real^M->real^1) (g:real^M->real^N) x.
      a differentiable (at x) /\ g differentiable (at x)
      ==> partial_derivative i (\x. drop(a x) % g x) x =
          drop(a x) % partial_derivative i g x +
          drop(partial_derivative i a x) % g x`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`drop o (a:real^M->real^1)`;
                 `drop o frechet_derivative (a:real^M->real^1) (at x)`;
                 `g:real^M->real^N`; `frechet_derivative (g:real^M->real^N) (at x)`;
                 `x:real^M`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th]));;

let PARTIAL_DERIVATIVE_CHAIN = prove
 (`!i (f:real^M->real^N) (g:real^N->real^P) x.
      f differentiable (at x) /\ g differentiable (at (f x))
      ==> partial_derivative i (g o f) x =
          frechet_derivative g (at (f x)) (partial_derivative i f x)`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^P`;
                 `frechet_derivative (f:real^M->real^N) (at x)`;
                 `frechet_derivative (g:real^N->real^P) (at (f(x:real^M)))`;
                 `x:real^M`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT th; o_THM]));;

let PARTIAL_DERIVATIVE_COMPONENT = prove
 (`!i k (f:real^M->real^N) x.
      f differentiable (at x)
      ==> partial_derivative i (\x. lift(f x$k)) x = lift(partial_derivative i f x$k)`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\x. lift((f:real^M->real^N) x$k)) has_derivative
                 (\h. lift(frechet_derivative f (at x) h$k))) (at x)` MP_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `\y:real^N. lift(y$k)`;
                   `frechet_derivative (f:real^M->real^N) (at x)`;
                   `\y:real^N. lift(y$k)`; `x:real^M`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_LIFT_COMPONENT; o_DEF];
    DISCH_THEN(MP_TAC o SPEC `i:num` o MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[partial_derivative]]);;

let PARTIAL_DERIVATIVE_SYM = prove
 (`!s (f:real^M->real^N) x i j.
      open s /\ x IN s /\
      1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:M) /\
      continuously_differentiable 2 s f
      ==> partial_derivative i (partial_derivative j f) x =
          partial_derivative j (partial_derivative i f) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHWARZ_C2 THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[IN_NUMSEG]);;

(* ========================================================================= *)
(* Smooth calculus on real^N, part 2: a criterion for smoothness of real     *)
(* functions of one variable through a sequence of successive derivatives.  *)
(* ========================================================================= *)

let SMOOTH_MAP_ON_REAL_SEQUENCE = prove
 (`!s (phi:num->real->real).
      real_open s /\
      (!n x. x IN s ==> (phi n has_real_derivative phi (SUC n) x) (atreal x))
      ==> !n. smooth_map_on (IMAGE lift s) (lift o phi n o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[differentiable_on; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
    REWRITE_TAC[GSYM REAL_DIFFERENTIABLE_AT; real_differentiable] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    EXISTS_TAC `\(x:real^1) (h:real^1). drop h % lift(phi (SUC n) (drop x))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real`]) THEN
      ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `h:real^1` THEN BETA_TAC THEN
      SUBGOAL_THEN `(\x:real^1. drop h % lift(phi (SUC n) (drop x))) =
                    (\x. drop h % (lift o phi (SUC n) o drop) x)` SUBST1_TAC THENL
       [REWRITE_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
      ASM_REWRITE_TAC[ETA_AX; GSYM REAL_OPEN]]]);;

let SMOOTH_MAP_ON_EXP_1D = prove
 (`smooth_map_on (:real^1) (lift o exp o drop)`,
  MP_TAC(ISPECL [`(:real)`; `\n:num. exp`] SMOOTH_MAP_ON_REAL_SEQUENCE) THEN
  REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; HAS_REAL_DERIVATIVE_EXP; IMAGE_LIFT_UNIV] THEN
  MESON_TAC[]);;

