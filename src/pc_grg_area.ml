(* ========================================================================= *)
(* Unit pc_grg_area (Riemannian geometry layer): the area formula for        *)
(* continuous maps from Lebesgue measurable subsets of real^N into a         *)
(* Riemannian manifold that are differentiable in charts (MFD_AREA_FORMULA), *)
(* and the volume comparison under a comparison of quadratic forms           *)
(* (MFD_HAS_VOLUME_COMPARE_QF).                                              *)
(* ========================================================================= *)

needs "src/pc_grg_vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The weighted area inequality in real^N.  For f differentiable within      *)
(* a Lebesgue measurable set s and a weight h >= 0 continuous on the image,  *)
(* the integral of h over IMAGE f s is at most the integral over s of        *)
(* |det f'| times h o f.  HOL has the unweighted case                        *)
(* (MEASURE_DIFFERENTIABLE_IMAGE); the weighted case follows on the pieces   *)
(* of s where h o f lies in (l, r l], for geometric levels l, by countable   *)
(* additivity, and then letting r tend to 1.                                 *)
(* ------------------------------------------------------------------------- *)

let GRGA_LE_LIMIT = prove
 (`!x y. &0 <= y /\ (!r. &1 < r ==> x <= r * y) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `y = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&2`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x + y) / (&2 * y)`) THEN
  SUBGOAL_THEN `(x + y) / (&2 * y) * y = (x + y) / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let GRGA_DIV2 = prove
 (`!m. (2 * m) DIV 2 = m /\ (2 * m + 1) DIV 2 = m`,
  GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
   [EXISTS_TAC `0`; EXISTS_TAC `1`] THEN ARITH_TAC);;

let GRGA_LEVELS = prove
 (`!r. &1 < r
       ==> ?l:num->real.
             (!j. &0 < l j) /\
             (!a. &0 < a ==> ?j. l j < a /\ a <= r * l j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `\j. if EVEN j then r pow (j DIV 2) else inv(r pow (j DIV 2 + 1))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV];
    ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `&1 < a` THENL
   [SUBGOAL_THEN `?n. a <= r pow n` MP_TAC THENL
     [MP_TAC(SPECL [`r:real`; `a:real`] REAL_ARCH_POW) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `a <= r pow n` THEN ASM_REWRITE_TAC[real_pow] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
      MATCH_MP (MESON[num_CASES] `~(n = 0) ==> ?m. n = SUC m`)) THEN
    EXISTS_TAC `2 * m` THEN REWRITE_TAC[EVEN_DOUBLE; GRGA_DIV2] THEN
    UNDISCH_TAC `a <= r pow SUC m` THEN REWRITE_TAC[real_pow] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= inv a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?n. inv a < r pow n` MP_TAC THENL
   [MATCH_MP_TAC REAL_ARCH_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `inv a < r pow n` THEN ASM_REWRITE_TAC[real_pow] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    MATCH_MP (MESON[num_CASES] `~(n = 0) ==> ?m. n = SUC m`)) THEN
  EXISTS_TAC `2 * m + 1` THEN
  REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; GRGA_DIV2; ARITH] THEN
  REWRITE_TAC[GSYM ADD1; real_pow] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LT; REAL_NOT_LT] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `inv a < r pow SUC m` THEN REWRITE_TAC[real_pow] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r pow m` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`inv a`; `r * r pow m`] REAL_LT_INV2) THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV];
    SUBGOAL_THEN `r * inv(r * r pow m) = inv(r pow m)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < r pow m` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r pow m`; `inv a`] REAL_LE_INV2) THEN
    ASM_SIMP_TAC[REAL_INV_INV]]);;

let GRGA_FIRST_UNIQUE = prove
 (`!(C:num->bool) i j.
        (C i /\ !k. k < i ==> ~C k) /\ (C j /\ !k. k < j ==> ~C k) ==> i = j`,
  MESON_TAC[LT_CASES]);;

let GRGA_LEVEL_SET_MEASURABLE = prove
 (`!(k:real^N->real) s a b.
        (\x. lift(k x)) continuous_on s /\ lebesgue_measurable s
        ==> lebesgue_measurable {x | x IN s /\ a < k x /\ k x <= b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c. lebesgue_measurable {x | x IN s /\ c < (k:real^N->real) x}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN_IN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. lift((k:real^N->real) x)`; `s:real^N->bool`;
                   `{y:real^1 | y$1 > c}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
    REWRITE_TAC[IN_ELIM_THM; LIFT_COMPONENT; real_gt];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN s /\ a < (k:real^N->real) x /\ k x <= b} =
    {x | x IN s /\ a < k x} DIFF {x | x IN s /\ b < k x}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[REAL_NOT_LT];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[]]);;

let GRGA_PIECE_BOUND = prove
 (`!f:real^N->real^N f' s h Q l r.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (\y. lift(h y)) continuous_on IMAGE f s /\
        (\x. lift(abs(det(matrix(f' x))) * h(f x))) absolutely_integrable_on s /\
        Q SUBSET s /\ lebesgue_measurable Q /\ &0 < l /\ &0 <= r /\
        (!x. x IN Q ==> l < h(f x) /\ h(f x) <= r * l)
        ==> lebesgue_measurable (IMAGE f Q) /\
            (\y. lift(h y)) absolutely_integrable_on IMAGE f Q /\
            drop(integral (IMAGE f Q) (\y. lift(h y))) <=
            r * drop(integral Q (\x. lift(abs(det(matrix(f' x))) * h(f x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN Q ==> ((f:real^N->real^N) has_derivative f' x) (at x within Q)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))) *
              h((f:real^N->real^N) x))) absolutely_integrable_on Q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))))) measurable_on Q`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `Q:real^N->bool`]
                  MEASURABLE_ON_DET_JACOBIAN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NORM) THEN
    REWRITE_TAC[NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Q
        ==> l * abs(det(matrix((f':real^N->real^N->real^N) x))) <=
            abs(det(matrix(f' x))) * h((f:real^N->real^N) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))))) integrable_on Q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     `\x. inv l % lift(abs(det(matrix((f':real^N->real^N->real^N) x))) *
                       h((f:real^N->real^N) x))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP; REAL_ABS_ABS] THEN
      SUBGOAL_THEN
       `inv l * (abs(det(matrix((f':real^N->real^N->real^N) x))) *
                 h((f:real^N->real^N) x)) =
        (abs(det(matrix(f' x))) * h(f x)) / l`
      SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `Q:real^N->bool`]
                MEASURABLE_DIFFERENTIABLE_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `Q:real^N->bool`;
                 `drop(integral Q (\x. lift(abs(det(matrix
                    ((f':real^N->real^N->real^N) x))))))`]
                MEASURE_DIFFERENTIABLE_IMAGE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN IMAGE (f:real^N->real^N) Q ==> l < h y /\ h y <= r * l`
  ASSUME_TAC THENL [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(h y)) absolutely_integrable_on IMAGE (f:real^N->real^N) Q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\y:real^N. lift(r * l)` THEN
    ASM_REWRITE_TAC[INTEGRABLE_ON_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (f:real^N->real^N) s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  SUBGOAL_THEN
   `drop(integral (IMAGE (f:real^N->real^N) Q) (\y. lift(h y))) <=
    measure(IMAGE f Q) * (r * l)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:real^N->real^N) Q`; `lift(r * l)`] INTEGRAL_CONST_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS
     `drop(integral (IMAGE (f:real^N->real^N) Q) (\y. lift(r * l)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; INTEGRABLE_ON_CONST;
                   LIFT_DROP];
      ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `l * drop(integral Q (\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x)))))) <=
    drop(integral Q (\x. lift(abs(det(matrix(f' x))) * h((f:real^N->real^N) x))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `measure(IMAGE (f:real^N->real^N) Q) * (r * l)` THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `drop(integral Q (\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x)))))) *
    (r * l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC(REAL_ARITH `r * (l * x) <= r * y ==> x * (r * l) <= r * y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let GRGA_PIECES_LE = prove
 (`!f:real^N->real^N f' s h (Q:num->real^N->bool) (l:num->real) r.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (\y. lift(h y)) continuous_on IMAGE f s /\
        (!y. y IN IMAGE f s ==> &0 <= h y) /\
        (\x. lift(abs(det(matrix(f' x))) * h(f x))) absolutely_integrable_on s /\
        &0 <= r /\
        (!j. Q j SUBSET s /\ lebesgue_measurable (Q j) /\ &0 < l j /\
             !x. x IN Q j ==> l j < h(f x) /\ h(f x) <= r * l j) /\
        (!i j. ~(i = j) ==> DISJOINT (IMAGE f (Q i)) (IMAGE f (Q j)))
        ==> (\y. lift(h y)) absolutely_integrable_on
            UNIONS {IMAGE f (Q j) | j IN (:num)} /\
            drop(integral (UNIONS {IMAGE f (Q j) | j IN (:num)}) (\y. lift(h y))) <=
            r * drop(integral s (\x. lift(abs(det(matrix(f' x))) * h(f x))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "Q") (LABEL_TAC "DJ")))))))) THEN
  SUBGOAL_THEN
   `!j. lebesgue_measurable (IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j)) /\
        (\y. lift(h y)) absolutely_integrable_on IMAGE f (Q j) /\
        drop(integral (IMAGE f (Q j)) (\y. lift(h y))) <=
        r * drop(integral (Q j) (\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))) *
            h((f:real^N->real^N) x))))`
  (LABEL_TAC "PB") THENL
   [X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC GRGA_PIECE_BOUND THEN EXISTS_TAC `s:real^N->bool` THEN
    EXISTS_TAC `(l:num->real) j` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Q" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. ~(i = j) ==> DISJOINT ((Q:num->real^N->bool) i) (Q j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "DJ" (MP_TAC o C MATCH_MP (ASSUME `~(i:num = j)`)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))) * h((f:real^N->real^N) x)))
       absolutely_integrable_on UNIONS {(Q:num->real^N->bool) j | j IN (:num)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\x. lift(abs(det(matrix((f':real^N->real^N->real^N) x))) *
      h((f:real^N->real^N) x)))`; `Q:num->real^N->bool`] GRGV_SUMS_PIECES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SB") (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `!j. &0 <= drop(integral (IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j))
                            (\y. lift(h y)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
     [USE_THEN "PB" (MP_TAC o SPEC `j:num`) THEN
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "Q" (MP_TAC o SPEC `j:num`) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. drop(integral (IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j))
                      (\y. lift(norm(lift(h y))))) =
        drop(integral (IMAGE f (Q j)) (\y. lift(h y)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    REWRITE_TAC[FORALL_IN_IMAGE; NORM_LIFT] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
    USE_THEN "Q" (MP_TAC o SPEC `j:num`) THEN
    DISCH_THEN(fun th ->
      MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 th))) THEN
      MP_TAC(MATCH_MP (CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))
                      (ASSUME `(x:real^N) IN (Q:num->real^N->bool) j`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^N. lift(h y)`;
                 `\j. IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j)`]
                GRGV_ABS_INTEGRABLE_UNIONS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
      EXISTS_TAC `\j. r * drop(integral ((Q:num->real^N->bool) j) (\x.
          lift(abs(det(matrix((f':real^N->real^N->real^N) x))) * h((f:real^N->real^N)
          x))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_summable] THEN
        EXISTS_TAC `r * drop(integral (UNIONS {(Q:num->real^N->bool) j | j IN (:num)})
                                      (\x. lift(abs(det(matrix((f':real^N->real^N->real^N)
                                          x))) * h((f:real^N->real^N) x))))` THEN
        MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `r * drop(integral (UNIONS {(Q:num->real^N->bool) j | j IN (:num)}) (\x.
       lift(abs(det(matrix((f':real^N->real^N->real^N) x))) * h((f:real^N->real^N) x))))`
       THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\j. drop(integral (IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j))
                         (\y. lift(h y)))`;
      `\j. r * drop(integral ((Q:num->real^N->bool) j) (\x.
          lift(abs(det(matrix((f':real^N->real^N->real^N) x))) * h((f:real^N->real^N)
          x))))`;
      `from 0`] THEN
    ASM_SIMP_TAC[REAL_SERIES_LMUL] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]]);;

let GRGA_WEIGHTED_AREA_LE_R = prove
 (`!f:real^N->real^N f' s h r.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (\y. lift(h y)) continuous_on IMAGE f s /\
        (!y. y IN IMAGE f s ==> &0 <= h y) /\
        (\x. lift(abs(det(matrix(f' x))) * h(f x))) absolutely_integrable_on s /\
        &1 < r
        ==> (\y. lift(h y)) absolutely_integrable_on IMAGE f s /\
            drop(integral (IMAGE f s) (\y. lift(h y))) <=
            r * drop(integral s (\x. lift(abs(det(matrix(f' x))) * h(f x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num->real` STRIP_ASSUME_TAC o MATCH_MP GRGA_LEVELS) THEN
  SUBGOAL_THEN `(\x. lift(h((f:real^N->real^N) x))) continuous_on s` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift(h((f:real^N->real^N) x))) = (\y. lift(h y)) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
    REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `C = \j t. (l:num->real) j < t /\ t <= r * l j /\
              !i. i < j ==> ~(l i < t /\ t <= r * l i)` THEN
  ABBREV_TAC
   `Q = \j. {x | x IN s /\ (C:num->real->bool) j (h((f:real^N->real^N) x))}` THEN
  SUBGOAL_THEN
   `!j. IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j) =
        {y | y IN IMAGE f s /\ (C:num->real->bool) j (h y)}`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (Q:num->real^N->bool) j SUBSET s /\ lebesgue_measurable (Q j) /\
        &0 < (l:num->real) j /\
        !x. x IN Q j ==> l j < h((f:real^N->real^N) x) /\ h(f x) <= r * l j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN SET_TAC[];
      SUBGOAL_THEN
       `(Q:num->real^N->bool) j =
        {x | x IN s /\ (l:num->real) j < h((f:real^N->real^N) x) /\ h(f x) <= r * l j}
        DIFF
        UNIONS (IMAGE (\i. {x | x IN s /\ l i < h(f x) /\ h(f x) <= r * l i})
                      {i | i < j})`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Q"; "C"] THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGA_LEVEL_SET_MEASURABLE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
        SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGA_LEVEL_SET_MEASURABLE THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["Q"; "C"] THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. ~(i = j)
          ==> DISJOINT (IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) i))
                       (IMAGE f (Q j))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGA_FIRST_UNIQUE THEN
    EXISTS_TAC `\k. (C:num->real->bool) k (h(y:real^N))` THEN
    REWRITE_TAC[] THEN UNDISCH_TAC `(C:num->real->bool) i (h(y:real^N))` THEN
    UNDISCH_TAC `(C:num->real->bool) j (h(y:real^N))` THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `s:real^N->bool`;
                 `h:real^N->real`; `Q:num->real^N->bool`; `l:num->real`; `r:real`]
                GRGA_PIECES_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {IMAGE (f:real^N->real^N) ((Q:num->real^N->bool) j) | j IN (:num)} =
    {y | y IN IMAGE f s /\ &0 < h y}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) MP_TAC) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
      MP_TAC(SPEC `j:num` (ASSUME `!j. &0 < (l:num->real) j`)) THEN
      MESON_TAC[REAL_LT_TRANS];
      STRIP_TAC THEN
      SUBGOAL_THEN `?j. (C:num->real->bool) j (h(y:real^N))` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `h(y:real^N):real`) THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `j:num` THEN EXPAND_TAC "C" THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
      EXISTS_TAC `{y | y IN IMAGE (f:real^N->real^N) s /\
                       (C:num->real->bool) j (h y)}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. if y IN IMAGE (f:real^N->real^N) s then lift(h y) else vec 0) =
    (\y. if y IN {y | y IN IMAGE f s /\ &0 < h y} then lift(h y) else vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    ASM_CASES_TAC `(y:real^N) IN IMAGE (f:real^N->real^N) s` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `h(y:real^N) = &0` (fun th -> REWRITE_TAC[th; LIFT_NUM]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (IMAGE (f:real^N->real^N) s) (\y. lift(h y)) =
    integral {y | y IN IMAGE f s /\ &0 < h y} (\y. lift(h y))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let GRGA_WEIGHTED_AREA_LE = prove
 (`!f:real^N->real^N f' s h.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (\y. lift(h y)) continuous_on IMAGE f s /\
        (!y. y IN IMAGE f s ==> &0 <= h y) /\
        (\x. lift(abs(det(matrix(f' x))) * h(f x))) absolutely_integrable_on s
        ==> (\y. lift(h y)) absolutely_integrable_on IMAGE f s /\
            drop(integral (IMAGE f s) (\y. lift(h y))) <=
            drop(integral s (\x. lift(abs(det(matrix(f' x))) * h(f x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `s:real^N->bool`;
                   `h:real^N->real`; `&2`] GRGA_WEIGHTED_AREA_LE_R) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGA_LE_LIMIT THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `f':real^N->real^N->real^N`; `s:real^N->bool`;
                   `h:real^N->real`; `r:real`] GRGA_WEIGHTED_AREA_LE_R) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Chart composites.  If the composite of Fm with one chart has derivative   *)
(* F' within S at Z, then the composite with any other chart containing Fm Z *)
(* has derivative (chart Jacobian) o F', and |det| times the density is      *)
(* chart independent.  Then the area inequality, and equality in the         *)
(* injective case, on a measurable piece P of S mapped into one chart.       *)
(* ------------------------------------------------------------------------- *)

let GRGA_CHART_COMPOSITE_DERIV = prove
 (`!top atlas (Fm:real^N->A) F' S (U:A->bool) (phi:A->real^M) (V:A->bool)
    (psi:A->real^M) Z.
        smooth_manifold_atlas top atlas /\
        continuous_map (subtopology euclidean S,top) Fm /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ Z IN S /\ Fm Z IN U /\ Fm Z IN V /\
        ((\W. phi(Fm W)) has_derivative F') (at Z within S)
        ==> ((\W. psi(Fm W)) has_derivative
             (chart_jac (U,phi) (V,psi) (Fm Z) o F')) (at Z within S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^M))->bool`;
                 `U:A->bool`; `phi:A->real^M`; `V:A->bool`; `psi:A->real^M`;
                 `(Fm:real^N->A) Z`] CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ !W. W IN S /\ dist(W,Z) < e ==> (Fm:real^N->A) W IN U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open_in (subtopology euclidean S) {W | W IN S /\ (Fm:real^N->A) W IN U}`
    MP_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology euclidean S,top) (Fm:real^N->A)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `Z:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `W:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `ball(Z:real^N,e) INTER S SUBSET {W | W IN S /\ (Fm:real^N->A) W IN U}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `W:real^N`) THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `chart_trans (U:A->bool,phi:A->real^M) (V,psi) o (\W. phi((Fm:real^N->A) W))` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `W:real^N` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^M))->bool`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]]);;

let GRGA_DENSITY_JAC = prove
 (`!top atlas (g:A->real^N^N) (U:A->bool) (phi:A->real^N) V psi x (F':real^N->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        x IN U INTER V /\ linear F'
        ==> abs(det(matrix(chart_jac (U,phi) (V,psi) x o F'))) *
            mfd_density atlas (V,psi) g (psi x) =
            abs(det(matrix F')) * mfd_density atlas (U,phi) g (phi x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`] GRGV_DENSITY_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

let GRGA_NONNEG_AI = prove
 (`!(f:real^N->real) s.
        (\x. lift(f x)) integrable_on s /\ (!x. x IN s ==> &0 <= f x)
        ==> (\x. lift(f x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LIFT_COMPONENT]);;

let GRGA_AREA_PIECE = prove
 (`!top atlas (g:A->real^N^N) (Fm:real^N->A) Fm' S P (V:A->bool) (psi:A->real^N).
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g
                             (SND(chart_at atlas (Fm Z)) (Fm Z))))
       absolutely_integrable_on S /\
       (V,psi) IN atlas /\ P SUBSET S /\ lebesgue_measurable P /\ IMAGE Fm P SUBSET V
       ==> lebesgue_measurable (IMAGE psi (IMAGE Fm P)) /\
           (\y. lift(mfd_density atlas (V,psi) g y)) absolutely_integrable_on
           IMAGE psi (IMAGE Fm P) /\
           drop(integral (IMAGE psi (IMAGE Fm P))
                         (\y. lift(mfd_density atlas (V,psi) g y))) <=
           drop(integral P
                 (\Z. lift(abs(det(matrix(Fm' Z))) *
                           mfd_density atlas (chart_at atlas (Fm Z)) g
                                       (SND(chart_at atlas (Fm Z)) (Fm Z))))) /\
           ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
            ==> drop(integral (IMAGE psi (IMAGE Fm P))
                              (\y. lift(mfd_density atlas (V,psi) g y))) =
                drop(integral P
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (psi:A->real^N) (IMAGE (Fm:real^N->A) P) = IMAGE (\W.
      (psi:A->real^N)((Fm:real^N->A) W)) P`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P
        ==> chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z) IN atlas /\
            Fm Z IN FST(chart_at atlas (Fm Z)) /\ Fm Z IN V /\ Z IN S`
  (LABEL_TAC "CZ") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(Fm:real^N->A) Z`] CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P ==> ((\W. (psi:A->real^N)((Fm:real^N->A) W)) has_derivative (chart_jac
       (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))
       (V:A->bool,psi:A->real^N) (Fm Z) o (Fm':real^N->real^N->real^N) Z)) (at Z within P)`
  (LABEL_TAC "DK") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    USE_THEN "CZ" (MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `S:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Fm:real^N->A`;
      `(Fm':real^N->real^N->real^N) Z`; `S:real^N->bool`;
      `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `V:A->bool`; `psi:A->real^N`; `Z:real^N`] GRGA_CHART_COMPOSITE_DERIV) THEN
    REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P
        ==> abs(det(matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
            ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N) (Fm Z) o
            (Fm':real^N->real^N->real^N) Z))) *
            mfd_density atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N) (psi(Fm Z)) =
            abs(det(matrix(Fm' Z))) *
            mfd_density atlas (chart_at atlas (Fm Z)) g (SND(chart_at atlas (Fm Z)) (Fm Z))`
  (LABEL_TAC "IE") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    USE_THEN "CZ" (MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `V:A->bool`; `psi:A->real^N`; `(Fm:real^N->A) Z`;
      `(Fm':real^N->real^N->real^N) Z`] GRGA_DENSITY_JAC) THEN
    REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
    MAP_EVERY EXISTS_TAC
     [`\W. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))
              (Fm W)`;
      `at (Z:real^N) within S`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density
      atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
      (Fm Z)))) absolutely_integrable_on P` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (\W. (psi:A->real^N)((Fm:real^N->A) W)) P)`
      ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
    ASM_REWRITE_TAC[LE_REFL; differentiable_on] THEN
    X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A)
        Z)) (V:A->bool,psi:A->real^N) (Fm Z) o (Fm':real^N->real^N->real^N) Z` THEN
        USE_THEN "DK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\W. (psi:A->real^N)((Fm:real^N->A) W))`; `(\Z. chart_jac (chart_at
       (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N)
       (Fm Z) o (Fm':real^N->real^N->real^N) Z)`; `P:real^N->bool`;
    `mfd_density atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`]
   GRGA_WEIGHTED_AREA_LE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "DK" ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(V:A->bool,psi:A->real^N)) (FST(V,psi))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC GRGV_DENSITY_CONTINUOUS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FST; SND] THEN ASM SET_TAC[]];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `(V:A->bool,psi:A->real^N)`; `(psi:A->real^N)((Fm:real^N->A) Z)`]
                    GRGV_DENSITY_POS) THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `(\Z.
          lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
          (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
          (Fm Z))))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral P (\x. lift(abs(det(matrix(chart_jac (chart_at atlas ((Fm:real^N->A) x))
                                    (V:A->bool,psi:A->real^N) (Fm x) o
                                  (Fm':real^N->real^N->real^N) x))) *
                         mfd_density atlas (V,psi) (g:A->real^N^N) (psi(Fm x)))) =
    integral P (\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density
        atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm
        Z)) (Fm Z))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`(\y. lift(mfd_density atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)
      y))`; `(\W. (psi:A->real^N)((Fm:real^N->A) W))`; `(\Z. chart_jac (chart_at
      (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N)
      (Fm Z) o (Fm':real^N->real^N->real^N) Z)`; `P:real^N->bool`; `integral P (\Z.
      lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas (chart_at
      atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z)) (Fm Z))))`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "DK" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `V:A->bool`; `psi:A->real^N`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL
     [`\x. abs(det(matrix(chart_jac (chart_at atlas ((Fm:real^N->A) x))
                                    (V:A->bool,psi:A->real^N) (Fm x) o
                          (Fm':real^N->real^N->real^N) x))) %
           lift(mfd_density atlas (V,psi) (g:A->real^N^N) (psi(Fm x)))`;
      `(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
          (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
          (Fm Z))))`; `P:real^N->bool`] GRGV_AI_EQ) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Countably many charts cover IMAGE Fm S (LINDELOF_OPEN_IN); the            *)
(* first-chart pieces of S partition S and their images partition the image; *)
(* summing the piece estimates gives the area formula, first for real^N      *)
(* (GRGA_AREA_FORMULA) and then for real^3 (MFD_AREA_FORMULA).               *)
(* ------------------------------------------------------------------------- *)

let GRGA_CHART_COVER_SEQ = prove
 (`!top atlas (Fm:real^N->A) S.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^M))->bool) /\
        IMAGE Fm S SUBSET topspace top /\
        continuous_map (subtopology euclidean S,top) Fm /\ ~(S = {})
        ==> ?d:num->(A->bool)#(A->real^M).
                (!k. d k IN atlas) /\ (!Z. Z IN S ==> ?k. Fm Z IN FST(d k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{{W | W IN S /\ (Fm:real^N->A) W IN FST(e:(A->bool)#(A->real^M))} |
      e IN atlas}`; `S:real^N->bool`] LINDELOF_OPEN_IN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:(A->bool)#(A->real^M)` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `continuous_map (subtopology euclidean S,top) (Fm:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^M))->bool`;
                   `FST(e:(A->bool)#(A->real^M))`; `SND(e:(A->bool)#(A->real^M))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS f' = S:real^N->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `Z:real^N` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^M))->bool`;
                   `(Fm:real^N->A) Z`] CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^M))->bool) ((Fm:real^N->A) Z)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f':(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `UNIONS {} = S:real^N->bool` THEN
    REWRITE_TAC[UNIONS_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f':(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N->bool` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN
   `!k. ?e. e IN atlas /\
            (w:num->real^N->bool) k =
            {W | W IN S /\ (Fm:real^N->A) W IN FST(e:(A->bool)#(A->real^M))}`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    UNDISCH_TAC
     `IMAGE (w:num->real^N->bool) (:num) SUBSET
      {{W | W IN S /\ (Fm:real^N->A) W IN FST(e:(A->bool)#(A->real^M))} | e IN atlas}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(A->bool)#(A->real^M)` (LABEL_TAC "D")) THEN
  EXISTS_TAC `d:num->(A->bool)#(A->real^M)` THEN CONJ_TAC THENL
   [USE_THEN "D" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. (Z:real^N) IN (w:num->real^N->bool) k` MP_TAC THENL
   [UNDISCH_TAC `UNIONS (IMAGE (w:num->real^N->bool) (:num)) = S` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `Z:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  USE_THEN "D" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]);;

let GRGA_FIRST_PIECES = prove
 (`!(S:real^N->bool) (Fm:real^N->A) (D:num->A->bool) (P:num->real^N->bool).
        (!Z. Z IN S ==> ?k. Fm Z IN D k) /\
        (!k Z. Z IN P k <=> Z IN S /\ Fm Z IN D k /\ !j. j < k ==> ~(Fm Z IN D j))
        ==> (!m n. ~(m = n) ==> DISJOINT (IMAGE Fm (P m)) (IMAGE Fm (P n))) /\
            (!m n. ~(m = n) ==> DISJOINT (P m) (P n)) /\
            UNIONS {P k | k IN (:num)} = S /\
            UNIONS {IMAGE Fm (P k) | k IN (:num)} = IMAGE Fm S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m n. ~(m = n) ==> DISJOINT (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) m))
                                (IMAGE Fm (P n))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Z:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `Z':real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(Fm:real^N->A) Z' = Fm Z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(Z:real^N) IN (P:num->real^N->bool) m` THEN
    UNDISCH_TAC `(Z':real^N) IN (P:num->real^N->bool) n` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `~(m:num = n)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGA_FIRST_UNIQUE THEN
    EXISTS_TAC `\k. (Fm:real^N->A) Z IN (D:num->A->bool) k` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ~(m = n) ==> DISJOINT ((P:num->real^N->bool) m) (P n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `~(m:num = n)`)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z. Z IN S <=> ?k. Z IN (P:num->real^N->bool) k` ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN S`)) THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN ASM_MESON_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

let GRGA_AREA_FORMULA = prove
 (`!top atlas g (Fm:real^N->A) Fm' S.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       lebesgue_measurable S /\ IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g (SND(chart_at atlas (Fm Z))
                     (Fm Z))))
       integrable_on S
       ==> ?v. mfd_has_volume (top,atlas) g (IMAGE Fm S) v /\
               v <= drop(integral S
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z))))) /\
               ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
                ==> v = drop(integral S
                           (\Z. lift(abs(det(matrix(Fm' Z))) *
                                     mfd_density atlas (chart_at atlas (Fm Z)) g
                                                 (SND(chart_at atlas (Fm Z)) (Fm Z))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!Z. Z IN S
        ==> &0 <= abs(det(matrix((Fm':real^N->real^N->real^N) Z))) *
                  mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N)
                              (SND(chart_at atlas (Fm Z)) (Fm Z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC GRGV_DENSITY_POS THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(Fm:real^N->A) Z`] CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density
      atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
      (Fm Z)))) absolutely_integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGA_NONNEG_AI THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `S:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC] THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[MFD_HAS_VOLUME_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Fm:real^N->A`; `S:real^N->bool`] GRGA_CHART_COVER_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `P = \k. {Z | Z IN S /\
                 (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k) /\
                 !j. j < k ==> ~(Fm Z IN FST(d j))}` THEN
  SUBGOAL_THEN
   `!k Z. Z IN (P:num->real^N->bool) k <=>
          Z IN S /\ (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k) /\
          !j. j < k ==> ~(Fm Z IN FST(d j))`
  ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `Fm:real^N->A`;
                 `\k. FST((d:num->(A->bool)#(A->real^N)) k)`; `P:num->real^N->bool`]
                GRGA_FIRST_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. lebesgue_measurable ((P:num->real^N->bool) k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
     `!j. lebesgue_measurable
            {Z | Z IN S /\
                 (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) j)}`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN_IN THEN
      EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `continuous_map (subtopology euclidean S,top) (Fm:real^N->A)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((d:num->(A->bool)#(A->real^N)) j)`;
                     `SND((d:num->(A->bool)#(A->real^N)) j)`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(P:num->real^N->bool) k =
      {Z | Z IN S /\ (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k)} DIFF
      UNIONS (IMAGE (\j. {Z | Z IN S /\ Fm Z IN FST(d j)}) {j | j < k})`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. lebesgue_measurable (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                                   (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) /\
        (\y. lift(mfd_density atlas (d k) (g:A->real^N^N) y)) absolutely_integrable_on
        IMAGE (SND(d k)) (IMAGE Fm (P k)) /\
        drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE (Fm:real^N->A)
            ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k) (g:A->real^N^N)
            y))) <= drop(integral ((P:num->real^N->bool) k) (\Z.
            lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
            (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
            (Fm Z))))) /\
        ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z') ==> drop(integral (IMAGE
            (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE (Fm:real^N->A)
            ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k) (g:A->real^N^N)
            y))) = drop(integral ((P:num->real^N->bool) k) (\Z.
            lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
            (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
            (Fm Z))))))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `Fm:real^N->A`; `Fm':real^N->real^N->real^N`;
                   `S:real^N->bool`; `(P:num->real^N->bool) k`;
                   `FST((d:num->(A->bool)#(A->real^N)) k)`;
                   `SND((d:num->(A->bool)#(A->real^N)) k)`] GRGA_AREA_PIECE) THEN
    REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 <= drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE
       (Fm:real^N->A) ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k)
       (g:A->real^N^N) y))) /\
        drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                             (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k)))
                      (\y. lift(norm(lift(mfd_density atlas (d k) (g:A->real^N^N) y))))) =
        drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE (Fm:real^N->A)
            ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k) (g:A->real^N^N)
            y)))`
  (LABEL_TAC "NN") THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
     `!y. y IN IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                     (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))
          ==> &0 < mfd_density atlas (d k) (g:A->real^N^N) y`
    ASSUME_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC GRGV_DENSITY_POS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
       [USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN
        SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
        REWRITE_TAC[LIFT_DROP] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
      ASM_SIMP_TAC[NORM_LIFT; REAL_ARITH `&0 < x ==> abs x = x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. drop(integral ((P:num->real^N->bool) k) (\Z.
       lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas (chart_at
       atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z)) (Fm Z))))))
       real_sums drop(integral S (\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z)))
       * mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N)
       (SND(chart_at atlas (Fm Z)) (Fm Z)))))) (from 0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) *
       mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at
       atlas (Fm Z)) (Fm Z))))`; `P:num->real^N->bool`] GRGV_SUMS_PIECES) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0) (\k. drop(integral (IMAGE
      (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE (Fm:real^N->A) ((P:num->real^N->bool)
      k))) (\y. lift(mfd_density atlas (d k) (g:A->real^N^N) y))))` MP_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN EXISTS_TAC `\k. drop(integral
       ((P:num->real^N->bool) k) (\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z)))
       * mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N)
       (SND(chart_at atlas (Fm Z)) (Fm Z)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_summable] THEN EXISTS_TAC `drop(integral S (\Z.
         lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
         (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
         (Fm Z)))))` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "NN" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN
      USE_THEN "PC" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `k:num`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_summable] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_has_volume; mfd_has_integral; GRGV_INTEGRAND_ONE] THEN
    MAP_EVERY EXISTS_TAC
     [`d:num->(A->bool)#(A->real^N)`;
      `\k. IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k)`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[mfd_chart_partition] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      GEN_TAC THEN USE_THEN "PC" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      ASM_REWRITE_TAC[real_summable] THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC [`\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
        (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k)
        (g:A->real^N^N) y)))`; `\k. drop(integral ((P:num->real^N->bool) k) (\Z.
        lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas (chart_at
        atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z)) (Fm Z)))))`;
        `from 0`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
        (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k)
        (g:A->real^N^N) y)))`; `from 0`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE
        (Fm:real^N->A) ((P:num->real^N->bool) k))) (\y. lift(mfd_density atlas (d k)
        (g:A->real^N^N) y)))) = (\k. drop(integral ((P:num->real^N->bool) k) (\Z.
        lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas (chart_at
        atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z)) (Fm Z))))))`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC(last(CONJUNCTS th))) THEN
    ASM_REWRITE_TAC[]]);;

let MFD_AREA_FORMULA = prove
 (`!top atlas g (Fm:real^3->A) Fm' S.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\
       lebesgue_measurable S /\ IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g (SND(chart_at atlas (Fm Z))
                     (Fm Z))))
       integrable_on S
       ==> ?v. mfd_has_volume (top,atlas) g (IMAGE Fm S) v /\
               v <= drop(integral S
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z))))) /\
               ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
                ==> v = drop(integral S
                           (\Z. lift(abs(det(matrix(Fm' Z))) *
                                     mfd_density atlas (chart_at atlas (Fm Z)) g
                                                 (SND(chart_at atlas (Fm Z)) (Fm Z))))))`,
  MATCH_ACCEPT_TAC GRGA_AREA_FORMULA);;

(* ------------------------------------------------------------------------- *)
(* MFD_HAS_VOLUME_COMPARE_QF.  If the quadratic forms satisfy q_g <= lam     *)
(* q_g' pointwise, then sqrt(det g) <= sqrt(lam)^N sqrt(det g') (square      *)
(* roots of positive semidefinite matrices and REAL_LE_NORM_MATRIX_MUL_DET), *)
(* hence by MFD_HAS_VOLUME_COMPARE vol_g(S) <= lam sqrt(lam) vol_g'(S) in    *)
(* dimension 3.                                                              *)
(* ------------------------------------------------------------------------- *)

let GRGA_QF_NORM = prove
 (`!(S:real^N^N) w.
        positive_semidefinite S ==> w dot ((S ** S) ** w) = norm(S ** w) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[positive_semidefinite; symmetric_matrix]) THEN
  ASM_REWRITE_TAC[]);;

let GRGA_SQRT_DET_QF_LE = prove
 (`!(G:real^N^N) G' lam.
        positive_semidefinite G /\ positive_semidefinite G' /\ &0 <= lam /\
        (!w. w dot (G ** w) <= lam * (w dot (G' ** w)))
        ==> sqrt(det G) <= sqrt lam pow dimindex(:N) * sqrt(det G')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:real^N^N` POSITIVE_SEMIDEFINITE_SQRT_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `G':real^N^N` POSITIVE_SEMIDEFINITE_SQRT_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S':real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[DET_MUL; GSYM REAL_POW_2; POW_2_SQRT_ABS] THEN
  SUBGOAL_THEN `abs(sqrt lam) = sqrt lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_REFL; SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt lam pow dimindex(:N) * abs(det(S':real^N^N)) = abs(det(sqrt lam %% S'))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[DET_CMUL; REAL_ABS_MUL; REAL_ABS_POW]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_NORM_MATRIX_MUL_DET THEN X_GEN_TAC `w:real^N` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; NORM_MUL] THEN
  SUBGOAL_THEN
   `sqrt lam * norm((S':real^N^N) ** w) = sqrt(lam * norm(S' ** w) pow 2)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; NORM_POS_LE; POW_2_SQRT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_SIMP_TAC[GRGA_QF_NORM]);;

let MFD_HAS_VOLUME_COMPARE_QF = prove
 (`!top atlas g g' S v v' lam.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ riemannian_metric atlas g' /\ &0 <= lam /\
       mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g' S v' /\
       (!y w. y IN S ==> w dot (g y ** w) <= lam * (w dot (g' y ** w)))
       ==> v <= lam * sqrt lam * v'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `\x:A. &1`; `S:A->bool`; `v:real`]
                  MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume] THEN SIMP_TAC[mfd_lebesgue_measurable];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g':A->real^3^3`; `g:A->real^3^3`; `S:A->bool`; `v':real`; `v:real`;
                 `lam * sqrt lam`] MFD_HAS_VOLUME_COMPARE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lam * sqrt lam = sqrt lam pow dimindex(:3)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH_RULE `3 = SUC 2`; real_pow] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGA_SQRT_DET_QF_LE THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN
  ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]);;

