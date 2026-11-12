(* ========================================================================= *)
(* Unit pc_p2a_wk8: FL9 (P2A_FLOW_MIN_GRAD_STATEMENT, pc_p2a_fldefs) from    *)
(* FL2: along a minimizer gamma to (q, tau), l is differentiable at (gamma   *)
(* s, s) for 0 < s < tau with grad l = velocity.  The upper bound is         *)
(* P2AW_FLOW_PT_TOUCH (pc_p2a_wk3) for the restricted minimizer; the lower   *)
(* bound is a barrier from the future: any admissible curve to a nearby (y,  *)
(* s') continued by a curve family back to (gamma s2, s2), s < s2 < tau,     *)
(* whose L-length is expanded at its LEFT end by reflecting the parameter (s *)
(* -> -s leaves the L-integrand invariant) and the right-end expansion       *)
(* P2AW_CFAM_TAYLOR_GEN.                                                     *)
(* ========================================================================= *)

needs "src/pc_p2a_wk4.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* P2AW_CFAM_TAYLOR (pc_p2a_wk3) without the sign condition 0 <= s1: the     *)
(* parameter interval [s1, sb] may lie in the negative reals (bound B0 on    *)
(* abs s1, abs sb).  Used with the reflection s -> -s, under which the       *)
(* L-integrand is invariant, for curve families perturbed at the LEFT end    *)
(* (the lower barrier from the future of FL9).  Same proof with the          *)
(* constants of the time estimate changed.                                   *)
(* ------------------------------------------------------------------------- *)

let P2AW_CFAM_TAYLOR_GEN = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt K0 M (y:real^1->real^N) A s1 sb B0.
     lrg_lsmooth U ta tb Gt /\ compact K0 /\ K0 SUBSET interval(lift ta,lift tb) PCROSS U /\
     &0 <= M /\ abs s1 <= B0 /\ abs sb <= B0 /\ s1 < sb /\
     (!s. s1 <= s /\ s <= sb
          ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN K0 /\ norm(A(lift s)) <= M /\
              (y has_vector_derivative A(lift s)) (at (lift s))) /\
     A continuous_on interval[lift s1,lift sb]
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d
                 ==> abs(p2a_cL Gt tt (p2aw_cfam y s1 sb w k) s1 (s1 + k * (sb - s1)) -
                         p2a_cL Gt tt y s1 sb -
                         ((k - &1) * p2aw_cfk Gt tt y A s1 sb + p2aw_cfw Gt tt y A s1 sb w))
                     <= C * (abs(k - &1) + norm w) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ABBREV_TAC `K1 = (K0:real^(1,N)finite_sum->bool) PCROSS cball(vec 0:real^N,M)` THEN
  SUBGOAL_THEN `compact(K1:real^((1,N)finite_sum,N)finite_sum->bool) /\
                K1 SUBSET (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; ASSUME `compact(K0:real^(1,N)finite_sum->bool)`] THEN
    REWRITE_TAC[SUBSET_PCROSS; SUBSET_UNIV;
                ASSUME `K0 SUBSET interval(lift ta,lift tb) PCROSS (U:real^N->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `open((interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)) /\
                smooth_map_on ((interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N))
                  (\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_SMOOTH_DIFF_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))))) THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_HESS_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HB"))) THEN
  ABBREV_TAC `Ce = &6 * B0 pow 2 + &2 * M + &1 + &2 / (sb - s1)` THEN
  SUBGOAL_THEN `&0 < Ce /\ &0 < sb - s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN EXPAND_TAC "Ce" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 < a + b + &1 + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min (inv(&2)) (d1 / (&2 * Ce))`;
                        `(sb - s1) * (&2 * B * Ce pow 2 + &2 * B2 * Ce)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `k:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(k - &1) <= inv(&2) /\ abs(k - &1) <= d1 / (&2 * Ce) /\
                norm(w:real^N) <= inv(&2) /\ norm w <= d1 / (&2 * Ce)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k /\ k <= &2 /\ inv k <= &2 /\ abs(inv k - &1) <= &2 * abs(k - &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      SUBGOAL_THEN `inv k - &1 = (&1 - k) * inv k` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `~(k = &0) ==> inv k - &1 = (&1 - k) * inv k`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&1 - k) = abs(k - &1)`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x /\ x <= &2 ==> abs x <= &2`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]]];
    ALL_TAC] THEN
  ABBREV_TAC `tq = abs(k - &1) + norm(w:real^N)` THEN
  SUBGOAL_THEN `&0 <= tq /\ abs(k - &1) <= tq /\ norm(w:real^N) <= tq /\
                abs(k - &1) pow 2 <= tq pow 2 /\ abs(k - &1) * norm w <= tq pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tq" THEN
    SUBGOAL_THEN `&0 <= abs(k - &1) /\ &0 <= norm(w:real^N)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the pointwise estimate *)
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                      ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w)
              IN interval(lift ta,lift tb) PCROSS U /\
            abs(k * p2aw_lagf (Gt:real->real^N->real^N^N) tt
                      (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                            (y(lift s) + ((s - s1) / (sb - s1)) % w))
                                 (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))) -
                p2aw_lagf Gt tt (p2aw_zc y A tt s) -
                ((k - &1) *
                 (p2aw_lagf Gt tt (p2aw_zc y A tt s) +
                  p2aw_d1 (p2aw_lagf Gt tt)
                    (pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0)) (--(A(lift s))))
                    (p2aw_zc y A tt s)) +
                 p2aw_d1 (p2aw_lagf Gt tt)
                   (pastecart (pastecart (vec 0) (((s - s1) / (sb - s1)) % w)) (inv(sb - s1) % w))
                   (p2aw_zc y A tt s)))
            <= (&2 * B * Ce pow 2 + &2 * B2 * Ce) * tq pow 2`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `r = s1 + k * (s - s1)` THEN
    SUBGOAL_THEN `&0 <= (s - s1) / (sb - s1) /\ (s - s1) / (sb - s1) <= &1 /\
                  &0 <= s - s1 /\ s - s1 <= &2 * B0 /\ abs s <= B0`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    (* time component *)
    SUBGOAL_THEN `s pow 2 - r pow 2 = --((k - &1) * (s - s1) * (&2 * s + (k - &1) * (s - s1))) /\
                  s pow 2 - r pow 2 - (k - &1) * --(&2 * s * (s - s1)) =
                  --((k - &1) pow 2 * (s - s1) pow 2)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `abs(s pow 2 - r pow 2) <= &6 * B0 pow 2 * abs(k - &1) /\
                  abs(s pow 2 - r pow 2 - (k - &1) * --(&2 * s * (s - s1))) <=
                  &4 * B0 pow 2 * abs(k - &1) pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_POW] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `abs(s - s1) <= &2 * B0 /\ abs(&2 * s + (k - &1) * (s - s1)) <= &3 * B0`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `abs((k - &1) * (s - s1)) <= B0` MP_TAC THENL
           [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `inv(&2) * (&2 * B0)` THEN CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
              REAL_ARITH_TAC];
            ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(k - &1) * (&2 * B0) * (&3 * B0)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
          REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(k - &1) pow 2 * (&2 * B0) pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    (* velocity component *)
    SUBGOAL_THEN
     `norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s))
      <= &2 * M * abs(k - &1) + &2 / (sb - s1) * norm(w:real^N) /\
      norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s) -
           ((k - &1) % --(A(lift s)) + inv(sb - s1) % w))
      <= &2 * M * abs(k - &1) pow 2 + &2 / (sb - s1) * abs(k - &1) * norm(w:real^N)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= inv k /\ &0 <= inv(sb - s1)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH
          `c % (a + d % w) - a:real^N = (c - &1) % a + (c * d) % w`] THEN
        MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
        REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * abs(k - &1)) * M` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
            REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_MUL] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
          REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
        `c % (a + d % w) - a - ((k - &1) % --a + d % w):real^N =
         (c - &1 + (k - &1)) % a + ((c - &1) * d) % w`] THEN
      SUBGOAL_THEN `inv k - &1 + (k - &1) = (k - &1) pow 2 * inv k` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_POW] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs(k - &1) pow 2 * &2) * M` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&2 * abs(k - &1)) * inv(sb - s1) * norm(w:real^N)` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    (* the points and the displacements *)
    ABBREV_TAC `x = p2aw_zc (y:real^1->real^N) A tt s` THEN
    ABBREV_TAC `z = pastecart (pastecart (lift(tt - r pow 2))
                                         ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                              (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))` THEN
    ABBREV_TAC `et = pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0:real^N))
                               (--((A:real^1->real^N)(lift s)))` THEN
    ABBREV_TAC `ew = pastecart (pastecart (vec 0:real^1) (((s - s1) / (sb - s1)) % w))
                               (inv(sb - s1) % (w:real^N))` THEN
    SUBGOAL_THEN
     `norm(z - x:real^((1,N)finite_sum,N)finite_sum) <= Ce * tq /\
      norm(z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum) <= Ce * tq pow 2`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z"; "x"; "et"; "ew"] THEN
      REWRITE_TAC[p2aw_zc; GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_SUB] THEN
      REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_ADD; VECTOR_MUL_RZERO;
                  VECTOR_ADD_RID; VECTOR_ADD_LID; VECTOR_ARITH `(a + b) - a:real^N = b`;
                  VECTOR_SUB_REFL; REAL_ARITH `(tt - r) - (tt - s):real = s - r`] THEN
      CONJ_TAC THEN
      MATCH_MP_TAC P2AW_NORM_PASTECART3 THEN
      REWRITE_TAC[NORM_LIFT; NORM_0; NORM_MUL] THENL
       [EXPAND_TAC "Ce" THEN EXPAND_TAC "tq" THEN
        SUBGOAL_THEN `abs((s - s1) / (sb - s1)) * norm(w:real^N) <= norm w` ASSUME_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= abs(k - &1) * (&2 / (sb - s1)) /\ &0 <= &2 / (sb - s1) /\
                      &0 <= norm w * (&6 * B0 pow 2 + &2 * M) /\
                      &0 <= abs(k - &1) * &1 /\ &0 <= norm(w:real^N) * &1`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
          REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
          TRY(MATCH_MP_TAC REAL_LE_DIV) THEN TRY ASM_REAL_ARITH_TAC THEN
          MATCH_MP_TAC REAL_LE_ADD THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2];
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Ce" THEN
        SUBGOAL_THEN `&0 <= &2 / (sb - s1) * tq pow 2 /\ &0 <= B0 pow 2 * tq pow 2 /\
                      &0 <= M * tq pow 2 /\ &0 <= tq pow 2 /\ &0 <= &2 / (sb - s1)`
        STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN `&0 <= &2 / (sb - s1)` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
          ALL_TAC] THEN
        SUBGOAL_THEN `&2 / (sb - s1) * abs(k - &1) * norm(w:real^N) <= &2 / (sb - s1) * tq pow 2 /\
                      (&4 * B0 pow 2) * abs(k - &1) pow 2 <= (&4 * B0 pow 2) * tq pow 2 /\
                      (&2 * M) * abs(k - &1) pow 2 <= (&2 * M) * tq pow 2`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_POS] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^((1,N)finite_sum,N)finite_sum) IN K1 /\
                  norm(z - x:real^((1,N)finite_sum,N)finite_sum) <= d1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "K1"] THEN
        REWRITE_TAC[p2aw_zc; PASTECART_IN_PCROSS; IN_CBALL_0] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ce * tq` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ce * (&2 * d1 / (&2 * Ce))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          EXPAND_TAC "tq" THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Ce` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    USE_THEN "DB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x:real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `x + (z - x):real^N = z`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `z IN (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      EXPAND_TAC "z" THEN SIMP_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt y)) differentiable
                  (at (x:real^((1,N)finite_sum,N)finite_sum))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt) (z - x) x =
      (k - &1) * p2aw_d1 (p2aw_lagf Gt tt) et x + p2aw_d1 (p2aw_lagf Gt tt) ew x +
      p2aw_d1 (p2aw_lagf Gt tt) (z - x - ((k - &1) % et + ew)) x`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p2aw_lagf (Gt:real->real^N->real^N^N) tt`; `&1`;
                     `z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum`;
                     `(k - &1) % et + ew:real^((1,N)finite_sum,N)finite_sum`;
                     `x:real^((1,N)finite_sum,N)finite_sum`] P2AW_D1_COMB) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `&1 % (a - b - c) + c:real^N = a - b`] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[P2AW_D1_COMB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    USE_THEN "HB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x:real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    ABBREV_TAC `nz = norm(z - x:real^((1,N)finite_sum,N)finite_sum)` THEN
    ABBREV_TAC `nzl = norm(z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum)` THEN
    SUBGOAL_THEN `&0 <= nz /\ &0 <= nzl` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nz"; "nzl"] THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `k * B * nz pow 2 <= &2 * B * Ce pow 2 * tq pow 2 /\
                  abs(k - &1) * B2 * nz <= B2 * Ce * tq pow 2 /\
                  B2 * nzl <= B2 * Ce * tq pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * B * nz pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
          REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tq * B2 * Ce * tq` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
          CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `abs(p2aw_lagf (Gt:real->real^N->real^N^N) tt z - p2aw_lagf Gt tt x -
                     p2aw_d1 (p2aw_lagf Gt tt) (z - x) x) <= B * nz pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt) (z - x) x) <= B2 * nz` THEN
    UNDISCH_TAC `abs(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                       (z - x - ((k - &1) % et + ew)) x) <= B2 * nzl` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `k * (B * nz pow 2) + abs(k - &1) * (B2 * nz) + B2 * nzl` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `k * p2aw_lagf (Gt:real->real^N->real^N^N) tt z - p2aw_lagf Gt tt x -
        ((k - &1) * (p2aw_lagf Gt tt x + p2aw_d1 (p2aw_lagf Gt tt) et x) +
         p2aw_d1 (p2aw_lagf Gt tt) ew x) =
        k * (p2aw_lagf Gt tt z - p2aw_lagf Gt tt x - p2aw_d1 (p2aw_lagf Gt tt) (z - x) x) +
        (k - &1) * p2aw_d1 (p2aw_lagf Gt tt) (z - x) x +
        p2aw_d1 (p2aw_lagf Gt tt) (z - x - ((k - &1) % et + ew)) x`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                                   (z - x:real^((1,N)finite_sum,N)finite_sum) x`)) THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs a <= x /\ abs b <= y /\ abs c <= z ==> abs(a + b + c) <= x + y + z`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      UNDISCH_TAC `k * B * nz pow 2 <= &2 * B * Ce pow 2 * tq pow 2` THEN
      UNDISCH_TAC `abs(k - &1) * B2 * nz <= B2 * Ce * tq pow 2` THEN
      UNDISCH_TAC `B2 * nzl <= B2 * Ce * tq pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* integration *)
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift sb]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(A:real^1->real^N)(lift s)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))
            IN interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `K0 SUBSET interval(lift ta,lift tb) PCROSS (U:real^N->bool)`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s1:real`; `sb:real`; `w:real^N`;
                 `k:real`] P2AW_CFAM_CL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 sb =
    real_integral (real_interval[s1,sb])
      (\s. p2aw_lagf Gt tt (p2aw_zc (y:real^1->real^N) A tt s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2aw_zc] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM P2AW_SFAM_ZERO] THEN
    MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                   `s1:real`; `sb:real`; `vec 0:real^N`] P2AW_SFAM_CL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
           (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                 ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                      (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))))
    real_integrable_on real_interval[s1,sb]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `\v:real^1. pastecart (pastecart (lift(tt - (s1 + k * (drop v - s1)) pow 2))
                                 ((y:real^1->real^N) v + ((drop v - s1) / (sb - s1)) % w))
                                 (inv k % ((A:real^1->real^N) v + inv(sb - s1) % w))`;
                   `s1:real`; `sb:real`] P2AW_LAGF_PATH_INTEGRABLE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[P2AW_TIME_PATH_CONT] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[ETA_AX; P2AW_MU_CONT];
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX]];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k * real_integral (real_interval[s1,sb])
          (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w)))) =
    real_integral (real_interval[s1,sb])
          (\s. k * p2aw_lagf Gt tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       (y(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % (A(lift s) + inv(sb - s1) % w))))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_cfk; p2aw_cfw] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&2 * B * Ce pow 2 + &2 * B2 * Ce) * tq pow 2) * (sb - s1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_INTEGRAL_DIFF4 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[p2aw_zc] THEN MATCH_MP_TAC P2AW_LAGF_CURVE_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[p2aw_zc] THEN MATCH_MP_TAC P2AW_LAGF_CURVE_INTEGRABLE THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                       `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                       `\v:real^1. pastecart (pastecart (lift(--(&2 * drop v * (drop v - s1))))
                                                        (vec 0:real^N))
                                             (--((A:real^1->real^N) v))`;
                       `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_INTEGRABLE) THEN
        REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          REWRITE_TAC[LIFT_NEG; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
          MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; LIFT_SUB] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
          MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[ETA_AX]]];
      MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                     `\v:real^1. pastecart (pastecart (vec 0:real^1)
                                                      (((drop v - s1) / (sb - s1)) % (w:real^N)))
                                           (inv(sb - s1) % w)`;
                     `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_INTEGRABLE) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST; P2AW_MU_CONT];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the s-form Lagrangian (as a function of                 *)
(* ((t,y),A)) in a direction with no time component: the first variation    *)
(* integrand of P2A_WEAK_EL,                                                 *)
(*   (1/2) A.(dG(dy)) A + 2 (tt - t) dR(dy) + dA.(G A).                      *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* The parameter reflection s -> -s.  The L-geodesic acceleration and the    *)
(* L-integrand are invariant under (s, A) -> (-s, -A), so the reflected      *)
(* curve of a solution solves the same equation and has the same L-length on *)
(* the reflected interval.  The left-perturbed curve family p2aw_lfam is the *)
(* reflection of the right-perturbed p2aw_cfam.                              *)
(* ------------------------------------------------------------------------- *)

let P2AW_LACC_REFLECT = prove
 (`!U (Gt:real->real^N->real^N^N) tt s y A.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> p2a_lacc Gt tt (--s) y (--A) = p2a_lacc Gt tt s y A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lacc; p2a_lricop] THEN
  SUBGOAL_THEN `(--s) pow 2 = s pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] CHRISTOFFEL_BILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BILINEAR_LNEG; BILINEAR_RNEG; VECTOR_NEG_NEG] THEN
  SUBGOAL_THEN
   `(lambda k. lricci (G:real^N->real^N^N) y (--A) (basis k)):real^N =
    --(lambda k. lricci G y A (basis k))`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_NEG_COMPONENT] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci")) (concl th) &&
      can (term_match [] `!b. linear (\a. lift(lricci (G:real^N->real^N^N) y a b))`)
          (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `A:real^N` o MATCH_MP LINEAR_NEG) THEN
    REWRITE_TAC[GSYM LIFT_NEG; LIFT_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG] THEN VECTOR_ARITH_TAC);;

let P2AW_LLAG_REFLECT = prove
 (`!(Gt:real->real^N->real^N^N) tt s y A.
     p2a_llag Gt tt (--s) y (--A) = p2a_llag Gt tt s y A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_llag] THEN
  SUBGOAL_THEN `(--s) pow 2 = s pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG]);;

let P2AW_VDERIV_REFLECT = prove
 (`!(f:real^1->real^N) f' x.
     (f has_vector_derivative f') (at x)
     ==> ((\v. f(--v)) has_vector_derivative (--f')) (at (--x))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[GSYM HAS_DERIVATIVE_AT_REFLECT] o
    REWRITE_RULE[has_vector_derivative]) THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; DROP_NEG] THEN BETA_TAC THEN REWRITE_TAC[DROP_NEG] THEN
  VECTOR_ARITH_TAC);;

let P2AW_CL_REFLECT = prove
 (`!(Gt:real->real^N->real^N^N) tt (c:real^1->real^N) a b.
     (!s. a <= s /\ s <= b ==> c differentiable (at (lift s)))
     ==> p2a_cL Gt tt (\v. c(--v)) (--b) (--a) = p2a_cL Gt tt c a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_cL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INTEGRAL_REFLECT] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `s:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(c:real^1->real^N) differentiable (at (lift(--s)))` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (\v. (c:real^1->real^N)(--v)) (at (lift s)) =
    --(vector_derivative c (at (lift(--s))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP P2AW_VDERIV_REFLECT) THEN
    REWRITE_TAC[GSYM LIFT_NEG; REAL_NEG_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_NEG] THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                 `(c:real^1->real^N)(lift(--s))`;
                 `--(vector_derivative (c:real^1->real^N) (at (lift(--s))))`]
                P2AW_LLAG_REFLECT) THEN
  REWRITE_TAC[VECTOR_NEG_NEG] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let p2aw_lfam = new_definition
 `p2aw_lfam (Y:real^1->real^N) (sa:real) (sb:real) (w:real^N) (k:real) =
    \v:real^1. Y(lift(sb - (sb - drop v) / k)) + ((sb - drop v) / (k * (sb - sa))) % w`;;

let P2AW_LFAM_CFAM = prove
 (`!(Y:real^1->real^N) sa sb w k.
     sa < sb /\ &0 < k
     ==> p2aw_lfam Y sa sb w k = (\v. p2aw_cfam (\u. Y(--u)) (--sb) (--sa) w k (--v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_lfam; p2aw_cfam; p2aw_sfam; FUN_EQ_THM] THEN
  X_GEN_TAC `v:real^1` THEN REWRITE_TAC[LIFT_DROP; DROP_NEG; GSYM LIFT_NEG] THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `sa < sb` THEN CONV_TAC REAL_FIELD]);;


(* ------------------------------------------------------------------------- *)
(* The left-end expansion.  For an L-geodesic chart curve Y on [sa, sb]      *)
(* (two-sided C^1 and the geodesic equation on the closed interval) the      *)
(* family p2aw_lfam Y sa sb w k starts at Y(sa) + w at the parameter sb - k  *)
(* (sb - sa) and ends at Y(sb) at sb; its L-length is that of Y plus (k - 1) *)
(* (sb - sa) (2 sa^2 R - A.GA/2)(sa) - w . G A(sa) up to second order (the   *)
(* first variation at the left end), by reflecting the right-end expansion   *)
(* P2AW_CFAM_TAYLOR_GEN on [-sb, -sa].                                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_LFAM_ENDS = prove
 (`!(Y:real^1->real^N) sa sb w k.
     &0 < k /\ sa < sb
     ==> p2aw_lfam Y sa sb w k (lift(sb - k * (sb - sa))) = Y(lift sa) + w /\
         p2aw_lfam Y sa sb w k (lift sb) = Y(lift sb)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_lfam; LIFT_DROP] THENL
   [SUBGOAL_THEN `sb - (sb - (sb - k * (sb - sa))) / k = sa /\
                  (sb - (sb - k * (sb - sa))) / (k * (sb - sa)) = &1`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    CONJ_TAC THEN UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `sa < sb` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_SUB_RZERO; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID]]);;

let P2AW_LOCAL_LBAR = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) A sa sb.
     lricci_flow U ta tb Gt /\ &0 < sa /\ sa < sb /\
     (!s. sa <= s /\ s <= sb ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ Y(lift s) IN U) /\
     A continuous_on interval[lift sa,lift sb] /\
     (!s. sa <= s /\ s <= sb
          ==> (Y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A(lift s))) (at (lift s)))
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d
                 ==> (!s. sa <= s /\ s <= sb ==> Y(lift s) + ((sb - s) / (sb - sa)) % w IN U) /\
                     abs(p2a_cL Gt tt (p2aw_lfam Y sa sb w k) (sb - k * (sb - sa)) sb -
                         p2a_cL Gt tt Y sa sb -
                         ((k - &1) *
                          ((sb - sa) *
                           (&2 * sa pow 2 * lscalar (Gt(tt - sa pow 2)) (Y(lift sa)) -
                            inv(&2) * (A(lift sa) dot (Gt(tt - sa pow 2) (Y(lift sa)) **
                                                       A(lift sa))))) -
                          w dot (Gt(tt - sa pow 2) (Y(lift sa)) ** A(lift sa))))
                     <= C * (abs(k - &1) + norm w) pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TR")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ABBREV_TAC `Yr = \v:real^1. (Y:real^1->real^N)(--v)` THEN
  ABBREV_TAC `Ar = \v:real^1. --((A:real^1->real^N)(--v))` THEN
  SUBGOAL_THEN
   `!s. --sb <= s /\ s <= --sa
        ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (Yr:real^1->real^N)(lift s) IN U /\
            Yr(lift s) = Y(lift(--s)) /\ (Ar:real^1->real^N)(lift s) = --(A(lift(--s))) /\
            (Yr has_vector_derivative Ar(lift s)) (at (lift s)) /\
            (Ar has_vector_derivative p2a_lacc Gt tt s (Yr(lift s)) (Ar(lift s))) (at (lift s))`
  (LABEL_TAC "R") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `sa <= --s /\ --s <= sb /\ (--s) pow 2 = s pow 2` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "TR" (MP_TAC o SPEC `--s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(--s) pow 2 = s pow 2`]) THEN
    USE_THEN "D" (MP_TAC o SPEC `--s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(Yr:real^1->real^N)(lift s) = Y(lift(--s)) /\
                  (Ar:real^1->real^N)(lift s) = --(A(lift(--s)))`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Yr"; "Ar"] THEN REWRITE_TAC[LIFT_NEG]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Yr" THEN
      MP_TAC(ISPECL [`Y:real^1->real^N`; `(A:real^1->real^N)(lift(--s))`; `lift(--s)`]
                    P2AW_VDERIV_REFLECT) THEN
      ASM_REWRITE_TAC[GSYM LIFT_NEG; REAL_NEG_NEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift(--s)))
               (--((A:real^1->real^N)(lift(--s)))) =
      p2a_lacc Gt tt (--s) (Y(lift(--s))) (A(lift(--s)))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                     `(Y:real^1->real^N)(lift(--s))`; `--((A:real^1->real^N)(lift(--s)))`]
                    P2AW_LACC_REFLECT) THEN
      ASM_REWRITE_TAC[VECTOR_NEG_NEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^1->real^N`;
                   `p2a_lacc (Gt:real->real^N->real^N^N) tt (--s) ((Y:real^1->real^N)(lift(--s)))
                              ((A:real^1->real^N)(lift(--s)))`; `lift(--s)`]
                  P2AW_VDERIV_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_NEG) THEN
    REWRITE_TAC[VECTOR_NEG_NEG; GSYM LIFT_NEG; REAL_NEG_NEG] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Yr:real^1->real^N) continuous_on interval[lift(--sb),lift(--sa)] /\
                (Ar:real^1->real^N) continuous_on interval[lift(--sb),lift(--sa)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    USE_THEN "R" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ta < tt - sb pow 2 /\ tt - sa pow 2 < tb /\ sa pow 2 <= sb pow 2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "TR" (MP_TAC o SPEC `sb:real`) THEN USE_THEN "TR" (MP_TAC o SPEC `sa:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K0 = interval[lift(tt - sb pow 2),lift(tt - sa pow 2)] PCROSS
                   IMAGE (Yr:real^1->real^N) (interval[lift(--sb),lift(--sa)])` THEN
  SUBGOAL_THEN `compact(K0:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K0:real^(1,N)finite_sum->bool) SUBSET interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN REWRITE_TAC[SUBSET_PCROSS] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "R" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --sb <= s /\ s <= --sa
        ==> pastecart (lift(tt - s pow 2)) ((Yr:real^1->real^N)(lift s)) IN K0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K0" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `sa pow 2 <= (--s) pow 2 /\ (--s) pow 2 <= sb pow 2 /\ (--s) pow 2 = s pow 2`
      MP_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE2) THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\ !s. --sb <= s /\ s <= --sa ==> norm((Ar:real^1->real^N)(lift s)) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Ar:real^1->real^N`; `interval[lift(--sb),lift(--sa)]`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `K0:real^(1,N)finite_sum->bool`; `M:real`; `Yr:real^1->real^N`;
                 `Ar:real^1->real^N`; `--sb`; `--sa`; `sb:real`] P2AW_CFAM_TAYLOR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "R" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `dt:real` (X_CHOOSE_THEN `Ct:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TAY")))))] THEN
  SUBGOAL_THEN
   `lricci_flow U ta tb (Gt:real->real^N->real^N^N) /\ --sb < --sa /\
    (!s. --sb <= s /\ s <= --sa
         ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (Yr:real^1->real^N)(lift s) IN U) /\
    Yr continuous_on interval[lift(--sb),lift(--sa)] /\
    (Ar:real^1->real^N) continuous_on interval[lift(--sb),lift(--sa)] /\
    (!s. --sb < s /\ s < --sa
         ==> (Yr has_vector_derivative Ar(lift s)) (at (lift s)) /\
             (Ar has_vector_derivative p2a_lacc Gt tt s (Yr(lift s)) (Ar(lift s))) (at (lift s)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "R" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "R" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Yr:real^1->real^N)(lift(--sa)) = Y(lift sa) /\
    (Ar:real^1->real^N)(lift(--sa)) = --(A(lift sa)) /\ (--sa) pow 2 = sa pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Yr"; "Ar"] THEN REWRITE_TAC[GSYM LIFT_NEG; REAL_NEG_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. p2aw_cfw Gt tt (Yr:real^1->real^N) Ar (--sb) (--sa) w =
        --(w dot (Gt(tt - sa pow 2) ((Y:real^1->real^N)(lift sa)) ** A(lift sa)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP
     (ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
              `Yr:real^1->real^N`; `Ar:real^1->real^N`; `--sb`; `--sa`; `w:real^N`]
             P2AW_CFW_EVAL)) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2aw_cfk Gt tt (Yr:real^1->real^N) Ar (--sb) (--sa) =
    (sb - sa) * (&2 * sa pow 2 * lscalar (Gt(tt - sa pow 2)) ((Y:real^1->real^N)(lift sa)) -
                 inv(&2) * (A(lift sa) dot (Gt(tt - sa pow 2) (Y(lift sa)) ** A(lift sa))))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP
     (ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
              `Yr:real^1->real^N`; `Ar:real^1->real^N`; `--sb`; `--sa`] P2AW_CFK_EVAL)) THEN
    ASM_REWRITE_TAC[p2aw_lagf; p2aw_zc; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                    MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cL (Gt:real->real^N->real^N^N) tt Yr (--sb) (--sa) = p2a_cL Gt tt Y sa sb`
  ASSUME_TAC THENL
   [EXPAND_TAC "Yr" THEN MATCH_MP_TAC P2AW_CL_REFLECT THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(A:real^1->real^N)(lift s)` THEN USE_THEN "D" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `IMAGE (Y:real^1->real^N) (interval[lift sa,lift sb])`]
                P2AW_COMPACT_THICK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(A:real^1->real^N)(lift s)` THEN USE_THEN "D" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "TR" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `du:real` (X_CHOOSE_THEN `kk:real^N->bool` STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC [`min (min dt du) (inv(&2))`; `Ct:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `&0 < inv(&2)` (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN MAP_EVERY X_GEN_TAC [`w:real^N`; `k:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift s) + ((sb - s) / (sb - sa)) % w IN kk`
      (fun th -> ASM SET_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * norm(w:real^N)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        SUBGOAL_THEN `&0 <= (sb - s) / (sb - sa) /\ (sb - s) / (sb - sa) <= &1` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2AW_LFAM_CFAM] THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`;
                 `p2aw_cfam (Yr:real^1->real^N) (--sb) (--sa) w k`; `--sb`;
                 `--sb + k * (--sa - --sb)`] P2AW_CL_REFLECT) THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `--(--sb + k * (--sa - --sb)) = sb - k * (sb - sa)`] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    MP_TAC(ISPECL [`Yr:real^1->real^N`; `(Ar:real^1->real^N)(lift(--sb + (r - --sb) / k))`;
                   `--sb`; `--sa`; `w:real^N`; `k:real`; `r:real`] P2AW_CFAM_DERIV) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "R" (MP_TAC o SPEC `--sb + (r - --sb) / k`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN `&0 <= (r - --sb) / k /\ (r - --sb) / k <= sb - sa` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "TAY" (MP_TAC o SPECL [`w:real^N`; `k:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> abs x <= c ==> abs y <= c`) THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The comparison from the future.  A minimizer gamma' to the start point    *)
(* (phi(gamma(sa^2)) + w, (sb - k (sb - sa))^2) of the left family,          *)
(* continued by the family (a chart curve, P2A_CHART_CURVE_SEG) up to        *)
(* (gamma(sb^2), sb^2), is admissible (P2A_SEG_GLUE); hence L(gamma(sb^2),   *)
(* sb^2) <= L(gamma') + cL(family).                                          *)
(* ------------------------------------------------------------------------- *)

let P2AW_LFAM_DERIV = prove
 (`!(Y:real^1->real^N) B sa sb w k r.
     &0 < k /\ (Y has_vector_derivative B) (at (lift(sb + (r - sb) / k)))
     ==> (p2aw_lfam Y sa sb w k has_vector_derivative (inv k % (B - inv(sb - sa) % w)))
           (at (lift r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p2aw_lfam (Y:real^1->real^N) sa sb w k =
    (\v. (Y o (\v. lift(sb + (drop v - sb) / k))) v +
         ((--(inv(k * (sb - sa)))) * drop v + sb * inv(k * (sb - sa))) % w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2aw_lfam; FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^1` THEN
    BINOP_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv k % ((B:real^N) - inv(sb - sa) % w) =
                drop(lift(inv k)) % B + (--(inv(k * (sb - sa)))) % w`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_DROP; REAL_INV_MUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[P2AW_AFFINE_VDERIV; ETA_AX] THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN REWRITE_TAC[P2AW_REPAR_VDERIV] THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2AW_FLOW_CMP_L = prove
 (`!top atlas a b (g:real->A->real^3^3) m p tau (gamma:real->A) U (phi:A->real^3)
    s0 sa sb s3 A w k (gamma':real->A).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < sa /\ sa < sb /\ sb < s3 /\ s3 pow 2 <= tau /\
     (!s. s0 <= s /\ s <= s3 ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift s3] /\
     (!s. s0 < s /\ s < s3
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     &0 < k /\ &0 < sb - k * (sb - sa) /\
     (!s. sa <= s /\ s <= sb
          ==> phi(gamma(s pow 2)) + ((sb - s) / (sb - sa)) % w IN IMAGE phi U) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
             ((sb - k * (sb - sa)) pow 2) gamma' /\
     gamma'((sb - k * (sb - sa)) pow 2) = chart_inv (U,phi) (phi(gamma(sa pow 2)) + w)
     ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (sb pow 2)
                (gamma(sb pow 2)) <=
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma'
                      ((sb - k * (sb - sa)) pow 2) +
         p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                (p2aw_lfam (\v. phi(gamma(drop v pow 2))) sa sb w k) (sb - k * (sb - sa)) sb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  ABBREV_TAC `sp = sb - k * (sb - sa)` THEN
  SUBGOAL_THEN `sp < sb /\ sb pow 2 < b - a /\ sb < sqrt(b - a) /\ sp pow 2 < sb pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sp < sb` ASSUME_TAC THENL
     [EXPAND_TAC "sp" THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> sb - x < sb`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sb pow 2 < b - a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `s3 pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sol = p2aw_lfam (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                              sa sb w k` THEN
  SUBGOAL_THEN
   `!r. s0 < sb + (r - sb) / k /\ sb + (r - sb) / k < s3
        ==> ((sol:real^1->real^3) has_vector_derivative
             (inv k % ((A:real^1->real^3)(lift(sb + (r - sb) / k)) - inv(sb - sa) % w)))
            (at (lift r))`
  (LABEL_TAC "SD") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sol" THEN MATCH_MP_TAC P2AW_LFAM_DERIV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. sp <= r /\ r <= sb
        ==> (sol:real^1->real^3) differentiable (at (lift r)) /\
            (\v. vector_derivative sol (at v)) continuous (at (lift r))`
  (LABEL_TAC "SC1") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AW_VDERIV_CONT_OPEN THEN
    EXISTS_TAC `\v:real^1. inv k % ((A:real^1->real^3) (lift(sb + (drop v - sb) / k)) -
                                    inv(sb - sa) % w)` THEN
    EXISTS_TAC `interval(lift(sb - k * (sb - s0)),lift(sb + k * (s3 - sb)))` THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 < k * (sb - s0) /\ &0 < k * (s3 - sb) /\ k * (sb - sa) < k * (sb - s0)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
      TRY(MATCH_MP_TAC REAL_LT_LMUL) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `v:real` THEN
      STRIP_TAC THEN USE_THEN "SD" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_ARITH
        `s0 < sb + x <=> --(sb - s0) < x`; REAL_ARITH `sb + x < s3 <=> x < s3 - sb`] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
      REWRITE_TAC[CONTINUOUS_CONST] THEN
      SUBGOAL_THEN `(\v:real^1. (A:real^1->real^3) (lift(sb + (drop v - sb) / k))) =
                    A o (\v. lift(sb + (drop v - sb) / k))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
        EXISTS_TAC `lift(inv k)` THEN REWRITE_TAC[P2AW_REPAR_VDERIV];
        REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
        EXISTS_TAC `interval[lift s0,lift s3]` THEN
        ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
        SUBGOAL_THEN `&0 <= (r - sb) / k + (sb - sa) /\ (r - sb) / k <= &0` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC(REAL_ARITH `--(sb - sa) <= x ==> &0 <= x + (sb - sa)`) THEN
            ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. sp <= r /\ r <= sb
        ==> (sol:real^1->real^3)(lift r) IN IMAGE (phi:A->real^3) (U INTER U)`
  (LABEL_TAC "SIN") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN
    REWRITE_TAC[p2aw_lfam; LIFT_DROP; INTER_IDEMPOT] THEN
    SUBGOAL_THEN `(sb - r) / (k * (sb - sa)) = (sb - (sb - (sb - r) / k)) / (sb - sa)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `sa < sb` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
      can (find_term ((=) `w:real^3`)) (concl th))) THEN
    SUBGOAL_THEN `&0 <= (sb - r) / k /\ (sb - r) / k <= sb - sa` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
      EXPAND_TAC "sp" THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`;
                 `sol:real^1->real^3`; `sp:real`; `sb:real`; `&0`; `sqrt(b - a)`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2 /\ &0 < s pow 2` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(b - a) pow 2 = b - a` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "SIN" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "SC1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift sp) = phi((gamma:real->A)(sa pow 2)) + w /\
                sol(lift sb) = phi(gamma(sb pow 2))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sol" THEN EXPAND_TAC "sp" THEN
    MP_TAC(ISPECL [`\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                   `sa:real`; `sb:real`; `w:real^3`; `k:real`] P2AW_LFAM_ENDS) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sp /\ sqrt(sp pow 2) = sp /\ sqrt(sb pow 2) = sb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "sp" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN EXPAND_TAC "sp" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `p:A`;
                 `\tau. chart_inv (U,phi:A->real^3) ((sol:real^1->real^3)(lift(sqrt tau)))`;
                 `gamma':real->A`;
                 `\tau. if tau <= sp pow 2 then (gamma':real->A) tau
                        else chart_inv (U,phi:A->real^3) ((sol:real^1->real^3)(lift(sqrt tau)))`;
                 `sb pow 2`; `sp pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[p2a_min];
      SIMP_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `t = sp pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `sb pow 2`;
                 `\tau. if tau <= sp pow 2 then (gamma':real->A) tau
                        else chart_inv (U,phi:A->real^3) ((sol:real^1->real^3)(lift(sqrt tau)))`]
                P2AW_FLOW_LX_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(sb pow 2 <= sp pow 2)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `chart_inv (U,phi) ((phi:A->real^3)((gamma:real->A)(sb pow 2))) = gamma(sb pow 2)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `s3:real`)) (concl th) &&
      can (find_term ((=) `U:A->bool`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
             (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> l <= x ==> l <= y`) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The lower barrier at an interior point of a minimizer in the (w, k)       *)
(* coordinates of the left family: for an interior segment [sa, sb] of the   *)
(* chart curve and minimizers to every point (FL2 as a hypothesis), L at the *)
(* start point (phi(gamma(sa^2)) + w, (sb - k (sb - sa))^2) is at least      *)
(* L(gamma(sa^2), sa^2) plus the first variation minus C (|k - 1| + |w|)^2.  *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_PT_LBAR = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s0 sa sb s3 A.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!q t. q IN topspace top /\ &0 < t /\ t < b - a
            ==> ?gm. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p t gm /\
                     gm t = q) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < sa /\ sa < sb /\ sb < s3 /\ s3 pow 2 <= tau /\
     (!s. s0 <= s /\ s <= s3 ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift s3] /\
     (!s. s0 < s /\ s < s3
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     (!s. s0 <= s /\ s <= s3
          ==> (A has_vector_derivative
                 p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      U b (U,phi)) b s
                          (phi(gamma(s pow 2))) (A(lift s)))
              (at (lift s) within interval[lift s0,lift s3]))
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d
                 ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (sa pow 2)
                       (gamma(sa pow 2)) -
                     ((k - &1) *
                      ((sb - sa) *
                       (&2 * sa pow 2 * mfd_scalar atlas (g(b - sa pow 2)) (gamma(sa pow 2)) -
                        inv(&2) * (A(lift sa) dot
                                   (metric_local atlas (U,phi) (g(b - sa pow 2))
                                      (phi(gamma(sa pow 2))) ** A(lift sa))))) -
                      w dot (metric_local atlas (U,phi) (g(b - sa pow 2)) (phi(gamma(sa pow 2))) **
                             A(lift sa))) -
                     C * (abs(k - &1) + norm w) pow 2
                     <= p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                          ((sb - k * (sb - sa)) pow 2)
                          (chart_inv (U,phi) (phi(gamma(sa pow 2)) + w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "MINEX") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `sa pow 2 < sb pow 2 /\ sb pow 2 < s3 pow 2 /\ &0 < sa pow 2 /\
                sqrt(sb pow 2) = sb /\ sqrt(sa pow 2) = sa`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(sa pow 2) IN U /\ gamma(sb pow 2) IN U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `s3:real`)) (concl th) && can (find_term ((=) `U:A->bool`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
             (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`; `b - sa pow 2`;
                 `(gamma:real->A)(sa pow 2)`] P2AW_FLOW_RLOCAL_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi)`;
                 `b:real`; `\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`; `sa:real`; `sb:real`] P2AW_LOCAL_LBAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `s pow 2 <= s3 pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `s3:real`)) (concl th) &&
          can (find_term ((=) `U:A->bool`)) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
                 (concl th)))) THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift s0,lift s3]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
              (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2AW_VDERIV_INTERIOR THEN
        MAP_EVERY EXISTS_TAC [`s0:real`; `s3:real`] THEN
        REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
        ASM_REAL_ARITH_TAC]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LB")))))] THEN
  MAP_EVERY EXISTS_TAC [`min (min d (inv(&2))) (sa / (&2 * (sb - sa)))`; `C:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN] THEN
  SUBGOAL_THEN `&0 < inv(&2) /\ &0 < sa / (&2 * (sb - sa))` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^3`; `k:real`] THEN STRIP_TAC THEN
  USE_THEN "LB" (MP_TAC o SPECL [`w:real^3`; `k:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  ABBREV_TAC `sp = sb - k * (sb - sa)` THEN
  SUBGOAL_THEN `abs(k - &1) * (sb - sa) <= sa / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sa / (&2 * (sb - sa)) * (sb - sa)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `sa < sb` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k /\ &0 < sp /\ sp < sb` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(k - &1) * (sb - sa) <= abs(k - &1) * (sb - sa)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "sp" THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> sb - x < sb`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `phi((gamma:real->A)(sa pow 2)) + w IN IMAGE (phi:A->real^3) U`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `sa:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `w:real^3`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(sb - sa) / (sb - sa) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sp pow 2 < b - a /\ &0 < sp pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `s3 pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "MINEX" (MP_TAC o SPECL
    [`chart_inv (U,phi) ((phi:A->real^3)((gamma:real->A)(sa pow 2)) + w)`; `sp pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv (U,phi) ((phi:A->real^3)((gamma:real->A)(sa pow 2)) + w) IN U`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `phi:A->real^3`; `s0:real`; `sa:real`; `sb:real`; `s3:real`;
                 `A:real^1->real^3`; `w:real^3`; `k:real`; `gm:real->A`] P2AW_FLOW_CMP_L) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `w:real^3`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sp pow 2`; `gm:real->A`] P2A_MIN_LX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
            (sb pow 2) gamma /\
    p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (sa pow 2) gamma`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `tau:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `sb pow 2`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`; `sa:real`; `A:real^1->real^3`] P2AW_FLOW_CUT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s3:real`)) (concl th) && can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
               (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift s0,lift s3]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
            (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
            (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sb pow 2`; `gamma:real->A`] P2A_MIN_LX) THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sa pow 2`; `gamma:real->A`] P2A_MIN_LX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `abs(p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                         (g:real->A->real^3^3)) U b (U,phi)) b
                     (p2aw_lfam (\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) sa sb w k)
                     sp sb -
                   p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                             (U,phi)) b (\v. phi(gamma(drop v pow 2))) sa sb -
                   ((k - &1) *
                    ((sb - sa) *
                     (&2 * sa pow 2 *
                      lscalar (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                 (U,phi) (b - sa pow 2)) (phi(gamma(sa pow 2))) -
                      inv(&2) * ((A:real^1->real^3)(lift sa) dot
                                 (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                    U b (U,phi) (b - sa pow 2) (phi(gamma(sa pow 2))) **
                                  A(lift sa))))) -
                    w dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                             (U,phi) (b - sa pow 2) (phi(gamma(sa pow 2))) ** A(lift sa))))
               <= C * (abs(k - &1) + norm w) pow 2` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The lower barrier at an interior point (gamma s, s) of a                  *)
(* minimizer in space-time chart coordinates z = (x, s):                    *)
(*   L(z) + dL(h) - C |h|^2 <= L(z + h),                                    *)
(* dL as in P2AW_FLOW_PT_TOUCH (the upper barrier for the restricted        *)
(* minimizer), from P2AW_FLOW_PT_LBAR with k - 1 = -(sqrt(s + e) - sqrt s) *)
(* / (sb - sa) and the sqrt Taylor bound.                                   *)
(* ------------------------------------------------------------------------- *)

let P2AW_LOWER_ARITH = prove
 (`!f0 f1 k cfk cfw C D st st' dt nh nw tau.
     &0 < D /\ &0 < st /\ &0 < tau /\ &0 <= C /\
     f0 - ((k - &1) * cfk - cfw) - C * (abs(k - &1) + nw) pow 2 <= f1 /\
     k - &1 = --((st' - st) / D) /\
     abs(st' - st - dt / (&2 * st)) <= dt pow 2 / (&2 * tau * st) /\
     abs(k - &1) <= nh / (st * D) /\ &0 <= nw /\ nw <= nh /\ abs dt <= nh
     ==> f0 + (cfw + cfk / (&2 * st * D) * dt) -
         (abs cfk / D / (&2 * tau * st) + C * (inv(st * D) + &1) pow 2) * nh pow 2 <= f1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--f0:real`; `--f1:real`; `&2 - k`; `--cfk:real`; `--cfw:real`; `C:real`;
                `D:real`; `st:real`; `st':real`; `dt:real`; `nh:real`; `nw:real`; `tau:real`]
               P2AW_TOUCH_ARITH2) THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ARITH `abs((&2 - k) - &1) = abs(k - &1)`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `f0 - ((k - &1) * cfk - cfw) - C * (abs(k - &1) + nw) pow 2 <= f1` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `k - &1 = --((st' - st) / D)` THEN REAL_ARITH_TAC];
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let P2AW_FLOW_PT_LOWER = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s x.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!q t. q IN topspace top /\ &0 < t /\ t < b - a
            ==> ?gm. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p t gm /\
                     gm t = q) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s /\ s < tau /\ gamma s IN U /\ phi(gamma s) = x
     ==> ?A0 d C. ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A0) (at (lift(sqrt s))) /\
           &0 < d /\
           !h. norm h < d
               ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s
                     (chart_inv (U,phi) x) +
                   (fstcart h dot (metric_local atlas (U,phi) (g(b - s)) x ** A0) +
                    (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
                     A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) /
                    (&4 * sqrt s) * drop(sndcart h)) -
                   C * norm h pow 2
                   <= p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                        (drop(sndcart(pastecart x (lift s) + h)))
                        (chart_inv (U,phi) (fstcart(pastecart x (lift s) + h)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "MINEX") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U,phi) (x:real^3) = (gamma:real->A) s` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:A->real^3)((gamma:real->A) s) = x`)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `?ep. &0 < ep /\
                     !t. &0 <= t /\ t <= tau /\ abs(t - s) < ep ==> (gamma:real->A) t IN U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real`; `U:A->bool`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) (b - s) = top` SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t0 = s - min s ep / &2` THEN
  ABBREV_TAC `t3 = s + min (tau - s) ep / &2` THEN
  ABBREV_TAC `tb = (s + t3) / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < s /\ s < tb /\ tb < t3 /\ t3 < tau /\
                s - ep < t0 /\ t3 < s + ep`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tb"; "t3"; "t0"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s0 = sqrt t0` THEN ABBREV_TAC `sa = sqrt s` THEN
  ABBREV_TAC `sb = sqrt tb` THEN ABBREV_TAC `s3 = sqrt t3` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 < sa /\ sa < sb /\ sb < s3 /\
                s0 pow 2 = t0 /\ sa pow 2 = s /\ sb pow 2 = tb /\ s3 pow 2 = t3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s0"; "sa"; "sb"; "s3"] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sa` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. s0 <= r /\ r <= s3 ==> (gamma:real->A)(r pow 2) IN U` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `t0 <= r pow 2 /\ r pow 2 <= t3` MP_TAC THENL
     [MAP_EVERY (fun t -> FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = t)))
        [`s0 pow 2 = t0`; `s3 pow 2 = t3`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p t3 gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt t3 = s3` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `t3:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`] P2AW_FLOW_MIN_CHART) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `t3:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`; `sa:real`; `sb:real`; `s3:real`;
                 `A:real^1->real^3`] P2AW_FLOW_PT_LBAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `C1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LB"))))) THEN
  SUBGOAL_THEN `&0 < sb - sa /\ &0 < sa * (sb - sa)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `cfk0 = (sb - sa) *
           (&2 * s * mfd_scalar atlas ((g:real->A->real^3^3)(b - s)) (gamma s) -
            inv(&2) * ((A:real^1->real^3)(lift sa) dot
                       (metric_local atlas (U,phi) (g(b - s)) x ** A(lift sa))))` THEN
  MAP_EVERY EXISTS_TAC
   [`(A:real^1->real^3)(lift sa)`; `min (min d1 (sa * (sb - sa) * d1)) s`;
    `abs cfk0 / (sb - sa) / (&2 * s * sa) + C1 * (inv(sa * (sb - sa)) + &1) pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "sa" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
          (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^(3,1)finite_sum` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_LT_MIN]) THEN
  REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_PASTECART; SNDCART_PASTECART; DROP_ADD;
              LIFT_DROP] THEN
  SUBGOAL_THEN `norm(fstcart(h:real^(3,1)finite_sum)) <= norm h /\
                abs(drop(sndcart h)) <= norm h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_FSTCART; ABS_DROP; NORM_SNDCART]; ALL_TAC] THEN
  ABBREV_TAC `w = fstcart(h:real^(3,1)finite_sum)` THEN
  ABBREV_TAC `e = drop(sndcart(h:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `&0 <= s + e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = &1 - (sqrt(s + e) - sa) / (sb - sa)` THEN
  SUBGOAL_THEN `sb - k * (sb - sa) = sqrt(s + e)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN UNDISCH_TAC `&0 < sb - sa` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt(s + e) - sa) <= abs e / sa` ASSUME_TAC THENL
   [EXPAND_TAC "sa" THEN
    MP_TAC(ISPECL [`s:real`; `s + e`; `s:real`] P2AW_SQRT_DIFF_LE) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `(s + e) - s = e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(k - &1) <= norm(h:real^(3,1)finite_sum) / (sa * (sb - sa))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `k - &1 = --((sqrt(s + e) - sa) / (sb - sa))` SUBST1_TAC THENL
     [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `norm(h:real^(3,1)finite_sum) / (sa * (sb - sa)) =
                  (norm h / sa) / (sb - sa)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs e / sa` THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(h:real^(3,1)finite_sum) / (sa * (sb - sa)) < d1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "LB" (MP_TAC o SPECL [`w:real^3`; `k:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real`; `s + e`] P2AW_SQRT_TAYLOR) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(s + e) - s = e`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p s
           ((gamma:real->A) s)`;
    `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
           (s + e) (chart_inv (U,phi) ((x:real^3) + w))`;
    `k:real`; `cfk0:real`;
    `w dot (metric_local atlas (U,phi) ((g:real->A->real^3^3)(b - s)) x **
            (A:real^1->real^3)(lift sa))`;
    `C1:real`; `sb - sa`; `sa:real`; `sqrt(s + e)`; `e:real`;
    `norm(h:real^(3,1)finite_sum)`; `norm(w:real^3)`; `s:real`] P2AW_LOWER_ARITH) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN EXPAND_TAC "k" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cfk0 / (&2 * sa * (sb - sa)) =
    (&4 * s * mfd_scalar atlas ((g:real->A->real^3^3)(b - s)) (gamma s) -
     (A:real^1->real^3)(lift sa) dot
     (metric_local atlas (U,phi) (g(b - s)) x ** A(lift sa))) / (&4 * sa)`
  SUBST1_TAC THENL
   [EXPAND_TAC "cfk0" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < sb - sa`; `&0 < sa`] THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Differentiability of L at an interior point of a minimizer (squeezed      *)
(* between P2AW_FLOW_PT_TOUCH for the restricted minimizer and               *)
(* P2AW_FLOW_PT_LOWER), in space-time chart coordinates (x, s).              *)
(* ------------------------------------------------------------------------- *)

let P2AW_SQUEEZE_DIFF = prove
 (`!(f:real^M->real) (l:real^M->real^1) x d C.
     linear l /\ &0 < d /\
     (!h. norm h < d ==> abs(f(x + h) - f x - drop(l h)) <= C * norm h pow 2)
     ==> ((\y. lift(f y)) has_derivative l) (at x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min d (e / (abs C + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^M` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y - x:real^M`) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x + (y - x):real^M = y`] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM LIFT_SUB; GSYM DROP_SUB; NORM_LIFT] THEN
  SUBGOAL_THEN `(l:real^M->real^1)(y - x) = lift(drop(l(y - x)))` SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * norm(y - x:real^M) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= norm(y - x:real^M) /\ (abs C + &1) * norm(y - x) <= e` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `norm(y - x:real^M) <= e / (abs C + &1)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < abs C + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((abs C + &1) * norm(y - x:real^M)) * norm(y - x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let P2AW_FLOW_LX_INTERIOR_DIFF = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s x.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!q t. q IN topspace top /\ &0 < t /\ t < b - a
            ==> ?gm. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p t gm /\
                     gm t = q) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s /\ s < tau /\ gamma s IN U /\ phi(gamma s) = x
     ==> ?A0. ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A0) (at (lift(sqrt s))) /\
              ((\z. lift(p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                (drop(sndcart z)) (chart_inv (U,phi) (fstcart z))))
               has_derivative
               (\h. lift(fstcart h dot (metric_local atlas (U,phi) (g(b - s)) x ** A0) +
                         (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
                          A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) /
                         (&4 * sqrt s) * drop(sndcart h))))
              (at (pastecart x (lift s)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP P2AW_FLOW_PT_LOWER th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3` (X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `C1:real`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (phi:A->real^3) U /\ (gamma:real->A) s = chart_inv (U,phi) x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(phi:A->real^3)((gamma:real->A) s) = x`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(phi:A->real^3)((gamma:real->A) s) = x`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p s gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `x:real^3`] P2AW_FLOW_PT_TOUCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `A1:real^3` (X_CHOOSE_THEN `d2:real`
    (X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `A1:real^3 = A0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`; `lift s0`;
                          `lift(sqrt s)`; `lift(sqrt s)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; HAS_VECTOR_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  EXISTS_TAC `A0:real^3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AW_SQUEEZE_DIFF THEN
  MAP_EVERY EXISTS_TAC [`min d1 d2`; `max C1 C2`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL; DROP_ADD;
                DROP_CMUL; DOT_LADD; DOT_LMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `h:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  REWRITE_TAC[LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^(3,1)finite_sum` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `C2:real`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^(3,1)finite_sum` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `C1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= norm(h:real^(3,1)finite_sum) pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `C1 * norm(h:real^(3,1)finite_sum) pow 2 <= max C1 C2 * norm h pow 2 /\
                C2 * norm h pow 2 <= max C1 C2 * norm h pow 2`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* FL9 (P2A_FLOW_MIN_GRAD_STATEMENT) at N = 3 from FL2. (i) 2 sqrt(s)        *)
(* l(gamma s, s) is the integral over [0, s] of the L-integrand (restriction *)
(* of minimizers, locality of the integrand); (ii) at 0 < s < tau, l is      *)
(* differentiable in (time, chart coordinates) of chart_at atlas (gamma s),  *)
(* and its spatial derivative is v . G w with v the velocity of the chart    *)
(* curve, from P2AW_FLOW_LX_INTERIOR_DIFF.                                   *)
(* ------------------------------------------------------------------------- *)

let P2AW_PARTIAL_FST = prove
 (`!(Fm:real^(M,N)finite_sum->real^P) (G:real^M->real^P) c Z0.
     Fm differentiable (at (pastecart Z0 c)) /\ (!Z. Fm(pastecart Z c) = G Z)
     ==> (G has_derivative
          (\v. frechet_derivative Fm (at (pastecart Z0 c)) (pastecart v (vec 0)))) (at Z0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^M->real^P) = (Fm:real^(M,N)finite_sum->real^P) o (\Z. pastecart Z c)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. frechet_derivative (Fm:real^(M,N)finite_sum->real^P) (at (pastecart Z0 c))
           (pastecart v (vec 0))) =
    frechet_derivative Fm (at (pastecart Z0 c)) o (\v:real^M. pastecart v (vec 0:real^N))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    BETA_TAC THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2AW_FL9_INTEGRAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b (gamma:real->A) s.
     p2a_min V tt x b gamma /\ &0 < s /\ s <= b
     ==> &2 * sqrt s * p2a_lx V tt x s (gamma s) =
         real_integral (real_interval[&0,s]) (p2a_L_integrand V tt gamma b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) tt x s gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * sqrt s * p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) tt x s ((gamma:real->A) s) =
                p2a_Lx V tt x s (gamma s)` SUBST1_TAC THENL
   [REWRITE_TAC[p2a_lx] THEN SUBGOAL_THEN `&0 < sqrt s` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2A_MIN_LX] THEN REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) tt (gamma:real->A) s`;
                 `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) tt (gamma:real->A) b`;
                 `&0`; `s:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`&0`; `s:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let P2AW_FL9_POINT = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) s.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\
     (!q t. q IN topspace top /\ &0 < t /\ t < b - a
            ==> ?gm. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p t gm /\
                     gm t = q) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s /\ s < tau
     ==> (?d1. ((\z. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                 b p (drop(fstcart z))
                                 (chart_inv (chart_at atlas (gamma s)) (sndcart z))))
                has_derivative d1)
               (at (pastecart (lift s) (SND(chart_at atlas (gamma s)) (gamma s))))) /\
         (?v. ((\r. SND(chart_at atlas (gamma s)) (gamma(drop r))) has_vector_derivative v)
                (at (lift s)) /\
              ((\y. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                b p s (chart_inv (chart_at atlas (gamma s)) y)))
               has_derivative
               (\w. lift(v dot
                         (metric_local atlas (chart_at atlas (gamma s)) (g(b - s))
                            (SND(chart_at atlas (gamma s)) (gamma s)) ** w))))
              (at (SND(chart_at atlas (gamma s)) (gamma s))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) (b - s) = top` SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(gamma:real->A) s`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((gamma:real->A) s)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  ABBREV_TAC `x = (phi:A->real^3)((gamma:real->A) s)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s:real`; `x:real^3`] P2AW_FLOW_LX_INTERIOR_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `Fl = \z:real^(3,1)finite_sum.
           lift(p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                       b p (drop(sndcart z)) (chart_inv (U,phi:A->real^3) (fstcart z)))` THEN
  SUBGOAL_THEN `&0 < sqrt s` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM differentiable] THEN
    SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum.
         lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                     b p (drop(fstcart z)) (chart_inv (U,phi:A->real^3) (sndcart z)))) =
      (\w:real^(3,1)finite_sum.
         inv(&2 * sqrt(drop(sndcart w))) % (Fl:real^(3,1)finite_sum->real^1) w) o
      (\z:real^(1,3)finite_sum. pastecart (sndcart z) (fstcart z))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fl" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; p2a_lx] THEN
      REWRITE_TAC[real_div; GSYM LIFT_CMUL; REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN
      REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                  PASTECART_ADD; GSYM PASTECART_CMUL];
      ALL_TAC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[differentiable] THEN EXISTS_TAC
       `\h:real^(3,1)finite_sum.
          lift(fstcart h dot (metric_local atlas (U,phi:A->real^3) ((g:real->A->real^3^3)(b - s))
                                x ** A0) +
               (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
                A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) / (&4 * sqrt s) *
               drop(sndcart h))` THEN
      EXPAND_TAC "Fl" THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `lift o (\w:real^(3,1)finite_sum. inv(&2 * sqrt(drop(sndcart w)))) =
      (lift o inv o drop) o (lift o (\w. &2 * sqrt(drop(sndcart w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `lift o (\h. inv(sqrt(drop(sndcart(pastecart (x:real^3) (lift s))))) *
                             drop(sndcart(h:real^(3,1)finite_sum)))` THEN
      MATCH_MP_TAC P2AW_SQRT_SNDCART_DERIV THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP];
      REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. --(inv(drop((lift o (\w:real^(3,1)finite_sum.
                                    &2 * sqrt(drop(sndcart w))))
                                  (pastecart (x:real^3) (lift s))) pow 2)) % h` THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LIFT_INV THEN
      REWRITE_TAC[o_THM; LIFT_DROP; SNDCART_PASTECART] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `inv(&2 * sqrt s) % (A0:real^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC
     [`(\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) o
       (\r:real^1. lift(sqrt(drop r)))`; `s:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; DIST_LIFT; o_THM; LIFT_DROP] THEN X_GEN_TAC `r:real` THEN
      DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * sqrt s) % (A0:real^3) = drop(lift(inv(&2 * sqrt s))) % A0`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(SPEC `s:real` HAS_REAL_DERIVATIVE_SQRT) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM];
      ASM_REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                     b p s (chart_inv (U,phi:A->real^3) y))) =
    (\y. inv(&2 * sqrt s) % (Fl:real^(3,1)finite_sum->real^1) (pastecart y (lift s)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fl" THEN
    REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; p2a_lx] THEN
    REWRITE_TAC[real_div; GSYM LIFT_CMUL; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w:real^3. lift((inv(&2 * sqrt s) % A0) dot
                      (metric_local atlas (U,phi:A->real^3) ((g:real->A->real^3^3)(b - s)) x **
                       w))) =
    (\w. inv(&2 * sqrt s) %
         lift(fstcart(pastecart w (vec 0:real^1)) dot
              (metric_local atlas (U,phi) (g(b - s)) x ** A0) +
              (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
               A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) / (&4 * sqrt s) *
              drop(sndcart(pastecart w (vec 0:real^1)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; REAL_MUL_RZERO;
                REAL_ADD_RID; GSYM LIFT_CMUL; LIFT_EQ; DOT_LMUL] THEN
    X_GEN_TAC `w:real^3` THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `transp(metric_local atlas (U,phi:A->real^3) ((g:real->A->real^3^3)(b - s)) x) =
                  metric_local atlas (U,phi) (g(b - s)) x` ASSUME_TAC THENL
     [MP_TAC(SPEC `b - s` (CONJUNCT2 (MATCH_MP P2AW_CBFLOW_METRICS
        (ASSUME `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)`)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND] THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "x" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM DOT_LMUL_MATRIX] THEN
    ASM_REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP] THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL [`Fl:real^(3,1)finite_sum->real^1`; `\y:real^3. (Fl:real^(3,1)finite_sum->real^1)
                                                              (pastecart y (lift s))`;
                 `lift s`; `x:real^3`] P2AW_PARTIAL_FST) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC
     `\h:real^(3,1)finite_sum.
        lift(fstcart h dot (metric_local atlas (U,phi:A->real^3) ((g:real->A->real^3^3)(b - s))
                              x ** A0) +
             (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
              A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) / (&4 * sqrt s) *
             drop(sndcart h))` THEN
    EXPAND_TAC "Fl" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Fl:real^(3,1)finite_sum->real^1) (at (pastecart x (lift s))) =
    (\h:real^(3,1)finite_sum.
        lift(fstcart h dot (metric_local atlas (U,phi:A->real^3) ((g:real->A->real^3^3)(b - s))
                              x ** A0) +
             (&4 * s * mfd_scalar atlas (g(b - s)) (chart_inv (U,phi) x) -
              A0 dot (metric_local atlas (U,phi) (g(b - s)) x ** A0)) / (&4 * sqrt s) *
             drop(sndcart h)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    EXPAND_TAC "Fl" THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN SIMP_TAC[]]);;

let P2AW_FL9_FROM_FL2 = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n ==> P2A_FLOW_MIN_GRAD_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2A_FLOW_MIN_EXISTS_STATEMENT; P2A_FLOW_MIN_GRAD_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`; `q:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!q' t. q' IN topspace top /\ &0 < t /\ t < b - a
           ==> ?gm. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                               (g:real->A->real^3^3)) b (p:A) t gm /\ gm t = q'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                    b (p:A) tau gamma /\ gamma tau = (q:A)`
  MP_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC P2AW_FL9_INTEGRAL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AW_FL9_POINT THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[]]);;


