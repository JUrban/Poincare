(* ========================================================================= *)
(* Unit pc_sch_b1canc: the shear that cancels the saddle with the cap tip,   *)
(* part H3 of the one-saddle base case of the smooth Schoenflies induction   *)
(* (H1 pc_sch_b1cls, H2 pc_sch_b1chart, H3 this unit, H4 pc_sch_base1).      *)
(* One-dimensional smooth max, the two-dimensional no-critical-point lemma,  *)
(* the vertical shear and the flow box of a field with third component 1,    *)
(* the shear field, the strip through the saddle and the tip, single         *)
(* sheetedness, and the shear (SCHY_CANCEL_SHEAR_THM).                       *)
(* ========================================================================= *)

needs "src/pc_sch_b1chart.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The one-dimensional smooth max.  With x = (phi - l)/2 and                 *)
(* eta(x) = sqrt(x^2 + eps^2) - x, psi = phi + chi * eta(x) is a smooth      *)
(* decreasing function above phi when the line l = A - c t lies above the   *)
(* part where phi increases and below phi near the two ends.                 *)
(* ------------------------------------------------------------------------- *)

let schy_eta = new_definition
 `schy_eta (eps:real) (x:real) = sqrt(x pow 2 + eps pow 2) - x`;;

let SCHY_ETA_FACTS = prove
 (`!eps x. ~(eps = &0)
           ==> &0 < sqrt(x pow 2 + eps pow 2) /\
               sqrt(x pow 2 + eps pow 2) pow 2 = x pow 2 + eps pow 2 /\
               abs x < sqrt(x pow 2 + eps pow 2) /\
               &0 < schy_eta eps x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x pow 2 + eps pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs x < sqrt(x pow 2 + eps pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_ABS] THEN
    SUBGOAL_THEN `abs(sqrt(x pow 2 + eps pow 2)) = sqrt(x pow 2 + eps pow 2)` (fun th ->
      GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; SQRT_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; schy_eta] THEN ASM_REAL_ARITH_TAC);;

let SCHY_ETA_DERIV = prove
 (`!eps x. ~(eps = &0)
           ==> (schy_eta eps has_real_derivative
                (x / sqrt(x pow 2 + eps pow 2) - &1)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `x:real`] SCHY_ETA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_eta eps = (\x. sqrt(x pow 2 + eps pow 2) - x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_eta]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x pow 2 + eps pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 < eps pow 2` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  UNDISCH_TAC `&0 < sqrt(x pow 2 + eps pow 2)` THEN CONV_TAC REAL_FIELD);;

let SCHY_ETA_BOUNDS = prove
 (`!eps x d0.
     ~(eps = &0) /\ &0 < d0
     ==> abs(x / sqrt(x pow 2 + eps pow 2)) < &1 /\
         (d0 <= x ==> schy_eta eps x <= eps pow 2 / (&2 * d0) /\
                      &1 - x / sqrt(x pow 2 + eps pow 2) <= eps pow 2 / (&2 * d0 pow 2)) /\
         (x <= --d0 ==> &1 + x / sqrt(x pow 2 + eps pow 2) <= eps pow 2 / (&2 * d0 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `x:real`] SCHY_ETA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = sqrt(x pow 2 + eps pow 2)` THEN
  SUBGOAL_THEN `(s - x) * (s + x) = eps pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `s pow 2 = x pow 2 + eps pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * d0 /\ &0 < &2 * d0 pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < x ==> &0 < &2 * x`]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < s ==> abs s = s`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN REWRITE_TAC[schy_eta] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `(s - x) * (&2 * d0) <= (s - x) * (s + x)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(s - x) * (s + x) = eps pow 2` THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];
      SUBGOAL_THEN `&1 - x / s = (s - x) / s` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      UNDISCH_TAC `(s - x) * (s + x) = eps pow 2` THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      SUBGOAL_THEN `(s - x) * (&2 * d0 pow 2) <= (s - x) * (s * (s + x))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `d * d <= s * x /\ d * d <= s * s ==> &2 * (d * d) <= s * (s + x)`) THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 + x / s = (s + x) / s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `(s - x) * (s + x) = eps pow 2` THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `(s + x) * (&2 * d0 pow 2) <= (s + x) * (s * (s - x))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `d * d <= s * --x /\ d * d <= s * s ==> &2 * (d * d) <= s * (s - x)`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let SCHY_PSI_NEG = prove
 (`!eps d0 c P Q bb p1 k k1 x.
     ~(eps = &0) /\ &0 < d0 /\ &0 < c /\ &0 <= P /\ &0 <= Q /\ &0 < bb /\
     (eps pow 2 / (&2 * d0 pow 2)) * P < c /\
     Q * (eps pow 2 / (&2 * d0)) + (eps pow 2 / (&2 * d0 pow 2)) * (P + c) / &2 < bb /\
     abs p1 <= P /\ &0 <= k /\ k <= &1 /\ abs k1 <= Q /\
     ((k = &1 /\ k1 = &0 /\ (p1 < &0 \/ x <= --d0)) \/ (d0 <= x /\ p1 <= --bb))
     ==> p1 + k1 * schy_eta eps x +
         k * (x / sqrt(x pow 2 + eps pow 2) - &1) * (p1 + c) / &2 < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    MP_TAC)))))))))))) THEN
  MP_TAC(SPECL [`eps:real`; `x:real`; `d0:real`] SCHY_ETA_BOUNDS) THEN
  MP_TAC(SPECL [`eps:real`; `x:real`] SCHY_ETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = x / sqrt(x pow 2 + eps pow 2)` THEN
  ABBREV_TAC `et = schy_eta eps x` THEN
  ABBREV_TAC `ep = eps pow 2 / (&2 * d0 pow 2)` THEN
  ABBREV_TAC `eq = eps pow 2 / (&2 * d0)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "UP") (LABEL_TAC "LO"))) THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < (&1 - m) * c /\ &0 <= (&1 + m) * --p1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
    USE_THEN "LO" (fun th -> MP_TAC(MP th (ASSUME `x <= --d0`))) THEN DISCH_TAC THEN
    SUBGOAL_THEN `m <= &0` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + m) * p1 <= ep * P /\ c <= (&1 - m) * c` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + m) * abs p1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `ep * P < c` THEN REAL_ARITH_TAC];
    USE_THEN "UP" (fun th -> MP_TAC(MP th (ASSUME `d0 <= x`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(k1 * et) <= Q * eq` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(k * (m - &1) * (p1 + c) / &2) <= ep * (P + c) / &2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= k ==> abs k = k`;
                   REAL_ARITH `abs m < &1 ==> abs(m - &1) = &1 - m`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`abs(k1 * et) <= Q * eq`; `abs(k * (m - &1) * (p1 + c) / &2) <= ep * (P + c) / &2`;
      `Q * eq + ep * (P + c) / &2 < bb`; `p1 <= --bb`] THEN
    REAL_ARITH_TAC]);;

let SCHY_PSI_DERIV = prove
 (`!(phi:real->real) chi eps A c p1 k1 t.
     ~(eps = &0) /\
     (phi has_real_derivative p1) (atreal t) /\ (chi has_real_derivative k1) (atreal t)
     ==> ((\t. phi t + chi t * schy_eta eps ((phi t - (A - c * t)) / &2)) has_real_derivative
          (p1 + k1 * schy_eta eps ((phi t - (A - c * t)) / &2) +
           chi t * ((phi t - (A - c * t)) / &2 /
                    sqrt(((phi t - (A - c * t)) / &2) pow 2 + eps pow 2) - &1) *
           (p1 + c) / &2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\t. (phi t - (A - c * t)) / &2) has_real_derivative ((p1 + c) / &2)) (atreal t)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\t. ((phi:real->real) t - (A - c * t)) / &2) =
                  (\t. inv(&2) * (phi t - (A - c * t)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(p1 + c) / &2 = inv(&2) * (p1 - --c)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
    REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t. schy_eta eps ((phi t - (A - c * t)) / &2)) has_real_derivative
                 ((p1 + c) / &2 * (((phi t - (A - c * t)) / &2) /
                   sqrt(((phi t - (A - c * t)) / &2) pow 2 + eps pow 2) - &1))) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. ((phi:real->real) t - (A - c * t)) / &2`; `schy_eta eps`;
                   `(p1 + c) / &2`;
                   `((phi:real->real) t - (A - c * t)) / &2 /
                    sqrt((((phi:real->real) t - (A - c * t)) / &2) pow 2 + eps pow 2) - &1`;
                   `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        BETA_TAC THEN MATCH_MP_TAC SCHY_ETA_DERIV THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `p1:real`;
                 `\t. (chi:real->real) t * schy_eta eps ((phi t - (A - c * t)) / &2)`;
                 `k1 * schy_eta eps ((phi t - (A - c * t)) / &2) +
                  (chi:real->real) t * (p1 + c) / &2 *
                  (((phi t - (A - c * t)) / &2) /
                   sqrt(((phi t - (A - c * t)) / &2) pow 2 + eps pow 2) - &1)`;
                 `atreal t`] HAS_REAL_DERIVATIVE_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`chi:real->real`; `k1:real`;
                   `\t. schy_eta eps (((phi:real->real) t - (A - c * t)) / &2)`;
                   `(p1 + c) / &2 * (((phi t - (A - c * t)) / &2) /
                     sqrt((((phi:real->real) t - (A - c * t)) / &2) pow 2 + eps pow 2) - &1)`;
                   `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    BETA_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The two-dimensional no-critical-point lemma.  On a strip                  *)
(* with coordinates (t,w), if F has a strict ridge along w = 0 and           *)
(* beta(w) rho(t) is added with rho >= 0, beta' <= 0 for w > 0, beta' >= 0   *)
(* for w < 0, beta(0) = 1, beta'(0) = 0 and d/dt (F(t,0) + rho t) < 0, then  *)
(* G = F + beta rho has no critical point.                                  *)
(* ------------------------------------------------------------------------- *)

let SCHY_COMP_DERIV = prove
 (`!(f:real->real) f' (z:real^N) i.
     1 <= i /\ i <= dimindex(:N) /\ (f has_real_derivative f') (atreal (z$i))
     ==> ((\z:real^N. lift(f(z$i))) has_derivative (\h. lift(f' * h$i))) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^N. lift(f(z$i))) = (lift o f o drop) o (\z. lift(z$i))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^N. lift(f' * h$i)) = (\x. f' % x) o (\h. lift(h$i))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_SIMP_TAC[LINEAR_LIFT_COMPONENT];
    REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN ASM_REWRITE_TAC[]]);;

let SCHY_GSUM_DERIV = prove
 (`!(Fh:real^2->real) DF beta b1 rho r1 (z:real^2).
     ((\z. lift(Fh z)) has_derivative DF) (at z) /\
     (beta has_real_derivative b1) (atreal (z$2)) /\
     (rho has_real_derivative r1) (atreal (z$1))
     ==> ((\z. lift(Fh z + beta(z$2) * rho(z$1))) has_derivative
          (\h. DF h + lift(beta(z$2) * r1 * h$1 + b1 * h$2 * rho(z$1)))) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z:real^2. beta(z$2):real`; `\h:real^2. b1 * h$2`;
                 `\z:real^2. lift(rho(z$1))`; `\h:real^2. lift(r1 * h$1)`; `z:real^2`]
    HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SCHY_COMP_DERIV THEN
      ASM_REWRITE_TAC[DIMINDEX_2; ARITH];
      MATCH_MP_TAC SCHY_COMP_DERIV THEN ASM_REWRITE_TAC[DIMINDEX_2; ARITH]];
    BETA_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC]);;

let SCHY_2D_NOCRIT = prove
 (`!(Fh:real^2->real) DF beta b1 rho r1 (z:real^2).
     ((\z. lift(Fh z)) has_derivative DF) (at z) /\
     (beta has_real_derivative b1) (atreal (z$2)) /\
     (rho has_real_derivative r1) (atreal (z$1)) /\
     &0 <= rho(z$1) /\
     ((&0 < z$2 /\ drop(DF(basis 2)) < &0 /\ b1 <= &0) \/
      (z$2 < &0 /\ &0 < drop(DF(basis 2)) /\ &0 <= b1) \/
      (z$2 = &0 /\ beta(&0) = &1 /\ drop(DF(basis 1)) + r1 < &0))
     ==> ~(frechet_derivative (\z. lift(Fh z + beta(z$2) * rho(z$1))) (at z) = (\h. vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`Fh:real^2->real`; `DF:real^2->real^1`; `beta:real->real`; `b1:real`;
                 `rho:real->real`; `r1:real`; `z:real^2`] SCHY_GSUM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THENL
   [EXISTS_TAC `basis 2:real^2`;
    EXISTS_TAC `basis 2:real^2`;
    EXISTS_TAC `basis 1:real^2`] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH; GSYM DROP_EQ; DROP_ADD; LIFT_DROP; DROP_VEC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; REAL_ADD_LID; REAL_MUL_RID;
                  REAL_MUL_LID] THEN
  TRY(MATCH_MP_TAC(REAL_ARITH `a < &0 /\ b <= &0 ==> ~(a + b = &0)`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --b * r ==> b * r <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
  TRY(MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(a + b = &0)`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Vertical shears.  x -> x + tau(x) e3 is a diffeomorphism of               *)
(* R^3 when tau is smooth, vanishes off a compact set and d tau / d x3 > -1. *)
(* ------------------------------------------------------------------------- *)

let SCHY_D3 = new_definition
 `SCHY_D3 (tau:real^3->real) (x:real^3) =
    drop(frechet_derivative (\x. lift(tau x)) (at x) (basis 3))`;;

let SCHY_VSHEAR_DERIV = prove
 (`!(tau:real^3->real) x.
     (\x. lift(tau x)) differentiable (at x)
     ==> ((\x. x + tau x % basis 3) has_derivative
          (\h. h + drop(frechet_derivative (\x. lift(tau x)) (at x) h) % basis 3)) (at x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  SUBGOAL_THEN `(\x:real^3. tau x % basis 3:real^3) = (\t. drop t % basis 3) o (\x. lift(tau x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^3. drop(frechet_derivative (\x. lift((tau:real^3->real) x)) (at x) h) %
                             basis 3:real^3) =
                (\t. drop t % basis 3) o frechet_derivative (\x. lift(tau x)) (at x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MP_TAC(ISPECL [`\t:real^1. t`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
  REWRITE_TAC[LINEAR_ID]);;

let SCHY_VSHEAR_DET = prove
 (`!(L:real^3->real^1).
     det(matrix(\h:real^3. h + drop(L h) % basis 3)) = &1 + drop(L(basis 3))`,
  GEN_TAC THEN REWRITE_TAC[DET_3] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_3; ARITH; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let SCHY_VLINE_DERIV = prove
 (`!(tau:real^3->real) a b s.
     (\x. lift(tau x)) differentiable (at (vector[a; b; s]))
     ==> ((\s. s + tau(vector[a; b; s])) has_real_derivative
          (&1 + SCHY_D3 tau (vector[a; b; s]))) (atreal s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; SCHY_D3; LIFT_DROP] THEN
  SUBGOAL_THEN `(lift o (\s. (tau:real^3->real)(vector[a; b; s])) o drop) =
                (\x. lift(tau x)) o (\t:real^1. vector[a; b; drop t]:real^3)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\x. lift((tau:real^3->real) x)) o (\t:real^1. vector[a; b; drop t]:real^3))
     has_vector_derivative
     frechet_derivative (\x. lift(tau x))
       (at ((\t:real^1. vector[a; b; drop t]:real^3) (lift s))) (basis 3)) (at (lift s))`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[LIFT_DROP]] THEN
  MATCH_MP_TAC SCHY_CURVE_CHAIN THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `basis 3:real^3 = vector[&0; &0; &1]` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; BASIS_COMPONENT; ARITH]; ALL_TAC] THEN
  MATCH_MP_TAC SCHY_VDERIV3 THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX; HAS_VECTOR_DERIVATIVE_ID; LIFT_NUM; HAS_VECTOR_DERIVATIVE_CONST]);;

let SCHY_VSHEAR_DIFFEO = prove
 (`!(tau:real^3->real) L.
     smooth_map_on (:real^3) (\x. lift(tau x)) /\ compact L /\ (!x. ~(x IN L) ==> tau x = &0) /\
     (!x. -- &1 < SCHY_D3 tau x)
     ==> ?Phi'. diffeomorphism_on (:real^3) (:real^3) (\x. x + tau x % basis 3) Phi'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. (\x. lift((tau:real^3->real) x)) differentiable (at x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. !x. abs((tau:real^3->real) x) <= M` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact(IMAGE (\x. lift((tau:real^3->real) x)) L)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `M:real` THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN L` THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b s t. s < t ==> s + (tau:real^3->real)(vector[a; b; s]) <
                                    t + tau(vector[a; b; t])` (LABEL_TAC "INC") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\s. s + (tau:real^3->real)(vector[a; b; s])`;
                   `\s. &1 + SCHY_D3 (tau:real^3->real) (vector[a; b; s])`; `s:real`; `t:real`]
      HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC SCHY_VLINE_DERIV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `vector[a; b; u]:real^3` o check (fun th ->
        can (term_match [] `!x. -- &1 < SCHY_D3 tau x`) (concl th))) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x + (tau:real^3->real) x % basis 3 = y + tau y % basis 3 ==> x = y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(tau:real^3->real)(vector[(y:real^3)$1; y$2; (x:real^3)$3]) = tau x /\
                  (tau:real^3->real)(vector[(y:real^3)$1; y$2; (y:real^3)$3]) = tau y`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `~(a < b) /\ ~(b < a) ==> a = b`) THEN CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "INC" (fun th -> MP_TAC(MP (SPECL [`(y:real^3)$1`; `(y:real^3)$2`;
        `(x:real^3)$3`; `(y:real^3)$3`] th) (ASSUME `(x:real^3)$3 < (y:real^3)$3`)));
      USE_THEN "INC" (fun th -> MP_TAC(MP (SPECL [`(y:real^3)$1`; `(y:real^3)$2`;
        `(y:real^3)$3`; `(x:real^3)$3`] th) (ASSUME `(y:real^3)$3 < (x:real^3)$3`)))] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
      can (term_match [] `!x. abs((tau:real^3->real) x) <= M`) (concl th))) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ?x. x + (tau:real^3->real) x % basis 3 = y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN
    MP_TAC(ISPECL [`\s. s + (tau:real^3->real)(vector[(y:real^3)$1; y$2; s])`;
                   `(y:real^3)$3 - M - &1`; `(y:real^3)$3 + M + &1`; `(y:real^3)$3`]
      REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
        REWRITE_TAC[real_differentiable_on] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
        REWRITE_TAC[real_differentiable] THEN
        EXISTS_TAC `&1 + SCHY_D3 (tau:real^3->real) (vector[(y:real^3)$1; y$2; u])` THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MATCH_MP_TAC SCHY_VLINE_DERIV THEN ASM_REWRITE_TAC[];
        BETA_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `vector[(y:real^3)$1; y$2; y$3 - M - &1]:real^3` o check (fun th ->
          can (term_match [] `!x. abs((tau:real^3->real) x) <= M`) (concl th))) THEN
        REAL_ARITH_TAC;
        BETA_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `vector[(y:real^3)$1; y$2; y$3 + M + &1]:real^3` o check (fun th ->
          can (term_match [] `!x. abs((tau:real^3->real) x) <= M`) (concl th))) THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `vector[(y:real^3)$1; y$2; s]:real^3` THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; ARITH; VECTOR_3; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
      UNDISCH_TAC `(\s. s + (tau:real^3->real)(vector[(y:real^3)$1; y$2; s])) s = y$3` THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\x. x + (tau:real^3->real) x % basis 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    SUBGOAL_THEN `(\x:real^3. tau x % basis 3:real^3) = (\t. drop t % basis 3) o (\x. lift(tau x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC(ISPECL [`\t:real^1. t`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
    REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. x + (tau:real^3->real) x % basis 3`; `(:real^3)`] SCHI_INJ_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT
      (MATCH_MP SCHY_VSHEAR_DERIV (SPEC `x:real^3` th)))]) THEN
    REWRITE_TAC[SCHY_VSHEAR_DET] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (term_match [] `!x. -- &1 < SCHY_D3 tau x`) (concl th))) THEN
    REWRITE_TAC[SCHY_D3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  SUBGOAL_THEN `IMAGE (\x. x + (tau:real^3->real) x % basis 3) (:real^3) = (:real^3)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The flow box of a complete smooth field with third                        *)
(* component 1: Psi(y) = flow(y3)(y1,y2,0) is a diffeomorphism of R^3 with   *)
(* inverse x -> (P flow(-x3)(x), x3), and heights are preserved.            *)
(* ------------------------------------------------------------------------- *)

let schy_fbox = new_definition
 `schy_fbox (X:real^3->real^3) (y:real^3) =
    ode_vf_flow X (:real^3) (lift(y$3)) (vector[y$1; y$2; &0])`;;

let schy_fboxi = new_definition
 `schy_fboxi (X:real^3->real^3) (x:real^3) =
    vector[(ode_vf_flow X (:real^3) (lift(--(x$3))) x)$1;
           (ode_vf_flow X (:real^3) (lift(--(x$3))) x)$2; x$3]:real^3`;;

let SCHY_FLOW_LIN_SMOOTH = prove
 (`!(X:real^3->real^3) (A:real^3->real^1) (V:real^3->real^3).
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     linear A /\ linear V
     ==> smooth_map_on (:real^3) (\x. ode_vf_flow X (:real^3) (A x) (V x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  SUBGOAL_THEN `(\x:real^3. ode_vf_flow (X:real^3->real^3) (:real^3) (A x) (V x)) =
                (\w. ode_vf_flow X (:real^3) (fstcart w) (sndcart w)) o
                (\x. pastecart ((A:real^3->real^1) x) ((V:real^3->real^3) x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^(1,3)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC LINEAR_PASTECART THEN ASM_REWRITE_TAC[]);;

let SCHY_FBOX_DIFFEO = prove
 (`!X:real^3->real^3.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1)
     ==> diffeomorphism_on (:real^3) (:real^3) (schy_fbox X) (schy_fboxi X) /\
         (!y. (schy_fbox X y)$3 = y$3) /\ (!x. (schy_fboxi X x)$3 = x$3)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!y. (schy_fbox (X:real^3->real^3) y)$3 = y$3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schy_fbox; VECTOR_3; LIFT_DROP; REAL_ADD_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. (schy_fboxi (X:real^3->real^3) x)$3 = x$3` ASSUME_TAC THENL
   [REWRITE_TAC[schy_fboxi; VECTOR_3]; ALL_TAC] THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  SUBGOAL_THEN `!y. schy_fboxi (X:real^3->real^3) (schy_fbox X y) = y` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[schy_fboxi] THEN
    REWRITE_TAC[schy_fbox] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. schy_fbox (X:real^3->real^3) (schy_fboxi X x) = x` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[schy_fbox] THEN
    SUBGOAL_THEN `vector[(schy_fboxi (X:real^3->real^3) x)$1; (schy_fboxi X x)$2; &0]:real^3 =
                  ode_vf_flow X (:real^3) (lift(--(x$3))) x` SUBST1_TAC THENL
     [REWRITE_TAC[schy_fboxi; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3] THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM LIFT_ADD] THEN
    REWRITE_TAC[REAL_ADD_LINV; LIFT_NUM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `schy_fbox (X:real^3->real^3) =
                  (\y. ode_vf_flow X (:real^3) (lift(y$3)) (vector[y$1; y$2; &0]))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; schy_fbox]; ALL_TAC] THEN
    MP_TAC(ISPECL [`X:real^3->real^3`; `\y:real^3. lift(y$3)`;
                   `\y:real^3. vector[y$1; y$2; &0]:real^3`] SCHY_FLOW_LIN_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LINEAR_LIFT_COMPONENT];
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `schy_fboxi (X:real^3->real^3) =
                  (\x. vector[(ode_vf_flow X (:real^3) (lift(--(x$3))) x)$1;
                              (ode_vf_flow X (:real^3) (lift(--(x$3))) x)$2; x$3]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_fboxi]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:real^3)
                   (\x. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(--(x$3))) x)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`X:real^3->real^3`; `\y:real^3. lift(--(y$3))`; `\y:real^3. y`]
        SCHY_FLOW_LIN_SMOOTH) THEN
      ASM_REWRITE_TAC[LINEAR_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^3)`;
                   `\x. vector[(ode_vf_flow (X:real^3->real^3) (:real^3) (lift(--(x$3))) x)$1;
                               (ode_vf_flow X (:real^3) (lift(--(x$3))) x)$2; x$3]:real^3`]
      SMOOTH_MAP_ON_COMPONENTWISE) THEN
    REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]) THEN
    MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN REWRITE_TAC[OPEN_UNIV; LINEAR_LIFT_COMPONENT; LINEAR_ID]]);;

(* ------------------------------------------------------------------------- *)
(* The shear field.  X = e3 + kin (v - e3) where kin is a model              *)
(* cutoff (inside a thin layer around the cylinder, inner heights) read      *)
(* through the chart, times (1 - bump around lpt).                           *)
(* ------------------------------------------------------------------------- *)

let SCHY_SL_SSTEP = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(smooth_step(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCHY_SMOOTH_TAC =
  REPEAT(CHANGED_TAC SCH3_SMOOTH_TAC ORELSE (MATCH_MP_TAC SCHY_SL_SSTEP THEN REPEAT CONJ_TAC));;

let SCHY_UNIT_MUL = prove
 (`!a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1 ==> &0 <= a * b /\ a * b <= &1`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL];
    MATCH_MP_TAC(REAL_ARITH `a * b <= &1 * &1 ==> a * b <= &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]]);;

let schy_kmod = new_definition
 `schy_kmod (s1:real) (H:real) (y:real^3) =
    (&1 - smooth_step(((y$1 pow 2 + y$2 pow 2) - (&1 + s1)) / s1)) *
    (&1 - smooth_step((y$3 pow 2 - (H - &2) pow 2) / ((H - &1) pow 2 - (H - &2) pow 2)))`;;

let SCHY_KMOD_PROPS = prove
 (`!s1 H. &0 < s1 /\ &3 <= H
          ==> smooth_map_on (:real^3) (\y. lift(schy_kmod s1 H y)) /\
              (!y. &0 <= schy_kmod s1 H y /\ schy_kmod s1 H y <= &1) /\
              (!y. y$1 pow 2 + y$2 pow 2 <= &1 + s1 /\ y$3 pow 2 <= (H - &2) pow 2
                   ==> schy_kmod s1 H y = &1) /\
              (!y. &1 + &2 * s1 <= y$1 pow 2 + y$2 pow 2 \/ (H - &1) pow 2 <= y$3 pow 2
                   ==> schy_kmod s1 H y = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (H - &1) pow 2 - (H - &2) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
  REWRITE_TAC[schy_kmod] THEN REPEAT CONJ_TAC THENL
   [SCHY_SMOOTH_TAC THEN REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC SCHY_UNIT_MUL THEN
    MP_TAC(SPEC `(((y:real^3)$1 pow 2 + y$2 pow 2) - (&1 + s1)) / s1` SMOOTH_STEP_BOUNDS) THEN
    MP_TAC(SPEC `((y:real^3)$3 pow 2 - (H - &2) pow 2) / ((H - &1) pow 2 - (H - &2) pow 2)`
      SMOOTH_STEP_BOUNDS) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_step((((y:real^3)$1 pow 2 + y$2 pow 2) - (&1 + s1)) / s1) = &0 /\
                  smooth_step((y$3 pow 2 - (H - &2) pow 2) / ((H - &1) pow 2 - (H - &2) pow 2)) = &0`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `smooth_step((((y:real^3)$1 pow 2 + y$2 pow 2) - (&1 + s1)) / s1) = &1`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC);
      SUBGOAL_THEN `smooth_step(((y:real^3)$3 pow 2 - (H - &2) pow 2) /
                                ((H - &1) pow 2 - (H - &2) pow 2)) = &1`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC)] THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC]);;

let SCHY_CYL_COMPACT = prove
 (`!a b. compact {y:real^3 | y$1 pow 2 + y$2 pow 2 <= a /\ abs(y$3) <= b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `interval[--((abs a + abs b + &1) % vec 1):real^3, (abs a + abs b + &1) % vec 1]` THEN
    REWRITE_TAC[BOUNDED_INTERVAL; SUBSET; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `abs((y:real^3)$1) - &1 / &2` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `abs((y:real^3)$2) - &1 / &2` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(y:real^3)$1` REAL_POW2_ABS) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_POW2_ABS) THEN
    MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `{y:real^3 | y$1 pow 2 + y$2 pow 2 <= a /\ abs(y$3) <= b} =
                  {y | lift(y$1 pow 2 + y$2 pow 2) IN {x:real^1 | x$1 <= a}} INTER
                  ({y | y$3 <= b} INTER {y | y$3 >= --b})` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN X_GEN_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$1 pow 2 + y$2 pow 2)`]
      SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ANTS_TAC THENL
     [MP_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN SCHY_SMOOTH_TAC;
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]]);;

let schy_kin = new_definition
 `schy_kin (Theta:real^3->real^3) (Theta':real^3->real^3) (H:real) (s1:real)
           (rho1:real) (rho2:real) (l:real^3) (x:real^3) =
    if x IN IMAGE Theta (sch5v_slab H)
    then schy_kmod s1 H (Theta' x) * (&1 - smooth_bump rho1 rho2 (x - l))
    else &0`;;

let schy_X = new_definition
 `schy_X (v:real^3->real^3) (kin:real^3->real) (x:real^3) =
    basis 3 + kin x % (v x - basis 3)`;;

let SCHY_X_FACTS = prove
 (`!(v:real^3->real^3) kin B.
     smooth_map_on (:real^3) v /\ (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
     smooth_map_on (:real^3) (\x. lift(kin x)) /\ (!x. &0 <= kin x /\ kin x <= &1)
     ==> smooth_map_on (:real^3) (schy_X v kin) /\ (!x. (schy_X v kin x)$3 = &1) /\
         (!x. norm(schy_X v kin x) <= B + &2) /\
         (!y. ode_vf_maxint (schy_X v kin) (:real^3) y = (:real^1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. norm(schy_X (v:real^3->real^3) kin x) <= B + &2` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[schy_X] THEN
    MP_TAC(ISPECL [`basis 3:real^3`; `(kin:real^3->real) x % ((v:real^3->real^3) x - basis 3)`]
      NORM_TRIANGLE) THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `abs((kin:real^3->real) x) * norm((v:real^3->real^3) x - basis 3) <=
                  &1 * (B + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `x:real^3` o check (fun th ->
        can (term_match [] `!x:real^3. &0 <= (kin:real^3->real) x /\ kin x <= &1`) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`(v:real^3->real^3) x`; `--(basis 3):real^3`] NORM_TRIANGLE) THEN
      SIMP_TAC[NORM_NEG; GSYM VECTOR_SUB; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
        can (term_match [] `!y. norm((v:real^3->real^3) y) <= B`) (concl th))) THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (schy_X (v:real^3->real^3) kin)` ASSUME_TAC THENL
   [SUBGOAL_THEN `schy_X (v:real^3->real^3) kin = (\x. basis 3 + kin x % (v x - basis 3))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_X]; ALL_TAC] THEN
    MP_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN SCHY_SMOOTH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[schy_X; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SCH5V_BOUNDED_COMPLETE THEN EXISTS_TAC `B + &2` THEN ASM_REWRITE_TAC[]]);;

let SCHY_KIN_PROPS = prove
 (`!(Theta:real^3->real^3) Theta' H s1 rho1 rho2 (l:real^3).
     diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
     &0 < s1 /\ s1 < &1 /\ &3 <= H /\ &0 <= rho1 /\ rho1 < rho2
     ==> smooth_map_on (:real^3) (\x. lift(schy_kin Theta Theta' H s1 rho1 rho2 l x)) /\
         (!x. &0 <= schy_kin Theta Theta' H s1 rho1 rho2 l x /\
              schy_kin Theta Theta' H s1 rho1 rho2 l x <= &1) /\
         (!x. ~(x IN IMAGE Theta (sch5v_slab H))
              ==> schy_kin Theta Theta' H s1 rho1 rho2 l x = &0) /\
         (!x. norm(x - l) <= rho1 ==> schy_kin Theta Theta' H s1 rho1 rho2 l x = &0) /\
         (!y. y IN sch5v_slab H
              ==> schy_kin Theta Theta' H s1 rho1 rho2 l (Theta y) =
                  schy_kmod s1 H y * (&1 - smooth_bump rho1 rho2 (Theta y - l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s1:real`; `H:real`] SCHY_KMOD_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H
                    ==> schy_kin (Theta:real^3->real^3) Theta' H s1 rho1 rho2 l (Theta y) =
                        schy_kmod s1 H y * (&1 - smooth_bump rho1 rho2 (Theta y - l))`
  (LABEL_TAC "TH") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[schy_kin] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN IMAGE (Theta:real^3->real^3) (sch5v_slab H))
                    ==> schy_kin Theta Theta' H s1 rho1 rho2 l x = &0` (LABEL_TAC "OUT") THENL
   [SIMP_TAC[schy_kin]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= schy_kin (Theta:real^3->real^3) Theta' H s1 rho1 rho2 l x /\
                    schy_kin Theta Theta' H s1 rho1 rho2 l x <= &1` (LABEL_TAC "BD") THENL
   [GEN_TAC THEN REWRITE_TAC[schy_kin] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN MATCH_MP_TAC SCHY_UNIT_MUL THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rho1:real`; `rho2:real`; `(x:real^3) - l`] SMOOTH_BUMP_BOUNDS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[schy_kin] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rho1:real`; `rho2:real`; `(x:real^3) - l`] SMOOTH_BUMP_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC] THEN
  (* smoothness, by the two open sets *)
  ABBREV_TAC `K = {y:real^3 | y$1 pow 2 + y$2 pow 2 <= &1 + &2 * s1 /\ abs(y$3) <= H - &1}` THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET sch5v_slab H` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; sch5v_slab] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (Theta:real^3->real^3) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5v_slab H` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      EXPAND_TAC "K" THEN REWRITE_TAC[SCHY_CYL_COMPACT]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5v_slab H)` THENL
   [EXISTS_TAC `IMAGE (Theta:real^3->real^3) (sch5v_slab H)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\x. lift(schy_kmod s1 H ((Theta':real^3->real^3) x) *
                         (&1 - smooth_bump rho1 rho2 (x - l)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[schy_kin] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SCH3_SL_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (Theta:real^3->real^3) (sch5v_slab H)`; `(:real^3)`;
                     `\y:real^3. lift(schy_kmod s1 H y)`; `Theta':real^3->real^3`]
        SCH3_SV_COMPOSE) THEN
      ASM_REWRITE_TAC[IN_UNIV];
      MATCH_MP_TAC SCH3_SL_SUB THEN ASM_REWRITE_TAC[SCH3_SL_CONST] THEN
      MP_TAC(ISPECL [`IMAGE (Theta:real^3->real^3) (sch5v_slab H)`; `(:real^3)`;
                     `\y:real^3. lift(smooth_bump rho1 rho2 y)`; `\x:real^3. x - l`]
        SCH3_SV_COMPOSE) THEN
      ASM_SIMP_TAC[IN_UNIV; SMOOTH_BUMP_SMOOTH] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DIFF IMAGE (Theta:real^3->real^3) K` THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
   [UNDISCH_TAC `~((x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5v_slab H))` THEN
    UNDISCH_TAC `(K:real^3->bool) SUBSET sch5v_slab H` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:real^3. lift(&0)` THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; SCH3_SL_CONST; IN_DIFF; IN_UNIV] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `(z:real^3) IN IMAGE (Theta:real^3->real^3) (sch5v_slab H)` THENL
   [ALL_TAC; USE_THEN "OUT" (fun th -> ASM_SIMP_TAC[th])] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `schy_kmod s1 H y = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `~((y:real^3) IN K)` MP_TAC THENL
   [UNDISCH_TAC `~((z:real^3) IN IMAGE (Theta:real^3->real^3) K)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LE] THEN
  STRIP_TAC THENL [DISJ1_TAC THEN ASM_REAL_ARITH_TAC; DISJ2_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Derivative facts for the chart Theta.  DTheta(y) e3 is                    *)
(* lam v(Theta y) (flow property); near lpt DTheta(y)(h,0) = (v - e3)(Theta y) *)
(* for the inward vector h of SCHY_CANCEL_CHART.                             *)
(* ------------------------------------------------------------------------- *)

let SCHY_DTHETA_E3 = prove
 (`!(v:real^3->real^3) (c:real^2->real^2) lam e (Theta:real^3->real^3) y.
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))) /\
     Theta differentiable (at y)
     ==> frechet_derivative Theta (at y) (basis 3) = lam % v(Theta y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  SUBGOAL_THEN `((\t:real^1. y + drop t % basis 3:real^3) has_vector_derivative basis 3)
                (at (vec 0))` ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\x:real^1. drop x % basis 3:real^3) = (\x. vec 0 + drop x % basis 3)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MP_TAC(ISPECL [`\t:real^1. t`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
    REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `(Theta:real^3->real^3) o (\t:real^1. y + drop t % basis 3)` THEN
  EXISTS_TAC `vec 0:real^1` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Theta:real^3->real^3`; `\t:real^1. y + drop t % basis 3:real^3`;
                   `basis 3:real^3`; `vec 0:real^1`] SCHY_CURVE_CHAIN) THEN
    ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) o (\t:real^1. y + drop t % basis 3) =
                (\s. ode_vf_flow v (:real^3) s (Theta y)) o (\t. lam % t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sch5v_pr((y:real^3) + drop t % basis 3) = sch5v_pr y` SUBST1_TAC THENL
     [SIMP_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lift(lam * ((y:real^3) + drop t % basis 3)$3) = lift(lam * y$3) + lam % t`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; LIFT_DROP; DROP_CMUL] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam % v((Theta:real^3->real^3) y) =
                drop(lam % vec 1:real^1) % v(ode_vf_flow v (:real^3) (lam % vec 0) (Theta y))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; DROP_CMUL; DROP_VEC; REAL_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID];
    BETA_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let SCHY_AT0_LINEAR = prove
 (`linear (sch5v_at (&0))`,
  REWRITE_TAC[linear; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let SCHY_X0_DERIV = prove
 (`!(c:real^2->real^2) c' e (y:real^3).
     (c has_derivative c') (at (sch5v_pr y))
     ==> ((\y. sch5v_at e (c(sch5v_pr y))) has_derivative
          (\k. sch5v_at (&0) (c'(sch5v_pr k)))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. ((\z:real^2. sch5v_at e z) has_derivative (\w. sch5v_at (&0) w)) (at z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z:real^2. sch5v_at e z) = (\z. sch5v_at (&0) z + vector[&0; &0; e])`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\w:real^2. sch5v_at (&0) w) = (\w. sch5v_at (&0) w + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[ETA_AX; SCHY_AT0_LINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. sch5v_at e ((c:real^2->real^2)(sch5v_pr y))) =
                (\z. sch5v_at e z) o (c o sch5v_pr)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\k. sch5v_at (&0) ((c':real^2->real^2)(sch5v_pr k))) =
                (\w. sch5v_at (&0) w) o (c' o sch5v_pr)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH]);;

let SCHY_PI_HF2 = prove
 (`!a (z:real^2).
     ~(z$1 pow 2 + z$2 pow 2 = &0)
     ==> frechet_derivative schy_pi (at (sch5v_at a z)) (sch5v_at (&0) (schy_hf2 z)) =
         vector[&1; &0; &0]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCHY_PI_FD; schy_hf2; sch5v_at; VECTOR_3; VECTOR_2] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  UNDISCH_TAC `~((z:real^2)$1 pow 2 + z$2 pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let SCHY_PI_INV_E1 = prove
 (`!(Fp:real^3) k.
     ~(Fp$1 pow 2 + Fp$2 pow 2 = &0) /\
     frechet_derivative schy_pi (at Fp) k = vector[&1; &0; &0]
     ==> k = schy_v0 Fp - basis 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHY_PI_DINJ THEN EXISTS_TAC `Fp:real^3` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SCHY_PI_FD; schy_v0; VECTOR_SUB_COMPONENT; VECTOR_3; BASIS_COMPONENT; DIMINDEX_3;
           ARITH] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  UNDISCH_TAC `~((Fp:real^3)$1 pow 2 + Fp$2 pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let SCHY_DTHETA_H = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) lam (Theta:real^3->real^3) O y h.
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. norm(v y) <= B) /\
     (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0) /\
     (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))) /\
     Theta differentiable (at y) /\ c differentiable (at (sch5v_pr y)) /\
     open O /\ y IN O /\
     (!y'. y' IN O ==> dist(sch5v_at e (c(sch5v_pr y')),schy_lpt e) < rho0 / &2 /\
                       B * abs(lam * y'$3) < rho0 / &2) /\
     frechet_derivative c (at (sch5v_pr y)) h = schy_hf2(c(sch5v_pr y))
     ==> frechet_derivative Theta (at y) (sch5v_at (&0) h) = v(Theta y) - basis 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  SUBGOAL_THEN `!x:real^3. dist(x,schy_lpt e) < rho0 ==> ~(x$1 pow 2 + x$2 pow 2 = &0)`
  (LABEL_TAC "NZ") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (x:real^3)$1 pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(sch5v_at e ((c:real^2->real^2)(sch5v_pr y)),schy_lpt e) < rho0 / &2 /\
                B * abs(lam * (y:real^3)$3) < rho0 / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist((Theta:real^3->real^3) y,sch5v_at e ((c:real^2->real^2)(sch5v_pr y))) <=
                B * abs(lam * (y:real^3)$3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`sch5v_at e ((c:real^2->real^2)(sch5v_pr y))`;
                               `lift(lam * (y:real^3)$3)`; `vec 0:real^1`]) THEN
    ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_SUB_RZERO; dist];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((Theta:real^3->real^3) y,schy_lpt e) < rho0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(Theta:real^3->real^3) y`; `sch5v_at e ((c:real^2->real^2)(sch5v_pr y))`;
                   `schy_lpt e`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. (schy_pi has_derivative frechet_derivative schy_pi (at x)) (at x)`
  ASSUME_TAC THENL
   [MESON_TAC[SCHY_PI_DERIV; differentiable; FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `((Theta:real^3->real^3) has_derivative frechet_derivative Theta (at y)) (at y) /\
                ((c:real^2->real^2) has_derivative frechet_derivative c (at (sch5v_pr y)))
                (at (sch5v_pr y))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  (* the two derivatives of Pi o Theta at y *)
  SUBGOAL_THEN
   `((\y':real^3. schy_pi(sch5v_at e ((c:real^2->real^2)(sch5v_pr y'))) +
                   (lam * y'$3) % vector[&1; &0; &1]) has_derivative
     (\k. frechet_derivative schy_pi (at (sch5v_at e (c(sch5v_pr y))))
            (sch5v_at (&0) (frechet_derivative c (at (sch5v_pr y)) (sch5v_pr k))) +
          (lam * k$3) % vector[&1; &0; &1])) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y':real^3. sch5v_at e ((c:real^2->real^2)(sch5v_pr y'))`;
                     `schy_pi`;
                     `\k:real^3. sch5v_at (&0)
                         (frechet_derivative (c:real^2->real^2) (at (sch5v_pr y)) (sch5v_pr k))`;
                     `frechet_derivative schy_pi (at (sch5v_at e ((c:real^2->real^2)(sch5v_pr y))))`;
                     `y:real^3`] DIFF_CHAIN_AT) THEN
      ASM_SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SCHY_X0_DERIV THEN ASM_REWRITE_TAC[ETA_AX]; DISCH_THEN ACCEPT_TAC];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_3] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y':real^3. schy_pi(sch5v_at e ((c:real^2->real^2)(sch5v_pr y'))) +
                   (lam * y'$3) % vector[&1; &0; &1]) has_derivative
     (frechet_derivative schy_pi (at ((Theta:real^3->real^3) y)) o frechet_derivative Theta (at y)))
    (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `schy_pi o (Theta:real^3->real^3)` THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_THETA_PI THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `rho0:real`; `e:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
            can (term_match [] `!x:real^3. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0`)
              (concl th))) THEN ASM_SIMP_TAC[];
          USE_THEN "NZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ th1 th2)))) THEN
  DISCH_THEN(MP_TAC o C AP_THM `sch5v_at (&0) (h:real^2)`) THEN
  REWRITE_TAC[o_THM; SCH5V_PR_AT] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(sch5v_at (&0) (h:real^2))$3 = &0` SUBST1_TAC THENL
   [REWRITE_TAC[SCH5V_PR_AT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `~(((c:real^2->real^2)(sch5v_pr y))$1 pow 2 + (c(sch5v_pr y))$2 pow 2 = &0)`
  ASSUME_TAC THENL
   [USE_THEN "NZ" (MP_TAC o SPEC `sch5v_at e ((c:real^2->real^2)(sch5v_pr y))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ d < r / &2 ==> d < r`) THEN
      ASM_REWRITE_TAC[DIST_POS_LE];
      REWRITE_TAC[sch5v_at; VECTOR_3]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SCHY_PI_HF2] THEN
  UNDISCH_TAC `dist((Theta:real^3->real^3) y,schy_lpt e) < rho0` THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`ode_vf_flow v (:real^3) (lift(lam * (y:real^3)$3))
              (sch5v_at e ((c:real^2->real^2)(sch5v_pr y)))`, `Fp:real^3`) THEN
  X_GEN_TAC `Fp:real^3` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3->real^3) Fp = schy_v0 Fp /\ ~(Fp$1 pow 2 + Fp$2 pow 2 = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Fp:real^3` o check (fun th ->
        can (term_match [] `!x:real^3. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0`)
          (concl th))) THEN ASM_SIMP_TAC[];
      USE_THEN "NZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_PI_INV_E1 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real-variable tools for the column lemma.  The derivative of              *)
(* the cap profile (nonnegative, positive below 7/8), the last-crossing      *)
(* lemma and the column principle: a function vanishing at 0 with positive   *)
(* derivative there, nondecreasing wherever it is below c, has no other zero. *)
(* ------------------------------------------------------------------------- *)

let SCHY_SSTEP_LT1 = prove
 (`!u. u < &1 ==> smooth_step u < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN
  MP_TAC(SPEC `u:real` CUTOFF_FLAT_DENOM_POS) THEN
  MP_TAC(SPEC `&1 - u` CUTOFF_FLAT_POS_LT) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let schy_ssd = new_definition
 `schy_ssd u = @d. (smooth_step has_real_derivative d) (atreal u)`;;

let SCHY_SSD_FACTS = prove
 (`!u. (smooth_step has_real_derivative schy_ssd u) (atreal u) /\ &0 <= schy_ssd u /\
       (&1 < u ==> schy_ssd u = &0)`,
  SUBGOAL_THEN `!u. (smooth_step has_real_derivative schy_ssd u) (atreal u)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[schy_ssd] THEN CONV_TAC SELECT_CONV THEN
    REWRITE_TAC[GSYM real_differentiable; REAL_DIFFERENTIABLE_AT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_STEP_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. &0 <= schy_ssd u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`smooth_step`; `schy_ssd`; `(:real)`] HAS_REAL_DERIVATIVE_INCREASING) THEN
    ASM_REWRITE_TAC[IS_REALINTERVAL_CLAUSES; WITHINREAL_UNIV; IN_UNIV] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NOT_EXISTS_THM; EXTENSION; IN_UNIV; IN_SING] THEN GEN_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `a + &1`) THEN REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th; SMOOTH_STEP_MONO])];
    ALL_TAC] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`smooth_step`; `u:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\x:real. &1`; `u - &1`] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let schy_profd = new_definition
 `schy_profd t =
    (&1 - smooth_step(&4 * t - &5 / &2)) + &4 * schy_ssd(&4 * t - &5 / &2) * (&3 / &2 - t)`;;

let SCHY_PROFILE_DERIV = prove
 (`!t. (sch_cap_profile has_real_derivative schy_profd t) (atreal t)`,
  GEN_TAC THEN
  SUBGOAL_THEN `((\t. smooth_step(&4 * t - &5 / &2)) has_real_derivative
                 (schy_ssd(&4 * t - &5 / &2) * &4)) (atreal t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real. &4 * t - &5 / &2`; `smooth_step`; `&4`;
                   `schy_ssd(&4 * t - &5 / &2)`; `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF; SCHY_SSD_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\t:real. &4 * t`; `&4`; `\t:real. &5 / &2`; `&0`; `atreal t`]
      HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\t:real. t`; `&1`; `&4`; `t:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile =
                (\t. (&1 - smooth_step(&4 * t - &5 / &2)) * (t - &1 / &2) +
                     smooth_step(&4 * t - &5 / &2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch_cap_profile]; ALL_TAC] THEN
  SUBGOAL_THEN `schy_profd t =
                ((&1 - smooth_step(&4 * t - &5 / &2)) * &1 +
                 (&0 - schy_ssd(&4 * t - &5 / &2) * &4) * (t - &1 / &2)) +
                schy_ssd(&4 * t - &5 / &2) * &4` SUBST1_TAC THENL
   [REWRITE_TAC[schy_profd] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\t. &1 - smooth_step(&4 * t - &5 / &2)`;
                 `&0 - schy_ssd(&4 * t - &5 / &2) * &4`;
                 `\t:real. t - &1 / &2`; `&1`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\t:real. &1`; `&0`; `\t. smooth_step(&4 * t - &5 / &2)`;
                   `schy_ssd(&4 * t - &5 / &2) * &4`; `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    MP_TAC(ISPECL [`\t:real. t`; `&1`; `\t:real. &1 / &2`; `&0`; `atreal t`]
      HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID; REAL_SUB_RZERO]]);;

let SCHY_PROFD_SIGN = prove
 (`!t. &0 <= schy_profd t /\ (t < &7 / &8 ==> &0 < schy_profd t)`,
  GEN_TAC THEN REWRITE_TAC[schy_profd] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SCHY_SSD_FACTS) THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ASM_CASES_TAC `&3 / &2 < t` THENL
   [SUBGOAL_THEN `smooth_step(&4 * t - &5 / &2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `schy_ssd(&4 * t - &5 / &2) = &0` SUBST1_TAC THENL
     [MP_TAC(SPEC `&4 * t - &5 / &2` SCHY_SSD_FACTS) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&4 * t - &5 / &2` SCHY_SSTEP_LT1) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let SCHY_PROFILE_LE1 = prove
 (`!t. sch_cap_profile t <= &1`,
  GEN_TAC THEN ASM_CASES_TAC `t <= &1 / &2` THENL
   [ASM_SIMP_TAC[SCH_CAP_PROFILE_TIP; REAL_ARITH `t <= &1 / &2 ==> t <= &5 / &8`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&7 / &8 <= t` THENL [ASM_SIMP_TAC[SCH_CAP_PROFILE_TOP; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` SCH_CAP_PROFILE_BOUNDS) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SCHY_LAST_CROSS = prove
 (`!(f:real->real) f' p q L.
     p < q /\ L <= f p /\ f q < L /\
     (!x. p <= x /\ x <= q ==> (f has_real_derivative f' x) (atreal x)) /\
     (!x. p < x /\ x < q /\ f x < L ==> &0 <= f' x)
     ==> F`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {x:real | p <= x /\ x <= q /\ L <= f x}` THEN
  SUBGOAL_THEN `(p:real) IN S /\ (!x. x IN S ==> p <= x /\ x <= q /\ L <= (f:real->real) x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `q:real` THEN ASM_MESON_TAC[]]; ALL_TAC] THEN
  ABBREV_TAC `s = sup S` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p <= s /\ s <= q` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. p <= x /\ x <= q ==> (f:real->real) real_continuous (atreal x)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]; ALL_TAC] THEN
  SUBGOAL_THEN `L <= (f:real->real) s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
    REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `L - (f:real->real) s`) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?x. x IN S /\ s - d < x` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s - d` o check (fun th ->
        can (term_match [] `!b. (!x:real. x IN S ==> x <= b) ==> s <= b`) (concl th))) THEN
      MP_TAC(REAL_ARITH `&0 < d ==> ~(s <= s - d)`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[REAL_NOT_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `x <= s /\ L <= (f:real->real) x` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `x:real = s` THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `L <= (f:real->real) s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. s < x /\ x <= q ==> (f:real->real) x < L` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      can (term_match [] `!x:real. x IN S ==> x <= s`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `s:real`; `q:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[real_differentiable_on; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[real_differentiable] THEN
      EXISTS_TAC `(f':real->real) u` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= (f':real->real) xi` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (f':real->real) xi * (q - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SCHY_DERIV_SIGN_LOCAL = prove
 (`!(f:real->real) f'.
     (f has_real_derivative f') (atreal (&0)) /\ f(&0) = &0 /\ &0 < f'
     ==> ?d. &0 < d /\
             !x. abs x < d ==> (&0 < x ==> &0 < f x) /\ (x < &0 ==> f x < &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_DERIVATIVE_ATREAL]) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `f':real`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  SUBGOAL_THEN `&0 < (f:real->real) x / x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `&0 < (f:real->real) x / x` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO];
    SUBGOAL_THEN `(f:real->real) x / x = --(f x) / --x` SUBST_ALL_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < --((f:real->real) x) / --x` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO; REAL_ARITH `x < &0 ==> &0 < --x`] THEN
    REAL_ARITH_TAC]);;

let SCHY_COLUMN_REAL = prove
 (`!(f:real->real) f' a b c.
     a < &0 /\ &0 < b /\ &0 < c /\
     (!t. a <= t /\ t <= b ==> (f has_real_derivative f' t) (atreal t)) /\
     f(&0) = &0 /\ &0 < f'(&0) /\
     (!t. a <= t /\ t <= b /\ f t < c ==> &0 <= f' t)
     ==> !t. a <= t /\ t <= b /\ f t = &0 ==> t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(f':real->real)(&0)`] SCHY_DERIV_SIGN_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `t = &0 <=> ~(&0 < t) /\ ~(t < &0)`] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [ABBREV_TAC `t0 = min (d / &2) (t / &2)` THEN
    SUBGOAL_THEN `&0 < t0 /\ t0 < t /\ abs t0 < d` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (f:real->real) t0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_LAST_CROSS THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `f':real->real`; `t0:real`; `t:real`;
                          `min ((f:real->real) t0) c / &2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ABBREV_TAC `t0 = max (--(d / &2)) (t / &2)` THEN
    SUBGOAL_THEN `t0 < &0 /\ t < t0 /\ abs t0 < d` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) t0 < &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_LAST_CROSS THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `f':real->real`; `t:real`; `t0:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The chart data, the model function F = |pr y|^2 - R(y3) of                *)
(* S1 in the chart, the model velocity of the shear field and the column     *)
(* lemma in the chart: along an X-line, F o Theta' has a unique zero.        *)
(* ------------------------------------------------------------------------- *)

let schy_cd = new_definition
 `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
          (Theta:real^3->real^3) Theta' <=>
    smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
    (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
    &0 < rho0 /\ (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0) /\
    smooth_map_on (ball(vec 0,&2)) c /\
    &0 < delta1 /\
    (!z. dist(z,--basis 1) < delta1
         ==> z IN ball(vec 0,&2) /\ dist(c z,vector[--(sqrt e); &0]) < rho0 / &2 /\
             ?h. z dot h < &0 /\ frechet_derivative c (at z) h = schy_hf2(c z)) /\
    &0 < lam /\ &3 <= H /\ B * lam * H < rho0 / &2 /\
    (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))) /\
    diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
    (!y. y IN sch5v_slab H ==> (Theta y)$3 = e + lam * y$3)`;;

let schy_F = new_definition
 `schy_F (y:real^3) = y$1 pow 2 + y$2 pow 2 - sch_cap_profile(--(y$3))`;;

let SCHY_F_DERIV = prove
 (`!y:real^3.
     ((\y. lift(schy_F y)) has_derivative
      (\w. lift(&2 * y$1 * w$1 + &2 * y$2 * w$2 + schy_profd(--(y$3)) * w$3))) (at y)`,
  GEN_TAC THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= 3
                    ==> ((\z:real^3. lift(z$k pow 2)) has_derivative
                         (\h. lift((&2 * (y:real^3)$k) * h$k))) (at y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\t:real. t pow 2`; `&2 * (y:real^3)$k`; `y:real^3`; `k:num`]
      SCHY_COMP_DERIV) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\t:real. t`; `&1`; `(y:real^3)$k`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\z:real^3. lift(sch_cap_profile(--(z$3)))) has_derivative
                 (\h. lift((--(schy_profd(--((y:real^3)$3)))) * h$3))) (at y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real. sch_cap_profile(--t)`; `--(schy_profd(--((y:real^3)$3)))`;
                   `y:real^3`; `3`] SCHY_COMP_DERIV) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\t:real. --t`; `sch_cap_profile`; `--(&1)`;
                   `schy_profd(--((y:real^3)$3))`; `(y:real^3)$3`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF; SCHY_PROFILE_DERIV] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `atreal((y:real^3)$3)`] HAS_REAL_DERIVATIVE_NEG) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^3. lift(schy_F y)) =
                (\z. (lift(z$1 pow 2) + lift(z$2 pow 2)) - lift(sch_cap_profile(--(z$3))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_F; GSYM LIFT_ADD; GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^3. lift(&2 * (y:real^3)$1 * w$1 + &2 * y$2 * w$2 +
                                 schy_profd(--(y$3)) * w$3)) =
                (\h. (lift((&2 * y$1) * h$1) + lift((&2 * y$2) * h$2)) -
                     lift((--(schy_profd(--(y$3)))) * h$3))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let SCHY_AT_DIST = prove
 (`!a (u:real^2) w. dist(sch5v_at a u,sch5v_at a w) = dist(u,w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist; NORM_EQ; DOT_3; DOT_2; sch5v_at; VECTOR_SUB_COMPONENT;
                                  VECTOR_3] THEN
  REAL_ARITH_TAC);;

let SCHY_LPT_AT = prove
 (`!e. schy_lpt e = sch5v_at e (vector[--(sqrt e); &0])`,
  REWRITE_TAC[schy_lpt; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2]);;

let SCHY_CD_FACTS = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'.
     schy_cd v B rho0 e c delta1 lam H Theta Theta'
     ==> &0 <= B /\ ~(lam = &0) /\ open(sch5v_slab H) /\ open(IMAGE Theta (sch5v_slab H)) /\
         diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
         (!y. y IN sch5v_slab H ==> Theta differentiable (at y)) /\
         (!x. x IN IMAGE Theta (sch5v_slab H) ==> Theta' differentiable (at x)) /\
         (!y. y IN sch5v_slab H ==> Theta' (Theta y) = y /\ Theta y IN IMAGE Theta (sch5v_slab H)) /\
         (!z. z IN ball(vec 0,&2) ==> c differentiable (at z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] `!y:real^3. (Theta:real^3->real^3) y =
           ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))`)
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
      can (term_match [] `!y:real^3. norm((v:real^3->real^3) y) <= B`) (concl th))) THEN
    MP_TAC(ISPEC `(v:real^3->real^3)(vec 0)` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `sch5v_slab H` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (Theta:real^3->real^3) (sch5v_slab H)` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:real^2,&2)` THEN ASM_REWRITE_TAC[OPEN_BALL]]);;

let SCHY_DTHETAI_V = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta' y.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ y IN sch5v_slab H
     ==> frechet_derivative Theta' (at (Theta y)) (v(Theta y)) = inv lam % basis 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `frechet_derivative (Theta:real^3->real^3) (at y) (basis 3) = lam % v(Theta y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_DTHETA_E3 THEN MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `e:real`] THEN
    UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch5v_slab H`; `IMAGE (Theta:real^3->real^3) (sch5v_slab H)`;
                 `Theta:real^3->real^3`; `Theta':real^3->real^3`; `y:real^3`; `basis 3:real^3`]
    SCH4_DIFFEO_DERIV_INV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Theta':real^3->real^3) (at ((Theta:real^3->real^3) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `(%) (inv lam):real^3->real^3`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]);;

let SCHY_EXPL_OPEN = prove
 (`!H delta1. open {y:real^3 | y IN sch5v_slab H /\ dist(sch5v_pr y,--basis 1) < delta1}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | y IN sch5v_slab H /\ dist(sch5v_pr y,--basis 1) < delta1} =
                sch5v_slab H INTER {y | sch5v_pr y IN ball(--basis 1,delta1)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL] THEN MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
   [REWRITE_TAC[sch5v_slab] THEN
    SUBGOAL_THEN `{y:real^3 | y$1 pow 2 + y$2 pow 2 < &4 /\ abs(y$3) < H} =
                  {y | lift(y$1 pow 2 + y$2 pow 2) IN {x:real^1 | x$1 < &4}} INTER
                  ({y | y$3 < H} INTER {y | y$3 > --H})` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN X_GEN_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$1 pow 2 + y$2 pow 2)`]
      SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ANTS_TAC THENL
     [MP_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN SCHY_SMOOTH_TAC;
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH]]);;

let SCHY_DTHETAI_G = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta' y.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ y IN sch5v_slab H /\
     dist(sch5v_pr y,--basis 1) < delta1
     ==> ?h. sch5v_pr y dot h < &0 /\
             frechet_derivative Theta' (at (Theta y)) (v(Theta y) - basis 3) = sch5v_at (&0) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `sch5v_pr y IN ball(vec 0,&2) /\
                dist((c:real^2->real^2)(sch5v_pr y),vector[--(sqrt e); &0]) < rho0 / &2 /\
                ?h. sch5v_pr y dot h < &0 /\
                    frechet_derivative c (at (sch5v_pr y)) h = schy_hf2(c(sch5v_pr y))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `h:real^2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frechet_derivative (Theta:real^3->real^3) (at y) (sch5v_at (&0) h) =
                v(Theta y) - basis 3` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_DTHETA_H THEN
    MAP_EVERY EXISTS_TAC
     [`B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`; `lam:real`;
      `{y':real^3 | y' IN sch5v_slab H /\ dist(sch5v_pr y',--basis 1) < delta1}`] THEN
    REWRITE_TAC[SCHY_EXPL_OPEN; IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y':real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SCHY_LPT_AT; SCHY_AT_DIST] THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `abs((y':real^3)$3) < H` ASSUME_TAC THENL
       [UNDISCH_TAC `(y':real^3) IN sch5v_slab H` THEN REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * lam * H` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SCH4_DIFFEO_DERIV_INV THEN
  MAP_EVERY EXISTS_TAC [`sch5v_slab H`; `IMAGE (Theta:real^3->real^3) (sch5v_slab H)`] THEN
  ASM_REWRITE_TAC[]);;

let SCHY_MODEL_VEL = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'
    kin y.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ y IN sch5v_slab H
     ==> frechet_derivative Theta' (at (Theta y)) (schy_X v kin (Theta y)) =
         inv lam % basis 3 -
         (&1 - kin(Theta y)) % frechet_derivative Theta' (at (Theta y)) (v(Theta y) - basis 3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `linear(frechet_derivative (Theta':real^3->real^3) (at ((Theta:real^3->real^3) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `schy_X (v:real^3->real^3) kin ((Theta:real^3->real^3) y) =
                v(Theta y) - (&1 - kin(Theta y)) % (v(Theta y) - basis 3)` SUBST1_TAC THENL
   [REWRITE_TAC[schy_X] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th; MATCH_MP LINEAR_CMUL th]) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_DTHETAI_V) THEN
  ASM_SIMP_TAC[]);;

let SCHY_SSTEP_POS = prove
 (`!u. &0 < u ==> &0 < smooth_step u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  ASM_REWRITE_TAC[CUTOFF_FLAT_POS_LT; CUTOFF_FLAT_DENOM_POS]);;

let SCHY_BUMP_POS = prove
 (`!a b (x:real^N). &0 <= a /\ a < b /\ norm x < b ==> &0 < smooth_bump a b x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_bump] THEN MATCH_MP_TAC SCHY_SSTEP_POS THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH] THEN ASM_REAL_ARITH_TAC);;

let SCHY_PHI_SIGN = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'
    s1 rho1 rho2 (kin:real^3->real) y.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ &0 <= rho1 /\ rho1 < rho2 /\
     (!y. y IN sch5v_slab H
          ==> kin(Theta y) = schy_kmod s1 H y * (&1 - smooth_bump rho1 rho2 (Theta y - schy_lpt e))) /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     y IN sch5v_slab H /\ schy_kmod s1 H y = &1
     ==> &0 <= drop(frechet_derivative (\y. lift(schy_F y)) (at y)
                     (frechet_derivative Theta' (at (Theta y)) (schy_X v kin (Theta y)))) /\
         (--(y$3) < &7 / &8 \/ dist(Theta y,schy_lpt e) < rho2
          ==> &0 < drop(frechet_derivative (\y. lift(schy_F y)) (at y)
                         (frechet_derivative Theta' (at (Theta y)) (schy_X v kin (Theta y)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT (SPEC `y:real^3` SCHY_F_DERIV)); LIFT_DROP] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `kin:real^3->real`; `y:real^3`] SCHY_MODEL_VEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&1 - (kin:real^3->real)(Theta y) =
                smooth_bump rho1 rho2 ((Theta:real^3->real^3) y - schy_lpt e)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `be = smooth_bump rho1 rho2 ((Theta:real^3->real^3) y - schy_lpt e)` THEN
  SUBGOAL_THEN `&0 <= be` ASSUME_TAC THENL
   [EXPAND_TAC "be" THEN REWRITE_TAC[SMOOTH_BUMP_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w$3 = inv lam ==> &0 <= schy_profd(--((y:real^3)$3)) * w$3 /\
                (--(y$3) < &7 / &8 ==> &0 < schy_profd(--(y$3)) * w$3)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `--((y:real^3)$3)` SCHY_PROFD_SIGN) THEN
    SUBGOAL_THEN `&0 < inv lam` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `be = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO;
             REAL_MUL_RID; REAL_ADD_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv lam % basis 3:real^3`) THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&0 < be` MP_TAC THENL
     [EXPAND_TAC "be" THEN MATCH_MP_TAC SCHY_BUMP_POS THEN ASM_REWRITE_TAC[GSYM dist];
      ASM_REWRITE_TAC[REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((Theta:real^3->real^3) y,schy_lpt e) < rho2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE; dist] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(be = &0)` THEN EXPAND_TAC "be" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_DTHETAI_G) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h:real^2` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < be` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(inv lam % basis 3 - be % sch5v_at (&0) h:real^3)$3 = inv lam` ASSUME_TAC THENL
   [SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[sch5v_at; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th' ->
    can (term_match [] `!w:real^3. w$3 = inv lam ==> P w`) (concl th')))) THEN
  SUBGOAL_THEN `&2 * (y:real^3)$1 * (inv lam % basis 3 - be % sch5v_at (&0) h:real^3)$1 +
                &2 * y$2 * (inv lam % basis 3 - be % sch5v_at (&0) h:real^3)$2 =
                &2 * be * --(sch5v_pr y dot h)` MP_TAC THENL
   [SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[sch5v_at; sch5v_pr; VECTOR_3; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * be * --(sch5v_pr y dot h)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SCHY_FD_COMPOSE = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
     f differentiable (at x) /\ g differentiable (at (f x))
     ==> frechet_derivative (g o f) (at x) =
         frechet_derivative g (at (f x)) o frechet_derivative f (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let SCHY_ALONG_FLOW = prove
 (`!(X:real^3->real^3) (g:real^3->real^1) p t.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     g differentiable (at (ode_vf_flow X (:real^3) (lift t) p))
     ==> ((\s. drop(g(ode_vf_flow X (:real^3) (lift s) p))) has_real_derivative
          drop(frechet_derivative g (at (ode_vf_flow X (:real^3) (lift t) p))
                 (X(ode_vf_flow X (:real^3) (lift t) p)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  SUBGOAL_THEN `(lift o (\s. drop((g:real^3->real^1)(ode_vf_flow X (:real^3) (lift s) p))) o drop) =
                g o (\s. ode_vf_flow X (:real^3) s p)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`g:real^3->real^1`; `\s:real^1. ode_vf_flow (X:real^3->real^3) (:real^3) s p`;
                 `(X:real^3->real^3)(ode_vf_flow X (:real^3) (lift t) p)`; `lift t`]
    SCHY_CURVE_CHAIN) THEN
  ASM_REWRITE_TAC[]);;

let SCHY_CHART_COLUMN = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'
    s1 rho1 rho2 (kin:real^3->real) p a b.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\
     &0 < s1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     smooth_map_on (:real^3) (\x. lift(kin x)) /\ (!x. &0 <= kin x /\ kin x <= &1) /\
     (!y. y IN sch5v_slab H
          ==> kin(Theta y) = schy_kmod s1 H y * (&1 - smooth_bump rho1 rho2 (Theta y - schy_lpt e))) /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     a < &0 /\ &0 < b /\
     (!t. a <= t /\ t <= b
          ==> ode_vf_flow (schy_X v kin) (:real^3) (lift t) p IN IMAGE Theta (sch5v_slab H) /\
              abs((Theta'(ode_vf_flow (schy_X v kin) (:real^3) (lift t) p))$3) <= H - &2) /\
     schy_F(Theta' p) = &0 /\
     (--((Theta' p)$3) < &7 / &8 \/ dist(p,schy_lpt e) < rho2)
     ==> !t. a <= t /\ t <= b /\
             schy_F(Theta'(ode_vf_flow (schy_X v kin) (:real^3) (lift t) p)) = &0
             ==> t = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (v:real^3->real^3) /\ (!y. norm(v y) <= B) /\
                (!y. (v y)$3 = &1) /\ &3 <= H` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `kin:real^3->real`; `B:real`] SCHY_X_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (schy_X (v:real^3->real^3) kin)`)) THEN
  MP_TAC(SPECL [`s1:real`; `H:real`] SCHY_KMOD_PROPS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* points of the image *)
  SUBGOAL_THEN `!x. x IN IMAGE (Theta:real^3->real^3) (sch5v_slab H)
                    ==> Theta'(x) IN sch5v_slab H /\ Theta(Theta' x) = x`
  (LABEL_TAC "IMG") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the sign of the derivative at a point of the column *)
  SUBGOAL_THEN
   `!x. x IN IMAGE (Theta:real^3->real^3) (sch5v_slab H) /\ abs((Theta' x)$3) <= H - &2 /\
        schy_F(Theta' x) < s1
        ==> &0 <= drop(frechet_derivative (\y. lift(schy_F y)) (at (Theta' x))
                        (frechet_derivative Theta' (at x) (schy_X v kin x))) /\
            (--((Theta' x)$3) < &7 / &8 \/ dist(x,schy_lpt e) < rho2
             ==> &0 < drop(frechet_derivative (\y. lift(schy_F y)) (at (Theta' x))
                            (frechet_derivative Theta' (at x) (schy_X v kin x))))`
  (LABEL_TAC "SIGN") THENL
   [X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(Theta':real^3->real^3)(Theta y) = y`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_PHI_SIGN THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `rho0:real`; `c:real^2->real^2`; `delta1:real`;
                          `lam:real`; `H:real`; `s1:real`; `rho1:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y:real^3. y$1 pow 2 + y$2 pow 2 <= &1 + s1 /\
                                     y$3 pow 2 <= (H - &2) pow 2 ==> schy_kmod s1 H y = &1`)
          (concl th))) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `schy_F y < s1` THEN REWRITE_TAC[schy_F] THEN
      MP_TAC(SPEC `--((y:real^3)$3)` SCHY_PROFILE_LE1) THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. schy_F((Theta':real^3->real^3)
              (ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift t) p))`;
    `\t. drop(frechet_derivative (\y. lift(schy_F y))
                (at ((Theta':real^3->real^3)
                     (ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift t) p)))
                (frechet_derivative Theta' (at (ode_vf_flow (schy_X v kin) (:real^3) (lift t) p))
                   (schy_X v kin (ode_vf_flow (schy_X v kin) (:real^3) (lift t) p))))`;
    `a:real`; `b:real`; `s1:real`] SCHY_COLUMN_REAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift(&0)) p = p`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[LIFT_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `p IN IMAGE (Theta:real^3->real^3) (sch5v_slab H) /\
                abs(((Theta':real^3->real^3) p)$3) <= H - &2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (term_match [] `!t. a <= t /\ t <= b ==> P t`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift t) p IN
                  IMAGE (Theta:real^3->real^3) (sch5v_slab H)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x = ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift t) p` THEN
    SUBGOAL_THEN `((\y. lift(schy_F y)) o (Theta':real^3->real^3)) differentiable (at x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[differentiable] THEN MESON_TAC[SCHY_F_DERIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`schy_X (v:real^3->real^3) kin`;
                   `(\y. lift(schy_F y)) o (Theta':real^3->real^3)`; `p:real^3`; `t:real`]
      SCHY_ALONG_FLOW) THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`Theta':real^3->real^3`; `\y. lift(schy_F y)`; `x:real^3`] SCHY_FD_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REWRITE_TAC[differentiable] THEN MESON_TAC[SCHY_F_DERIV];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM]];
    USE_THEN "SIGN" (MP_TAC o SPEC `p:real^3`) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "SIGN" (MP_TAC o SPEC
      `ode_vf_flow (schy_X (v:real^3->real^3) kin) (:real^3) (lift t) p`) THEN
    ASM_SIMP_TAC[]]);;

let SCHY_IMAGE_NBHD = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'
    dc x y0 D.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\
     (!z q. norm z <= &1 /\ dist(c z,q) < dc ==> q IN IMAGE c (ball(vec 0,&2))) /\
     norm(sch5v_pr y0) <= &1 /\ abs(y0$3) <= &2 /\
     dist(x,Theta y0) <= D /\ D + B * (&2 * lam + D) + B * (&2 * lam) < dc /\
     &2 * lam + D < lam * H
     ==> x IN IMAGE Theta (sch5v_slab H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (v:real^3->real^3) /\
                (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
                (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\ &0 < lam`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Theta:real^3->real^3) y =
                    ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))`
  (LABEL_TAC "TH") THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    SIMP_TAC[schy_cd];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!u:real^3 r. ode_vf_flow (v:real^3->real^3) (:real^3) (lift(--r))
                               (ode_vf_flow v (:real^3) (lift r) u) = u` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `((Theta:real^3->real^3) y0)$3 = e + lam * (y0:real^3)$3` ASSUME_TAC THENL
   [USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SCH5V_PR_AT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(e - (x:real^3)$3) <= &2 * lam + D` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(x:real^3) - (Theta:real^3->real^3) y0`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; GSYM dist] THEN
    SUBGOAL_THEN `lam * abs((y0:real^3)$3) <= lam * &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dist(x:real^3,(Theta:real^3->real^3) y0) <= D` THEN
    UNDISCH_TAC `((Theta:real^3->real^3) y0)$3 = e + lam * (y0:real^3)$3` THEN
    SPEC_TAC(`(Theta:real^3->real^3) y0`,`ty:real^3`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(lam * (y0:real^3)$3) = lam * abs(y0$3)` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = ode_vf_flow (v:real^3->real^3) (:real^3) (lift(e - x$3)) x` THEN
  SUBGOAL_THEN `(w:real^3)$3 = e` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dist(w:real^3,x) <= B * (&2 * lam + D)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `lift(e - (x:real^3)$3)`; `vec 0:real^1`] o
      check (fun th -> can (term_match []
        `!x s t. norm(ode_vf_flow v (:real^3) s x - ode_vf_flow v (:real^3) t x) <=
                 B * abs(drop s - drop t)`) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_SUB_RZERO; GSYM dist] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((Theta:real^3->real^3) y0,sch5v_at e ((c:real^2->real^2)(sch5v_pr y0))) <=
                B * (&2 * lam)` ASSUME_TAC THENL
   [USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`sch5v_at e ((c:real^2->real^2)(sch5v_pr y0))`;
      `lift(lam * (y0:real^3)$3)`; `vec 0:real^1`] o check (fun th ->
      can (term_match []
        `!x s t. norm(ode_vf_flow v (:real^3) s x - ode_vf_flow v (:real^3) t x) <=
                 B * abs(drop s - drop t)`) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_SUB_RZERO; GSYM dist] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
    MATCH_MP_TAC(REAL_ARITH `lam * a <= lam * &2 ==> lam * a <= &2 * lam`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_at e (sch5v_pr (w:real^3)) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3)$3 = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((c:real^2->real^2)(sch5v_pr y0),sch5v_pr (w:real^3)) < dc` ASSUME_TAC THENL
   [SUBGOAL_THEN `dist((c:real^2->real^2)(sch5v_pr y0),sch5v_pr (w:real^3)) =
                  dist(sch5v_at e (c(sch5v_pr y0)),w)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`e:real`; `(c:real^2->real^2)(sch5v_pr y0)`; `sch5v_pr (w:real^3)`]
        SCHY_AT_DIST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(w:real^3,x) + dist(x,(Theta:real^3->real^3) y0) +
                dist(Theta y0,sch5v_at e ((c:real^2->real^2)(sch5v_pr y0)))` THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_pr (w:real^3) IN IMAGE (c:real^2->real^2) (ball(vec 0,&2))` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!z q. norm z <= &1 /\ dist((c:real^2->real^2) z,q) < dc ==> P q`)
        (concl th))) THEN
    EXISTS_TAC `sch5v_pr (y0:real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sch5v_at (((x:real^3)$3 - e) / lam) (z:real^2)` THEN CONJ_TAC THENL
   [USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SCH5V_PR_AT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(c:real^2->real^2) z`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lam * (((x:real^3)$3 - e) / lam) = --(e - x$3)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      concl th = `sch5v_at e (sch5v_pr (w:real^3)) = w`)) THEN
    EXPAND_TAC "w" THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th ->
      can (term_match [] `!u:real^3 r. ode_vf_flow v (:real^3) (lift(--r))
                                 (ode_vf_flow v (:real^3) (lift r) u) = u`) (concl th)));
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM; sch5v_at; VECTOR_3] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN ball(vec 0,&2)` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(z:real^2) pow 2 < &2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH]; ALL_TAC] THEN
      REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < lam ==> abs lam = lam`; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC]]);;

let SCHY_S1_IN_CHART = prove
 (`!(S:real^3->bool) S1 S2 (Theta:real^3->real^3) Theta' H y.
     sch_slab_config S S1 S2 Theta /\ &3 <= H /\
     diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
     (!y. y IN sch5v_slab H ==> (Theta y IN S <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
     y IN sch5v_slab H /\ y$3 < &1 /\ Theta y IN S1
     ==> schy_F y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sch_slab_config]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `TN:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (term_match [] `diffeomorphism_on (sch5v_slab H) (s:real^3->bool) (f:real^3->real^3) (g:real^3->real^3)`) (concl th))) THEN
  UNDISCH_TAC `(Theta:real^3->real^3) y IN S1` THEN ASM_REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(Theta:real^3->real^3) y IN S` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 <= --(&7 / &8)` THENL
     [ASM_REWRITE_TAC[schy_F] THEN
      SUBGOAL_THEN `sch_cap_profile(--((y:real^3)$3)) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (term_match [] `sch_slab_nbhd SUBSET n`) (concl th))) THEN
      REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (term_match [] `!y:real^3. y IN N ==> ((Theta:real^3->real^3) y IN E1 <=> P y) /\ Q y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `(y':real^3) IN sch5v_slab H` ASSUME_TAC THENL
     [UNDISCH_TAC `(y':real^3) IN sch_cap1` THEN
      REWRITE_TAC[sch_cap1; sch5v_slab; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPEC `--((y':real^3)$3)` SCHY_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = y'` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y':real^3) IN sch_cap1` THEN REWRITE_TAC[sch_cap1; IN_ELIM_THM; schy_F] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The column lemma in the box.  Along a vertical segment                    *)
(* through a point of S in the box, where X = e3, the only point of S1 is    *)
(* the start, provided no point of the dome projects to the same point.      *)
(* ------------------------------------------------------------------------- *)

let SCHY_BOX_COLUMN = prove
 (`!(S:real^3->bool) S1 (Theta:real^3->real^3) r (X:real^3->real^3) p R.
     schy_chart S r /\ S1 SUBSET S UNION IMAGE Theta sch_cap1 /\
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     p IN S /\ p$1 pow 2 + p$2 pow 2 < r pow 2 /\ abs(p$3) + R < r /\ &0 <= R /\
     (!t. abs t <= R ==> X(p + t % basis 3) = basis 3) /\
     (!y. y IN sch_cap1 /\ ~(Theta y IN S) ==> ~(sch5v_pr(Theta y) = sch5v_pr p))
     ==> !t. abs t <= R /\ ode_vf_flow X (:real^3) (lift t) p IN S1 ==> t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ode_vf_flow (X:real^3->real^3) (:real^3) (lift t) p = p + t % basis 3`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:real^3->real^3`; `{p + s % basis 3:real^3 | abs s <= R}`;
                   `p:real^3`; `lift t`; `basis 3:real^3`] SCH5V_FLOW_TRANSLATE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_ELIM_THM] THEN X_GEN_TAC `u:real^1` THEN
      STRIP_TAC THEN EXISTS_TAC `drop u` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x$1 pow 2 + x$2 pow 2 < r pow 2 /\ abs(x$3) < r
                           ==> (x IN S <=> x$3 = x$1 pow 2 - x$2 pow 2)` (LABEL_TAC "CH") THENL
   [UNDISCH_TAC `schy_chart (S:real^3->bool) r` THEN SIMP_TAC[schy_chart]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3)$3 = p$1 pow 2 - p$2 pow 2` ASSUME_TAC THENL
   [USE_THEN "CH" (MP_TAC o SPEC `p:real^3`) THEN
    REWRITE_TAC[ASSUME `(p:real^3) IN S`;
                ASSUME `(p:real^3)$1 pow 2 + p$2 pow 2 < r pow 2`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^3) + t % basis 3 IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "CH" (MP_TAC o SPEC `(p:real^3) + t % basis 3`) THEN
    REWRITE_TAC[ASSUME `(p:real^3) + t % basis 3 IN S`] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    REWRITE_TAC[ASSUME `(p:real^3)$1 pow 2 + p$2 pow 2 < r pow 2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) + t % basis 3 IN S UNION IMAGE (Theta:real^3->real^3) sch_cap1`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
    can (term_match [] `!y:real^3. y IN sch_cap1 /\ ~((Theta:real^3->real^3) y IN S) ==> ~(P y)`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `(p:real^3) + t % basis 3`)) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO;
           REAL_ADD_RID]);;

(* ------------------------------------------------------------------------- *)
(* The left branch of the hyperbola x1^2 - x2^2 = e near P0,                 *)
(* parametrized by Im U = 2 x1 x2 (schy_gam), and its smoothness.            *)
(* ------------------------------------------------------------------------- *)

let schy_gq = new_definition
 `schy_gq (e:real) (tau:real) = sqrt((sqrt(e pow 2 + tau pow 2) + e) / &2)`;;

let schy_gam = new_definition
 `schy_gam (e:real) (tau:real) =
    vector[--(schy_gq e tau); --(tau / (&2 * schy_gq e tau))]:real^2`;;

let SCHY_GQ_FACTS = prove
 (`!e tau. &0 < e
           ==> &0 < schy_gq e tau /\
               schy_gq e tau pow 2 = (sqrt(e pow 2 + tau pow 2) + e) / &2 /\
               sqrt(e pow 2 + tau pow 2) pow 2 = e pow 2 + tau pow 2 /\
               e <= sqrt(e pow 2 + tau pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `e <= sqrt(e pow 2 + tau pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN MP_TAC(SPEC `tau:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[schy_gq] THEN
  SUBGOAL_THEN `&0 < (sqrt(e pow 2 + tau pow 2) + e) / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC SQRT_POW_2 THEN MP_TAC(SPEC `tau:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let SCHY_GAM_FACTS = prove
 (`!e tau. &0 < e
           ==> (schy_gam e tau)$1 < &0 /\
               (schy_gam e tau)$1 pow 2 - (schy_gam e tau)$2 pow 2 = e /\
               &2 * (schy_gam e tau)$1 * (schy_gam e tau)$2 = tau /\
               schy_gam e (&0) = vector[--(sqrt e); &0]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `tau:real`] SCHY_GQ_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[schy_gam; VECTOR_2] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ABBREV_TAC `q = schy_gq e tau` THEN ABBREV_TAC `s = sqrt(e pow 2 + tau pow 2)` THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_DIV; REAL_POW_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau pow 2 = (s - e) * (s + e)` SUBST1_TAC THENL
     [UNDISCH_TAC `s pow 2 = e pow 2 + tau pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s + e` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < schy_gq e tau` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; schy_gq] THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_ADD_RID; real_div; REAL_MUL_LZERO; REAL_NEG_0] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `(e + e) * inv(&2) = e`]]);;

let SCHY_GAM_SMOOTH = prove
 (`!e s (f:real^N->real).
     &0 < e /\ open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. schy_gam e (f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\x:real^N. lift(schy_gq e (f x)))` ASSUME_TAC THENL
   [REWRITE_TAC[schy_gq] THEN MATCH_MP_TAC SCH3_SL_SQRT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SCH3_SL_DIV THEN ASM_REWRITE_TAC[SCH3_SL_CONST] THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC SCH3_SL_ADD THEN ASM_REWRITE_TAC[SCH3_SL_CONST] THEN
      MATCH_MP_TAC SCH3_SL_SQRT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SCH3_SL_ADD THEN ASM_REWRITE_TAC[SCH3_SL_CONST] THEN
        MATCH_MP_TAC SCH3_SL_POW THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `(f:real^N->real) x` REAL_LE_POW_2) THEN
        MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN
        SUBGOAL_THEN `&0 < e pow 2` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC]];
      GEN_TAC THEN DISCH_TAC THEN
      MP_TAC(SPECL [`e:real`; `(f:real^N->real) x`] SCHY_GQ_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[schy_gam] THEN MATCH_MP_TAC SCH3_SV_VECTOR2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SCH3_SL_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCH3_SL_NEG THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH3_SL_DIV THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH3_SL_MUL THEN ASM_REWRITE_TAC[SCH3_SL_CONST];
      GEN_TAC THEN DISCH_TAC THEN
      MP_TAC(SPECL [`e:real`; `(f:real^N->real) x`] SCHY_GQ_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC]]);;

let SCHY_GAM_CONT = prove
 (`!e eps. &0 < e /\ &0 < eps
           ==> ?d. &0 < d /\ !tau. abs tau < d
                                 ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `(:real^1)`; `drop:real^1->real`] SCHY_GAM_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
  REWRITE_TAC[continuous_at; DROP_VEC] THEN
  MP_TAC(SPEC `e:real` SCHY_GAM_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `&0` th)))]) THEN
  DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift tau`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_0; NORM_LIFT] THEN ASM_REWRITE_TAC[]);;

(* The circle point over the branch point: z(tau) = c'(gamma(tau)).         *)

let SCHY_ZT_BASIC = prove
 (`!(c:real^2->real^2) c' e rs.
     sch_ball c c' /\ &0 < e /\ &0 < rs /\
     c(--basis 1) = vector[--(sqrt e); &0] /\
     (!x. dist(x,vector[--(sqrt e); &0]) < rs
          ==> (x IN IMAGE c (sphere(vec 0,&1)) <=> x$1 pow 2 - x$2 pow 2 = e))
     ==> ?ts. &0 < ts /\
              !tau. abs tau < ts
                    ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                        c(c'(schy_gam e tau)) = schy_gam e tau /\
                        c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                        dist(schy_gam e tau,vector[--(sqrt e); &0]) < rs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `rs:real`] SCHY_GAM_CONT) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ts:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch_ball]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `schy_gam e tau IN IMAGE (c:real^2->real^2) (sphere(vec 0,&1))` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `schy_gam e tau` o check (fun th ->
      can (term_match [] `!x:real^2. dist(x,vector[--(sqrt e); &0]) < rs ==> P x`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`e:real`; `tau:real`] SCHY_GAM_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2)(schy_gam e tau) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SCHY_SPHERE_CURVE = prove
 (`!(Zc:real^1->real^N) t0 O.
     open O /\ t0 IN O /\ (!t. t IN O ==> Zc t dot Zc t = &1) /\ Zc differentiable (at t0)
     ==> Zc t0 dot frechet_derivative Zc (at t0) (vec 1) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  ABBREV_TAC `D = frechet_derivative (Zc:real^1->real^N) (at t0)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x y:real^N. lift(x dot y)`; `Zc:real^1->real^N`; `Zc:real^1->real^N`;
                 `D:real^1->real^N`; `D:real^1->real^N`; `t0:real^1`]
    HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\t. lift((Zc:real^1->real^N) t dot Zc t)) has_derivative (\h. vec 0)) (at t0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\t:real^1. lift(&1)`; `O:real^1->bool`] THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. lift((Zc:real^1->real^N) t dot Zc t)`;
                 `\d:real^1. lift((Zc:real^1->real^N) t0 dot (D:real^1->real^N) d) +
                             lift(D d dot Zc t0)`;
                 `\h:real^1. vec 0:real^1`; `t0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `vec 1:real^1`) THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_NUM; LIFT_EQ] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let SCHY_GAM_D0 = prove
 (`!e. &0 < e
       ==> &2 * --(sqrt e) *
           (frechet_derivative (\t. schy_gam e (drop t)) (at (vec 0)) (vec 1))$2 = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t:real^1. schy_gam e (drop t)) differentiable (at (vec 0))` MP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`e:real`; `(:real^1)`; `drop:real^1->real`] SCHY_GAM_SMOOTH) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
  ABBREV_TAC `D = frechet_derivative (\t:real^1. schy_gam e (drop t)) (at (vec 0))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `bilinear (\(x:real^2) (y:real^2). lift(&2 * x$1 * y$2))` ASSUME_TAC THENL
   [REWRITE_TAC[bilinear; linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD;
                LIFT_CMUL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(x:real^2) (y:real^2). lift(&2 * x$1 * y$2)`; `\t:real^1. schy_gam e (drop t)`;
                 `\t:real^1. schy_gam e (drop t)`; `D:real^1->real^2`; `D:real^1->real^2`;
                 `vec 0:real^1`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\t:real^1. lift(&2 * (schy_gam e (drop t))$1 * (schy_gam e (drop t))$2)) =
                (\t. t)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real^1` THEN
    MP_TAC(SPECL [`e:real`; `drop(t:real^1)`] SCHY_GAM_FACTS) THEN ASM_SIMP_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. lift(&2 * (schy_gam e (drop t))$1 * (schy_gam e (drop t))$2)`;
                 `\d:real^1. lift(&2 * (schy_gam e (drop(vec 0)))$1 * (D d)$2) +
                             lift(&2 * (D d:real^2)$1 * (schy_gam e (drop(vec 0)))$2)`;
                 `\h:real^1. h`; `vec 0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
        `(f has_derivative (f':real^1->real^1)) (at (vec 0))`) (concl th) &&
        not (can (term_match [] `((g:real^1->real^2) has_derivative (D:real^1->real^2)) (at (vec 0))`) (concl th)))) THEN
      REWRITE_TAC[DROP_VEC];
      ASM_REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `vec 1:real^1`) THEN
  MP_TAC(SPEC `e:real` SCHY_GAM_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `&0`) THEN
  REWRITE_TAC[DROP_VEC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_2; REAL_MUL_RZERO; LIFT_NUM; VECTOR_ADD_RID] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC);;

let SCHY_ZT_DERIV = prove
 (`!(c:real^2->real^2) c' e ts.
     sch_ball c c' /\ &0 < e /\ &0 < ts /\ c(--basis 1) = vector[--(sqrt e); &0] /\
     (!tau. abs tau < ts ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                             c'(schy_gam e tau) IN sphere(vec 0,&1))
     ==> smooth_map_on (ball(vec 0,ts)) (\t. c'(schy_gam e (drop t))) /\
         c'(schy_gam e (&0)) = --basis 1 /\
         ~((frechet_derivative (\t. c'(schy_gam e (drop t))) (at (vec 0)) (vec 1))$2 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [sch_ball]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIFFEOMORPHISM_ON_SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (term_match [] `diffeomorphism_on (ball(vec 0:real^2,&2)) t (f:real^2->real^2) g`)
        (concl th))) THEN
  SUBGOAL_THEN `!t:real^1. t IN ball(vec 0,ts) ==> abs(drop t) < ts` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_REAL; GSYM drop]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^1) (\t:real^1. schy_gam e (drop t))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real`; `(:real^1)`; `drop:real^1->real`] SCHY_GAM_SMOOTH) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,ts)) (\t:real^1. (c':real^2->real^2)(schy_gam e (drop t)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^1,ts)`; `IMAGE (c:real^2->real^2) (ball(vec 0,&2))`;
                   `c':real^2->real^2`; `\t:real^1. schy_gam e (drop t)`] SCH3_SV_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2)(schy_gam e (&0)) = --basis 1` ASSUME_TAC THENL
   [MP_TAC(SPEC `e:real` SCHY_GAM_FACTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `&0` th)))]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `(c:real^2->real^2)(--basis 1)`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL_0; NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Zc = \t:real^1. (c':real^2->real^2)(schy_gam e (drop t))` THEN
  SUBGOAL_THEN `(Zc:real^1->real^2) differentiable (at (vec 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^1,ts)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* the first component of the derivative vanishes *)
  SUBGOAL_THEN `((frechet_derivative (Zc:real^1->real^2) (at (vec 0))) (vec 1))$1 = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Zc:real^1->real^2`; `vec 0:real^1`; `ball(vec 0:real^1,ts)`]
      SCHY_SPHERE_CURVE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXPAND_TAC "Zc" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop(t:real^1)` o check (fun th ->
        can (term_match [] `!tau. abs tau < ts ==> P tau`) (concl th))) THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Zc:real^1->real^2)(vec 0) = --basis 1` SUBST1_TAC THENL
     [EXPAND_TAC "Zc" THEN ASM_REWRITE_TAC[DROP_VEC]; ALL_TAC] THEN
    SIMP_TAC[DOT_2; VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the derivative is nonzero *)
  SUBGOAL_THEN `~((frechet_derivative (Zc:real^1->real^2) (at (vec 0))) (vec 1) = vec 0)`
  MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `((frechet_derivative (Zc:real^1->real^2) (at (vec 0))) (vec 1))$1 = &0` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN MESON_TAC[]] THEN
  SUBGOAL_THEN `frechet_derivative (Zc:real^1->real^2) (at (vec 0)) =
                frechet_derivative (c':real^2->real^2) (at (schy_gam e (drop(vec 0)))) o
                frechet_derivative (\t:real^1. schy_gam e (drop t)) (at (vec 0))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(Zc:real^1->real^2) = (c':real^2->real^2) o (\t:real^1. schy_gam e (drop t))`
    SUBST1_TAC THENL [EXPAND_TAC "Zc" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_FD_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (c:real^2->real^2) (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[DROP_VEC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
        can (term_match [] `!tau. abs tau < ts ==> P tau`) (concl th))) THEN
      ASM_SIMP_TAC[REAL_ABS_0]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; DROP_VEC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (c:real^2->real^2) (ball(vec 0,&2))`; `ball(vec 0:real^2,&2)`;
                 `c':real^2->real^2`; `c:real^2->real^2`; `schy_gam e (&0)`;
                 `frechet_derivative (\t:real^1. schy_gam e (drop t)) (at (vec 0)) (vec 1)`]
    SCH4_DIFFEO_DERIV_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (term_match [] `!tau. abs tau < ts ==> P tau`) (concl th))) THEN
    ASM_SIMP_TAC[REAL_ABS_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (c:real^2->real^2) (at (--basis 1)))`
  (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_NEG] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN REWRITE_TAC[VEC_COMPONENT] THEN
  MP_TAC(SPEC `e:real` SCHY_GAM_D0) THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

let schy_bz = new_definition
 `schy_bz (c':real^2->real^2) (e:real) (tau:real) = (c'(schy_gam e tau))$2`;;

let schy_bzd = new_definition
 `schy_bzd (c':real^2->real^2) (e:real) (tau:real) =
    (frechet_derivative (\t. c'(schy_gam e (drop t))) (at (lift tau)) (vec 1))$2`;;

let SCHY_R1_EXPAND = prove
 (`!h:real^1. h = drop h % vec 1`,
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC; REAL_MUL_RID]);;

let SCHY_BZ_FACTS = prove
 (`!(c:real^2->real^2) c' e ts.
     sch_ball c c' /\ &0 < e /\ &0 < ts /\ c(--basis 1) = vector[--(sqrt e); &0] /\
     (!tau. abs tau < ts ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                             c'(schy_gam e tau) IN sphere(vec 0,&1))
     ==> ?t0 kap. &0 < t0 /\ t0 < ts /\ &0 < kap /\
                  !tau. abs tau <= t0
                        ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                            kap <= abs(schy_bzd c' e tau) /\ abs(schy_bzd c' e tau) <= &3 * kap /\
                            abs(schy_bz c' e tau) <= &3 * kap * abs tau /\
                            &0 <= schy_bz c' e tau * schy_bzd c' e tau * tau /\
                            (~(tau = &0) ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `ts:real`] SCHY_ZT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(schy_bzd c' e (&0) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schy_bzd; LIFT_NUM]; ALL_TAC] THEN
  ABBREV_TAC `Zc = \t:real^1. (c':real^2->real^2)(schy_gam e (drop t))` THEN
  SUBGOAL_THEN `!tau. abs tau < ts ==> (Zc:real^1->real^2) differentiable (at (lift tau))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:real^1,ts)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. abs tau < ts
                      ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; schy_bzd] THEN
    SUBGOAL_THEN `(lift o schy_bz c' e o drop) = (\v:real^2. lift(v$2)) o (Zc:real^1->real^2)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Zc" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; schy_bz]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    ABBREV_TAC `D = frechet_derivative (Zc:real^1->real^2) (at (lift tau))` THEN DISCH_TAC THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\h:real^1. drop h % lift(((D:real^1->real^2) (vec 1))$2)) =
                  (\v:real^2. lift(v$2)) o D` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
      SUBGOAL_THEN `linear(D:real^1->real^2)` ASSUME_TAC THENL
       [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
      SUBGOAL_THEN `(D:real^1->real^2) h = drop h % D(vec 1)` SUBST1_TAC THENL
       [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SCHY_R1_EXPAND] THEN
        ASM_SIMP_TAC[LINEAR_CMUL];
        REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_CMUL]];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  (* continuity of the derivative at 0 *)
  SUBGOAL_THEN `(\t:real^1. lift((frechet_derivative (Zc:real^1->real^2) (at t) (vec 1))$2))
                continuous (at (vec 0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^1,ts)`; `Zc:real^1->real^2`; `vec 1:real^1`]
      SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^1,ts)`;
                   `\t:real^1. frechet_derivative (Zc:real^1->real^2) (at t) (vec 1)`; `2`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `kap = abs(schy_bzd c' e (&0)) / &2` THEN
  SUBGOAL_THEN `&0 < kap` ASSUME_TAC THENL
   [EXPAND_TAC "kap" THEN UNDISCH_TAC `~(schy_bzd c' e (&0) = &0)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_at]) THEN
  DISCH_THEN(MP_TAC o SPEC `kap:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!tau. abs tau < d ==> abs(schy_bzd c' e tau - schy_bzd c' e (&0)) < kap`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `lift tau`) THEN
    REWRITE_TAC[DIST_0; NORM_LIFT; DIST_LIFT; schy_bzd; LIFT_NUM] THEN
    EXPAND_TAC "Zc" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min d ts / &2` THEN EXISTS_TAC `kap:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. abs x <= min d ts / &2
                    ==> kap <= abs(schy_bzd c' e x) /\ abs(schy_bzd c' e x) <= &3 * kap /\
                        &0 < schy_bzd c' e x * schy_bzd c' e (&0)` (LABEL_TAC "BD") THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      can (term_match [] `!tau. abs tau < d ==> abs(schy_bzd c' e tau - schy_bzd c' e (&0)) < kap`)
        (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(schy_bzd c' e (&0)) / &2 = kap` THEN
    ASM_CASES_TAC `&0 < schy_bzd c' e (&0)` THENL
     [ALL_TAC;
      SUBGOAL_THEN `schy_bzd c' e (&0) < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
    REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs tau < ts` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "BD" (MP_TAC o SPEC `tau:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[] THEN
  (* mean value theorem between 0 and tau *)
  SUBGOAL_THEN `schy_bz c' e (&0) = &0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schy_bz] THEN SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2;
                                            ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?xi. abs xi <= abs tau /\
                     schy_bz c' e tau = schy_bzd c' e xi * tau` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= tau` THENL
     [MP_TAC(ISPECL [`schy_bz c' e`; `schy_bzd c' e`; `&0`; `tau:real`] REAL_MVT_VERY_SIMPLE);
      MP_TAC(ISPECL [`schy_bz c' e`; `schy_bzd c' e`; `tau:real`; `&0`] REAL_MVT_VERY_SIMPLE)] THEN
    (ANTS_TAC THENL
      [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
       MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
         can (term_match [] `!tau. abs tau < ts ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)`) (concl th))) THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `xi:real` THEN CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `schy_bz c' e (&0) = &0` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "BD" (MP_TAC o SPEC `xi:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < schy_bzd c' e xi * schy_bzd c' e tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (schy_bzd c' e xi * schy_bzd c' e (&0)) *
                       (schy_bzd c' e tau * schy_bzd c' e (&0))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(a * c) * (b * c) = (a * b) * c pow 2`] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN
    MP_TAC(SPEC `schy_bzd c' e (&0)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(schy_bzd c' e xi * tau) * schy_bzd c' e tau * tau =
                (schy_bzd c' e xi * schy_bzd c' e tau) * tau pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE]]);;

(* ------------------------------------------------------------------------- *)
(* The box points near lpt in the chart.  The point of S over                *)
(* (-t,w) is Theta of the circle point z(-2tw) at height (t^2-w^2-e)/lam.    *)
(* ------------------------------------------------------------------------- *)

let SCHY_BOX_AGREE = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) c' delta1 lam H (Theta:real^3->real^3)
    Theta' tau t w.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ sch_ball c c' /\ &0 < e /\
     schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
     dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2 /\
     &0 < t /\ tau = --(&2 * t * w) /\ abs((t pow 2 - w pow 2 - e) / lam) < H
     ==> Theta(sch5v_at ((t pow 2 - w pow 2 - e) / lam) (c'(schy_gam e tau))) =
         vector[--t; w; t pow 2 - w pow 2]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `tau = --(&2 * t * w)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (v:real^3->real^3) /\
                (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
                (!y. norm(v y) <= B) /\
                (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0) /\
                &0 < lam /\ B * lam * H < rho0 / &2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_cd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Theta:real^3->real^3) y =
                    ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))`
  (LABEL_TAC "TH") THENL
   [UNDISCH_TAC `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    SIMP_TAC[schy_cd];
    ALL_TAC] THEN
  ABBREV_TAC `Y = (t pow 2 - w pow 2 - e) / lam` THEN
  SUBGOAL_THEN `t pow 2 - w pow 2 - e = lam * Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->real^2)(c'(schy_gam e tau)) = schy_gam e tau` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch_ball]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `B * abs(lam * Y) < rho0 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * lam * H` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(sch5v_at e (schy_gam e tau),schy_lpt e) < rho0 / &2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SCHY_LPT_AT; SCHY_AT_DIST]; ALL_TAC] THEN
  ABBREV_TAC `p = (Theta:real^3->real^3)(sch5v_at Y (c'(schy_gam e tau)))` THEN
  SUBGOAL_THEN `(p:real^3) = ode_vf_flow v (:real^3) (lift(lam * Y)) (sch5v_at e (schy_gam e tau))`
  ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th; SCH5V_PR_AT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_pi p = schy_pi(sch5v_at e (schy_gam e tau)) + (lam * Y) % vector[&1; &0; &1]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_THETA_PI THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `rho0:real`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (x:real^3)$1 pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(p:real^3,schy_lpt e) < rho0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`sch5v_at e (schy_gam e tau)`; `lift(lam * Y)`; `vec 0:real^1`]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
      (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
    ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_SUB_RZERO; GSYM dist] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^3`; `sch5v_at e (schy_gam e tau)`; `schy_lpt e`] DIST_TRIANGLE) THEN
    UNDISCH_TAC `dist(ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * Y))
                   (sch5v_at e (schy_gam e tau)),sch5v_at e (schy_gam e tau)) <= B * abs(lam * Y)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SCHY_PI_INJ THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0`)
        (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`e:real`; `tau:real`] SCHY_GAM_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[schy_pi; sch5v_at; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `t pow 2 - w pow 2 - e = lam * Y`) THEN
  MP_TAC(ASSUME `--(&2 * t * w) = tau`) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The strip.  Coordinates z = (t,w).  Box part (-t,w,t^2-w^2)               *)
(* for t <= tb; model part Theta(m) beyond, with m = ma (polar form over the *)
(* dome, B coordinate B0 = b(-2tw)) for t <= tm and m = mb (Cartesian near  *)
(* the tip) beyond.  be blends the height from t^2 - w^2 to t^2 - lam B0^2.  *)
(* ------------------------------------------------------------------------- *)

let schy_B0 = new_definition
 `schy_B0 (c':real^2->real^2) e (z:real^2) = schy_bz c' e (--(&2 * z$1 * z$2))`;;

let schy_G = new_definition
 `schy_G (c':real^2->real^2) e lam (be:real->real) (z:real^2) =
    (&1 - be(z$1)) * z$2 pow 2 + be(z$1) * lam * schy_B0 c' e z pow 2`;;

let schy_Ya = new_definition
 `schy_Ya (c':real^2->real^2) e lam (be:real->real) (z:real^2) =
    (z$1 pow 2 - e - schy_G c' e lam be z) / lam`;;

let schy_ma = new_definition
 `schy_ma (c':real^2->real^2) e lam (be:real->real) (z:real^2) =
    vector[--(sqrt(sch_cap_profile(--(schy_Ya c' e lam be z)) - schy_B0 c' e z pow 2));
           schy_B0 c' e z; schy_Ya c' e lam be z]:real^3`;;

let schy_mb = new_definition
 `schy_mb (c':real^2->real^2) e (A0:real->real) (z:real^2) =
    vector[A0(z$1); schy_B0 c' e z; --(&1 / &2) - A0(z$1) pow 2 - schy_B0 c' e z pow 2]:real^3`;;

let schy_sbox = new_definition
 `schy_sbox (z:real^2) = vector[--(z$1); z$2; z$1 pow 2 - z$2 pow 2]:real^3`;;

let schy_strip = new_definition
 `schy_strip (Theta:real^3->real^3) (c':real^2->real^2) e lam (be:real->real) A0 tb tm
             (z:real^2) =
    if z$1 <= tb then schy_sbox z
    else Theta(if z$1 <= tm then schy_ma c' e lam be z else schy_mb c' e A0 z)`;;

(* The box point near lpt is Theta of ma when be = 0 and the height is on the cylinder. *)

let SCHY_BOX_MA = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) c' delta1 lam H (Theta:real^3->real^3)
    Theta' (be:real->real) (z:real^2).
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ sch_ball c c' /\ &0 < e /\
     schy_gam e (--(&2 * z$1 * z$2)) IN IMAGE c (ball(vec 0,&2)) /\
     c'(schy_gam e (--(&2 * z$1 * z$2))) IN sphere(vec 0,&1) /\
     (c'(schy_gam e (--(&2 * z$1 * z$2))))$1 < &0 /\
     dist(schy_gam e (--(&2 * z$1 * z$2)),vector[--(sqrt e); &0]) < rho0 / &2 /\
     &0 < z$1 /\ be(z$1) = &0 /\
     abs((z$1 pow 2 - z$2 pow 2 - e) / lam) < H /\
     (z$1 pow 2 - z$2 pow 2 - e) / lam <= --(&7 / &8)
     ==> Theta(schy_ma c' e lam be z) = schy_sbox z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `c':real^2->real^2`; `delta1:real`; `lam:real`; `H:real`;
                 `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                 `--(&2 * (z:real^2)$1 * z$2)`; `(z:real^2)$1`; `(z:real^2)$2`]
    SCHY_BOX_AGREE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[schy_sbox] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `schy_Ya c' e lam be (z:real^2) = (z$1 pow 2 - z$2 pow 2 - e) / lam` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schy_Ya; schy_G] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[schy_ma; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC[schy_B0; schy_bz] THEN
  SUBGOAL_THEN `sch_cap_profile(--(((z:real^2)$1 pow 2 - z$2 pow 2 - e) / lam)) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (c':real^2->real^2)(schy_gam e (--(&2 * (z:real^2)$1 * z$2)))` THEN
  UNDISCH_TAC `(q:real^2) IN sphere(vec 0,&1)` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 - (q:real^2)$2 pow 2 = q$1 pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `(q:real^2)$1 * q$1 + q$2 * q$2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT_ABS] THEN ASM_REAL_ARITH_TAC);;

let SCHY_MA_MB = prove
 (`!(c':real^2->real^2) e lam (be:real->real) (A0:real->real) (z:real^2).
     &0 < lam /\ be(z$1) = &1 /\
     A0(z$1) = --(sqrt(e / lam - &1 / &2 - z$1 pow 2 / lam)) /\
     &0 < e / lam - &1 / &2 - z$1 pow 2 / lam /\
     --(schy_Ya c' e lam be z) <= &5 / &8
     ==> schy_ma c' e lam be z = schy_mb c' e A0 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_Ya c' e lam be (z:real^2) =
                (z$1 pow 2 - e) / lam - schy_B0 c' e z pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[schy_Ya; schy_G] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile(--(schy_Ya c' e lam be (z:real^2))) =
                --(schy_Ya c' e lam be z) - &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_TIP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[schy_ma; schy_mb; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REAL_ARITH `y = x:real ==> x = y`) THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    SUBGOAL_THEN `sqrt(e / lam - &1 / &2 - (z:real^2)$1 pow 2 / lam) pow 2 =
                  e / lam - &1 / &2 - z$1 pow 2 / lam` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD]);;

(* A connected subset of S off Theta(lat) that meets the lower cylinder lies in S1. *)

let SCHY_SLAB_CONN = prove
 (`!S S1 S2 (Theta:real^3->real^3) K.
     sch_slab_config S S1 S2 Theta /\ closed S1 /\ closed S2 /\
     connected K /\ K SUBSET S /\ (!y. y IN sch_lat ==> ~(Theta y IN K)) /\
     (?y. y IN sch_slab_nbhd /\ y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < -- &1 /\ Theta y IN K)
     ==> K SUBSET S1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `TN:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (term_match [] `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta g`) (concl th))) THEN
  SUBGOAL_THEN `sch_lat SUBSET N /\ sch_cap1 SUBSET N /\ sch_cap2 SUBSET N /\
                (y0:real^3) IN N` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `sch_slab_nbhd SUBSET n`) (concl th))) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `sch_slab_nbhd` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; sch_lat; sch_cap1; sch_cap2; sch_slab_nbhd; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN TRY(MP_TAC(SPEC `--((x:real^3)$3)` SCHY_PROFILE_LE1)) THEN
    TRY(MP_TAC(SPEC `(x:real^3)$3` SCHY_PROFILE_LE1)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN N ==> ((Theta:real^3->real^3) y IN E1 ==> y$3 < -- &1) /\
                               (Theta y IN E2 ==> &1 < y$3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (Theta:real^3->real^3) sch_cap1) E2 /\
                DISJOINT (E1:real^3->bool) (IMAGE (Theta:real^3->real^3) sch_cap2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN CONJ_TAC THEN
    X_GEN_TAC `x:real^3` THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN sch_cap1` THEN REWRITE_TAC[sch_cap1; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_ARITH `y <= --(&1 / &2) ==> ~(&1 < y)`];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_ARITH `&1 / &2 <= y ==> ~(y < -- &1)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure E1 SUBSET (S1:real^3->bool) /\ closure E2 SUBSET (S2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (closure E1) (E2:real^3->bool) /\ DISJOINT (E1:real^3->bool) (closure E2)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET E1 UNION E2` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:real^3->bool) SUBSET S` THEN
    UNDISCH_TAC `!y. y IN sch_lat ==> ~((Theta:real^3->real^3) y IN K)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) y0 IN E1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^3->bool) INTER E2 = {}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED] o check (fun th ->
      concl th = `connected (K:real^3->bool)`)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`closure(E1:real^3->bool)`; `closure(E2:real^3->bool)`]) THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN
    MP_TAC(ISPEC `E1:real^3->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPEC `E2:real^3->bool` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `DISJOINT (closure E1) (E2:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (E1:real^3->bool) (closure E2)` THEN
    UNDISCH_TAC `(K:real^3->bool) SUBSET E1 UNION E2` THEN
    UNDISCH_TAC `(Theta:real^3->real^3) y0 IN E1` THEN
    UNDISCH_TAC `(Theta:real^3->real^3) y0 IN K` THEN
    UNDISCH_TAC `DISJOINT (E1:real^3->bool) E2` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(K:real^3->bool) SUBSET E1 UNION E2` THEN
  UNDISCH_TAC `(K:real^3->bool) INTER E2 = {}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One-variable functions of the strip.  f1(t) is the ridge                  *)
(* coordinate A on the paraboloid at height t^2; A0 blends f1 into the line  *)
(* t - ta through the tip ta = sqrt(e - lam/2); H0 = e - lam/2 - lam A0^2 is *)
(* the ridge height (= t^2 where A0 = f1).                                   *)
(* ------------------------------------------------------------------------- *)

let schy_ta = new_definition
 `schy_ta e lam = sqrt(e - lam / &2)`;;

let schy_f1 = new_definition
 `schy_f1 e lam t = --(sqrt((schy_ta e lam pow 2 - t pow 2) / lam))`;;

let schy_A0 = new_definition
 `schy_A0 e lam m1 m2 t =
    (&1 - smooth_step((t - m1) / (m2 - m1))) * schy_f1 e lam t +
    smooth_step((t - m1) / (m2 - m1)) * (t - schy_ta e lam)`;;

let schy_H0 = new_definition
 `schy_H0 e lam m1 m2 t = e - lam / &2 - lam * schy_A0 e lam m1 m2 t pow 2`;;

let SCHY_TA_FACTS = prove
 (`!e lam. &0 < lam /\ lam < e
           ==> &0 < schy_ta e lam /\ schy_ta e lam pow 2 = e - lam / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[schy_ta] THEN
  SUBGOAL_THEN `&0 < e - lam / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]);;

let SCHY_F1_FACTS = prove
 (`!e lam t. &0 < lam /\ lam < e /\ abs t < schy_ta e lam
             ==> schy_f1 e lam t < &0 /\
                 schy_f1 e lam t pow 2 = (schy_ta e lam pow 2 - t pow 2) / lam /\
                 e - lam / &2 - lam * schy_f1 e lam t pow 2 = t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < schy_ta e lam` ASSUME_TAC THENL
   [MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (schy_ta e lam pow 2 - t pow 2) / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[schy_f1; REAL_POW_NEG; ARITH] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_ARITH `&0 < x ==> --x < &0`] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD);;

let SCHY_F1_DERIV = prove
 (`!e lam t. &0 < lam /\ lam < e /\ abs t < schy_ta e lam
             ==> (schy_f1 e lam has_real_derivative
                  (t / (lam * sqrt((schy_ta e lam pow 2 - t pow 2) / lam)))) (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_F1_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (schy_ta e lam pow 2 - t pow 2) / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = (schy_ta e lam pow 2 - t pow 2) / lam` THEN
  SUBGOAL_THEN `schy_f1 e lam = (\x. --(sqrt((schy_ta e lam pow 2 - x pow 2) / lam)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_f1]; ALL_TAC] THEN
  SUBGOAL_THEN `t / (lam * sqrt q) = --(inv(&2 * sqrt q) * (--(&2 * t) / lam))` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt q` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
  MP_TAC(ISPECL [`\x. (schy_ta e lam pow 2 - x pow 2) / lam`; `sqrt`; `--(&2 * t) / lam`;
                 `inv(&2 * sqrt q)`; `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    MP_TAC(ISPECL [`\x:real. schy_ta e lam pow 2`; `&0`; `\x:real. x pow 2`; `&2 * t`;
                   `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_LZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `t:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1; REAL_MUL_RID];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[]]);;

let SCHY_SSD_FLAT = prove
 (`!u. u <= &0 \/ &1 <= u ==> schy_ssd u = &0`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
  MAP_EVERY EXISTS_TAC [`smooth_step`; `u:real`; `(:real)`] THEN
  REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV; SCHY_SSD_FACTS] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [DISJ2_TAC THEN ASM_SIMP_TAC[SMOOTH_STEP_0; SMOOTH_STEP_BOUNDS];
    DISJ1_TAC THEN ASM_SIMP_TAC[SMOOTH_STEP_1; SMOOTH_STEP_BOUNDS]]);;

let schy_f1d = new_definition
 `schy_f1d e lam t = t / (lam * sqrt((schy_ta e lam pow 2 - t pow 2) / lam))`;;

let schy_A0d = new_definition
 `schy_A0d e lam m1 m2 t =
    (&1 - smooth_step((t - m1) / (m2 - m1))) * schy_f1d e lam t +
    smooth_step((t - m1) / (m2 - m1)) +
    schy_ssd((t - m1) / (m2 - m1)) / (m2 - m1) * (t - schy_ta e lam - schy_f1 e lam t)`;;

let SCHY_A0_FACTS = prove
 (`!e lam m1 m2.
     &0 < lam /\ lam < e /\ lam <= &1 /\ &0 < m1 /\ m1 < m2 /\ m2 < schy_ta e lam
     ==> (!t. t <= m1 ==> schy_A0 e lam m1 m2 t = schy_f1 e lam t) /\
         (!t. m2 <= t ==> schy_A0 e lam m1 m2 t = t - schy_ta e lam) /\
         (!t. &0 < t ==> (schy_A0 e lam m1 m2 has_real_derivative schy_A0d e lam m1 m2 t)
                         (atreal t) /\ &0 < schy_A0d e lam m1 m2 t) /\
         (!t. m2 <= t ==> schy_A0d e lam m1 m2 t = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < m2 - m1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t <= m1 ==> smooth_step((t - m1) / (m2 - m1)) = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. m2 <= t ==> smooth_step((t - m1) / (m2 - m1)) = &1 /\
                                schy_ssd((t - m1) / (m2 - m1)) = &0` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= (t - m1) / (m2 - m1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SMOOTH_STEP_1; SCHY_SSD_FLAT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[schy_A0] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[schy_A0] THEN REAL_ARITH_TAC;
    ALL_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[schy_A0d] THEN REAL_ARITH_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `m2 < t` THENL
   [(* locally A0 is the line *)
    ASM_SIMP_TAC[schy_A0d; REAL_LT_IMP_LE] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
                REAL_ARITH `&0 / x = &0`] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x. x - schy_ta e lam`; `t - m2`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[schy_A0] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        can (term_match [] `!t. m2 <= t ==> smooth_step((t - m1) / (m2 - m1)) = &1 /\ Q t`)
          (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\x:real. x`; `&1`; `\x:real. schy_ta e lam`; `&0`; `atreal t`]
        HAS_REAL_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO]];
    ALL_TAC] THEN
  (* t <= m2 < ta: f1 is differentiable *)
  SUBGOAL_THEN `abs t < schy_ta e lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_F1_DERIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_F1_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `u = (t - m1) / (m2 - m1)` THEN
  SUBGOAL_THEN `((\x. smooth_step((x - m1) / (m2 - m1))) has_real_derivative
                 schy_ssd u * inv(m2 - m1)) (atreal t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (x - m1) / (m2 - m1)`; `smooth_step`; `inv(m2 - m1)`;
                   `schy_ssd u`; `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[SCHY_SSD_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`\x:real. x - m1`; `&1`; `inv(m2 - m1)`; `t:real`]
      HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `\x:real. (m1:real)`; `&0`; `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `schy_A0 e lam m1 m2 =
                  (\x. (&1 - smooth_step((x - m1) / (m2 - m1))) * schy_f1 e lam x +
                       smooth_step((x - m1) / (m2 - m1)) * (x - schy_ta e lam))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; schy_A0]; ALL_TAC] THEN
    SUBGOAL_THEN `schy_A0d e lam m1 m2 t =
                  ((&1 - smooth_step u) * schy_f1d e lam t +
                   (&0 - schy_ssd u * inv(m2 - m1)) * schy_f1 e lam t) +
                  (smooth_step u * &1 + schy_ssd u * inv(m2 - m1) * (t - schy_ta e lam))`
    SUBST1_TAC THENL
     [REWRITE_TAC[schy_A0d] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. &1 - smooth_step((x - m1) / (m2 - m1))`;
                     `&0 - schy_ssd u * inv(m2 - m1)`; `schy_f1 e lam`;
                     `schy_f1d e lam t`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[schy_f1d] THEN ANTS_TAC THENL
       [MP_TAC(ISPECL [`\x:real. &1`; `&0`; `\x. smooth_step((x - m1) / (m2 - m1))`;
                       `schy_ssd u * inv(m2 - m1)`; `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
        ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\x. smooth_step((x - m1) / (m2 - m1))`; `schy_ssd u * inv(m2 - m1)`;
                     `\x:real. x - schy_ta e lam`; `&1`; `t:real`]
        HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MP_TAC(ISPECL [`\x:real. x`; `&1`; `\x:real. schy_ta e lam`; `&0`; `atreal t`]
          HAS_REAL_DERIVATIVE_SUB) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* positivity *)
  SUBGOAL_THEN `&0 < schy_f1d e lam t` ASSUME_TAC THENL
   [REWRITE_TAC[schy_f1d] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t - schy_ta e lam - schy_f1 e lam t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a - t <= --f ==> &0 <= t - a - f`) THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `(schy_ta e lam - t) pow 2 * lam <= (schy_ta e lam - t) pow 2` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(schy_ta e lam - t) pow 2 <= schy_ta e lam pow 2 - t pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `&0 <= t * (schy_ta e lam - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[schy_A0d] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `u:real` SMOOTH_STEP_BOUNDS) THEN MP_TAC(SPEC `u:real` SCHY_SSD_FACTS) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a + b /\ &0 <= c ==> &0 < a + b + c`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `smooth_step u = &1` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC]);;

(* A real function smooth on the line has a bounded derivative on bounded intervals. *)

let SCHY_DERIV_BOUNDED = prove
 (`!(f:real->real) fd a b.
     smooth_map_on (:real^1) (lift o f o drop) /\
     (!t. (f has_real_derivative fd t) (atreal t))
     ==> ?P. &0 < P /\ !t. a <= t /\ t <= b ==> abs(fd t) <= P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. fd t = drop(frechet_derivative (lift o f o drop) (at (lift t)) (vec 1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o (f:real->real) o drop`; `vec 1:real^1`]
    SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (\x:real^1. frechet_derivative (lift o (f:real->real) o drop) (at x) (vec 1))
                              (interval[lift a,lift b]))` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `P:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= n ==> n <= P ==> abs x <= P`) THEN
  REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP; REAL_LE_REFL]);;

let SCHY_OPEN_HALFLINES = prove
 (`!a. open {t:real^1 | drop t < a} /\ open {t:real^1 | a < drop t} /\
       open {t:real^1 | abs(drop t) < a}`,
  GEN_TAC THEN REWRITE_TAC[drop] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
    SUBGOAL_THEN `{t:real^1 | abs(t$1) < a} = ball(vec 0,a)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0; NORM_REAL; GSYM drop]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_BALL]]);;

let SCHY_A0_SMOOTH = prove
 (`!e lam m1 m2.
     &0 < lam /\ lam < e /\ lam <= &1 /\ &0 < m1 /\ m1 < m2 /\ m2 < schy_ta e lam
     ==> smooth_map_on {t:real^1 | &0 < drop t} (lift o schy_A0 e lam m1 m2 o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN ASM_CASES_TAC `drop(t:real^1) < schy_ta e lam` THENL
   [EXISTS_TAC `{x:real^1 | abs(drop x) < schy_ta e lam}` THEN
    REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_DEF; schy_A0; schy_f1] THEN
    MP_TAC(ISPEC `schy_ta e lam` SCHY_OPEN_HALFLINES) THEN STRIP_TAC THEN
    SUBGOAL_THEN `!x:real^1. x IN {x | abs(drop x) < schy_ta e lam}
                             ==> &0 < (schy_ta e lam pow 2 - drop x pow 2) / lam` ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^1. x IN {x | abs(drop x) < schy_ta e lam} ==> ~(m2 - m1 = &0) /\ ~(lam = &0)`
    ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SCHY_SMOOTH_TAC THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `{x:real^1 | m2 < drop x}` THEN REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\x:real^1. lift(drop x - schy_ta e lam)` THEN
    REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM; o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL [`e:real`; `lam:real`; `m1:real`; `m2:real`] SCHY_A0_FACTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[SCHY_OPEN_HALFLINES; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]]);;

let schy_Hr = new_definition
 `schy_Hr e lam m1 m2 t = if t <= m1 then t pow 2 else schy_H0 e lam m1 m2 t`;;

let schy_Hrd = new_definition
 `schy_Hrd e lam m1 m2 t =
    if t <= &0 then &2 * t
    else --(&2 * lam * schy_A0 e lam m1 m2 t * schy_A0d e lam m1 m2 t)`;;

let SCHY_HR_FACTS = prove
 (`!e lam m1 m2.
     &0 < lam /\ lam < e /\ lam <= &1 /\ &0 < m1 /\ m1 < m2 /\ m2 < schy_ta e lam
     ==> (!t. &0 < t ==> schy_Hr e lam m1 m2 t = schy_H0 e lam m1 m2 t) /\
         (!t. t <= m1 ==> schy_Hr e lam m1 m2 t = t pow 2) /\
         (!t. m2 <= t ==> schy_Hr e lam m1 m2 t =
                          e - lam / &2 - lam * (t - schy_ta e lam) pow 2) /\
         (!t. (schy_Hr e lam m1 m2 has_real_derivative schy_Hrd e lam m1 m2 t) (atreal t)) /\
         (!t. &0 <= t ==> schy_Hr e lam m1 m2 t <= e - lam / &2) /\
         (!t. t < &0 \/ schy_ta e lam < t ==> schy_Hrd e lam m1 m2 t < &0) /\
         smooth_map_on (:real^1) (lift o schy_Hr e lam m1 m2 o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `m1:real`; `m2:real`] SCHY_A0_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 < t ==> schy_Hr e lam m1 m2 t = schy_H0 e lam m1 m2 t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[schy_Hr] THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_F1_FACTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_SIMP_TAC[schy_H0] THEN TRY(UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD);
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t <= m1 ==> schy_Hr e lam m1 m2 t = t pow 2` ASSUME_TAC THENL
   [SIMP_TAC[schy_Hr]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[schy_H0]];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[schy_Hrd] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\x:real. x pow 2`; `m1 - t`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!t. t <= m1 ==> schy_Hr e lam m1 m2 t = t pow 2`) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`\x:real. x`; `&1`; `t:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[REAL_POW_1; REAL_MUL_RID]];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`schy_H0 e lam m1 m2`; `t:real`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!t. &0 < t ==> schy_Hr e lam m1 m2 t = schy_H0 e lam m1 m2 t`) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `schy_H0 e lam m1 m2 = (\x. e - lam / &2 - lam * schy_A0 e lam m1 m2 x pow 2)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_H0]; ALL_TAC] THEN
        SUBGOAL_THEN `--(&2 * lam * schy_A0 e lam m1 m2 t * schy_A0d e lam m1 m2 t) =
                      &0 - lam * (&2 * schy_A0 e lam m1 m2 t pow (2 - 1) * schy_A0d e lam m1 m2 t)`
        SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_POW_ATREAL THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
          can (term_match [] `!t. &0 < t ==> (A has_real_derivative B t) (atreal t) /\ C t`)
            (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ETA_AX]]]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_CASES_TAC `t <= m1` THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m1 pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `m1 pow 2 <= schy_ta e lam pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[schy_H0] THEN
      MP_TAC(SPEC `schy_A0 e lam m1 m2 t` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `&0 <= lam * schy_A0 e lam m1 m2 t pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_THEN DISJ_CASES_TAC THEN REWRITE_TAC[schy_Hrd] THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(t <= &0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < schy_A0 e lam m1 m2 t` ASSUME_TAC THENL
     [ASM_CASES_TAC `m2 <= t` THENL
       [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (term_match [] `!t. &0 < t ==> (A has_real_derivative B t) (atreal t) /\ C t`)
        (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    (* smoothness *)
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `t:real^1` THEN ASM_CASES_TAC `drop(t:real^1) < m1` THENL
     [EXISTS_TAC `{x:real^1 | drop x < m1}` THEN ASM_REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:real^1. lift(drop x pow 2)` THEN
      REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM; o_THM] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPEC `m1:real` SCHY_OPEN_HALFLINES) THEN STRIP_TAC THEN
        SCHY_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID]];
      EXISTS_TAC `{x:real^1 | &0 < drop x}` THEN REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `\x:real^1. lift(e - lam / &2 - lam * drop((lift o schy_A0 e lam m1 m2 o drop) x) pow 2)` THEN
      REWRITE_TAC[SCHY_OPEN_HALFLINES; IN_ELIM_THM; o_THM; LIFT_DROP] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        ASM_SIMP_TAC[schy_H0];
        MP_TAC(SPECL [`e:real`; `lam:real`; `m1:real`; `m2:real`] SCHY_A0_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MP_TAC(ISPEC `&0` SCHY_OPEN_HALFLINES) THEN STRIP_TAC THEN
        SCHY_SMOOTH_TAC THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
        UNDISCH_TAC `smooth_map_on {t:real^1 | &0 < drop t} (lift o schy_A0 e lam m1 m2 o drop)` THEN
        REWRITE_TAC[o_DEF]]]]);;

(* ------------------------------------------------------------------------- *)
(* Step functions.  schy_st a b goes from 0 (t <= a) to 1                    *)
(* (t >= b); schy_bw a w = 1 - st(w^2/a^2) is the even transversal profile;  *)
(* schy_cut a1 b1 a2 b2 is 1 on [b1,a2] and 0 off (a1,b2).                   *)
(* ------------------------------------------------------------------------- *)

let schy_st = new_definition
 `schy_st a b t = smooth_step((t - a) / (b - a))`;;

let SCHY_ST_FACTS = prove
 (`!a b. a < b
         ==> (!t. t <= a ==> schy_st a b t = &0) /\
             (!t. b <= t ==> schy_st a b t = &1) /\
             (!t. &0 <= schy_st a b t /\ schy_st a b t <= &1) /\
             (!t. (schy_st a b has_real_derivative schy_ssd((t - a) / (b - a)) / (b - a))
                  (atreal t)) /\
             (!t. &0 <= schy_ssd((t - a) / (b - a)) / (b - a)) /\
             (!t. t <= a \/ b <= t ==> schy_ssd((t - a) / (b - a)) / (b - a) = &0) /\
             smooth_map_on (:real^1) (lift o schy_st a b o drop)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[schy_st; SMOOTH_STEP_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN
    SUBGOAL_THEN `schy_st a b = (\x. smooth_step((x - a) * inv(b - a)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; schy_st; real_div]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`\x. (x - a) * inv(b - a)`; `smooth_step`; `inv(b - a)`;
                   `schy_ssd((t - a) * inv(b - a))`; `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF; SCHY_SSD_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\x:real. x - a`; `&1`; `inv(b - a)`; `t:real`]
      HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `\x:real. (a:real)`; `&0`; `atreal t`]
      HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO];
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[SCHY_SSD_FACTS] THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC SCHY_SSD_FLAT THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO; REAL_MUL_LID;
                 GSYM real_div] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_DEF; schy_st] THEN MATCH_MP_TAC SCHY_SL_SSTEP THEN REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC(INST_TYPE [`:1`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!x:real^1. x IN (:real^1) ==> ~(b - a = &0)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SCHY_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC]);;

let schy_bw = new_definition
 `schy_bw a w = &1 - smooth_step(w pow 2 / a pow 2)`;;

let SCHY_BW_FACTS = prove
 (`!a. &0 < a
       ==> schy_bw a (&0) = &1 /\
           (!w. &0 <= schy_bw a w /\ schy_bw a w <= &1) /\
           (!w. a <= abs w ==> schy_bw a w = &0) /\
           (!w. (schy_bw a has_real_derivative
                 --(schy_ssd(w pow 2 / a pow 2) * (&2 * w) * inv(a pow 2))) (atreal w)) /\
           (!w. &0 <= w ==> --(schy_ssd(w pow 2 / a pow 2) * (&2 * w) * inv(a pow 2)) <= &0) /\
           (!w. w <= &0 ==> &0 <= --(schy_ssd(w pow 2 / a pow 2) * (&2 * w) * inv(a pow 2))) /\
           smooth_map_on (:real^1) (lift o schy_bw a o drop)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(a pow 2)` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[schy_bw; REAL_POW_ZERO; ARITH; real_div; REAL_MUL_LZERO] THEN
    SIMP_TAC[SMOOTH_STEP_0; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[schy_bw] THEN
    MP_TAC(SPEC `w pow 2 / a pow 2` SMOOTH_STEP_BOUNDS) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[schy_bw] THEN
    SUBGOAL_THEN `smooth_step(w pow 2 / a pow 2) = &1` (fun th -> REWRITE_TAC[th] THEN
      REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN
    SUBGOAL_THEN `schy_bw a = (\w. &1 - smooth_step(w pow 2 * inv(a pow 2)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; schy_bw; real_div]; ALL_TAC] THEN
    SUBGOAL_THEN `--(schy_ssd(w pow 2 / a pow 2) * (&2 * w) * inv(a pow 2)) =
                  &0 - schy_ssd(w pow 2 * inv(a pow 2)) * (&2 * w pow (2 - 1) * &1) * inv(a pow 2)`
    SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_div; REAL_POW_1] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    MP_TAC(ISPECL [`\w:real. w pow 2 * inv(a pow 2)`; `smooth_step`;
                   `(&2 * w pow (2 - 1) * &1) * inv(a pow 2)`;
                   `schy_ssd(w pow 2 * inv(a pow 2))`; `w:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF; SCHY_SSD_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_POW_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[SCHY_SSD_FACTS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `--(s * (&2 * w) * i) = s * (&2 * --w) * i`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[SCHY_SSD_FACTS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_DEF; schy_bw] THEN
    MP_TAC(INST_TYPE [`:1`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!x:real^1. x IN (:real^1) ==> ~(a pow 2 = &0)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SCHY_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC]);;

let schy_cut = new_definition
 `schy_cut a1 b1 a2 b2 t = schy_st a1 b1 t * (&1 - schy_st a2 b2 t)`;;

let schy_cutd = new_definition
 `schy_cutd a1 b1 a2 b2 t =
    schy_st a1 b1 t * (&0 - schy_ssd((t - a2) / (b2 - a2)) / (b2 - a2)) +
    schy_ssd((t - a1) / (b1 - a1)) / (b1 - a1) * (&1 - schy_st a2 b2 t)`;;

let SCHY_CUT_FACTS = prove
 (`!a1 b1 a2 b2. a1 < b1 /\ b1 <= a2 /\ a2 < b2
     ==> (!t. b1 <= t /\ t <= a2 ==> schy_cut a1 b1 a2 b2 t = &1) /\
         (!t. t <= a1 \/ b2 <= t ==> schy_cut a1 b1 a2 b2 t = &0) /\
         (!t. &0 <= schy_cut a1 b1 a2 b2 t /\ schy_cut a1 b1 a2 b2 t <= &1) /\
         (!t. (schy_cut a1 b1 a2 b2 has_real_derivative schy_cutd a1 b1 a2 b2 t) (atreal t)) /\
         (!t. b1 <= t /\ t <= a2 ==> schy_cutd a1 b1 a2 b2 t = &0) /\
         (!t. t <= a1 \/ b2 <= t ==> schy_cutd a1 b1 a2 b2 t = &0) /\
         smooth_map_on (:real^1) (lift o schy_cut a1 b1 a2 b2 o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a1:real`; `b1:real`] SCHY_ST_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a2:real`; `b2:real`] SCHY_ST_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_cut a1 b1 a2 b2 = (\t. schy_st a1 b1 t * (&1 - schy_st a2 b2 t))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_cut]; ALL_TAC] THEN
  REWRITE_TAC[schy_cutd] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_UNIT_MUL THEN
    SUBGOAL_THEN `&0 <= schy_st a1 b1 t /\ schy_st a1 b1 t <= &1 /\
                  &0 <= schy_st a2 b2 t /\ schy_st a2 b2 t <= &1` MP_TAC THENL
     [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    GEN_TAC THEN
    MP_TAC(ISPECL [`schy_st a1 b1`; `schy_ssd((t - a1) / (b1 - a1)) / (b1 - a1)`;
                   `\t. &1 - schy_st a2 b2 t`;
                   `&0 - schy_ssd((t - a2) / (b2 - a2)) / (b2 - a2)`; `t:real`]
      HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
        ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX]];
      REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `schy_ssd((t - a2) / (b2 - a2)) / (b2 - a2) = &0 /\
                  schy_ssd((t - a1) / (b1 - a1)) / (b1 - a1) = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `schy_ssd((t - a2) / (b2 - a2)) / (b2 - a2) = &0 /\
                  schy_ssd((t - a1) / (b1 - a1)) / (b1 - a1) = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[o_DEF; schy_st] THEN
    MP_TAC(INST_TYPE [`:1`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!x:real^1. x IN (:real^1) ==> ~(b1 - a1 = &0) /\ ~(b2 - a2 = &0)`
    ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SCHY_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC]);;

let schy_K = new_definition
 `schy_K r = &1 - schy_st (&49 / &64) (&225 / &256) (r pow 2)`;;

let SCHY_K_FACTS = prove
 (`(!r. abs r <= &7 / &8 ==> schy_K r = &1) /\ (!r. &15 / &16 <= abs r ==> schy_K r = &0) /\
   (!r. &0 <= schy_K r /\ schy_K r <= &1) /\
   smooth_map_on (:real^1) (lift o schy_K o drop)`,
  MP_TAC(SPECL [`&49 / &64`; `&225 / &256`] SCHY_ST_FACTS) THEN
  REWRITE_TAC[REAL_ARITH `&49 / &64 < &225 / &256`] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[schy_K] THEN
    SUBGOAL_THEN `schy_st (&49 / &64) (&225 / &256) (r pow 2) = &0` (fun th -> REWRITE_TAC[th] THEN
      REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `x pow 2 <= (&7 / &8) pow 2 ==> x pow 2 <= &49 / &64`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[schy_K] THEN
    SUBGOAL_THEN `schy_st (&49 / &64) (&225 / &256) (r pow 2) = &1` (fun th -> REWRITE_TAC[th] THEN
      REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `(&15 / &16) pow 2 <= x pow 2 ==> &225 / &256 <= x pow 2`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[schy_K] THEN
    SUBGOAL_THEN `&0 <= schy_st (&49 / &64) (&225 / &256) (r pow 2) /\
                  schy_st (&49 / &64) (&225 / &256) (r pow 2) <= &1`
    MP_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    REWRITE_TAC[o_DEF; schy_K; schy_st] THEN
    MP_TAC(INST_TYPE [`:1`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!x:real^1. x IN (:real^1) ==> ~(&225 / &256 - &49 / &64 = &0)`
    ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SCHY_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The abstract shear.  The flow box of a unit vertical field                *)
(* X straightens the X-lines: fbox(y + t e3) = flow_X(t)(fbox y).  For a     *)
(* strip Gam on S1, transversal to X, whose X-columns of half-length 4 shat  *)
(* meet S1 only at Gam, the tube Psi(s,z) = flow_X(z)(Gam s), |z| < 2 shat,   *)
(* is a diffeomorphism onto an open set, and the time-1 flow of f X, with   *)
(* f(Psi(s,z)) = T(s) K(z / shat(s)), moves Gam(s) to flow_X(T(s))(Gam s).    *)
(* ------------------------------------------------------------------------- *)

let SCHY_FBOX_SHIFT = prove
 (`!X:real^3->real^3.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1)
     ==> (!y t. schy_fbox X (y + t % basis 3) =
                ode_vf_flow X (:real^3) (lift t) (schy_fbox X y)) /\
         (!x t. schy_fboxi X (ode_vf_flow X (:real^3) (lift t) x) =
                schy_fboxi X x + t % basis 3) /\
         (!x. schy_fbox X (schy_fboxi X x) = x) /\ (!y. schy_fboxi X (schy_fbox X y) = y)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_DIFFEO) THEN
  ASM_REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[schy_fbox] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; LIFT_ADD];
    REPEAT GEN_TAC THEN REWRITE_TAC[schy_fboxi] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `lift t + lift(--((x:real^3)$3 + t)) = lift(--(x$3))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC]);;

let SCHY_FBOX_DERIVS = prove
 (`!X:real^3->real^3.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1)
     ==> (!x. schy_fboxi X differentiable (at x)) /\ (!y. schy_fbox X differentiable (at y)) /\
         (!x. frechet_derivative (schy_fboxi X) (at x) (X x) = basis 3) /\
         (!x h. frechet_derivative (schy_fboxi X) (at x) h = vec 0 ==> h = vec 0) /\
         (!y h. frechet_derivative (schy_fbox X) (at y) h = vec 0 ==> h = vec 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_SHIFT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_DIFFEO) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIFFEOMORPHISM_ON_SYM) THEN
  SUBGOAL_THEN `(!x. schy_fboxi (X:real^3->real^3) differentiable (at x)) /\
                (!y. schy_fbox (X:real^3->real^3) differentiable (at y))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    SUBGOAL_THEN `(((schy_fboxi (X:real^3->real^3)) o (\s. ode_vf_flow X (:real^3) s x))
                  has_derivative (\h. vec 0 + drop h % basis 3)) (at (vec 0))` ASSUME_TAC THENL
     [SUBGOAL_THEN `(schy_fboxi (X:real^3->real^3)) o (\s. ode_vf_flow X (:real^3) s x) =
                    (\s. schy_fboxi X x + drop s % basis 3)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `s:real^1` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `drop s`] o check (fun th ->
          can (term_match [] `!x t. schy_fboxi X (ode_vf_flow X (:real^3) (lift t) x) =
                                    schy_fboxi X x + t % basis 3`) (concl th))) THEN
        REWRITE_TAC[LIFT_DROP];
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MP_TAC(ISPECL [`\x:real^1. x`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(((schy_fboxi (X:real^3->real^3)) o (\s. ode_vf_flow X (:real^3) s x))
                  has_derivative
                  (frechet_derivative (schy_fboxi X) (at x) o (\h. drop h % X x))) (at (vec 0))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `vec 0:real^1`] o check (fun th ->
          can (term_match [] `!x t. ((\s. ode_vf_flow v (:real^3) s x) has_vector_derivative
                                     v(ode_vf_flow v (:real^3) t x)) (at t)`) (concl th))) THEN
        ASM_REWRITE_TAC[has_vector_derivative];
        ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(schy_fboxi (X:real^3->real^3)) o (\s. ode_vf_flow X (:real^3) s x)`;
                   `frechet_derivative (schy_fboxi (X:real^3->real^3)) (at x) o (\h. drop h % X x)`;
                   `\h:real^1. vec 0 + drop h % basis 3:real^3`; `vec 0:real^1`]
      FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
    REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID; VECTOR_ADD_LID];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `schy_fboxi (X:real^3->real^3)`;
                   `schy_fbox (X:real^3->real^3)`; `x:real^3`; `h:real^3`]
      ODE_DIFFEO_DERIVATIVE_INVERSE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `frechet_derivative (schy_fbox (X:real^3->real^3)) (at (schy_fboxi X x))`
      LINEAR_0) THEN
    ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `schy_fbox (X:real^3->real^3)`;
                   `schy_fboxi (X:real^3->real^3)`; `y:real^3`; `h:real^3`]
      ODE_DIFFEO_DERIVATIVE_INVERSE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `frechet_derivative (schy_fboxi (X:real^3->real^3)) (at (schy_fbox X y))`
      LINEAR_0) THEN
    ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

let SCHY_TUBE_OPEN = prove
 (`!(Q:real^2->bool) (shat:real^2->real).
     open Q /\ (\s. lift(shat s)) continuous_on Q
     ==> open {z:real^3 | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. lift(abs(z$3) - shat(sch5v_pr z))`;
                 `{z:real^3 | sch5v_pr z IN Q}`; `{x:real^1 | x$1 < &0}`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `a - b < &0 <=> a < b`] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS_COMPONENT THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      SUBGOAL_THEN `(\z:real^3. lift(shat(sch5v_pr z))) = (\s. lift(shat s)) o sch5v_pr`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Q:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH]]);;

let SCHY_FLOW_BACK = prove
 (`!X:real^3->real^3.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1))
     ==> (!b c x. ode_vf_flow X (:real^3) (lift c) (ode_vf_flow X (:real^3) (lift b) x) =
                  ode_vf_flow X (:real^3) (lift(b + c)) x) /\
         (!x. ode_vf_flow X (:real^3) (lift(&0)) x = x)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  ASM_REWRITE_TAC[LIFT_ADD; LIFT_NUM]);;

let SCHY_TUBE_INJ = prove
 (`!(X:real^3->real^3) (Q:real^2->bool) (Gam:real^2->real^3) (shat:real^2->real) S1 z z'.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!s. s IN Q ==> Gam s IN S1) /\
     (!s s'. s IN Q /\ s' IN Q /\ Gam s = Gam s' ==> s = s') /\
     (!s t. s IN Q /\ abs t < &2 * shat s /\
            ode_vf_flow X (:real^3) (lift t) (Gam s) IN S1 ==> t = &0) /\
     sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z) /\
     sch5v_pr z' IN Q /\ abs(z'$3) < shat(sch5v_pr z') /\
     ode_vf_flow X (:real^3) (lift(z$3)) (Gam(sch5v_pr z)) =
     ode_vf_flow X (:real^3) (lift(z'$3)) (Gam(sch5v_pr z'))
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FLOW_BACK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ode_vf_flow X (:real^3) (lift((z:real^3)$3 - (z':real^3)$3))
                  ((Gam:real^2->real^3)(sch5v_pr z)) = Gam(sch5v_pr z') /\
                ode_vf_flow X (:real^3) (lift((z':real^3)$3 - (z:real^3)$3))
                  ((Gam:real^2->real^3)(sch5v_pr z')) = Gam(sch5v_pr z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(AP_TERM `ode_vf_flow (X:real^3->real^3) (:real^3) (lift(--((z':real^3)$3)))`
        (ASSUME `ode_vf_flow (X:real^3->real^3) (:real^3) (lift((z:real^3)$3))
                   (Gam(sch5v_pr z)) =
                 ode_vf_flow X (:real^3) (lift((z':real^3)$3)) ((Gam:real^2->real^3)(sch5v_pr z'))`));
      MP_TAC(AP_TERM `ode_vf_flow (X:real^3->real^3) (:real^3) (lift(--((z:real^3)$3)))`
        (SYM(ASSUME `ode_vf_flow (X:real^3->real^3) (:real^3) (lift((z:real^3)$3))
                   (Gam(sch5v_pr z)) =
                 ode_vf_flow X (:real^3) (lift((z':real^3)$3)) ((Gam:real^2->real^3)(sch5v_pr z'))`)))] THEN
    ASM_REWRITE_TAC[REAL_ADD_RINV; GSYM real_sub; REAL_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$3 = (z':real^3)$3` ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `shat(sch5v_pr(z':real^3)) <= shat(sch5v_pr(z:real^3)) \/
                               shat(sch5v_pr z) <= shat(sch5v_pr z')`) THENL
     [MATCH_MP_TAC(REAL_ARITH `a - b = &0 ==> a = b`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `sch5v_pr(z:real^3)` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `b - a = &0 ==> a = b`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `sch5v_pr(z':real^3)` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_pr(z:real^3) = sch5v_pr(z':real^3)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ode_vf_flow X (:real^3) (lift((z':real^3)$3 - (z:real^3)$3))
                  ((Gam:real^2->real^3)(sch5v_pr z')) = Gam(sch5v_pr z)` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3)$3 = (z':real^3)$3` THEN
  REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2] THEN
  MESON_TAC[]);;

let SCHY_TUBE_DET = prove
 (`!(X:real^3->real^3) (Q:real^2->bool) (Gam:real^2->real^3) z.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1) /\
     open Q /\ smooth_map_on Q Gam /\ sch5v_pr z IN Q /\
     (!a c. frechet_derivative Gam (at (sch5v_pr z)) a + c % X(Gam(sch5v_pr z)) = vec 0
            ==> a = vec 0 /\ c = &0)
     ==> ~(det(matrix(frechet_derivative
              (\x. ode_vf_flow X (:real^3) (lift(x$3)) (Gam(sch5v_pr x))) (at z))) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_SHIFT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_DERIVS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = sch5v_pr(z:real^3)` THEN
  SUBGOAL_THEN `(Gam:real^2->real^3) differentiable (at s)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Q:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(x$3)) (Gam(sch5v_pr x))) =
                schy_fbox X o (\x. schy_fboxi X ((Gam:real^2->real^3)(sch5v_pr x)) + x$3 % basis 3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\x. schy_fboxi (X:real^3->real^3) ((Gam:real^2->real^3)(sch5v_pr x)) +
                      x$3 % basis 3) has_derivative
                 (\h. frechet_derivative (schy_fboxi X) (at (Gam s))
                        (frechet_derivative Gam (at s) (sch5v_pr h)) + h$3 % basis 3)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. schy_fboxi (X:real^3->real^3) ((Gam:real^2->real^3)(sch5v_pr x))) =
                    schy_fboxi X o (Gam o sch5v_pr)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h. frechet_derivative (schy_fboxi (X:real^3->real^3))
                           (at ((Gam:real^2->real^3) s))
                           (frechet_derivative Gam (at s) (sch5v_pr h))) =
                    frechet_derivative (schy_fboxi X) (at (Gam s)) o
                    (frechet_derivative Gam (at s) o sch5v_pr)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
          ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
        ASM_REWRITE_TAC[o_THM; GSYM FRECHET_DERIVATIVE_WORKS]];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MP_TAC(ISPECL [`\x:real^3. lift(x$3)`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (schy_fbox (X:real^3->real^3) o
                  (\x. schy_fboxi X ((Gam:real^2->real^3)(sch5v_pr x)) + x$3 % basis 3)) (at z) =
                frechet_derivative (schy_fbox X) (at (schy_fboxi X (Gam s) + (z:real^3)$3 % basis 3)) o
                (\h. frechet_derivative (schy_fboxi X) (at (Gam s))
                       (frechet_derivative Gam (at s) (sch5v_pr h)) + h$3 % basis 3)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (schy_fbox (X:real^3->real^3))
                         (at (schy_fboxi X ((Gam:real^2->real^3) s) + (z:real^3)$3 % basis 3))) /\
                linear(frechet_derivative (schy_fboxi (X:real^3->real^3)) (at ((Gam:real^2->real^3) s))) /\
                linear(frechet_derivative (Gam:real^2->real^3) (at s))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (schy_fbox (X:real^3->real^3))
                         (at (schy_fboxi X ((Gam:real^2->real^3) s) + (z:real^3)$3 % basis 3)) o
                       (\h. frechet_derivative (schy_fboxi X) (at (Gam s))
                              (frechet_derivative Gam (at s) (sch5v_pr h)) + h$3 % basis 3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\h. frechet_derivative (schy_fboxi (X:real^3->real^3))
                           (at ((Gam:real^2->real^3) s))
                           (frechet_derivative Gam (at s) (sch5v_pr h))) =
                    frechet_derivative (schy_fboxi X) (at (Gam s)) o
                    (frechet_derivative Gam (at s) o sch5v_pr)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
      MP_TAC(ISPECL [`\x:real^3. lift(x$3)`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT; LIFT_DROP]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[NOT_EXISTS_THM; o_THM; TAUT `~(~a /\ b) <=> b ==> a`] THEN
  X_GEN_TAC `h:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (schy_fboxi (X:real^3->real^3)) (at ((Gam:real^2->real^3) s))
                  (frechet_derivative Gam (at s) (sch5v_pr h) + h$3 % X(Gam s)) = vec 0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y h. frechet_derivative (schy_fbox X) (at y) h = vec 0 ==> h = vec 0`)
        (concl th))) THEN
    EXISTS_TAC `schy_fboxi (X:real^3->real^3) ((Gam:real^2->real^3) s) + (z:real^3)$3 % basis 3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (Gam:real^2->real^3) (at s) (sch5v_pr h) + h$3 % X(Gam s) = vec 0`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x h. frechet_derivative (schy_fboxi X) (at x) h = vec 0 ==> h = vec 0`)
        (concl th))) THEN
    EXISTS_TAC `(Gam:real^2->real^3) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th' ->
    can (term_match [] `!a c. frechet_derivative (Gam:real^2->real^3) (at (s:real^2)) a +
                                    c % (X:real^3->real^3)(Gam s) = vec 0
                              ==> a = vec 0 /\ c = &0`) (concl th')))) THEN
  REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2;
              VEC_COMPONENT] THEN
  MESON_TAC[]);;

let SCHY_TUBE = prove
 (`!(X:real^3->real^3) (Q:real^2->bool) (Gam:real^2->real^3) (shat:real^2->real) S1.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1) /\
     open Q /\ smooth_map_on Q Gam /\ smooth_map_on Q (\s. lift(shat s)) /\
     (!s. s IN Q ==> &0 < shat s /\ Gam s IN S1) /\
     (!s s'. s IN Q /\ s' IN Q /\ Gam s = Gam s' ==> s = s') /\
     (!s t. s IN Q /\ abs t < &2 * shat s /\
            ode_vf_flow X (:real^3) (lift t) (Gam s) IN S1 ==> t = &0) /\
     (!s a c. s IN Q /\ frechet_derivative Gam (at s) a + c % X(Gam s) = vec 0
              ==> a = vec 0 /\ c = &0)
     ==> open {z:real^3 | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)} /\
         ?g. diffeomorphism_on {z:real^3 | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)}
               (IMAGE (\x. ode_vf_flow X (:real^3) (lift(x$3)) (Gam(sch5v_pr x)))
                      {z | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)})
               (\x. ode_vf_flow X (:real^3) (lift(x$3)) (Gam(sch5v_pr x))) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {z:real^3 | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_TUBE_OPEN THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN Q ==> (Gam:real^2->real^3) s IN S1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHI_INJ_DIFFEO THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_SHIFT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `X:real^3->real^3` SCHY_FBOX_DIFFEO) THEN
    ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(\x. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(x$3)) (Gam(sch5v_pr x))) =
                  schy_fbox X o (\x. schy_fboxi X ((Gam:real^2->real^3)(sch5v_pr x)) + x$3 % basis 3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. schy_fboxi (X:real^3->real^3) ((Gam:real^2->real^3)(sch5v_pr x))) =
                    schy_fboxi X o (Gam o sch5v_pr)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Q:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH]];
      MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^3. lift(x$3)`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT; LIFT_DROP]];
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`z:real^3`; `z':real^3`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`X:real^3->real^3`; `Q:real^2->bool`; `Gam:real^2->real^3`;
                   `shat:real^2->real`; `S1:real^3->bool`; `z:real^3`; `z':real^3`]
      SCHY_TUBE_INJ) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC SCHY_TUBE_DET THEN EXISTS_TAC `Q:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `c:real`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s a c. s IN (Q:real^2->bool) /\
               frechet_derivative (Gam:real^2->real^3) (at s) a + c % (X:real^3->real^3)(Gam s) =
               vec 0 ==> a = vec 0 /\ c = &0`) (concl th))) THEN
    EXISTS_TAC `sch5v_pr(z:real^3)` THEN ASM_REWRITE_TAC[]]);;

let SCHY_TUBE_COMPACT = prove
 (`!(Q:real^2->bool) Qc (shat:real^2->real).
     compact Qc /\ Qc SUBSET Q /\ (\s. lift(shat s)) continuous_on Q
     ==> compact {z:real^3 | sch5v_pr z IN Qc /\ abs(z$3) <= shat(sch5v_pr z)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. lift((shat:real^2->real) s)) continuous_on Qc` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `closed {z:real^3 | sch5v_pr z IN Qc}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. lift((shat:real^2->real) s)`; `Qc:real^2->bool`]
      COMPACT_CONTINUOUS_IMAGE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `b1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `b2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b1 + b2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)`) THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
    SUBGOAL_THEN `norm(z:real^3) <= norm(sch5v_pr z) + abs(z$3)` MP_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT)))] THEN
      REWRITE_TAC[sch5v_at] THEN
      SUBGOAL_THEN `vector[(sch5v_pr z)$1; (sch5v_pr z)$2; (z:real^3)$3]:real^3 =
                    vector[(sch5v_pr z)$1; (sch5v_pr z)$2; &0] + z$3 % basis 3` SUBST1_TAC THENL
       [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^3) = x /\ norm(b:real^3) = y ==> norm(a + b) <= x + y`) THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      REWRITE_TAC[NORM_EQ; DOT_2; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\z:real^3. lift(abs(z$3) - shat(sch5v_pr z))`;
                   `{z:real^3 | sch5v_pr z IN Qc}`; `{x:real^1 | x$1 <= &0}`]
      CONTINUOUS_CLOSED_PREIMAGE) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= &0 <=> a <= b`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS_COMPONENT THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      SUBGOAL_THEN `(\z:real^3. lift(shat(sch5v_pr z))) = (\s. lift(shat s)) o sch5v_pr`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Qc:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]]);;

let SCHY_FLOW_REPARAM = prove
 (`!(X:real^3->real^3) (Z:real^3->real^3) p a.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     smooth_map_on (:real^3) Z /\
     (!t. &0 <= t /\ t <= &1
          ==> Z(ode_vf_flow X (:real^3) (lift(t * a)) p) =
              a % X(ode_vf_flow X (:real^3) (lift(t * a)) p))
     ==> ode_vf_flow Z (:real^3) (lift(&1)) p = ode_vf_flow X (:real^3) (lift a) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (X:real^3->real^3)`)) THEN
  MP_TAC(ISPECL [`Z:real^3->real^3`; `(:real^3)`; `interval[vec 0:real^1,lift(&1)]`;
                 `\t:real^1. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(drop t * a)) p`;
                 `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_INTERVAL; IN_UNIV; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_POS; REAL_MUL_LZERO; LIFT_NUM] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `smooth_map_on (:real^3) (Z:real^3->real^3)` THEN SIMP_TAC[smooth_map_on];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(\t:real^1. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(drop t * a)) p) =
                  (\s. ode_vf_flow X (:real^3) s p) o (\t. lift(drop t * a))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `a % (X:real^3->real^3)(ode_vf_flow X (:real^3) (lift(drop t * a)) p) =
                  drop(lift a) % X(ode_vf_flow X (:real^3) ((\t. lift(drop t * a)) t) p)`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\x:real^1. drop x % lift a) = (\t. lift(drop t * a))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; REAL_POS; REAL_LE_REFL; VECTOR_SUB_RZERO;
                    REAL_MUL_LID; LIFT_NUM] THEN
    MESON_TAC[]]);;

let SCHY_SM_PR = prove
 (`!(W:real^3->bool) (Q:real^2->bool) (h:real^2->real).
     open W /\ open Q /\ (!z. z IN W ==> sch5v_pr z IN Q) /\ smooth_map_on Q (\s. lift(h s))
     ==> smooth_map_on W (\z. lift(h(sch5v_pr z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^3. lift((h:real^2->real)(sch5v_pr z))) = (\s. lift(h s)) o sch5v_pr`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Q:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH]]);;

let SCHY_SHEAR = prove
 (`!(X:real^3->real^3) (Q:real^2->bool) Qc (Gam:real^2->real^3) (shat:real^2->real)
    (Tf:real^2->real) S1.
     smooth_map_on (:real^3) X /\ (!y. ode_vf_maxint X (:real^3) y = (:real^1)) /\
     (!y. (X y)$3 = &1) /\
     open Q /\ compact Qc /\ Qc SUBSET Q /\
     smooth_map_on Q Gam /\ smooth_map_on Q (\s. lift(shat s)) /\
     smooth_map_on Q (\s. lift(Tf s)) /\
     (!s. s IN Q ==> &0 < shat s /\ &8 * abs(Tf s) <= &7 * shat s /\ Gam s IN S1) /\
     (!s. s IN Q /\ ~(s IN Qc) ==> Tf s = &0) /\
     (!s s'. s IN Q /\ s' IN Q /\ Gam s = Gam s' ==> s = s') /\
     (!s t. s IN Q /\ abs t < &2 * shat s /\
            ode_vf_flow X (:real^3) (lift t) (Gam s) IN S1 ==> t = &0) /\
     (!s a c. s IN Q /\ frechet_derivative Gam (at s) a + c % X(Gam s) = vec 0
              ==> a = vec 0 /\ c = &0)
     ==> ?Phi Phi' L.
           diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ compact L /\
           (!x. ~(x IN L) ==> Phi x = x) /\
           (!s. s IN Qc ==> Gam s IN L) /\
           (!x. x IN L /\ x IN S1 ==> ?s. s IN Qc /\ x = Gam s) /\
           (!s. s IN Q ==> Phi(Gam s) = ode_vf_flow X (:real^3) (lift(Tf s)) (Gam s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN Q ==> &0 < shat s /\ (Gam:real^2->real^3) s IN S1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^3->real^3` SCHY_FLOW_BACK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^3->real^3`; `Q:real^2->bool`; `Gam:real^2->real^3`;
                 `shat:real^2->real`; `S1:real^3->bool`] SCHY_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = {z:real^3 | sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)}` THEN
  ABBREV_TAC `Psi = \x. ode_vf_flow (X:real^3->real^3) (:real^3) (lift(x$3))
                          ((Gam:real^2->real^3)(sch5v_pr x))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `g:real^3->real^3`)) THEN
  SUBGOAL_THEN `!z:real^3. Psi z = ode_vf_flow (X:real^3->real^3) (:real^3) (lift(z$3))
                                     ((Gam:real^2->real^3)(sch5v_pr z))` (LABEL_TAC "PSI") THENL
   [EXPAND_TAC "Psi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN W <=> sch5v_pr z IN Q /\ abs(z$3) < shat(sch5v_pr z)`
  (LABEL_TAC "WD") THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (term_match [] `diffeomorphism_on (W:real^3->bool) (IMAGE (Psi:real^3->real^3) W) Psi g`)
      (concl th))) THEN
  ABBREV_TAC `Lc = {z:real^3 | sch5v_pr z IN Qc /\ abs(z$3) <= &15 / &16 * shat(sch5v_pr z)}` THEN
  SUBGOAL_THEN `!z:real^3. z IN Lc <=> sch5v_pr z IN Qc /\ abs(z$3) <= &15 / &16 * shat(sch5v_pr z)`
  (LABEL_TAC "LD") THENL
   [EXPAND_TAC "Lc" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(Lc:real^3->bool) /\ Lc SUBSET W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Lc" THEN
      MP_TAC(ISPECL [`Q:real^2->bool`; `Qc:real^2->bool`; `\s:real^2. &15 / &16 * shat s`]
        SCHY_TUBE_COMPACT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN
      USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "WD" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `sch5v_pr(z:real^3) IN Q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)` o check (fun th -> can (term_match []
        `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                       (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L = IMAGE (Psi:real^3->real^3) Lc` THEN
  SUBGOAL_THEN `compact(L:real^3->bool) /\ L SUBSET IMAGE (Psi:real^3->real^3) W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `TK = \z:real^3. (Tf:real^2->real)(sch5v_pr z) * schy_K(z$3 / shat(sch5v_pr z))` THEN
  ABBREV_TAC `f = \x:real^3. if x IN IMAGE (Psi:real^3->real^3) W then (TK:real^3->real)(g x)
                             else &0` THEN
  SUBGOAL_THEN `!x:real^3. ~(x IN L) ==> f x = &0` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    SUBGOAL_THEN `(g:real^3->real^3) x = z` SUBST1_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(x:real^3) = Psi(z:real^3)`)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN (W:real^3->bool) ==> (g:real^3->real^3)((Psi:real^3->real^3) x) = x`)
        (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3) IN Lc)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN L)` THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(z:real^3) IN W` THEN USE_THEN "WD" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN EXPAND_TAC "TK" THEN REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(Tf:real^2->real)(sch5v_pr(z:real^3)) = &0`
        (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!s. s IN (Q:real^2->bool) /\ ~(s IN Qc) ==> (Tf:real^2->real) s = &0`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `schy_K((z:real^3)$3 / shat(sch5v_pr z)) = &0`
        (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
      MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 SCHY_K_FACTS)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)` o check (fun th -> can (term_match []
        `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                       (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      SUBGOAL_THEN `abs(shat(sch5v_pr(z:real^3))) = shat(sch5v_pr z)` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`&15 / &16`; `abs((z:real^3)$3)`; `shat(sch5v_pr(z:real^3)):real`]
        REAL_LE_RDIV_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\x. lift((f:real^3->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_SMOOTH_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE (Psi:real^3->real^3) W` THENL
     [EXISTS_TAC `IMAGE (Psi:real^3->real^3) W` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `\x:real^3. lift((TK:real^3->real)(g x))` THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(\x:real^3. lift((TK:real^3->real)(g x))) = (\z. lift(TK z)) o g`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      SUBGOAL_THEN `!z:real^3. z IN W ==> sch5v_pr z IN Q /\ &0 < shat(sch5v_pr z)`
      ASSUME_TAC THENL
       [GEN_TAC THEN USE_THEN "WD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)` o check (fun th -> can (term_match []
          `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                         (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      EXPAND_TAC "TK" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SCH3_SL_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SCHY_SM_PR THEN EXISTS_TAC `Q:real^2->bool` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(\z:real^3. lift(schy_K(z$3 / shat(sch5v_pr z)))) =
                    (lift o schy_K o drop) o (\z. lift(z$3 / shat(sch5v_pr z)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCHY_K_FACTS] THEN
      MATCH_MP_TAC SCH3_SL_DIV THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SCHY_SM_PR THEN EXISTS_TAC `Q:real^2->bool` THEN ASM_SIMP_TAC[];
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> can (term_match []
          `!z. z IN (W:real^3->bool) ==> sch5v_pr z IN (Q:real^2->bool) /\
                                         &0 < (shat:real^2->real)(sch5v_pr z)`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      EXISTS_TAC `(:real^3) DIFF L` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:real^3. lift(&0)` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV;
                   SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. s IN Q /\ &0 <= t /\ t <= &1
                      ==> (f:real^3->real)(ode_vf_flow X (:real^3) (lift(t * Tf s))
                                             ((Gam:real^2->real^3) s)) = Tf s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real^2` o check (fun th -> can (term_match []
      `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                     &8 * abs((Tf:real^2->real) s) <= &7 * shat s /\
                                     (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `abs(t * (Tf:real^2->real) s) <= abs(Tf s)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sch5v_at (t * (Tf:real^2->real) s) (s:real^2) IN W` ASSUME_TAC THENL
     [USE_THEN "WD" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[SCH5V_PR_AT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ode_vf_flow X (:real^3) (lift(t * Tf s)) ((Gam:real^2->real^3) s) =
                  (Psi:real^3->real^3)(sch5v_at (t * Tf s) s)` SUBST1_TAC THENL
     [USE_THEN "PSI" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SCH5V_PR_AT]; ALL_TAC] THEN
    EXPAND_TAC "f" THEN
    SUBGOAL_THEN `(Psi:real^3->real^3)(sch5v_at (t * Tf s) s) IN IMAGE Psi W`
      (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^3)((Psi:real^3->real^3)(sch5v_at (t * Tf s) s)) =
                  sch5v_at (t * Tf s) s` SUBST1_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN (W:real^3->bool) ==> (g:real^3->real^3)((Psi:real^3->real^3) x) = x`)
        (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "TK" THEN REWRITE_TAC[SCH5V_PR_AT] THEN
    SUBGOAL_THEN `schy_K((t * (Tf:real^2->real) s) / shat(s:real^2)) = &1`
      (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
    MATCH_MP_TAC(CONJUNCT1 SCHY_K_FACTS) THEN REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `abs(shat(s:real^2)) = shat s` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`abs(t * (Tf:real^2->real) s)`; `&7 / &8`; `shat(s:real^2):real`]
      REAL_LE_LDIV_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Z = \x:real^3. (f:real^3->real) x % (X:real^3->real^3) x` THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (Z:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC SCH3_SV_CMUL THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Z:real^3->real^3`; `(:real^3)`; `L:real^3->bool`] ODE_VF_COMPLETE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Z" THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ode_vf_flow (Z:real^3->real^3) (:real^3) (lift(&1))`;
                        `ode_vf_flow (Z:real^3->real^3) (:real^3) (--(lift(&1)))`;
                        `L:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN EXPAND_TAC "L" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `sch5v_at (&0) (s:real^2)` THEN
    USE_THEN "PSI" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT; REAL_ABS_NUM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^2` o check (fun th -> can (term_match []
        `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                       (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN EXPAND_TAC "L" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `sch5v_pr(z:real^3)` THEN
    UNDISCH_TAC `(z:real^3) IN Lc` THEN USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3)$3 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!s t. s IN (Q:real^2->bool) /\ abs t < &2 * (shat:real^2->real) s /\
               ode_vf_flow (X:real^3->real^3) (:real^3) (lift t) ((Gam:real^2->real^3) s) IN S1
               ==> t = &0`) (concl th))) THEN
      EXISTS_TAC `sch5v_pr(z:real^3)` THEN
      SUBGOAL_THEN `sch5v_pr(z:real^3) IN Q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `sch5v_pr(z:real^3)` o check (fun th -> can (term_match []
        `!s. s IN (Q:real^2->bool) ==> &0 < (shat:real^2->real) s /\
                                       (Gam:real^2->real^3) s IN S1`) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN S1` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PSI" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN USE_THEN "PSI" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SCHY_FLOW_REPARAM THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "Z" THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Critical points after the shear.  Off the compact support                 *)
(* L the sheared neck Phi o g1 has the critical points of g1; on L, which   *)
(* meets S1 only along the strip Gam(Qc), the height of Phi o g1 o g1' o Gam *)
(* is the function Hs with nonzero derivative, so there is none.            *)
(* ------------------------------------------------------------------------- *)

let SCHY_CRIT_SHEAR = prove
 (`!(g1:real^3->real^3) g1' (Phi:real^3->real^3) Phi' L (Q:real^2->bool) Qc
    (Gam:real^2->real^3) (Hs:real^2->real).
     sch_neck g1 g1' /\ diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ compact L /\
     (!x. ~(x IN L) ==> Phi x = x) /\
     open Q /\ Qc SUBSET Q /\ smooth_map_on Q Gam /\
     (!s. s IN Q ==> Gam s IN IMAGE g1 (sphere(vec 0,&1))) /\
     (!x. x IN L /\ x IN IMAGE g1 (sphere(vec 0,&1)) ==> ?s. s IN Qc /\ x = Gam s) /\
     (!s. s IN Q ==> (Phi(Gam s))$3 = Hs s) /\
     (!s. s IN Qc ==> ~(frechet_derivative (\s. lift(Hs s)) (at s) = (\v. vec 0)))
     ==> !t. sch_crit (Phi o g1) t <=> sch_crit g1 t /\ ~(g1 t IN L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real^3` THEN
  ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[sch_crit]] THEN
  ASM_CASES_TAC `(g1:real^3->real^3) t IN L` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MATCH_MP_TAC SCH3_CRIT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`g1':real^3->real^3`; `(:real^3) DIFF L`] THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; o_THM]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g1:real^3->real^3) t` o check (fun th -> can (term_match []
    `!x. x IN (L:real^3->bool) /\ x IN IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))
         ==> ?s. s IN (Qc:real^2->bool) /\ x = (Gam:real^2->real^3) s`) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s0:real^2) IN Q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    GEN_REWRITE_RULE I [sch_neck] o check (fun th -> can (term_match []
      `sch_neck (g1:real^3->real^3) g1'`) (concl th))) THEN
  SUBGOAL_THEN `!s. s IN Q ==> (g1':real^3->real^3)((Gam:real^2->real^3) s) IN sphere(vec 0,&1) /\
                               (g1:real^3->real^3)(g1'(Gam s)) = Gam s /\
                               Gam s IN IMAGE g1 (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real^2` o check (fun th -> can (term_match []
      `!s. s IN (Q:real^2->bool)
           ==> (Gam:real^2->real^3) s IN IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))`)
      (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t':real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `t':real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(g1':real^3->real^3)((Gam:real^2->real^3) s0) = t` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(g1:real^3->real^3) t = Gam(s0:real^2)`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g1':real^3->real^3) o (Gam:real^2->real^3) has_derivative
                 frechet_derivative g1' (at (Gam s0)) o frechet_derivative Gam (at s0)) (at s0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `Q:real^2->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE (g1:real^3->real^3) (annulus (&1 / &2) (&2))` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((Phi:real^3->real^3) o (g1:real^3->real^3)) differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      ASM_MESON_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\s. lift(((((Phi:real^3->real^3) o (g1:real^3->real^3)) o
                            ((g1':real^3->real^3) o (Gam:real^2->real^3))) s)$3)) has_derivative
                 (\a. lift((frechet_derivative (Phi o g1) (at t)
                              ((frechet_derivative g1' (at (Gam s0)) o
                                frechet_derivative Gam (at s0)) a))$3))) (at s0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. lift(((((Phi:real^3->real^3) o (g1:real^3->real^3)) o
                            ((g1':real^3->real^3) o (Gam:real^2->real^3))) s)$3)) =
                  (\x:real^3. lift(x$3)) o ((Phi o g1) o (g1' o Gam))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\a. lift((frechet_derivative ((Phi:real^3->real^3) o (g1:real^3->real^3)) (at t)
                              ((frechet_derivative (g1':real^3->real^3) (at ((Gam:real^2->real^3) s0)) o
                                frechet_derivative Gam (at s0)) a))$3)) =
                  (\x:real^3. lift(x$3)) o
                  (frechet_derivative (Phi o g1) (at t) o
                   (frechet_derivative g1' (at (Gam s0)) o frechet_derivative Gam (at s0)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  REWRITE_TAC[sch_crit] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:real^2` o check (fun th -> can (term_match []
    `!s. s IN (Qc:real^2->bool)
         ==> ~(frechet_derivative (\s. lift((Hs:real^2->real) s)) (at s) = (\v. vec 0))`)
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. lift(((((Phi:real^3->real^3) o (g1:real^3->real^3)) o
                         ((g1':real^3->real^3) o (Gam:real^2->real^3))) s)$3)` THEN
  FIRST_ASSUM(MP_TAC o SPEC `s0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check
    (fun th -> concl th = `open(Q:real^2->bool)`)) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^2) IN Q` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v:real^2. vec 0:real^1) =
                (\a. lift((frechet_derivative ((Phi:real^3->real^3) o (g1:real^3->real^3)) (at t)
                             ((frechet_derivative (g1':real^3->real^3) (at ((Gam:real^2->real^3) s0)) o
                               frechet_derivative Gam (at s0)) a))$3))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^2` THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[orthogonal] THEN
    MP_TAC(ISPECL [`(g1':real^3->real^3) o (Gam:real^2->real^3)`;
                   `frechet_derivative (g1':real^3->real^3) (at ((Gam:real^2->real^3) s0)) o
                    frechet_derivative Gam (at s0)`; `Q:real^2->bool`; `s0:real^2`]
      SCH3_SPHERE_MAP_ORTHO) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Geometric separation near the saddle box.  Inside the box                 *)
(* the component C is the left branch of x1^2 - x2^2 = e; points right of    *)
(* x1 = -sqrt e/2, and points near P0 below the level, lie in the outside of *)
(* J = pr C; a point of the outside close to inside J union J is close to J. *)
(* ------------------------------------------------------------------------- *)

let SCHY_C_LEFT = prove
 (`!(g:real^3->real^3) r e C q.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ ~(schy_rpt e IN C) /\
     q IN C /\ q$1 pow 2 + q$2 pow 2 < r pow 2
     ==> q$3 = e /\ q$1 = --(sqrt(e + q$2 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3) IN sch_level g e` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[sch_level; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
    can (term_match [] `schy_chart s r`) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `q:real^3`))) THEN
  SUBGOAL_THEN `e < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `r pow 2 < r` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(ASSUME_TAC o SYM)] THEN
  SUBGOAL_THEN `(q:real^3)$1 < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(&0 < x) /\ ~(x = &0) ==> x < &0`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `q:real^3`] SCHY_BRANCH_COMP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(schy_rpt e IN C)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [IN_COMPONENTS] o check (fun th ->
          can (term_match [] `(C:real^3->bool) IN components s`) (concl th))) THEN
      SUBGOAL_THEN `connected_component (sch_level (g:real^3->real^3) e) q = C` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN ASM_REWRITE_TAC[GSYM IN];
      DISCH_TAC THEN UNDISCH_TAC `(q:real^3)$1 pow 2 - q$2 pow 2 = e` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `(q:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e + (q:real^3)$2 pow 2 = q$1 pow 2` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[POW_2_SQRT_ABS] THEN ASM_REAL_ARITH_TAC);;

let SCHY_J_LEFT = prove
 (`!(g:real^3->real^3) r e C z:real^2.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ ~(schy_rpt e IN C) /\
     z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C /\ norm z < r
     ==> z$1 = --(sqrt(e + z$2 pow 2)) /\ z$1 <= --(sqrt e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `y:real^3`]
    SCHY_C_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `norm(z:real^2) < r` THEN
    ASM_REWRITE_TAC[NORM_LT_SQUARE; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_2] THEN REWRITE_TAC[REAL_LE_NEG2] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

let SCHY_OUT_RIGHT = prove
 (`!(g:real^3->real^3) r e C x:real^2.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
     --(sqrt e) / &2 <= x$1 /\ norm x < r
     ==> x IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SIDE") THEN
  ABBREV_TAC `J = IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ &4 * sqrt e < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
        can (term_match [] `schy_chart s r`) (concl th))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z0 = vector[--(sqrt e) / &2; &0]:real^2` THEN
  SUBGOAL_THEN `(z0:real^2) IN outside J` ASSUME_TAC THENL
   [USE_THEN "SIDE" (MP_TAC o SPEC `z0:real^2`) THEN
    EXPAND_TAC "z0" THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[REAL_ARITH `(--s / &2 + s) pow 2 + &0 pow 2 = s pow 2 / &4 /\
                            (--s / &2) pow 2 - &0 pow 2 = s pow 2 / &4`] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN EXISTS_TAC `z0:real^2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[connected_component] THEN EXISTS_TAC `segment[z0:real^2,x]` THEN
  REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `{z:real^2 | z$1 >= --(sqrt e) / &2} INTER ball(vec 0,r)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{z:real^2 | z$1 >= --(sqrt e) / &2} INTER ball(vec 0,r)`;
                   `z0:real^2`; `x:real^2`] CONVEX_CONTAINS_SEGMENT_IMP) THEN
    SIMP_TAC[CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_GE; CONVEX_BALL] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; real_ge] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "z0" THEN REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN
    REWRITE_TAC[NORM_LT_SQUARE; DOT_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL_0; IN_DIFF; IN_UNIV; real_ge] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `z:real^2`]
      SCHY_J_LEFT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SCHY_OUT_NEAR = prove
 (`!(J:real^2->bool) x z d.
     x IN outside J /\ (z IN inside J \/ z IN J) /\ dist(x,z) < d
     ==> ?q. q IN J /\ dist(x,q) < d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)) THENL
   [ALL_TAC; EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `segment[x:real^2,z] INTER J = {}` THENL
   [SUBGOAL_THEN `(z:real^2) IN outside J` ASSUME_TAC THENL
     [MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[connected_component] THEN EXISTS_TAC `segment[x:real^2,z]` THEN
      REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^2` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x:real^2`; `z:real^2`; `q:real^2`] DIST_IN_CLOSED_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`x:real^2`; `q:real^2`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC]);;

let SCHY_SQRT_DIFF = prove
 (`!e a. &0 < e /\ abs a <= sqrt e
         ==> sqrt e <= sqrt(e + a pow 2) /\ sqrt(e + a pow 2) - sqrt e <= abs a / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y + c ==> x - y <= c`) THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  SUBGOAL_THEN `&0 <= sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THENL [MP_TAC(SPEC `a:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs a * abs a <= abs a * sqrt e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs a * sqrt e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_POW2_ABS] THEN
  REWRITE_TAC[REAL_ARITH `(s + b / &2) pow 2 = s pow 2 + s * b + b pow 2 / &4`] THEN
  ASM_REWRITE_TAC[REAL_POW2_ABS] THEN REAL_ARITH_TAC);;

let SCHY_NEAR_J = prove
 (`!(g:real^3->real^3) r e C x z d.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ ~(schy_rpt e IN C) /\
     x IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
     (z IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) \/
      z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
     dist(x,z) < d /\ norm x + d < r /\ abs(x$2) + d <= sqrt e
     ==> abs(x$1 + sqrt e) <= abs(x$2) + &2 * d`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`; `x:real^2`; `z:real^2`; `d:real`]
    SCHY_OUT_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs((x:real^2)$1 - (q:real^2)$1) < d /\ abs(x$2 - q$2) < d /\ norm q < r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(x:real^2,q) < d` THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`x - q:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x - q:real^2`; `2`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`q:real^2`; `x:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x:real^2`; `q:real^2`] NORM_SUB) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `q:real^2`]
    SCHY_J_LEFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `(q:real^2)$2`] SCHY_SQRT_DIFF) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REAL_ARITH_TAC);;

let SCHY_C_UNIF = prove
 (`!(c:real^2->real^2) d.
     c continuous_on ball(vec 0,&2) /\ &0 < d
     ==> ?s1. &0 < s1 /\ s1 < &1 / &4 /\
              !z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1
                  ==> dist(c z,c(inv(norm z) % z)) < d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `cball(vec 0:real^2,&3 / &2)`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^2,&2)` THEN ASM_REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min del (&1 / &8) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(z:real^2) < &1 + min del (&1 / &8) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 + &2 * min del (&1 / &8) / &2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `(&1 + x) pow 2 = &1 + &2 * x + x pow 2`] THEN
    MP_TAC(SPEC `min del (&1 / &8) / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_CBALL_0] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `z - inv(norm z) % z:real^2 = (&1 - inv(norm z)) % z` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `abs(&1 - inv(norm(z:real^2))) * norm z = norm z - &1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 <= &1 - inv(norm(z:real^2))` MP_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The concrete strip.  sq(k) = sqrt(e - k lam); the blend be                *)
(* runs on [sq(9/16), sq(17/32)], the tip blend A0 on [sq(65/128),           *)
(* sq(129/256)]; the box part ends at sq(1), the polar part at sq(33/64).    *)
(* hf = Hr(t) - G(t,w) is the height along the strip.  SCHY_PARTIAL reads a *)
(* partial derivative off a one-variable real derivative.                    *)
(* ------------------------------------------------------------------------- *)

let schy_sq = new_definition
 `schy_sq e lam k = sqrt(e - k * lam)`;;

let SCHY_SQ_FACTS = prove
 (`!e lam. &0 < lam /\ &2 * lam < e
           ==> (!k. &0 <= k /\ k <= &1
                    ==> &0 < schy_sq e lam k /\ schy_sq e lam k pow 2 = e - k * lam /\
                        schy_sq e lam k <= sqrt e) /\
               (!k k'. &0 <= k /\ k < k' /\ k' <= &1 ==> schy_sq e lam k' < schy_sq e lam k) /\
               schy_ta e lam = schy_sq e lam (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[schy_sq] THEN
    SUBGOAL_THEN `&0 < e - k * lam /\ k * lam <= lam` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `k * lam <= &1 * lam` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `&0 <= k * lam` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
    SUBGOAL_THEN `k * lam < k' * lam /\ k' * lam <= &1 * lam` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_RMUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[schy_ta; schy_sq] THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let schy_bec = new_definition
 `schy_bec e lam = schy_st (schy_sq e lam (&9 / &16)) (schy_sq e lam (&17 / &32))`;;

let schy_Ac = new_definition
 `schy_Ac e lam = schy_A0 e lam (schy_sq e lam (&65 / &128)) (schy_sq e lam (&129 / &256))`;;

let schy_Acd = new_definition
 `schy_Acd e lam = schy_A0d e lam (schy_sq e lam (&65 / &128)) (schy_sq e lam (&129 / &256))`;;

let schy_Hc = new_definition
 `schy_Hc e lam = schy_Hr e lam (schy_sq e lam (&65 / &128)) (schy_sq e lam (&129 / &256))`;;

let schy_Hcd = new_definition
 `schy_Hcd e lam = schy_Hrd e lam (schy_sq e lam (&65 / &128)) (schy_sq e lam (&129 / &256))`;;

let schy_hf = new_definition
 `schy_hf (c':real^2->real^2) e lam (z:real^2) =
    schy_Hc e lam (z$1) - schy_G c' e lam (schy_bec e lam) z`;;

let schy_gm = new_definition
 `schy_gm (Theta:real^3->real^3) (c':real^2->real^2) e lam =
    schy_strip Theta c' e lam (schy_bec e lam) (schy_Ac e lam) (schy_sq e lam (&1))
               (schy_sq e lam (&33 / &64))`;;

let SCHY_PARTIAL = prove
 (`!(f:real^2->real^1) z i a.
     f differentiable (at z) /\
     ((\t. drop(f(z + t % basis i))) has_real_derivative a) (atreal (&0))
     ==> drop(frechet_derivative f (at z) (basis i)) = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_FRECHET_DERIVATIVE_AT]) THEN
  REWRITE_TAC[LIFT_NUM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((lift o (\t. drop((f:real^2->real^1)(z + t % basis i))) o drop) has_derivative
                 (frechet_derivative f (at z) o (\h. drop h % basis i))) (at (vec 0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(lift o (\t. drop((f:real^2->real^1)(z + t % basis i))) o drop) =
                  f o (\x:real^1. z + drop x % basis i)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\h:real^1. drop h % basis i:real^2) = (\h. vec 0 + drop h % basis i)`
      SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MP_TAC(ISPECL [`\x:real^1. x`; `basis i:real^2`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_ID];
      REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lift o (\t. drop((f:real^2->real^1)(z + t % basis i))) o drop`;
                 `frechet_derivative (f:real^2->real^1) (at z) o (\h. drop h % basis i)`;
                 `\x:real^1. a % x`; `vec 0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP; REAL_MUL_RID]);;

let SCHY_CPAR = prove
 (`!e lam. &0 < lam /\ &2 * lam < e
   ==> &0 < schy_sq e lam (&1) /\
       schy_sq e lam (&1) < schy_sq e lam (&7 / &8) /\
       schy_sq e lam (&7 / &8) < schy_sq e lam (&9 / &16) /\
       schy_sq e lam (&9 / &16) < schy_sq e lam (&17 / &32) /\
       schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64) /\
       schy_sq e lam (&33 / &64) < schy_sq e lam (&65 / &128) /\
       schy_sq e lam (&65 / &128) < schy_sq e lam (&129 / &256) /\
       schy_sq e lam (&129 / &256) < schy_ta e lam /\ schy_ta e lam < sqrt e /\
       &0 < sqrt e /\ sqrt e pow 2 = e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_SQ_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!k k'. &0 <= k /\ k < k' /\ k' <= &1 ==> schy_sq e lam k' < schy_sq e lam k`) (concl th))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> can (term_match []
    `!k. &0 <= k /\ k <= &1 ==> P k`) (concl th))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[] THEN NO_TAC) THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC);;

let SCHY_SM_COORD = prove
 (`!(f:real->real) s i.
     smooth_map_on (:real^1) (lift o f o drop) /\ open s
     ==> smooth_map_on s (\z:real^N. lift(f(z$i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^N. lift((f:real->real)(z$i))) = (lift o f o drop) o (\z. lift(z$i))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE]);;

let SCHY_B0_SMOOTH = prove
 (`!(c:real^2->real^2) c' e ts.
     sch_ball c c' /\ &0 < e /\
     (!tau. abs tau < ts ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)))
     ==> open {z:real^2 | abs(&2 * z$1 * z$2) < ts} /\
         smooth_map_on {z:real^2 | abs(&2 * z$1 * z$2) < ts} (\z. lift(schy_B0 c' e z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z:real^2. lift(&2 * z$1 * z$2))` ASSUME_TAC THENL
   [MP_TAC(INST_TYPE [`:2`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN SCH3_SMOOTH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^2 | abs(&2 * z$1 * z$2) < ts}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^2. lift(&2 * z$1 * z$2)`; `ball(vec 0:real^1,ts)`]
      CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[schy_B0; schy_bz] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z:real^2. (c':real^2->real^2)(schy_gam e (--(&2 * z$1 * z$2)))) =
                c' o (\z. schy_gam e (--(&2 * z$1 * z$2)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    GEN_REWRITE_RULE I [sch_ball]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (c:real^2->real^2) (ball(vec 0,&2))` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NEG];
    MATCH_MP_TAC SCHY_GAM_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let schy_becd = new_definition
 `schy_becd e lam t =
    schy_ssd((t - schy_sq e lam (&9 / &16)) /
             (schy_sq e lam (&17 / &32) - schy_sq e lam (&9 / &16))) /
    (schy_sq e lam (&17 / &32) - schy_sq e lam (&9 / &16))`;;

let SCHY_CFUN_FACTS = prove
 (`!e lam. &0 < lam /\ &2 * lam < e /\ lam <= &1
   ==> (!t. t <= schy_sq e lam (&9 / &16) ==> schy_bec e lam t = &0) /\
       (!t. schy_sq e lam (&17 / &32) <= t ==> schy_bec e lam t = &1) /\
       (!t. &0 <= schy_bec e lam t /\ schy_bec e lam t <= &1) /\
       (!t. (schy_bec e lam has_real_derivative schy_becd e lam t) (atreal t)) /\
       (!t. &0 <= schy_becd e lam t) /\
       (!t. t <= schy_sq e lam (&9 / &16) \/ schy_sq e lam (&17 / &32) <= t
            ==> schy_becd e lam t = &0) /\
       smooth_map_on (:real^1) (lift o schy_bec e lam o drop) /\
       (!t. t <= schy_sq e lam (&65 / &128) ==> schy_Hc e lam t = t pow 2) /\
       (!t. &0 < t ==> schy_Hc e lam t = e - lam / &2 - lam * schy_Ac e lam t pow 2) /\
       (!t. schy_sq e lam (&129 / &256) <= t
            ==> schy_Hc e lam t = e - lam / &2 - lam * (t - schy_ta e lam) pow 2 /\
                schy_Ac e lam t = t - schy_ta e lam /\ schy_Acd e lam t = &1) /\
       (!t. t <= schy_sq e lam (&65 / &128) ==> schy_Ac e lam t = schy_f1 e lam t) /\
       (!t. &0 < t ==> (schy_Ac e lam has_real_derivative schy_Acd e lam t) (atreal t) /\
                       &0 < schy_Acd e lam t) /\
       (!t. (schy_Hc e lam has_real_derivative schy_Hcd e lam t) (atreal t)) /\
       (!t. &0 <= t ==> schy_Hc e lam t <= e - lam / &2) /\
       (!t. t < &0 \/ schy_ta e lam < t ==> schy_Hcd e lam t < &0) /\
       (!t. t < schy_sq e lam (&65 / &128) ==> schy_Hcd e lam t = &2 * t) /\
       smooth_map_on (:real^1) (lift o schy_Hc e lam o drop) /\
       smooth_map_on {t:real^1 | &0 < drop t} (lift o schy_Ac e lam o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`schy_sq e lam (&9 / &16)`; `schy_sq e lam (&17 / &32)`] SCHY_ST_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM schy_bec; GSYM schy_becd] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `schy_sq e lam (&65 / &128)`;
                `schy_sq e lam (&129 / &256)`] SCHY_A0_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM schy_Ac; GSYM schy_Acd] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `schy_sq e lam (&65 / &128)`;
                `schy_sq e lam (&129 / &256)`] SCHY_HR_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM schy_Hc; GSYM schy_Hcd; GSYM schy_H0] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `schy_sq e lam (&65 / &128)`;
                `schy_sq e lam (&129 / &256)`] SCHY_A0_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM schy_Ac] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[schy_H0; GSYM schy_Ac];
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `schy_Hc e lam` THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. x pow 2`; `schy_sq e lam (&65 / &128) - t`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN BETA_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t <= schy_sq e lam (&65 / &128) ==> schy_Hc e lam t = t pow 2`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\x:real. x`; `&1`; `t:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_POW_1; REAL_MUL_RID]]]);;

let SCHY_HF_SMOOTH = prove
 (`!(c:real^2->real^2) c' e lam ts.
     sch_ball c c' /\ &0 < lam /\ &2 * lam < e /\ lam <= &1 /\
     (!tau. abs tau < ts ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)))
     ==> smooth_map_on {z:real^2 | abs(&2 * z$1 * z$2) < ts} (\z. lift(schy_hf c' e lam z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `ts:real`] SCHY_B0_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W0 = {z:real^2 | abs(&2 * z$1 * z$2) < ts}` THEN
  SUBGOAL_THEN `smooth_map_on W0 (\z:real^2. lift(schy_Hc e lam (z$1))) /\
                smooth_map_on W0 (\z:real^2. lift(schy_bec e lam (z$1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCHY_SM_COORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[schy_hf; schy_G] THEN SCH3_SMOOTH_TAC);;

let SCHY_B0_ZERO = prove
 (`!(c:real^2->real^2) c' e.
     sch_ball c c' /\ c(--basis 1) = vector[--(sqrt e); &0] /\ &0 < e
     ==> schy_bz c' e (&0) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schy_bz] THEN
  ASM_SIMP_TAC[SCHY_GAM_FACTS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `vector[--(sqrt e); &0]:real^2`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    GEN_REWRITE_RULE I [sch_ball]) THEN
  SUBGOAL_THEN `(c':real^2->real^2)(c(--basis 1)) = --basis 1` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0; NORM_NEG] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC]);;

let SCHY_DIFF_U = prove
 (`!(u:real->real) u' A a lam z2.
     (u has_real_derivative u') (atreal (&0))
     ==> ((\t. A - ((&1 - a) * (z2 + t) pow 2 + a * lam * u t pow 2)) has_real_derivative
          --((&1 - a) * (&2 * z2) + a * lam * (&2 * u(&0) * u'))) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\t. (z2 + t) pow 2) has_real_derivative (&2 * z2)) (atreal (&0))`
  ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\t. (u:real->real) t pow 2) has_real_derivative (&2 * u(&0) * u'))
                (atreal (&0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real->real`; `u':real`; `&0`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `--((&1 - a) * (&2 * z2) + a * lam * (&2 * u(&0) * u')) =
                &0 - ((&1 - a) * (&2 * z2) + a * (lam * (&2 * (u:real->real)(&0) * u')))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN ASM_REWRITE_TAC[]);;

let SCHY_HF_DW = prove
 (`!(c':real^2->real^2) e lam t0 (z:real^2).
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)) /\
     abs(&2 * z$1 * z$2) <= t0
     ==> ((\t. schy_hf c' e lam (z + t % basis 2)) has_real_derivative
          --((&1 - schy_bec e lam (z$1)) * (&2 * z$2) +
             schy_bec e lam (z$1) * lam *
             (&2 * schy_B0 c' e z * (schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * z$1)))))
         (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. schy_hf c' e lam (z + t % basis 2)) =
                (\t. schy_Hc e lam (z$1) -
                     ((&1 - schy_bec e lam (z$1)) * (z$2 + t) pow 2 +
                      schy_bec e lam (z$1) * lam *
                      (\t. schy_bz c' e (--(&2 * z$1 * (z$2 + t)))) t pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_hf; schy_G; schy_B0] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_B0 c' e (z:real^2) =
                (\t. schy_bz c' e (--(&2 * z$1 * (z$2 + t)))) (&0)` SUBST1_TAC THENL
   [REWRITE_TAC[schy_B0; REAL_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC SCHY_DIFF_U THEN
  SUBGOAL_THEN `(\t. schy_bz c' e (--(&2 * (z:real^2)$1 * (z$2 + t)))) =
                schy_bz c' e o (\t. --(&2 * z$1 * (z$2 + t)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG]]);;

let SCHY_HF_DT0 = prove
 (`!(c:real^2->real^2) c' e lam (z:real^2).
     sch_ball c c' /\ c(--basis 1) = vector[--(sqrt e); &0] /\
     &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ z$2 = &0
     ==> ((\t. schy_hf c' e lam (z + t % basis 1)) has_real_derivative
          schy_Hcd e lam (z$1)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`] SCHY_B0_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. schy_hf c' e lam (z + t % basis 1)) =
                schy_Hc e lam o (\t. (z:real^2)$1 + t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; schy_hf; schy_G; schy_B0] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; REAL_NEG_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (z:real^2)$1 + t`; `schy_Hc e lam`; `&1`; `schy_Hcd e lam ((z:real^2)$1)`;
                 `&0`] REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let SCHY_HF_DW_SIGN = prove
 (`!(c':real^2->real^2) e lam t0 (z:real^2).
     &0 < lam /\ &2 * lam < e /\ lam <= &1 /\
     (!tau. abs tau <= t0 /\ ~(tau = &0)
            ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau) /\
     abs(&2 * z$1 * z$2) <= t0 /\ ~(z$2 = &0)
     ==> (&0 < z$2 ==>
          --((&1 - schy_bec e lam (z$1)) * (&2 * z$2) +
             schy_bec e lam (z$1) * lam *
             (&2 * schy_B0 c' e z * (schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * z$1)))) < &0) /\
         (z$2 < &0 ==>
          &0 < --((&1 - schy_bec e lam (z$1)) * (&2 * z$2) +
             schy_bec e lam (z$1) * lam *
             (&2 * schy_B0 c' e z * (schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * z$1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[schy_B0] THEN
  ABBREV_TAC `be = schy_bec e lam ((z:real^2)$1)` THEN
  ABBREV_TAC `tau = --(&2 * (z:real^2)$1 * z$2)` THEN
  SUBGOAL_THEN `be * lam * (&2 * schy_bz c' e tau * (schy_bzd c' e tau * --(&2 * (z:real^2)$1))) =
                --(&4 * (be * lam * z$1) * (schy_bz c' e tau * schy_bzd c' e tau))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bb = schy_bz c' e tau * schy_bzd c' e tau` THEN
  SUBGOAL_THEN `&0 <= be /\ be <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "be" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `be = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_NEG_0; REAL_SUB_RZERO; REAL_MUL_LID;
                    REAL_ADD_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^2)$1` ASSUME_TAC THENL
   [SUBGOAL_THEN `~((z:real^2)$1 <= schy_sq e lam (&9 / &16))` MP_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(z:real^2)$1` o check (fun th ->
        can (term_match [] `!t. t <= schy_sq e lam (&9 / &16) ==> schy_bec e lam t = &0`)
          (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < be * lam * (z:real^2)$1` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < bb * tau` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "tau" THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_NEG_EQ_0; REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `bb < &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> x < &0`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= bb * --tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "tau" THEN
        REWRITE_TAC[REAL_NEG_NEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (be * lam * (z:real^2)$1) * --bb` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - be) * (&2 * (z:real^2)$2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < bb` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(x <= &0) ==> &0 < x`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= --bb * tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "tau" THEN REWRITE_TAC[REAL_ARITH `--(&2 * a * b) = &2 * a * --b`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (be * lam * (z:real^2)$1) * bb` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - be) * --(&2 * (z:real^2)$2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The one-dimensional cancellation.  The line                               *)
(* l(t) = lA - lam/16 t passes 2 d0 = lam/4096 above the tip height; the     *)
(* cutoff chi is 1 on [tL + lam/8, ta + 1/64] and 0 off (tL, ta + 1/32),     *)
(* tL = -sq(1/4); psi = Hr + chi eta((Hr - l)/2) has negative derivative     *)
(* everywhere once the smoothing parameter eps is small.                     *)
(* ------------------------------------------------------------------------- *)

let schy_tL = new_definition `schy_tL e lam = --(schy_sq e lam (&1 / &4))`;;

let schy_chi = new_definition
 `schy_chi e lam = schy_cut (schy_tL e lam) (schy_tL e lam + lam / &8)
                            (schy_ta e lam + &1 / &64) (schy_ta e lam + &1 / &32)`;;

let schy_chid = new_definition
 `schy_chid e lam = schy_cutd (schy_tL e lam) (schy_tL e lam + lam / &8)
                              (schy_ta e lam + &1 / &64) (schy_ta e lam + &1 / &32)`;;

let schy_lA = new_definition
 `schy_lA e lam = e - lam / &2 + &2 * (lam / &8192) + lam / &16 * schy_ta e lam`;;

let schy_xi = new_definition
 `schy_xi e lam t = (schy_Hc e lam t - (schy_lA e lam - lam / &16 * t)) / &2`;;

let schy_rho = new_definition
 `schy_rho e lam eps t = schy_chi e lam t * schy_eta eps (schy_xi e lam t)`;;

let schy_psid = new_definition
 `schy_psid e lam eps t =
    schy_Hcd e lam t + schy_chid e lam t * schy_eta eps (schy_xi e lam t) +
    schy_chi e lam t * (schy_xi e lam t / sqrt(schy_xi e lam t pow 2 + eps pow 2) - &1) *
    (schy_Hcd e lam t + lam / &16) / &2`;;

let SCHY_CHI_FACTS = prove
 (`!e lam. &0 < lam /\ &64 * lam < e /\ &16 * e < &1
   ==> schy_tL e lam + lam / &8 < &0 /\ schy_tL e lam < schy_tL e lam + lam / &8 /\
       schy_tL e lam + lam / &8 <= schy_ta e lam + &1 / &64 /\
       schy_tL e lam pow 2 = e - lam / &4 /\ &0 < schy_ta e lam /\
       schy_ta e lam pow 2 = e - lam / &2 /\ schy_ta e lam < sqrt e /\
       sqrt e < &1 / &4 /\ lam / &4 <= sqrt(e - lam / &4) /\
       (!t. schy_tL e lam + lam / &8 <= t /\ t <= schy_ta e lam + &1 / &64
            ==> schy_chi e lam t = &1 /\ schy_chid e lam t = &0) /\
       (!t. t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t
            ==> schy_chi e lam t = &0 /\ schy_chid e lam t = &0) /\
       (!t. &0 <= schy_chi e lam t /\ schy_chi e lam t <= &1) /\
       (!t. (schy_chi e lam has_real_derivative schy_chid e lam t) (atreal t)) /\
       smooth_map_on (:real^1) (lift o schy_chi e lam o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_SQ_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ sqrt e < &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_ta e lam < sqrt e` ASSUME_TAC THENL
   [REWRITE_TAC[schy_ta] THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lam / &4 <= sqrt(e - lam / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    SUBGOAL_THEN `(lam / &4) pow 2 <= lam / &4` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_tL e lam pow 2 = e - lam / &4 /\ schy_tL e lam = --(sqrt(e - lam / &4))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schy_tL; schy_sq; REAL_POW_NEG; ARITH] THEN
    REWRITE_TAC[REAL_ARITH `&1 / &4 * lam = lam / &4`] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_tL e lam + lam / &8 < &0 /\ schy_tL e lam + lam / &8 <= schy_ta e lam + &1 / &64`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`schy_tL e lam`; `schy_tL e lam + lam / &8`; `schy_ta e lam + &1 / &64`;
                `schy_ta e lam + &1 / &32`] SCHY_CUT_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM schy_chi; GSYM schy_chid] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHY_PSI_1D = prove
 (`!e lam. &0 < lam /\ &64 * lam < e /\ &16 * e < &1
   ==> ?eps1. &0 < eps1 /\ !eps t. &0 < eps /\ eps < eps1 ==> schy_psid e lam eps t < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`schy_Hc e lam`; `schy_Hcd e lam`; `schy_tL e lam`;
                 `schy_ta e lam + &1 / &32`] SCHY_DERIV_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`schy_chi e lam`; `schy_chid e lam`; `schy_tL e lam`;
                 `schy_ta e lam + &1 / &32`] SCHY_DERIV_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d0 = lam / &8192` THEN
  ABBREV_TAC `K = &2 * P + Q * d0 + lam / &16 + &1` THEN
  SUBGOAL_THEN `&0 < d0` ASSUME_TAC THENL [EXPAND_TAC "d0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q * d0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [EXPAND_TAC "K" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u1 = (lam / &64) / K` THEN
  SUBGOAL_THEN `&0 < u1 /\ u1 * K = lam / &64` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `sqrt(&2 * d0 pow 2 * u1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `u = eps pow 2 / (&2 * d0 pow 2)` THEN
  SUBGOAL_THEN `&0 <= u /\ u < u1 /\ eps pow 2 / (&2 * d0) = u * d0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `&0 < &2 * d0 pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `eps pow 2 < sqrt(&2 * d0 pow 2 * u1) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &2 * d0 pow 2 * u1` ASSUME_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < d0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `u * P < lam / &16 /\
                Q * (u * d0) + u * (P + lam / &16) / &2 < lam / &32` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `u * P <= u1 * K /\
                  u * (Q * d0 + (P + lam / &16) / &2) <= u1 * K` MP_TAC THENL
     [SUBGOAL_THEN `&0 <= Q * d0` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `x = schy_xi e lam t` THEN
  REWRITE_TAC[schy_psid] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `schy_lA e lam - lam / &16 * t =
                e - lam / &2 + &2 * d0 + lam / &16 * (schy_ta e lam - t)` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[schy_lA] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * x = schy_Hc e lam t - (e - lam / &2 + &2 * d0 + lam / &16 * (schy_ta e lam - t))`
  ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[schy_xi] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k k1. &0 <= k /\ k <= &1 /\ abs k1 <= Q /\ abs(schy_Hcd e lam t) <= P /\
                       ((k = &1 /\ k1 = &0 /\ (schy_Hcd e lam t < &0 \/ x <= --d0)) \/
                        (d0 <= x /\ schy_Hcd e lam t <= --(lam / &32)))
                       ==> schy_Hcd e lam t + k1 * schy_eta eps x +
                           k * (x / sqrt(x pow 2 + eps pow 2) - &1) *
                           (schy_Hcd e lam t + lam / &16) / &2 < &0` (LABEL_TAC "NEG") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHY_PSI_NEG THEN
    MAP_EVERY EXISTS_TAC [`d0:real`; `P:real`; `Q:real`; `lam / &32`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_tL e lam = --(sqrt(e - lam / &4)) /\ sqrt(e - lam / &4) < &1 / &4`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[schy_tL; schy_sq] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt e` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t` THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
      `!t. t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t
           ==> schy_chi e lam t = &0 /\ schy_chid e lam t = &0`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. t < &0 \/ schy_ta e lam < t ==> schy_Hcd e lam t < &0`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(schy_Hcd e lam t) <= P /\ abs(schy_chid e lam t) <= Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "NEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t <= schy_tL e lam + lam / &8` THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `schy_Hcd e lam t = &2 * t /\ schy_Hc e lam t = t pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `s = sqrt(e - lam / &4)` THEN
    SUBGOAL_THEN `(s - lam / &8) pow 2 <= t pow 2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lam / &4 * s <= lam / &16 /\
                  lam / &16 * (schy_ta e lam - t) <= lam / &32` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `a <= (lam / &4) * (&1 / &4) ==> a <= lam / &16`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `(lam / &16) * a <= (lam / &16) * (&1 / &2) ==> lam / &16 * a <= lam / &32`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `s pow 2 = e - lam / &4` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(s - lam / &8) pow 2 <= t pow 2` THEN
    REWRITE_TAC[REAL_ARITH `(s - l) pow 2 = s pow 2 - &2 * l * s + l pow 2`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "d0" THEN
    MP_TAC(SPEC `lam / &8` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= schy_ta e lam + &1 / &64` THENL
   [DISJ1_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
      `!t. schy_tL e lam + lam / &8 <= t /\ t <= schy_ta e lam + &1 / &64
           ==> schy_chi e lam t = &1 /\ schy_chid e lam t = &0`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t < &0 \/ schy_ta e lam < t` THENL
     [DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t < &0 \/ schy_ta e lam < t ==> schy_Hcd e lam t < &0`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      SUBGOAL_THEN `schy_Hc e lam t <= e - lam / &2 /\ &0 <= lam / &16 * (schy_ta e lam - t)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    DISJ2_TAC THEN
    SUBGOAL_THEN `schy_sq e lam (&129 / &256) <= t /\ &0 < t` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `schy_Hcd e lam t = --(&2 * lam * (t - schy_ta e lam))` ASSUME_TAC THENL
     [REWRITE_TAC[schy_Hcd; schy_Hrd; GSYM schy_Ac; GSYM schy_Acd] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> ~(t <= &0)`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    ABBREV_TAC `v = t - schy_ta e lam` THEN
    SUBGOAL_THEN `&0 <= (v - &1 / &64) * (&1 / &32 - v)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lam * ((v - &1 / &64) * (&1 / &32 - v)) /\ lam / &64 <= lam * v`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `lam * &1 / &64 <= lam * v ==> lam / &64 <= lam * v`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `schy_Hc e lam t = e - lam / &2 - lam * v pow 2` ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
        `!t. schy_sq e lam (&129 / &256) <= t
             ==> schy_Hc e lam t = e - lam / &2 - lam * (t - schy_ta e lam) pow 2 /\ P t`)
        (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `&2 * x = schy_Hc e lam t -
                 (e - lam / &2 + &2 * d0 + lam / &16 * (schy_ta e lam - t))` THEN
    SUBGOAL_THEN `schy_ta e lam - t = --v` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "d0" THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The two-dimensional cancellation.  rho = chi eta(xi) >= 0                 *)
(* is smooth with derivative psid - Hr'; the sheared height                  *)
(* hf(t,w) + beta(w) rho(t) has no critical point where the strip function   *)
(* b is differentiable.                                                      *)
(* ------------------------------------------------------------------------- *)

let SCHY_RHO_FACTS = prove
 (`!e lam eps. &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < eps
   ==> (!t. (schy_rho e lam eps has_real_derivative
             (schy_psid e lam eps t - schy_Hcd e lam t)) (atreal t)) /\
       (!t. &0 <= schy_rho e lam eps t) /\
       (!t. t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t
            ==> schy_rho e lam eps t = &0) /\
       (!t. schy_rho e lam eps t <= schy_eta eps (schy_xi e lam t)) /\
       smooth_map_on (:real^1) (lift o schy_rho e lam eps o drop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1 /\ ~(eps = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN `schy_rho e lam eps =
                  (\t. (\t. schy_Hc e lam t + schy_chi e lam t *
                            schy_eta eps ((schy_Hc e lam t - (schy_lA e lam - lam / &16 * t)) / &2))
                       t - schy_Hc e lam t)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; schy_rho; schy_xi] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[schy_psid; schy_xi] THEN
    MATCH_MP_TAC SCHY_PSI_DERIV THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN REWRITE_TAC[schy_rho] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SCHY_ETA_FACTS; REAL_LT_IMP_LE];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[schy_rho] THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    GEN_TAC THEN REWRITE_TAC[schy_rho] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[SCHY_ETA_FACTS; REAL_LT_IMP_LE];
    REWRITE_TAC[o_DEF; schy_rho; schy_xi; schy_eta] THEN
    MP_TAC(INST_TYPE [`:1`,`:N`] OPEN_UNIV) THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_map_on (:real^1) (\t. lift(schy_chi e lam (drop t))) /\
                  smooth_map_on (:real^1) (\t. lift(schy_Hc e lam (drop t)))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th ->
          concl th = `smooth_map_on (:real^1) (lift o schy_chi e lam o drop)`));
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          concl th = `smooth_map_on (:real^1) (lift o schy_Hc e lam o drop)`))] THEN
      REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^1. x IN (:real^1)
                  ==> &0 < ((schy_Hc e lam (drop x) - (schy_lA e lam - lam / &16 * drop x)) / &2)
                            pow 2 + eps pow 2` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LT];
      ALL_TAC] THEN
    SCH3_SMOOTH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX; SMOOTH_MAP_ON_ID; IN_UNIV] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SCHY_HS_NOCRIT = prove
 (`!(c:real^2->real^2) c' e lam ts t0 eps wb (z:real^2).
     sch_ball c c' /\ c(--basis 1) = vector[--(sqrt e); &0] /\
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < eps /\
     (!t. schy_psid e lam eps t < &0) /\ &0 < wb /\
     (!tau. abs tau < ts ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2))) /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)) /\
     (!tau. abs tau <= t0 /\ ~(tau = &0)
            ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau) /\
     t0 < ts /\ abs(&2 * z$1 * z$2) <= t0
     ==> ~(frechet_derivative
             (\z. lift(schy_hf c' e lam z + schy_bw wb (z$2) * schy_rho e lam eps (z$1)))
             (at z) = (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `lam:real`; `ts:real`]
    SCHY_HF_SMOOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `ts:real`] SCHY_B0_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift(schy_hf c' e lam z)) differentiable (at (z:real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^2 | abs(&2 * z$1 * z$2) < ts}` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `wb:real` SCHY_BW_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC SCHY_2D_NOCRIT THEN
  MAP_EVERY EXISTS_TAC
   [`frechet_derivative (\z. lift(schy_hf c' e lam z)) (at (z:real^2))`;
    `--(schy_ssd(((z:real^2)$2) pow 2 / wb pow 2) * (&2 * z$2) * inv(wb pow 2))`;
    `schy_psid e lam eps ((z:real^2)$1) - schy_Hcd e lam (z$1)`] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  SUBGOAL_THEN `drop(frechet_derivative (\z. lift(schy_hf c' e lam z)) (at (z:real^2)) (basis 2)) =
                --((&1 - schy_bec e lam (z$1)) * (&2 * z$2) +
                   schy_bec e lam (z$1) * lam *
                   (&2 * schy_B0 c' e z * (schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * z$1))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SCHY_PARTIAL THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC SCHY_HF_DW THEN EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c':real^2->real^2`; `e:real`; `lam:real`; `t0:real`; `z:real^2`]
    SCHY_HF_DW_SIGN) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(z:real^2)$2 = &0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `drop(frechet_derivative (\z. lift(schy_hf c' e lam z)) (at (z:real^2)) (basis 1)) =
                  schy_Hcd e lam (z$1)` SUBST1_TAC THENL
     [MATCH_MP_TAC SCHY_PARTIAL THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC SCHY_HF_DT0 THEN EXISTS_TAC `c:real^2->real^2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(z:real^2)$1` o check (fun th -> can (term_match []
      `!t. schy_psid e lam eps t < &0`) (concl th))) THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN
    ASM_CASES_TAC `&0 < (z:real^2)$2` THENL
     [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISJ2_TAC THEN
      SUBGOAL_THEN `(z:real^2)$2 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* The cancellation context.  schy_ctx bundles the box chart,                *)
(* the level component C with its ball chart c, the chart Theta of H2 and    *)
(* the smallness 64 lam < e.  Chart points with |pr y|^2 < 1 + 2 s1 project  *)
(* close to the closed inside J union inside J of J = pr C.                  *)
(* ------------------------------------------------------------------------- *)

let schy_ctx = new_definition
 `schy_ctx (g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam
           H (Theta:real^3->real^3) Theta' <=>
    schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
    C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
    (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
    sch_ball c c' /\ IMAGE (\z. sch5v_at e (c z)) (sphere(vec 0,&1)) = C /\
    IMAGE c (ball(vec 0,&1)) = inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
    c(--basis 1) = vector[--(sqrt e); &0] /\
    schy_cd v B rho0 e c delta1 lam H Theta Theta' /\
    (!y. y IN sch5v_slab H
         ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
    &64 * lam < e /\ &5 <= H`;;

let SCHY_CTX_J = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta'.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta'
     ==> IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C = IMAGE c (sphere(vec 0,&1)) /\
         IMAGE c (cball(vec 0,&1)) =
           inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) UNION
           IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C =
                IMAGE (c:real^2->real^2) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `C:real^3->bool`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; sch5v_at; VECTOR_3] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[]);;

let SCHY_PR_DIST = prove
 (`!a b:real^3. dist(sch5v_pr a,sch5v_pr b) <= dist(a,b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dist; sch5v_pr; NORM_LE; DOT_2; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  MP_TAC(SPEC `(a:real^3)$3 - (b:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let SCHY_THETA_DISP = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta' y.
     schy_cd v B rho0 e c delta1 lam H Theta Theta'
     ==> dist(Theta y,sch5v_at e (c(sch5v_pr y))) <= B * lam * abs(y$3) /\
         dist(sch5v_pr(Theta y),c(sch5v_pr y)) <= B * lam * abs(y$3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd]) THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) y =
                ode_vf_flow v (:real^3) (lift(lam * (y:real^3)$3)) (sch5v_at e (c(sch5v_pr y)))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `!y. (Theta:real^3->real^3) y = f y`) (concl th))) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sch5v_at e (c(sch5v_pr(y:real^3)))`; `lift(lam * (y:real^3)$3)`;
                            `vec 0:real^1`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_SUB_RZERO; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  REWRITE_TAC[GSYM dist] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ode_vf_flow v (:real^3) (lift(lam * (y:real^3)$3)) (sch5v_at e (c(sch5v_pr y)))`;
                 `sch5v_at e (c(sch5v_pr(y:real^3)))`] SCHY_PR_DIST) THEN
  REWRITE_TAC[SCH5V_PR_AT] THEN ASM_REAL_ARITH_TAC);;

let SCHY_CHART_NEAR_J = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' s1 ds y.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\ &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 + &2 * s1
     ==> ?z. (z IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) \/
              z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
             dist(sch5v_pr(Theta y),z) < B * lam * H + ds`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_J) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_THETA_DISP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCHY_CD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `B * lam * abs((y:real^3)$3) <= B * lam * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
        can (term_match [] `schy_cd v B rho0 e c delta1 lam H Theta Theta'`) (concl th))) THEN
      SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `(y:real^3) IN sch5v_slab H` THEN REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `w = sch5v_pr(y:real^3)` THEN
  SUBGOAL_THEN `norm(w:real^2) pow 2 = (y:real^3)$1 pow 2 + y$2 pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_POW_2; DOT_2; sch5v_pr; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(w:real^2) < &1` THENL
   [EXISTS_TAC `(c:real^2->real^2) w` THEN
    CONJ_TAC THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `(c:real^2->real^2) w IN IMAGE c (ball(vec 0,&1))` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `(c:real^2->real^2)(inv(norm w) % w)` THEN CONJ_TAC THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`sch5v_pr((Theta:real^3->real^3) y)`; `(c:real^2->real^2) w`;
                     `(c:real^2->real^2)(inv(norm w) % w)`] DIST_TRIANGLE) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> can (term_match []
        `!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1
             ==> dist((c:real^2->real^2) z,c(inv(norm z) % z)) < ds`) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC]]);;

let SCHY_KIN_ZERO = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' s1 ds rho1 rho2 x.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\ &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     sch5v_pr x IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
     norm(sch5v_pr x) + (B * lam * H + ds) < r /\ abs(x$2) + (B * lam * H + ds) <= sqrt e /\
     (abs(x$1 + sqrt e) <= abs(x$2) + &2 * (B * lam * H + ds)
      ==> norm(x - schy_lpt e) <= rho1)
     ==> schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCHY_CD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 <= H` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Theta:real^3->real^3`; `Theta':real^3->real^3`; `H:real`; `s1:real`;
                 `rho1:real`; `rho2:real`; `schy_lpt e`] SCHY_KIN_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^3) IN IMAGE Theta (sch5v_slab H)` THENL
   [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_IMAGE] o
    check (fun th -> concl th = `(x:real^3) IN IMAGE Theta (sch5v_slab H)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(x:real^3) = Theta(y:real^3)`)) THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`s1:real`; `H:real`] SCHY_KMOD_PROPS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `&1 + &2 * s1 <= (y:real^3)$1 pow 2 + y$2 pow 2` THENL
   [ASM_SIMP_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((Theta:real^3->real^3) y - schy_lpt e) <= rho1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                   `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `s1:real`; `ds:real`; `y:real^3`]
      SCHY_CHART_NEAR_J) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `sch5v_pr((Theta:real^3->real^3) y)`; `z:real^2`; `B * lam * H + ds`]
      SCHY_NEAR_J) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[sch5v_pr; VECTOR_2] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[sch5v_pr; VECTOR_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_bump rho1 rho2 ((Theta:real^3->real^3) y - schy_lpt e) = &1`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The box part of the strip.  Box points project into the                   *)
(* outside of J; no dome point off S lies over a box point (near P0 the     *)
(* explicit chart gives Re U = f(c(pr y)) + lam y3 >= e - lam).              *)
(* ------------------------------------------------------------------------- *)

let SCHY_BOXPR_OUT = prove
 (`!(g:real^3->real^3) r e C x:real^2.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
     &0 < x$1 + sqrt e /\ x$1 pow 2 - x$2 pow 2 < e /\ x$2 pow 2 < e / &4 /\ norm x < r
     ==> x IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `--(sqrt e) / &2 <= (x:real^2)$1` THENL
   [MATCH_MP_TAC SCHY_OUT_RIGHT THEN EXISTS_TAC `g:real^3->real^3` THEN
    EXISTS_TAC `r:real` THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `((x:real^2)$1 + sqrt e) pow 2 < e / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(sqrt e / &2) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_DIV] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

let SCHY_DOME_AVOID = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' p.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch5v_pr p IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
     norm(sch5v_pr p) + (B * lam + lam) < r /\
     &2 * abs(p$2) + &3 * (B * lam + lam) < rho0 / &2 /\
     &2 * abs(p$2) + &3 * (B * lam + lam) < sqrt e /\
     (abs(p$1 + sqrt e) <= abs(p$2) + &2 * (B * lam + lam)
      ==> p$1 pow 2 - p$2 pow 2 <= e - lam)
     ==> !y. y IN sch_cap1 /\ ~(Theta y IN IMAGE g (sphere(vec 0,&1)))
             ==> ~(sch5v_pr(Theta y) = sch5v_pr p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_J) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd]) THEN
  SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 <= &1 /\ -- &1 <= y$3 /\ y$3 <= --(&1 / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sch_cap1` THEN REWRITE_TAC[sch_cap1; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SCHY_PROFILE_LE1];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab H` ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_THETA_DISP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th -> can (term_match []
      `!y. norm((v:real^3->real^3) y) <= B`) (concl th))) THEN
    MP_TAC(ISPEC `(v:real^3->real^3)(vec 0)` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B * lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `B * lam * abs((y:real^3)$3) <= B * lam` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y * &1 ==> x <= y`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = (c:real^2->real^2)(sch5v_pr(y:real^3))` THEN
  SUBGOAL_THEN `z IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) \/
                z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `IMAGE (c:real^2->real^2) (cball(vec 0,&1))`)) THEN
    EXPAND_TAC "z" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_CBALL_0; NORM_LE_SQUARE; DOT_2; sch5v_pr; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `sch5v_pr(p:real^3)`; `z:real^2`; `B * lam + lam`] SCHY_NEAR_J) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[sch5v_pr; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[sch5v_pr; VECTOR_2] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `(p:real^3)$1 pow 2 - p$2 pow 2 <= e - lam` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `dist(z,vector[--(sqrt e); &0]:real^2) < rho0 / &2 /\
                dist(z,vector[--(sqrt e); &0]:real^2) < sqrt e` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `dist(sch5v_pr(p:real^3),vector[--(sqrt e); &0]:real^2) <=
                  abs(p$1 + sqrt e) + abs(p$2)` ASSUME_TAC THENL
     [REWRITE_TAC[dist] THEN
      W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT; sch5v_pr; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z:real^2`; `sch5v_pr(p:real^3)`; `vector[--(sqrt e); &0]:real^2`]
      DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`z:real^2`; `sch5v_pr(p:real^3)`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B * abs(lam * (y:real^3)$3) < rho0 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
    SUBGOAL_THEN `&0 <= (B * lam) * (H - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `sch5v_at e z`;
                 `lam * (y:real^3)$3`] SCHY_THETA_PI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SCHY_LPT_AT; SCHY_AT_DIST] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> can (term_match []
      `!x. dist(x,schy_lpt e) < rho0 ==> (v:real^3->real^3) x = schy_v0 x /\ x$1 < &0`)
      (concl th))) THEN
    ASM_REWRITE_TAC[SCHY_LPT_AT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 < (x:real^3)$1 pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ode_vf_flow v (:real^3) (lift(lam * (y:real^3)$3)) (sch5v_at e z) =
                (Theta:real^3->real^3) y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$1`) THEN
  REWRITE_TAC[schy_pi; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3; sch5v_at] THEN
  SUBGOAL_THEN `((Theta:real^3->real^3) y)$1 = (p:real^3)$1 /\ (Theta y)$2 = p$2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5v_pr((Theta:real^3->real^3) y) = sch5v_pr(p:real^3)` THEN
    REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `dist(z,vector[--(sqrt e); &0]:real^2) < sqrt e` THEN
    REWRITE_TAC[dist; NORM_LT_SQUARE; DOT_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `e <= (z:real^2)$1 pow 2 - z$2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(x < e) ==> e <= x`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` INSIDE_INTER_OUTSIDE) THEN
    MP_TAC(ISPEC `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` OUTSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `z IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) \/
                 z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 pow 2 - z$2 pow 2 = e` ASSUME_TAC THENL
   [SUBGOAL_THEN `--lam <= lam * (y:real^3)$3` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `lam * -- &1 <= lam * y ==> --lam <= lam * y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_pr(y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^2) IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` MP_TAC THENL
     [FIRST_ASSUM((fun th -> MATCH_MP_TAC(snd(EQ_IMP_RULE th))) o check (fun th ->
        is_iff(concl th) &&
        lhand(concl th) = `(z:real^2) IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `IMAGE (c:real^2->real^2) (sphere(vec 0,&1))`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
      GEN_REWRITE_RULE I [sch_ball] o check (fun th -> can (term_match []
        `sch_ball (c:real^2->real^2) c'`) (concl th))) THEN
    SUBGOAL_THEN `u IN ball(vec 0:real^2,&2) /\ sch5v_pr(y:real^3) IN ball(vec 0,&2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(u:real^2) IN sphere(vec 0,&1)` THEN
        REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_BALL_0; NORM_LT_SQUARE; DOT_2; sch5v_pr; VECTOR_2] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^2->real^2) u = c(sch5v_pr(y:real^3))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `u:real^2 = sch5v_pr(y:real^3)` (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
    FIRST_ASSUM((fun th ->
      MP_TAC(MP (SPEC `u:real^2` th) (ASSUME `(u:real^2) IN ball(vec 0,&2)`)) THEN
      MP_TAC(MP (SPEC `sch5v_pr(y:real^3)` th) (ASSUME `sch5v_pr(y:real^3) IN ball(vec 0,&2)`)))
      o check (fun th -> can (term_match []
        `!x. x IN ball(vec 0:real^2,&2) ==> (c':real^2->real^2)((c:real^2->real^2) x) = x`)
        (concl th))) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `(c:real^2->real^2) u = c(sch5v_pr(y:real^3))`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((Theta:real^3->real^3) y IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `sch5v_pr(y:real^3) IN sphere(vec 0,&1)` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_2; sch5v_pr; VECTOR_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The circle point z(tau) = c'(gamma(tau)) for small tau, and               *)
(* the strip formulas: box points for t <= sq(1); Theta(ma) on the polar     *)
(* part; Theta(mb) beyond sq(17/32) (where ma = mb).                         *)
(* ------------------------------------------------------------------------- *)

let SCHY_GAM_NBHD = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta'.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta'
     ==> ?ts. &0 < ts /\
              !tau. abs tau < ts
                    ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                        c(c'(schy_gam e tau)) = schy_gam e tau /\
                        c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                        (c'(schy_gam e tau))$1 < &0 /\
                        dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_J) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd]) THEN
  SUBGOAL_THEN `&0 < sqrt e` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "SIDE")] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`;
                 `min (rho0 / &2) (sqrt e / &2)`] SCHY_ZT_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    USE_THEN "SIDE" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `dist(x,vector[--(sqrt e); &0]:real^2) < sqrt e / &2` THEN
      REWRITE_TAC[dist; NORM_LT_SQUARE; DOT_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
      ASM_SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `ts1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ZT")))] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    GEN_REWRITE_RULE I [sch_ball] o check (fun th -> can (term_match []
      `sch_ball (c:real^2->real^2) c'`) (concl th))) THEN
  SUBGOAL_THEN `--basis 1 IN ball(vec 0:real^2,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2)(vector[--(sqrt e); &0]) = --basis 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `vector[--(sqrt e); &0]:real^2`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2) continuous (at (vector[--(sqrt e); &0]))` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (c:real^2->real^2) (ball(vec 0,&2))` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `vector[--(sqrt e); &0]:real^2`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))) THEN
  MP_TAC(SPECL [`e:real`; `d1:real`] SCHY_GAM_CONT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min ts1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  USE_THEN "ZT" (fun th -> MP_TAC(MP (SPEC `tau:real` th) (ASSUME `abs tau < ts1`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  USE_THEN "CT" (MP_TAC o SPEC `schy_gam e tau`) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist] THEN
  MP_TAC(ISPECL [`(c':real^2->real^2)(schy_gam e tau) - --basis 1`; `1`] COMPONENT_LE_NORM) THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REAL_ARITH_TAC);;

let schy_Q = new_definition
 `schy_Q e lam wq = {z:real^2 | schy_tL e lam - lam / &16 < z$1 /\
                                z$1 < schy_ta e lam + &1 / &16 /\ abs(z$2) < wq}`;;

let SCHY_Q_FACTS = prove
 (`!e lam wq z. &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < wq /\ z IN schy_Q e lam wq
   ==> abs(z$1) < &1 / &2 /\ abs(&2 * z$1 * z$2) < wq /\ abs(z$2) < wq /\
       schy_tL e lam - lam / &16 < z$1 /\ z$1 < schy_ta e lam + &1 / &16`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_Q; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((z:real^2)$1) < &1 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(e - lam / &4) < &1 / &4` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt e` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `schy_tL e lam = --(sqrt(e - lam / &4))` ASSUME_TAC THENL
     [REWRITE_TAC[schy_tL; schy_sq] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `abs((z:real^2)$1) * abs(z$2) <= (&1 / &2) * abs(z$2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let SCHY_F1_BOUND = prove
 (`!e lam t. &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
             schy_sq e lam (&17 / &32) <= t /\ t < schy_ta e lam
             ==> abs(schy_f1 e lam t) <= &1 / &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam /\
                &0 < schy_sq e lam (&17 / &32)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2; MATCH_MP_TAC SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_F1_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&17 / &32) pow 2 <= t pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= abs(&1 / &4) ==> abs x <= &1 / &4`) THEN
  REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let SCHY_AC_BOUND = prove
 (`!e lam t. &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
             schy_sq e lam (&17 / &32) <= t /\ t <= schy_ta e lam + &1 / &16
             ==> abs(schy_Ac e lam t) <= &1 / &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < e /\ &2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `m1 = schy_sq e lam (&65 / &128)` THEN
  ABBREV_TAC `m2 = schy_sq e lam (&129 / &256)` THEN
  SUBGOAL_THEN `m1 pow 2 = e - &65 / &128 * lam /\ m2 pow 2 = e - &129 / &256 * lam`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN REWRITE_TAC[schy_sq] THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_ta e lam <= m1 + &1 / &16` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(m + &1 / &16 < t) ==> t <= m + &1 / &16`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(m1 + &1 / &16) pow 2 < schy_ta e lam pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `(m + &1 / &16) pow 2 = m pow 2 + m / &8 + &1 / &256`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= m1` THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SCHY_F1_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m2 <= t` THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[schy_Ac; schy_A0] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = smooth_step((t - m1) / (m2 - m1))` THEN
  SUBGOAL_THEN `&0 <= s /\ s <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(schy_f1 e lam t) <= &1 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_F1_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - s) * abs(schy_f1 e lam t) <= (&1 - s) * (&1 / &4) /\
                s * abs(t - schy_ta e lam) <= s * (&1 / &16)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((&1 - s) * schy_f1 e lam t) + abs(s * (t - schy_ta e lam))` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s /\ s <= &1 ==> abs(&1 - s) = &1 - s /\ abs s = s`] THEN
  ASM_REAL_ARITH_TAC);;

let SCHY_GM_PIECES = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq z.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\ z IN schy_Q e lam wq
     ==> (z$1 <= schy_sq e lam (&7 / &8) ==> schy_gm Theta c' e lam z = schy_sbox z) /\
         (schy_sq e lam (&1) < z$1 /\ z$1 <= schy_sq e lam (&33 / &64)
          ==> schy_ma c' e lam (schy_bec e lam) z IN sch5v_slab H /\
              &1 / &128 <= sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) z)) -
                           schy_B0 c' e z pow 2 /\
              schy_gm Theta c' e lam z = Theta(schy_ma c' e lam (schy_bec e lam) z) /\
              (schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
              (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 =
              sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) z)$3)) /\
              --(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3 /\
              (schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)) /\
         (schy_sq e lam (&17 / &32) <= z$1
          ==> schy_mb c' e (schy_Ac e lam) z IN sch5v_slab H /\
              schy_gm Theta c' e lam z = Theta(schy_mb c' e (schy_Ac e lam) z) /\
              (schy_mb c' e (schy_Ac e lam) z)$1 pow 2 + (schy_mb c' e (schy_Ac e lam) z)$2 pow 2 =
              sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) z)$3)) /\
              --(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3 /\
              (schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2)) /\
         (schy_gm Theta c' e lam z)$3 = schy_hf c' e lam z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
    can (term_match [] `schy_cd v B rho0 e c delta1 lam H Theta Theta'`) (concl th))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `!y. (Theta:real^3->real^3) y = f y`) (concl th))) THEN
  SUBGOAL_THEN `&16 * e < &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
      can (term_match [] `schy_chart s r`) (concl th))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `r pow 2 < &1` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < &1 * &1 ==> x < &1`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * lam < e /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_SQ_FACTS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "SQ" o CONJUNCT1)] THEN
  SUBGOAL_THEN `!k. &0 <= k /\ k <= &1 ==> schy_sq e lam k pow 2 = e - k * lam`
  (LABEL_TAC "SQ2") THENL [USE_THEN "SQ" (fun th -> MESON_TAC[th]); ALL_TAC] THEN

  ABBREV_TAC `tau = --(&2 * (z:real^2)$1 * z$2)` THEN
  SUBGOAL_THEN `abs tau < wq` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[REAL_ABS_NEG]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
    `!tau. abs tau < ts ==> schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\ P tau`)
    (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `schy_B0 c' e (z:real^2) pow 2 <= &1 / &256` ASSUME_TAC THENL
   [REWRITE_TAC[schy_B0] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= (&1 / &16) pow 2 ==> x <= &1 / &256`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$2 pow 2 <= lam / &100` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wq pow 2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= schy_bec e lam ((z:real^2)$1) /\ schy_bec e lam (z$1) <= &1`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= schy_G c' e lam (schy_bec e lam) (z:real^2) /\
                schy_G c' e lam (schy_bec e lam) z <= lam / &100 + lam / &256` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schy_G] THEN
    SUBGOAL_THEN `&0 <= (&1 - schy_bec e lam ((z:real^2)$1)) * z$2 pow 2 /\
                  (&1 - schy_bec e lam (z$1)) * z$2 pow 2 <= &1 * lam / &100 /\
                  &0 <= schy_bec e lam (z$1) * lam * schy_B0 c' e z pow 2 /\
                  schy_bec e lam (z$1) * lam * schy_B0 c' e z pow 2 <= &1 * lam * &1 / &256`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&1) pow 2 = e - lam /\
                schy_sq e lam (&7 / &8) pow 2 = e - &7 / &8 * lam /\
                schy_sq e lam (&33 / &64) pow 2 = e - &33 / &64 * lam /\
                schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "SQ2" (fun th -> REWRITE_TAC[REAL_MUL_LID] THEN
      MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `&7 / &8` th) THEN MP_TAC(SPEC `&33 / &64` th) THEN
      MP_TAC(SPEC `&17 / &32` th)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `Y = schy_Ya c' e lam (schy_bec e lam) (z:real^2)` THEN
  SUBGOAL_THEN `lam * Y = (z:real^2)$1 pow 2 - e - schy_G c' e lam (schy_bec e lam) z`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[schy_Ya] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 <= schy_sq e lam (&7 / &8)
                ==> schy_gm Theta c' e lam z = schy_sbox z` ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[schy_gm; schy_strip] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_BOX_MA THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->real^3`; `B:real`; `rho0:real`; `c:real^2->real^2`;
                          `delta1:real`; `H:real`; `Theta':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e - lam < (z:real^2)$1 pow 2 /\ z$1 pow 2 <= e - &7 / &8 * lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&1) pow 2 = e - lam`)) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&7 / &8) pow 2 = e - &7 / &8 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < lam ==> abs lam = lam`; REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `&5 * lam <= H * lam` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&1) < (z:real^2)$1 /\ z$1 <= schy_sq e lam (&33 / &64)
                ==> schy_ma c' e lam (schy_bec e lam) z IN sch5v_slab H /\
                    &1 / &128 <= sch_cap_profile(--Y) - schy_B0 c' e z pow 2 /\
                    schy_gm Theta c' e lam z = Theta(schy_ma c' e lam (schy_bec e lam) z) /\
                    (schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
                    (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 =
                    sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) z)$3)) /\
                    --(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3 /\
                    (schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `e - lam < (z:real^2)$1 pow 2 /\ z$1 pow 2 <= e - &33 / &64 * lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&1) pow 2 = e - lam`)) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&33 / &64) pow 2 = e - &33 / &64 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `--(&1 + &1 / &100 + &1 / &256) <= Y /\ Y <= --(&33 / &64)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `lam * --(&1 + &1 / &100 + &1 / &256) <= lam * Y /\
                    lam * Y <= lam * --(&33 / &64)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &64 <= sch_cap_profile(--Y) /\ sch_cap_profile(--Y) <= &1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SCHY_PROFILE_LE1] THEN ASM_CASES_TAC `--Y <= &5 / &8` THENL
       [ASM_SIMP_TAC[SCH_CAP_PROFILE_TIP] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `--Y` SCH_CAP_PROFILE_LB) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[schy_ma; sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
      SUBGOAL_THEN `sqrt(sch_cap_profile(--Y) - schy_B0 c' e (z:real^2) pow 2) pow 2 =
                    sch_cap_profile(--Y) - schy_B0 c' e z pow 2` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[schy_gm; schy_strip] THEN
      ASM_SIMP_TAC[REAL_ARITH `a < b ==> ~(b <= a)`];
      REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
      SUBGOAL_THEN `sqrt(sch_cap_profile(--Y) - schy_B0 c' e (z:real^2) pow 2) pow 2 =
                    sch_cap_profile(--Y) - schy_B0 c' e z pow 2` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&17 / &32) <= (z:real^2)$1
                ==> schy_mb c' e (schy_Ac e lam) z IN sch5v_slab H /\
                    schy_gm Theta c' e lam z = Theta(schy_mb c' e (schy_Ac e lam) z) /\
                    (schy_mb c' e (schy_Ac e lam) z)$1 pow 2 +
                    (schy_mb c' e (schy_Ac e lam) z)$2 pow 2 =
                    sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) z)$3)) /\
                    --(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3 /\
                    (schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `schy_Ac e lam ((z:real^2)$1) pow 2 <= &1 / &16` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= (&1 / &4) pow 2 ==> x <= &1 / &16`) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC SCHY_AC_BOUND THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(schy_mb c' e (schy_Ac e lam) z)$1 pow 2 +
                  (schy_mb c' e (schy_Ac e lam) z)$2 pow 2 =
                  sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) (z:real^2))$3)) /\
                  --(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3 /\
                  (schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[schy_mb; VECTOR_3] THEN
      MP_TAC(SPEC `schy_Ac e lam ((z:real^2)$1)` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `schy_B0 c' e (z:real^2)` REAL_LE_POW_2) THEN REPEAT STRIP_TAC THEN
      TRY ASM_REAL_ARITH_TAC THEN
      MP_TAC(SPEC `--(--(&1 / &2) - schy_Ac e lam ((z:real^2)$1) pow 2 - schy_B0 c' e z pow 2)`
        SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[schy_mb; sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN
      MP_TAC(SPEC `schy_Ac e lam ((z:real^2)$1)` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `schy_B0 c' e (z:real^2)` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[schy_gm; schy_strip] THEN
    SUBGOAL_THEN `~((z:real^2)$1 <= schy_sq e lam (&1))` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SCHY_MA_MB THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^2)$1 pow 2 <= e - &33 / &64 * lam /\ e - &17 / &32 * lam <= z$1 pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&33 / &64) pow 2 = e - &33 / &64 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_TA_FACTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `schy_bec e lam ((z:real^2)$1) = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `schy_Ac e lam ((z:real^2)$1) = schy_f1 e lam (z$1)` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[schy_f1] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `e / lam - &1 / &2 - (z:real^2)$1 pow 2 / lam =
                    (e - lam / &2 - z$1 pow 2) / lam` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `lam * schy_B0 c' e (z:real^2) pow 2 <= lam * (&1 / &256)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `lam * --(&5 / &8) <= lam * Y` MP_TAC THENL
       [ASM_REWRITE_TAC[schy_G; REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H ==> ((Theta:real^3->real^3) y)$3 = e + lam * y$3`
  (LABEL_TAC "HT") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&7 / &8)` THENL
   [FIRST_X_ASSUM((fun th -> SUBST1_TAC(MP th (ASSUME
      `(z:real^2)$1 <= schy_sq e lam (&7 / &8)`))) o check (fun th ->
      can (term_match [] `(z:real^2)$1 <= schy_sq e lam (&7 / &8) ==> P`) (concl th))) THEN
    REWRITE_TAC[schy_sbox; VECTOR_3; schy_hf; schy_G] THEN
    SUBGOAL_THEN `schy_Hc e lam ((z:real^2)$1) = z$1 pow 2 /\ schy_bec e lam (z$1) = &0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `schy_sq e lam (&1) < (z:real^2)$1 /\ z$1 <= schy_sq e lam (&33 / &64) ==> P`)
      (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "HT" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `schy_ma c' e lam (schy_bec e lam) (z:real^2) IN sch5v_slab H`)]) THEN
    REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[schy_hf] THEN
    SUBGOAL_THEN `schy_Hc e lam ((z:real^2)$1) = z$1 pow 2` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `schy_sq e lam (&17 / &32) <= (z:real^2)$1 ==> P`) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "HT" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `schy_mb c' e (schy_Ac e lam) (z:real^2) IN sch5v_slab H`)]) THEN
  REWRITE_TAC[schy_mb; VECTOR_3; schy_hf; schy_G] THEN
  SUBGOAL_THEN `schy_Hc e lam ((z:real^2)$1) = e - lam / &2 - lam * schy_Ac e lam (z$1) pow 2 /\
                schy_bec e lam (z$1) = &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SCHY_Q_OPEN = prove
 (`!e lam wq. open(schy_Q e lam wq)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `schy_Q e lam wq =
                {z:real^2 | schy_tL e lam - lam / &16 < z$1} INTER
                {z:real^2 | z$1 < schy_ta e lam + &1 / &16} INTER
                {z:real^2 | z$2 < wq} INTER {z:real^2 | --wq < z$2}` SUBST1_TAC THENL
   [REWRITE_TAC[schy_Q; EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT; GSYM real_gt]);;

let SCHY_CTX_BASIC = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta'.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta'
     ==> &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < e /\ &2 * lam < e /\ lam <= &1 /\
         &5 <= H /\ &0 < rho0 /\ &0 <= B /\ B * lam * H < rho0 / &2 /\ &0 < r /\ r < &1 /\
         &16 * e < r pow 2 /\ &0 <= B * lam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_ctx] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_chart]) THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th -> can (term_match []
      `!y. norm((v:real^3->real^3) y) <= B`) (concl th))) THEN
    MP_TAC(ISPEC `(v:real^3->real^3)(vec 0)` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < &1 * &1 ==> x < &1`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let SCHY_GM_SMOOTH = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam
     ==> smooth_map_on (schy_Q e lam wq) (schy_gm Theta c' e lam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCHY_CD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `ts:real`] SCHY_B0_SMOOTH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `Q = schy_Q e lam wq` THEN
  SUBGOAL_THEN `open(Q:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[SCHY_Q_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN Q ==> abs(&2 * z$1 * z$2) < ts` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Q (\z:real^2. lift(schy_B0 c' e z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^2 | abs(&2 * z$1 * z$2) < ts}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN Q
                ==> (z$1 <= schy_sq e lam (&7 / &8) ==> schy_gm Theta c' e lam z = schy_sbox z) /\
                    (schy_sq e lam (&1) < z$1 /\ z$1 <= schy_sq e lam (&33 / &64)
                     ==> schy_ma c' e lam (schy_bec e lam) z IN sch5v_slab H /\
                         &1 / &128 <= sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) z)) -
                                      schy_B0 c' e z pow 2 /\
                         schy_gm Theta c' e lam z = Theta(schy_ma c' e lam (schy_bec e lam) z)) /\
                    (schy_sq e lam (&17 / &32) <= z$1
                     ==> schy_mb c' e (schy_Ac e lam) z IN sch5v_slab H /\
                         schy_gm Theta c' e lam z = Theta(schy_mb c' e (schy_Ac e lam) z))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                   `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z:real^2. lift(schy_bec e lam (z$1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_SM_COORD THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC SCH3_SMOOTH_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(z:real^2)$1 < schy_sq e lam (&7 / &8)` THENL
   [EXISTS_TAC `Q INTER {z:real^2 | z$1 < schy_sq e lam (&7 / &8)}` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT; IN_INTER; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `schy_sbox` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "PC" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN Q`))) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `schy_sbox = (\z:real^2. vector[--(z$1); z$2; z$1 pow 2 - z$2 pow 2]:real^3)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_sbox]; ALL_TAC] THEN
      SUBGOAL_THEN `open(Q INTER {z:real^2 | z$1 < schy_sq e lam (&7 / &8)})` MP_TAC THENL
       [ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
      DISCH_TAC THEN SCH3_SMOOTH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (sch5v_slab H) (Theta:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 < schy_sq e lam (&33 / &64)` THENL
   [ABBREV_TAC `U = Q INTER {z:real^2 | schy_sq e lam (&1) < z$1} INTER
                    {z:real^2 | z$1 < schy_sq e lam (&33 / &64)}` THEN
    SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT;
                   GSYM real_gt];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^2. x IN U <=> x IN Q /\ schy_sq e lam (&1) < x$1 /\
                                       x$1 < schy_sq e lam (&33 / &64)` (LABEL_TAC "UD") THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(Theta:real^3->real^3) o schy_ma c' e lam (schy_bec e lam)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "PC" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN Q`))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^2. x IN U
                  ==> schy_ma c' e lam (schy_bec e lam) x IN sch5v_slab H /\
                      &0 < sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) x)) -
                           schy_B0 c' e x pow 2` ASSUME_TAC THENL
     [X_GEN_TAC `x:real^2` THEN USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      USE_THEN "PC" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN Q`))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch5v_slab H` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on U (\x:real^2. lift(schy_B0 c' e x)) /\
                  smooth_map_on U (\x:real^2. lift(schy_bec e lam (x$1)))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `Q:real^2->bool`; EXISTS_TAC `(:real^2)`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN USE_THEN "UD" (fun th -> REWRITE_TAC[SUBSET; th]) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on U (\x:real^2. lift(schy_Ya c' e lam (schy_bec e lam) x))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `!x:real^2. x IN U ==> ~(lam = &0)` ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[schy_Ya; schy_G] THEN SCH3_SMOOTH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on U
                    (\x:real^2. lift(sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) x))))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\x:real^2. lift(sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) x)))) =
                    (lift o sch_cap_profile o drop) o
                    (\x. lift(--(schy_Ya c' e lam (schy_bec e lam) x)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH_CAP_PROFILE_SMOOTH] THEN SCH3_SMOOTH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `schy_ma c' e lam (schy_bec e lam) =
                  (\x:real^2. vector[--(sqrt(sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) x)) -
                                             schy_B0 c' e x pow 2));
                                     schy_B0 c' e x; schy_Ya c' e lam (schy_bec e lam) x]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_ma]; ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^2. x IN U
                  ==> &0 < sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) x)) -
                           schy_B0 c' e x pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SCH3_SMOOTH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = Q INTER {z:real^2 | schy_sq e lam (&17 / &32) < z$1}` THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; GSYM real_gt];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN U <=> x IN Q /\ schy_sq e lam (&17 / &32) < x$1`
  (LABEL_TAC "UD") THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(Theta:real^3->real^3) o schy_mb c' e (schy_Ac e lam)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "PC" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN Q`))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch5v_slab H` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
    USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    USE_THEN "PC" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN Q`))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\x:real^2. lift(schy_B0 c' e x)) /\
                smooth_map_on U (\x:real^2. lift(schy_Ac e lam (x$1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Q:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "UD" (fun th -> REWRITE_TAC[SUBSET; th]) THEN SIMP_TAC[];
      SUBGOAL_THEN `(\x:real^2. lift(schy_Ac e lam (x$1))) =
                    (lift o schy_Ac e lam o drop) o (\x. lift(x$1))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{t:real^1 | &0 < drop t}` THEN ASM_REWRITE_TAC[SCHY_OPEN_HALFLINES] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; LIFT_DROP] THEN
      USE_THEN "UD" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_mb c' e (schy_Ac e lam) =
                (\x:real^2. vector[schy_Ac e lam (x$1); schy_B0 c' e x;
                                   --(&1 / &2) - schy_Ac e lam (x$1) pow 2 -
                                   schy_B0 c' e x pow 2]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_mb]; ALL_TAC] THEN
  SCH3_SMOOTH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The strip lies on S1.  Model points on the cap profile with               *)
(* -5/4 < y3 <= -1/2 lie on S1 (cap1, or the lower cylinder which is in E1); *)
(* the box part below the junction lies in E1 by SCHY_SLAB_CONN.             *)
(* ------------------------------------------------------------------------- *)

let SCHY_PROFILE_S1 = prove
 (`!S S1 S2 (Theta:real^3->real^3) y.
     sch_slab_config S S1 S2 Theta /\
     y$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3)) /\
     --(&5 / &4) < y$3 /\ y$3 <= --(&1 / &2)
     ==> Theta y IN S1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sch_slab_config] o check (fun th ->
    can (term_match [] `sch_slab_config S S1 S2 Theta`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `TN:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[IN_UNION] THEN
  ASM_CASES_TAC `-- &1 <= (y:real^3)$3` THENL
   [DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[sch_cap1; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    DISJ1_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `sch_slab_nbhd SUBSET n`) (concl th))) THEN
    REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN
    MP_TAC(SPEC `--((y:real^3)$3)` SCHY_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> can (term_match []
    `!y. y IN (N:real^3->bool) ==> ((Theta:real^3->real^3) y IN E1 <=> P y) /\ Q y`)
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC);;

let SCHY_JUNCTION = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq z.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\ z IN schy_Q e lam wq /\
     sqrt(e - &17 / &16 * lam) <= z$1 /\ z$1 <= schy_sq e lam (&7 / &8)
     ==> Theta(schy_ma c' e lam (schy_bec e lam) z) = schy_sbox z /\
         (schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
         (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 = &1 /\
         --(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3 /\
         (schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&7 / &8) /\
         (schy_ma c' e lam (schy_bec e lam) z)$3 = ((z$1) pow 2 - z$2 pow 2 - e) / lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tau = --(&2 * (z:real^2)$1 * z$2)` THEN
  SUBGOAL_THEN `abs tau < wq` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[REAL_ABS_NEG]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
    `!tau. abs tau < ts ==> schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\ P tau`)
    (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(e - &17 / &16 * lam) /\
                sqrt(e - &17 / &16 * lam) pow 2 = e - &17 / &16 * lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&7 / &8) pow 2 = e - &7 / &8 * lam` ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e - &17 / &16 * lam <= (z:real^2)$1 pow 2 /\ z$1 pow 2 <= e - &7 / &8 * lam`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `sqrt(e - &17 / &16 * lam) pow 2 = e - &17 / &16 * lam`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `schy_sq e lam (&7 / &8) pow 2 = e - &7 / &8 * lam`))] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$2 pow 2 <= lam / &100` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wq pow 2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_bec e lam ((z:real^2)$1) = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `schy_Ya c' e lam (schy_bec e lam) (z:real^2) = (z$1 pow 2 - z$2 pow 2 - e) / lam`
  ASSUME_TAC THENL
   [REWRITE_TAC[schy_Ya; schy_G] THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&5 / &4) < ((z:real^2)$1 pow 2 - z$2 pow 2 - e) / lam /\
                (z$1 pow 2 - z$2 pow 2 - e) / lam <= --(&7 / &8)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile(--(((z:real^2)$1 pow 2 - z$2 pow 2 - e) / lam)) = &1`
  ASSUME_TAC THENL [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCHY_BOX_MA THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->real^3`; `B:real`; `rho0:real`; `c:real^2->real^2`;
                          `delta1:real`; `H:real`; `Theta':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < lam ==> abs lam = lam`; REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `&5 * lam <= H * lam` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    SUBGOAL_THEN `sqrt(&1 - schy_B0 c' e (z:real^2) pow 2) pow 2 = &1 - schy_B0 c' e z pow 2`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[schy_B0] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= (&1 / &16) pow 2 ==> &0 <= &1 - x`) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[schy_ma; VECTOR_3] THEN ASM_REWRITE_TAC[]]);;

let SCHY_Q_CONVEX = prove
 (`!e lam wq. convex(schy_Q e lam wq)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `schy_Q e lam wq =
                {z:real^2 | z$1 > schy_tL e lam - lam / &16} INTER
                {z:real^2 | z$1 < schy_ta e lam + &1 / &16} INTER
                {z:real^2 | z$2 < wq} INTER {z:real^2 | z$2 > --wq}` SUBST1_TAC THENL
   [REWRITE_TAC[schy_Q; EXTENSION; IN_INTER; IN_ELIM_THM; real_gt] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GT]);;

let SCHY_SBOX_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s schy_sbox`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schy_sbox = (\z:real^2. vector[--(z$1); z$2; z$1 pow 2 - z$2 pow 2]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_sbox]; ALL_TAC] THEN
  SCH3_SMOOTH_TAC);;

(* A lattice point of the chart never projects to the right half (x1 >= 0) *)
(* of the box near the saddle: its projection is within B lam of J.          *)

let SCHY_LAT_RIGHT = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' y.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\ y IN sch_lat /\
     &0 <= (sch5v_pr(Theta y))$1 /\
     (sch5v_pr(Theta y))$1 pow 2 + (sch5v_pr(Theta y))$2 pow 2 < &2 * e /\
     abs((sch5v_pr(Theta y))$2) + &2 * (B * lam + lam) < sqrt e
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  SUBGOAL_THEN `(c:real^2->real^2)(sch5v_pr y) IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o MATCH_MP SCHY_CTX_J) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `(y:real^3) IN sch_lat` THEN
    REWRITE_TAC[sch_lat; IN_ELIM_THM; IN_SPHERE_0; NORM_EQ_1; sch5v_pr; DOT_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  SUBGOAL_THEN `dist(sch5v_pr((Theta:real^3->real^3) y),(c:real^2->real^2)(sch5v_pr y)) <
                B * lam + lam` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                   `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `y:real^3`] SCHY_THETA_DISP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    SUBGOAL_THEN `B * lam * abs((y:real^3)$3) <= B * lam` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC(REAL_ARITH `a * t <= a * &1 ==> a * t <= a`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN sch_lat` THEN REWRITE_TAC[sch_lat; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * sqrt e < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(&4 * sqrt e) < abs r` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_SQUARE_ABS; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `x = sch5v_pr((Theta:real^3->real^3) y)` THEN
  SUBGOAL_THEN `norm(x:real^2) < &2 * sqrt e` ASSUME_TAC THENL
   [REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[DOT_2; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_OUT_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `e:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `x:real^2`;
                 `(c:real^2->real^2)(sch5v_pr y)`; `B * lam + lam`] SCHY_NEAR_J) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCHY_GM_S1 = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq S1 S2.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\ closed S1 /\ closed S2 /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     wq + &2 * (B * lam + lam) < sqrt e
     ==> !z. z IN schy_Q e lam wq ==> schy_gm Theta c' e lam z IN S1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  SUBGOAL_THEN `!z. z IN schy_Q e lam wq
                    ==> (z$1 <= schy_sq e lam (&7 / &8) ==> schy_gm Theta c' e lam z = schy_sbox z) /\
                        (schy_sq e lam (&1) < z$1 /\ z$1 <= schy_sq e lam (&33 / &64)
                         ==> schy_gm Theta c' e lam z = Theta(schy_ma c' e lam (schy_bec e lam) z) /\
                             (schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
                             (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 =
                             sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) z)$3)) /\
                             --(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3 /\
                             (schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)) /\
                        (schy_sq e lam (&17 / &32) <= z$1
                         ==> schy_gm Theta c' e lam z = Theta(schy_mb c' e (schy_Ac e lam) z) /\
                             (schy_mb c' e (schy_Ac e lam) z)$1 pow 2 +
                             (schy_mb c' e (schy_Ac e lam) z)$2 pow 2 =
                             sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) z)$3)) /\
                             --(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3 /\
                             (schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                   `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `zb = sqrt(e - &17 / &16 * lam)` THEN
  SUBGOAL_THEN `&0 < zb /\ zb pow 2 = e - &17 / &16 * lam /\ zb < schy_sq e lam (&1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zb" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2;
      REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN schy_Q e lam wq /\ z$1 <= zb
                ==> z$1 pow 2 < e /\ z$2 pow 2 < lam / &50 /\ abs(z$2) < wq /\
                    --(sqrt e) < z$1` (LABEL_TAC "BX") THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `schy_tL e lam = --(sqrt(e - lam / &4))` ASSUME_TAC THENL
     [REWRITE_TAC[schy_tL; schy_sq] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(e - lam / &4) + lam / &16 <= sqrt e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN
      SUBGOAL_THEN `sqrt(e - lam / &4) pow 2 = e - lam / &4 /\ sqrt(e - lam / &4) < &1 / &4`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt e` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(s + l) pow 2 = s pow 2 + &2 * l * s + l pow 2`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * lam / &16 * sqrt(e - lam / &4) <= lam / &32 /\
                    (lam / &16) pow 2 <= lam / &256` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `(lam / &8) * s <= (lam / &8) * (&1 / &4)
                                   ==> &2 * lam / &16 * s <= lam / &32`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_POW_2] THEN
          MATCH_MP_TAC(REAL_ARITH `(lam / &16) * l <= (lam / &16) * (&1 / &16)
                                   ==> lam / &16 * l <= lam / &256`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2)$2 pow 2 <= wq pow 2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((z:real^2)$1) < sqrt e` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt e pow 2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 < r` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC(REAL_ARITH `r * r < r * &1 ==> r * r < r`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kb = IMAGE schy_sbox {z:real^2 | z IN schy_Q e lam wq /\ z$1 <= zb}` THEN
  SUBGOAL_THEN `vector[zb; &0]:real^2 IN schy_Q e lam wq` ASSUME_TAC THENL
   [REWRITE_TAC[schy_Q; IN_ELIM_THM; VECTOR_2; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kb:real^3->bool) SUBSET S1` (LABEL_TAC "KS1") THENL
   [MATCH_MP_TAC SCHY_SLAB_CONN THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `S2:real^3->bool`;
                          `Theta:real^3->real^3`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Kb" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SCHY_SBOX_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        SUBGOAL_THEN `{z:real^2 | z IN schy_Q e lam wq /\ z$1 <= zb} =
                      schy_Q e lam wq INTER {z:real^2 | z$1 <= zb}` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[SCHY_Q_CONVEX; CONVEX_HALFSPACE_COMPONENT_LE]];
      EXPAND_TAC "Kb" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      USE_THEN "BX" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `schy_chart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) r` THEN
      REWRITE_TAC[schy_chart] THEN
      DISCH_THEN(MP_TAC o SPEC `schy_sbox z` o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[schy_sbox; VECTOR_3] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
        MP_TAC(SPEC `(z:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_NEG; ARITH]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Kb" THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      USE_THEN "BX" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `((Theta:real^3->real^3) y)$3 = (z:real^2)$1 pow 2 - z$2 pow 2 /\
                    sch5v_pr((Theta:real^3->real^3) y) = vector[--((z:real^2)$1); z$2]`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
          concl th = `(Theta:real^3->real^3) y = schy_sbox z`)) THEN
        REWRITE_TAC[schy_sbox; sch5v_pr; VECTOR_3];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        concl th = `(Theta:real^3->real^3) y = schy_sbox z`)) THEN
      ASM_CASES_TAC `&0 <= (z:real^2)$1` THENL
       [SUBGOAL_THEN `((Theta:real^3->real^3) y)$3 = e + lam * (y:real^3)$3` MP_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [schy_cd] o
            check (fun th -> can (term_match []
              `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                       (Theta:real^3->real^3) Theta'`) (concl th))) THEN
          UNDISCH_TAC `(y:real^3) IN sch_lat` THEN
          REWRITE_TAC[sch_lat; sch5v_slab; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `(y:real^3) IN sch_lat` THEN REWRITE_TAC[sch_lat; IN_ELIM_THM] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `--lam <= lam * (y:real^3)$3` MP_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `lam * --(&1) <= lam * y ==> --lam <= lam * y`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(z:real^2)$1 pow 2 <= zb pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                       `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                       `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                       `Theta':real^3->real^3`; `y:real^3`] SCHY_LAT_RIGHT) THEN
        ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
        ASM_REWRITE_TAC[VECTOR_2; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                     `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                     `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `ts:real`; `wq:real`; `vector[zb; &0]:real^2`]
        SCHY_JUNCTION) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ABBREV_TAC `y0 = schy_ma c' e lam (schy_bec e lam) (vector[zb; &0]:real^2)` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)))) THEN
      REWRITE_TAC[VECTOR_2] THEN
      SUBGOAL_THEN `(zb pow 2 - &0 pow 2 - e) / lam = --(&17 / &16)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      DISCH_TAC THEN EXISTS_TAC `y0:real^3` THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kb" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_2; REAL_LE_REFL]]];
    ALL_TAC] THEN
  REMOVE_THEN "BX" (K ALL_TAC) THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  REMOVE_THEN "PC" (MP_TAC o C MP (ASSUME `(z:real^2) IN schy_Q e lam wq`) o SPEC `z:real^2`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "P2") (LABEL_TAC "P3"))) THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&7 / &8)` THENL
   [REMOVE_THEN "P1" (fun th ->
      REWRITE_TAC[MP th (ASSUME `(z:real^2)$1 <= schy_sq e lam (&7 / &8)`)]) THEN
    ASM_CASES_TAC `(z:real^2)$1 <= zb` THENL
     [REMOVE_THEN "KS1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      EXPAND_TAC "Kb" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                     `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                     `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_JUNCTION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
      MATCH_MP_TAC SCHY_PROFILE_S1 THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `S2:real^3->bool`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` THENL
     [REMOVE_THEN "P2" MP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];
      REMOVE_THEN "P3" MP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SCHY_PROFILE_S1 THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `S2:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The shear data.  Tf = beta(w) rho(t) is the vertical shift,               *)
(* sh = 8/7 rho + eps0 the half-height of the tube, Qc the compact support.  *)
(* Bounds on rho: at most e - t^2 + eps on the box part, 53/100 lam + eps    *)
(* beyond sq(1), and e + eps everywhere.                                     *)
(* ------------------------------------------------------------------------- *)

let SCHY_ETA_LE = prove
 (`!eps x. &0 < eps ==> schy_eta eps x <= abs x - x + eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schy_eta] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= abs x + eps ==> s - x <= abs x - x + eps`) THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs x * eps` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) pow 2 = a pow 2 + &2 * a * b + b pow 2`; REAL_POW2_ABS] THEN
  REAL_ARITH_TAC);;

let SCHY_RHO_BOUND = prove
 (`!e lam eps t. &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < eps
   ==> (abs t <= sqrt e /\ t <= schy_sq e lam (&1)
        ==> schy_rho e lam eps t <= e - t pow 2 + eps) /\
       (schy_sq e lam (&1) <= t ==> schy_rho e lam eps t <= &53 / &100 * lam + eps) /\
       schy_rho e lam eps t <= e + eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `schy_rho e lam eps t <= abs(schy_xi e lam t) - schy_xi e lam t + eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `schy_eta eps (schy_xi e lam t)` THEN
    ASM_SIMP_TAC[SCHY_ETA_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam / &16 * schy_ta e lam <= lam / &64` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(lam / &16) * a <= (lam / &16) * (&1 / &4)
                             ==> (lam / &16) * a <= lam / &64`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&1) pow 2 = e - lam` ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq; REAL_MUL_LID] THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t <= sqrt e /\ t <= schy_sq e lam (&1)
                ==> schy_rho e lam eps t <= e - t pow 2 + eps` (LABEL_TAC "C1") THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `schy_Hc e lam t = t pow 2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t <= schy_sq e lam (&65 / &128) ==> schy_Hc e lam t = t pow 2`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(lam / &16 * t) <= lam / &64` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(lam / &16) = lam / &16` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `(lam / &16) * a <= (lam / &16) * (&1 / &4)
                               ==> (lam / &16) * a <= lam / &64`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t pow 2 <= e` ASSUME_TAC THENL
     [SUBGOAL_THEN `abs t pow 2 <= sqrt e pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        ASM_REWRITE_TAC[REAL_POW2_ABS]];
      ALL_TAC] THEN
    UNDISCH_TAC `schy_rho e lam eps t <= abs(schy_xi e lam t) - schy_xi e lam t + eps` THEN
    ASM_REWRITE_TAC[schy_xi; schy_lA] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&1) <= t ==> schy_rho e lam eps t <= &53 / &100 * lam + eps`
  (LABEL_TAC "C2") THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `schy_ta e lam + &1 / &32 <= t` THENL
     [SUBGOAL_THEN `schy_rho e lam eps t = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!t. t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t
               ==> schy_rho e lam eps t = &0`) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `e - lam <= schy_Hc e lam t` ASSUME_TAC THENL
     [ASM_CASES_TAC `t <= schy_sq e lam (&65 / &128)` THENL
       [SUBGOAL_THEN `schy_Hc e lam t = t pow 2` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!t. t <= schy_sq e lam (&65 / &128) ==> schy_Hc e lam t = t pow 2`) (concl th))) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `schy_sq e lam (&1) pow 2 = e - lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `schy_Hc e lam t = e - lam / &2 - lam * schy_Ac e lam t pow 2`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!t. &0 < t ==> schy_Hc e lam t = e - lam / &2 - lam * schy_Ac e lam t pow 2`)
            (concl th))) THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        MP_TAC(SPECL [`e:real`; `lam:real`; `t:real`] SCHY_AC_BOUND) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
        SUBGOAL_THEN `schy_Ac e lam t pow 2 <= (&1 / &4) pow 2` ASSUME_TAC THENL
         [SUBGOAL_THEN `abs(schy_Ac e lam t) pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
            REWRITE_TAC[REAL_POW2_ABS]];
          ALL_TAC] THEN
        SUBGOAL_THEN `lam * schy_Ac e lam t pow 2 <= lam * (&1 / &4) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lam / &16 * t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `schy_rho e lam eps t <= abs(schy_xi e lam t) - schy_xi e lam t + eps` THEN
    REWRITE_TAC[schy_xi; schy_lA] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "C1" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "C2" ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t <= schy_tL e lam` THENL
   [SUBGOAL_THEN `schy_rho e lam eps t = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t <= schy_tL e lam \/ schy_ta e lam + &1 / &32 <= t
             ==> schy_rho e lam eps t = &0`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(sqrt e) < schy_tL e lam` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(schy_tL e lam) < abs(sqrt e)` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= schy_sq e lam (&1)` THENL
   [REMOVE_THEN "C1" MP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    REMOVE_THEN "C2" MP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let schy_Tf = new_definition
 `schy_Tf e lam eps wb (z:real^2) = schy_bw wb (z$2) * schy_rho e lam eps (z$1)`;;

let schy_sh = new_definition
 `schy_sh e lam eps eps0 (z:real^2) = &8 / &7 * schy_rho e lam eps (z$1) + eps0`;;

let schy_Qc = new_definition
 `schy_Qc e lam wb = {z:real^2 | schy_tL e lam <= z$1 /\ z$1 <= schy_ta e lam + &1 / &32 /\
                                 abs(z$2) <= wb}`;;

let SCHY_TF_FACTS = prove
 (`!e lam eps eps0 wb wq.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < eps /\ &0 < eps0 /\
     &0 < wb /\ wb < wq
     ==> (!s. open s ==> smooth_map_on s (\z. lift(schy_Tf e lam eps wb z)) /\
                         smooth_map_on s (\z. lift(schy_sh e lam eps eps0 z))) /\
         (!z. &0 < schy_sh e lam eps eps0 z /\
              &0 <= schy_Tf e lam eps wb z /\
              schy_Tf e lam eps wb z <= schy_rho e lam eps (z$1) /\
              &8 * abs(schy_Tf e lam eps wb z) <= &7 * schy_sh e lam eps eps0 z) /\
         (!z. ~(z IN schy_Qc e lam wb) ==> schy_Tf e lam eps wb z = &0) /\
         compact(schy_Qc e lam wb) /\ schy_Qc e lam wb SUBSET schy_Q e lam wq /\
         vec 0 IN schy_Qc e lam wb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `wb:real` SCHY_BW_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_map_on s (\z:real^2. lift(schy_bw wb (z$2))) /\
                  smooth_map_on s (\z:real^2. lift(schy_rho e lam eps (z$1)))` STRIP_ASSUME_TAC
    THENL [CONJ_TAC THEN MATCH_MP_TAC SCHY_SM_COORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[schy_Tf; schy_sh] THEN CONJ_TAC THEN SCH3_SMOOTH_TAC;
    GEN_TAC THEN REWRITE_TAC[schy_Tf; schy_sh] THEN
    SUBGOAL_THEN `&0 <= schy_bw wb ((z:real^2)$2) * schy_rho e lam eps (z$1) /\
                  schy_bw wb (z$2) * schy_rho e lam eps (z$1) <= schy_rho e lam eps (z$1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `a * r <= &1 * r ==> a * r <= r`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(z:real^2)$1` o check (fun th -> can (term_match []
      `!t. &0 <= schy_rho e lam eps t`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[schy_Qc; IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LE] THEN
    REWRITE_TAC[schy_Tf] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `schy_rho e lam eps ((z:real^2)$1) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      SUBGOAL_THEN `schy_rho e lam eps ((z:real^2)$1) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      SUBGOAL_THEN `schy_bw wb ((z:real^2)$2) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    SUBGOAL_THEN `schy_Qc e lam wb =
                  interval[vector[schy_tL e lam; --wb],vector[schy_ta e lam + &1 / &32; wb]]`
    SUBST1_TAC THENL
     [REWRITE_TAC[schy_Qc; EXTENSION; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_2; FORALL_2;
                  VECTOR_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[COMPACT_INTERVAL]];
    REWRITE_TAC[schy_Qc; schy_Q; SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schy_Qc; IN_ELIM_THM; VEC_COMPONENT; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The field X of the shear and the column lemma on the box                  *)
(* part of the strip (t <= sq(1)): there X = e3 on the vertical column (kin  *)
(* vanishes by SCHY_KIN_ZERO) and the dome misses the column.                *)
(* ------------------------------------------------------------------------- *)

let SCHY_FIELD = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' s1 rho1 rho2.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2
     ==> smooth_map_on (:real^3) (schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))) /\
         (!x. (schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) x)$3 = &1) /\
         (!x. norm(schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) x) <= B + &2) /\
         (!y. ode_vf_maxint (schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)))
                (:real^3) y = (:real^1)) /\
         smooth_map_on (:real^3) (\x. lift(schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x)) /\
         (!x. &0 <= schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x /\
              schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x <= &1) /\
         (!y. y IN sch5v_slab H
              ==> schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) (Theta y) =
                  schy_kmod s1 H y * (&1 - smooth_bump rho1 rho2 (Theta y - schy_lpt e))) /\
         (!x. schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x = &0
              ==> schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) x = basis 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
    can (term_match [] `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                               (Theta:real^3->real^3) Theta'`) (concl th))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] `!y:real^3. (Theta:real^3->real^3) y =
           ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))`)
        (concl th))) THEN
  MP_TAC(ISPECL [`Theta:real^3->real^3`; `Theta':real^3->real^3`; `H:real`; `s1:real`;
                 `rho1:real`; `rho2:real`; `schy_lpt e`] SCHY_KIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)`;
                 `B:real`] SCHY_X_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[schy_X; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let SCHY_SLAB_S1_SUB = prove
 (`!S S1 S2 (Theta:real^3->real^3).
     sch_slab_config S S1 S2 Theta ==> S1 SUBSET S UNION IMAGE Theta sch_cap1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `TN:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let SCHY_SBOX_VERT = prove
 (`!(z:real^2) t.
     sch5v_pr(schy_sbox z + t % basis 3) = vector[--(z$1); z$2] /\
     (schy_sbox z + t % basis 3)$1 = --(z$1) /\ (schy_sbox z + t % basis 3)$2 = z$2 /\
     (schy_sbox z + t % basis 3)$3 = z$1 pow 2 - z$2 pow 2 + t /\
     sch5v_pr(schy_sbox z) = vector[--(z$1); z$2]`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[sch5v_pr; schy_sbox; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH; VECTOR_3] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

(* Facts on a box point of the strip below sq(1). *)

let SCHY_BOXPT = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' wq z.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\ z IN schy_Q e lam wq /\ z$1 <= schy_sq e lam (&1)
     ==> z$1 pow 2 < e /\ z$2 pow 2 < lam / &50 /\ abs(z$2) < wq /\ abs(z$1) < sqrt e /\
         schy_sbox z IN IMAGE g (sphere(vec 0,&1)) /\
         norm(vector[--(z$1); z$2]:real^2) < &2 * sqrt e /\
         &0 < sqrt e /\ sqrt e pow 2 = e /\ sqrt e < &1 / &4 /\ &4 * sqrt e < r /\
         r pow 2 < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CHI_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_tL e lam = --(sqrt(e - lam / &4))` ASSUME_TAC THENL
   [REWRITE_TAC[schy_tL; schy_sq] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(e - lam / &4) + lam / &16 <= sqrt e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    SUBGOAL_THEN `sqrt(e - lam / &4) pow 2 = e - lam / &4 /\ sqrt(e - lam / &4) < &1 / &4`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt e` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(s + l) pow 2 = s pow 2 + &2 * l * s + l pow 2`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * lam / &16 * sqrt(e - lam / &4) <= lam / &32 /\
                  (lam / &16) pow 2 <= lam / &256` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `(lam / &8) * s <= (lam / &8) * (&1 / &4)
                                 ==> &2 * lam / &16 * s <= lam / &32`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `(lam / &16) * l <= (lam / &16) * (&1 / &16)
                                 ==> lam / &16 * l <= lam / &256`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$2 pow 2 <= wq pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((z:real^2)$1) < sqrt e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 pow 2 < e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt e pow 2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$2 pow 2 < lam / &50` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 < r` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC(REAL_ARITH `r * r < r * &1 ==> r * r < r`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * sqrt e < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(&4 * sqrt e) < abs r` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_SQUARE_ABS; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `schy_ctx g r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
                         (Theta:real^3->real^3) Theta'` THEN
    REWRITE_TAC[schy_ctx; schy_chart] THEN
    DISCH_THEN(MP_TAC o SPEC `schy_sbox z` o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    REWRITE_TAC[schy_sbox; VECTOR_3] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
      MP_TAC(SPEC `(z:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_NEG; ARITH]];
    REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[DOT_2; VECTOR_2; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* The shear field is vertical on the box columns of the strip (t <= sq(1)). *)

let SCHY_BOX_KIN0 = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' s1 ds rho1 rho2 wq eps eps0 z t'.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\
     &0 < eps /\ eps <= e /\ &0 < eps0 /\ eps0 <= e /\
     &8 * (wq + B * lam * H + ds + eps + eps0 + lam) <= rho1 /\
     wq + &2 * (B * lam * H + ds) < sqrt e /\
     z IN schy_Q e lam wq /\ z$1 <= schy_sq e lam (&1) /\
     abs t' <= &2 * schy_sh e lam eps eps0 z
     ==> schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) (schy_sbox z + t' % basis 3) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  SUBGOAL_THEN `&0 <= B * lam * H` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `wq:real`; `z:real^2`] SCHY_BOXPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `(z:real^2)$1`] SCHY_RHO_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`abs((z:real^2)$1) < sqrt e`; `(z:real^2)$1 <= schy_sq e lam (&1)`] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  SUBGOAL_THEN `vector[--((z:real^2)$1); z$2]:real^2 IN
                outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_BOXPR_OUT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `e:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[VECTOR_2] THEN
    MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `ds:real`; `rho1:real`; `rho2:real`;
                 `schy_sbox z + t' % basis 3`] SCHY_KIN_ZERO) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[SCHY_SBOX_VERT] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`norm(vector[--((z:real^2)$1); z$2]:real^2) < &2 * sqrt e`; `&4 * sqrt e < r`;
      `wq + &2 * (B * lam * H + ds) < sqrt e`; `&0 < wq`; `&0 < sqrt e`] THEN
    REAL_ARITH_TAC;
    MAP_EVERY (MP_TAC o ASSUME)
     [`abs((z:real^2)$2) < wq`; `wq + &2 * (B * lam * H + ds) < sqrt e`;
      `&0 <= B * lam * H`; `&0 < ds`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(((schy_sbox z + t' % basis 3) - schy_lpt e)$1) +
              abs(((schy_sbox z + t' % basis 3) - schy_lpt e)$2) +
              abs(((schy_sbox z + t' % basis 3) - schy_lpt e)$3)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `(schy_sbox z + t' % basis 3) - schy_lpt e` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; SCHY_SBOX_VERT; schy_lpt; VECTOR_3; REAL_SUB_RZERO;
              REAL_ARITH `--a - --b = --a + b`] THEN
  SUBGOAL_THEN `e - (z:real^2)$1 pow 2 <= (abs(z$2) + &2 * (B * lam * H + ds)) * (&1 / &2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `e - (z:real^2)$1 pow 2 = (sqrt e - z$1) * (sqrt e + z$1)` SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt e pow 2 = e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`abs(--((z:real^2)$1) + sqrt e) <= abs(z$2) + &2 * (B * lam * H + ds)`;
      `abs((z:real^2)$1) < sqrt e`; `sqrt e < &1 / &4`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t' <= &16 / &7 * (e - (z:real^2)$1 pow 2 + eps) + &2 * eps0`
  ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`abs t' <= &2 * schy_sh e lam eps eps0 z`;
      `schy_rho e lam eps ((z:real^2)$1) <= e - z$1 pow 2 + eps`] THEN
    REWRITE_TAC[schy_sh] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(((z:real^2)$1 pow 2 - z$2 pow 2 + t') - e) <=
                (e - z$1 pow 2) + z$2 pow 2 + abs t'` ASSUME_TAC THENL
   [MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
    MP_TAC(ASSUME `(z:real^2)$1 pow 2 < e`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t' <= &8 / &7 * (abs((z:real^2)$2) + &2 * (B * lam * H + ds)) +
                          &16 / &7 * eps + &2 * eps0` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`abs t' <= &16 / &7 * (e - (z:real^2)$1 pow 2 + eps) + &2 * eps0`;
      `e - (z:real^2)$1 pow 2 <= (abs(z$2) + &2 * (B * lam * H + ds)) * (&1 / &2)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a1 a2 a3 u q T w D eps eps0 wq lam rho1.
      a1 <= w + &2 * D /\ a3 <= u + q + T /\ u <= (w + &2 * D) * (&1 / &2) /\
      T <= &8 / &7 * (w + &2 * D) + &16 / &7 * eps + &2 * eps0 /\
      q < lam / &50 /\ w < wq /\ &8 * (wq + D + eps + eps0 + lam) <= rho1 /\
      &0 <= w /\ &0 <= D /\ &0 < eps /\ &0 < eps0 /\ &0 < lam /\ a2 = w
      ==> a1 + a2 + a3 <= rho1`) THEN
  MAP_EVERY EXISTS_TAC [`e - (z:real^2)$1 pow 2`; `(z:real^2)$2 pow 2`; `abs t'`;
                        `abs((z:real^2)$2)`; `B * lam * H + ds`; `eps:real`; `eps0:real`;
                        `wq:real`; `lam:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [`&8 * (wq + B * lam * H + ds + eps + eps0 + lam) <= rho1`; `&0 <= B * lam * H`;
    `&0 < ds`] THEN
  REAL_ARITH_TAC);;

(* The column lemma on the box part of the strip. *)

let SCHY_GM_BOXCOL = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' S1 S2 s1 ds rho1 rho2 ts wq eps eps0.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\
     &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     &0 < eps /\ eps <= e /\ &0 < eps0 /\ eps0 <= e /\
     &8 * (wq + B * lam * H + ds + eps + eps0 + lam) <= rho1 /\
     &2 * wq + &3 * (B * lam + lam) < rho0 / &2 /\
     &2 * wq + &3 * (B * lam + lam) < sqrt e /\
     wq + &2 * (B * lam * H + ds) < sqrt e
     ==> !z t. z IN schy_Q e lam wq /\ z$1 <= schy_sq e lam (&1) /\
               abs t <= &2 * schy_sh e lam eps eps0 z /\
               ode_vf_flow (schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))) (:real^3)
                 (lift t) (schy_gm Theta c' e lam z) IN S1
               ==> t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`] SCHY_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= B * lam * H` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kin = schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)` THEN
  ABBREV_TAC `X = schy_X v (kin:real^3->real)` THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `schy_gm Theta c' e lam z = schy_sbox z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                   `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `wq:real`; `z:real^2`] SCHY_BOXPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `(z:real^2)$1`] SCHY_RHO_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= schy_rho e lam eps ((z:real^2)$1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&1) pow 2 = e - lam` ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq; REAL_MUL_LID] THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  SUBGOAL_THEN `vector[--((z:real^2)$1); z$2]:real^2 IN
                outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_BOXPR_OUT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `e:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[VECTOR_2] THEN
    MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `S1:real^3->bool`;
                 `Theta:real^3->real^3`; `r:real`; `X:real^3->real^3`; `schy_sbox z`;
                 `&2 * schy_sh e lam eps eps0 z`] SCHY_BOX_COLUMN) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ode_vf_flow (X:real^3->real^3) (:real^3) (lift t)
                   (schy_gm (Theta:real^3->real^3) c' e lam z) IN S1` THEN
    ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHY_SLAB_S1_SUB THEN EXISTS_TAC `S2:real^3->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[schy_sbox; VECTOR_3; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schy_sbox; VECTOR_3; schy_sh] THEN
    MP_TAC(SPEC `(z:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schy_sh] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t':real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x. (kin:real^3->real) x = &0 ==> (X:real^3->real^3) x = basis 3`) (concl th))) THEN
    EXPAND_TAC "kin" THEN MATCH_MP_TAC SCHY_BOX_KIN0 THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`; `c:real^2->real^2`;
                          `c':real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`;
                          `delta1:real`; `lam:real`; `ds:real`; `wq:real`; `eps:real`;
                          `eps0:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                   `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `schy_sbox z`] SCHY_DOME_AVOID) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
    REWRITE_TAC[SCHY_SBOX_VERT] THEN REWRITE_TAC[schy_sbox; VECTOR_3; REAL_POW_NEG; ARITH] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY (MP_TAC o ASSUME)
       [`norm(vector[--((z:real^2)$1); z$2]:real^2) < &2 * sqrt e`; `&4 * sqrt e < r`;
        `&2 * wq + &3 * (B * lam + lam) < sqrt e`; `&0 < wq`; `&0 < sqrt e`] THEN
      REAL_ARITH_TAC;
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs((z:real^2)$2) < wq`; `&2 * wq + &3 * (B * lam + lam) < rho0 / &2`] THEN
      REAL_ARITH_TAC;
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs((z:real^2)$2) < wq`; `&2 * wq + &3 * (B * lam + lam) < sqrt e`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `&0 <= (z:real^2)$1` THENL
     [SUBGOAL_THEN `(z:real^2)$1 pow 2 <= schy_sq e lam (&1) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
      MP_TAC(ASSUME `schy_sq e lam (&1) pow 2 = e - lam`) THEN REAL_ARITH_TAC;
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs(--((z:real^2)$1) + sqrt e) <= abs(z$2) + &2 * (B * lam + lam)`;
        `~(&0 <= (z:real^2)$1)`; `abs((z:real^2)$2) < wq`;
        `&2 * wq + &3 * (B * lam + lam) < sqrt e`; `&0 <= B * lam`; `&0 < lam`;
        `&0 < wq`] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The column lemma on the model part of the strip (t > sq(1))               *)
(* by SCHY_CHART_COLUMN: the strip point is Theta(m) with m on the model     *)
(* surface F = 0, strict either on the dome (y3 > -7/8) or near lpt; the    *)
(* column stays in the chart (SCHY_IMAGE_NBHD) at model heights below 1, so *)
(* its points on S1 have F = 0 (SCHY_S1_IN_CHART).                          *)
(* ------------------------------------------------------------------------- *)

let SCHY_GM_MODEL = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq rho2 z.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     (!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2) /\
     B * lam * H < rho2 / &2 /\
     z IN schy_Q e lam wq /\ schy_sq e lam (&1) < z$1
     ==> ?m. m IN sch5v_slab H /\ schy_gm Theta c' e lam z = Theta m /\ schy_F m = &0 /\
             --(&5 / &4) < m$3 /\ m$3 <= --(&1 / &2) /\ norm(sch5v_pr m) <= &1 /\
             (--(m$3) < &7 / &8 \/ dist(schy_gm Theta c' e lam z,schy_lpt e) < rho2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "P2")
    (CONJUNCTS_THEN2 (LABEL_TAC "P3") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `!m:real^3. m$1 pow 2 + m$2 pow 2 = sch_cap_profile(--(m$3))
                           ==> schy_F m = &0 /\ norm(sch5v_pr m) <= &1` (LABEL_TAC "FM") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(m:real^3)$1 pow 2 + m$2 pow 2 = sch_cap_profile(--(m$3))` THEN
      REWRITE_TAC[schy_F] THEN REAL_ARITH_TAC;
      REWRITE_TAC[vector_norm; sch5v_pr; DOT_2; VECTOR_2] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
      MP_TAC(SPEC `--((m:real^3)$3)` SCHY_PROFILE_LE1) THEN
      UNDISCH_TAC `(m:real^3)$1 pow 2 + m$2 pow 2 = sch_cap_profile(--(m$3))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` THENL
   [USE_THEN "P2" (MP_TAC o C MP (CONJ (ASSUME `schy_sq e lam (&1) < (z:real^2)$1`)
                                      (ASSUME `(z:real^2)$1 <= schy_sq e lam (&33 / &64)`))) THEN
    STRIP_TAC THEN
    EXISTS_TAC `schy_ma c' e lam (schy_bec e lam) z` THEN
    USE_THEN "FM" (MP_TAC o SPEC `schy_ma c' e lam (schy_bec e lam) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `--((schy_ma c' e lam (schy_bec e lam) z)$3) < &7 / &8` THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `tau = --(&2 * (z:real^2)$1 * z$2)` THEN
    SUBGOAL_THEN `abs tau < wq` ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[REAL_ABS_NEG]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
      `!tau. abs tau < ts ==> schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\ P tau`)
      (concl th))) THEN
    ANTS_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`abs tau < wq`; `wq <= ts`] THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MP_TAC(MP (SPEC `tau:real` (ASSUME
      `!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2`))
      (ASSUME `abs tau < wq`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `sch5v_pr(schy_ma c' e lam (schy_bec e lam) z) =
                  (c':real^2->real^2)(schy_gam e tau)` ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_pr; schy_ma; VECTOR_3; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      SUBGOAL_THEN `sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) z)) = &1`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN
        UNDISCH_TAC `~(--((schy_ma c' e lam (schy_bec e lam) z)$3) < &7 / &8)` THEN
        REWRITE_TAC[schy_ma; VECTOR_3] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[schy_B0] THEN ASM_REWRITE_TAC[schy_bz] THEN
      ABBREV_TAC `q = (c':real^2->real^2)(schy_gam e tau)` THEN
      UNDISCH_TAC `(q:real^2) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_2] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&1 - (q:real^2)$2 pow 2 = q$1 pow 2` SUBST1_TAC THENL
       [UNDISCH_TAC `(q:real^2)$1 * q$1 + q$2 * q$2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[POW_2_SQRT_ABS] THEN
      UNDISCH_TAC `(q:real^2)$1 < &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                   `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `schy_ma c' e lam (schy_bec e lam) z`]
      SCHY_THETA_DISP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `B * lam * abs((schy_ma c' e lam (schy_bec e lam) z)$3) <= B * lam * H`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&0 <= B * lam`; `--(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3`;
        `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)`; `&5 <= H`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(Theta(schy_ma c' e lam (schy_bec e lam) z),sch5v_at e (schy_gam e tau)) +
                dist(sch5v_at e (schy_gam e tau),schy_lpt e)` THEN
    REWRITE_TAC[DIST_TRIANGLE] THEN REWRITE_TAC[SCHY_LPT_AT; SCHY_AT_DIST] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`dist(Theta(schy_ma c' e lam (schy_bec e lam) z),sch5v_at e (schy_gam e tau)) <=
       B * lam * abs((schy_ma c' e lam (schy_bec e lam) z)$3)`;
      `B * lam * abs((schy_ma c' e lam (schy_bec e lam) z)$3) <= B * lam * H`;
      `B * lam * H < rho2 / &2`;
      `dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2`] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `schy_sq e lam (&17 / &32) <= (z:real^2)$1` ASSUME_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME)
       [`~((z:real^2)$1 <= schy_sq e lam (&33 / &64))`;
        `schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "P3" (MP_TAC o C MP (ASSUME `schy_sq e lam (&17 / &32) <= (z:real^2)$1`)) THEN
    STRIP_TAC THEN
    EXISTS_TAC `schy_mb c' e (schy_Ac e lam) z` THEN
    USE_THEN "FM" (MP_TAC o SPEC `schy_mb c' e (schy_Ac e lam) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `--((schy_mb c' e (schy_Ac e lam) z)$3) < &7 / &8` ASSUME_TAC THENL
     [REWRITE_TAC[schy_mb; VECTOR_3] THEN
      MP_TAC(SPECL [`e:real`; `lam:real`; `(z:real^2)$1`] SCHY_AC_BOUND) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `abs(schy_B0 c' e z) <= &1 / &16` ASSUME_TAC THENL
       [REWRITE_TAC[schy_B0] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16`) (concl th))) THEN
        ASM_REWRITE_TAC[REAL_ABS_NEG];
        ALL_TAC] THEN
      SUBGOAL_THEN `abs(schy_Ac e lam ((z:real^2)$1)) pow 2 <= (&1 / &4) pow 2 /\
                    abs(schy_B0 c' e z) pow 2 <= (&1 / &16) pow 2` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let SCHY_GM_CHARTCOL = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' S1 S2 s1 rho1 rho2 ts wq eps eps0 dc.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     (!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2) /\
     B * lam * H < rho2 / &2 /\
     &0 < eps /\ eps <= lam / &100 /\ &0 < eps0 /\ eps0 <= lam / &100 /\
     (!z q. norm z <= &1 /\ dist(c z,q) < dc ==> q IN IMAGE c (ball(vec 0,&2))) /\
     (B + &2) * (&13 / &10 * lam) + B * (&2 * lam + (B + &2) * (&13 / &10 * lam)) +
     B * (&2 * lam) < dc /\
     &2 * lam + (B + &2) * (&13 / &10 * lam) < lam * H
     ==> !z t. z IN schy_Q e lam wq /\ schy_sq e lam (&1) < z$1 /\
               abs t < &2 * schy_sh e lam eps eps0 z /\
               ode_vf_flow (schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))) (:real^3)
                 (lift t) (schy_gm Theta c' e lam z) IN S1
               ==> t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`] SCHY_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
    can (term_match [] `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                               (Theta:real^3->real^3) Theta'`) (concl th))) THEN
  ABBREV_TAC `kin = schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)` THEN
  ABBREV_TAC `X = schy_X v (kin:real^3->real)` THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `rho2:real`; `z:real^2`]
    SCHY_GM_MODEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `m:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `(z:real^2)$1`] SCHY_RHO_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [MP_TAC(ASSUME `schy_sq e lam (&1) < (z:real^2)$1`) THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < schy_sh e lam eps eps0 z /\
                &2 * schy_sh e lam eps eps0 z <= &13 / &10 * lam` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schy_sh] THEN
    MP_TAC(SPEC `(z:real^2)$1` (ASSUME `!t. &0 <= schy_rho e lam eps t`)) THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`schy_rho e lam eps ((z:real^2)$1) <= &53 / &100 * lam + eps`; `eps <= lam / &100`;
      `eps0 <= lam / &100`; `&0 < eps0`; `&0 < lam`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs s <= &2 * schy_sh e lam eps eps0 z
        ==> ode_vf_flow X (:real^3) (lift s) (Theta m) IN IMAGE Theta (sch5v_slab H) /\
            Theta'(ode_vf_flow X (:real^3) (lift s) (Theta m)) IN sch5v_slab H /\
            Theta(Theta'(ode_vf_flow X (:real^3) (lift s) (Theta m))) =
              ode_vf_flow X (:real^3) (lift s) (Theta m) /\
            (Theta'(ode_vf_flow X (:real^3) (lift s) (Theta m)))$3 = m$3 + s / lam /\
            abs(s / lam) <= &13 / &10` (LABEL_TAC "COL") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ode_vf_flow X (:real^3) (lift s) ((Theta:real^3->real^3) m) IN
                  IMAGE Theta (sch5v_slab H)` ASSUME_TAC THENL
     [MATCH_MP_TAC SCHY_IMAGE_NBHD THEN
      MAP_EVERY EXISTS_TAC [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`;
                            `c:real^2->real^2`; `delta1:real`; `lam:real`;
                            `Theta':real^3->real^3`; `dc:real`; `m:real^3`;
                            `(B + &2) * (&13 / &10 * lam)`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MAP_EVERY (MP_TAC o ASSUME)
         [`--(&5 / &4) < (m:real^3)$3`; `(m:real^3)$3 <= --(&1 / &2)`] THEN
        REAL_ARITH_TAC;
        MP_TAC(ISPEC `X:real^3->real^3` SCHY_FLOW_BACK) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
        MP_TAC(ISPECL [`X:real^3->real^3`; `B + &2`] SCH5V_FLOW_DISPLACEMENT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`(Theta:real^3->real^3) m`; `lift s`; `lift(&0)`]) THEN
        ASM_REWRITE_TAC[LIFT_DROP; REAL_SUB_RZERO; GSYM dist] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(B + &2) * abs s` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&0 <= B`; `abs s <= &2 * schy_sh e lam eps eps0 z`;
          `&2 * schy_sh e lam eps eps0 z <= &13 / &10 * lam`] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE] o check (fun th ->
      concl th = `ode_vf_flow X (:real^3) (lift s) ((Theta:real^3->real^3) m) IN
                  IMAGE Theta (sch5v_slab H)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Theta':real^3->real^3)((Theta:real^3->real^3) y') = y'` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((Theta:real^3->real^3) y')$3 = e + lam * y'$3 /\
                  ((Theta:real^3->real^3) m)$3 = e + lam * m$3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!y. y IN sch5v_slab H ==> ((Theta:real^3->real^3) y)$3 = e + lam * y$3`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `X:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`lift s`; `(Theta:real^3->real^3) m`]) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
      UNDISCH_TAC `~(lam = &0)` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[REAL_ABS_DIV; ASSUME `&0 < lam`; REAL_ARITH `&0 < lam ==> abs lam = lam`;
               REAL_LE_LDIV_EQ] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs s <= &2 * schy_sh e lam eps eps0 z`;
        `&2 * schy_sh e lam eps eps0 z <= &13 / &10 * lam`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`; `kin:real^3->real`;
                 `(Theta:real^3->real^3) m`; `--(&2 * schy_sh e lam eps eps0 z)`;
                 `&2 * schy_sh e lam eps eps0 z`] SCHY_CHART_COLUMN) THEN
  REWRITE_TAC[ASSUME `schy_X v (kin:real^3->real) = X`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(ASSUME `&0 < schy_sh e lam eps eps0 z`) THEN REAL_ARITH_TAC;
      MP_TAC(ASSUME `&0 < schy_sh e lam eps eps0 z`) THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "COL" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `--(&2 * schy_sh e lam eps eps0 z) <= s /\ s <= &2 * schy_sh e lam eps eps0 z` THEN
        REAL_ARITH_TAC;
        STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs(s / lam) <= &13 / &10`; `--(&5 / &4) < (m:real^3)$3`;
        `(m:real^3)$3 <= --(&1 / &2)`; `&5 <= H`] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `(Theta':real^3->real^3)((Theta:real^3->real^3) m) = m` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(Theta':real^3->real^3)((Theta:real^3->real^3) m) = m` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `--((m:real^3)$3) < &7 / &8 \/
                   dist(schy_gm (Theta:real^3->real^3) c' e lam z,schy_lpt e) < rho2` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  SUBGOAL_THEN `abs t <= &2 * schy_sh e lam eps eps0 z` ASSUME_TAC THENL
   [MP_TAC(ASSUME `abs t < &2 * schy_sh e lam eps eps0 z`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "COL" (MP_TAC o C MP (ASSUME `abs t <= &2 * schy_sh e lam eps eps0 z`) o
                  SPEC `t:real`) THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ASSUME `abs t <= &2 * schy_sh e lam eps eps0 z`) THEN REAL_ARITH_TAC;
    MP_TAC(ASSUME `abs t <= &2 * schy_sh e lam eps eps0 z`) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SCHY_S1_IN_CHART THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `S1:real^3->bool`;
                          `S2:real^3->bool`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                          `H:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(ASSUME `&5 <= H`) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`abs(t / lam) <= &13 / &10`; `(m:real^3)$3 <= --(&1 / &2)`] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ode_vf_flow (X:real^3->real^3) (:real^3) (lift t)
                     (schy_gm (Theta:real^3->real^3) c' e lam z) IN S1` THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity of the strip.  Helpers: a function with                       *)
(* derivative bounded away from 0 is injective (Rolle); Ac is increasing;   *)
(* bec is Lipschitz; the cap profile exceeds 1/32 beyond 17/32.             *)
(* ------------------------------------------------------------------------- *)

let SCHY_DERIV_INJ = prove
 (`!(f:real->real) f' a b kap.
     &0 < kap /\
     (!t. a <= t /\ t <= b ==> (f has_real_derivative f' t) (atreal t) /\ kap <= abs(f' t))
     ==> !x y. a <= x /\ x <= b /\ a <= y /\ y <= b /\ f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. a <= x /\ x < y /\ y <= b ==> ~((f:real->real) x = f y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `x:real`; `y:real`] REAL_ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[real_differentiable_on; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN REWRITE_TAC[real_differentiable] THEN
      EXISTS_TAC `(f':real->real) u` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[NOT_EXISTS_THM; IN_REAL_INTERVAL] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x < y` THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[REAL_LT_TOTAL]]);;

let SCHY_AC_INC = prove
 (`!e lam a b. &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ &0 < a /\ a < b
               ==> schy_Ac e lam a < schy_Ac e lam b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `schy_Acd e lam` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> can (term_match []
    `!t. &0 < t ==> (schy_Ac e lam has_real_derivative schy_Acd e lam t) (atreal t) /\
                    &0 < schy_Acd e lam t`) (concl th))) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]));;

let SCHY_AC_LOW = prove
 (`!e lam t. &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ schy_sq e lam (&33 / &64) <= t
             ==> --(&1 / &8) <= schy_Ac e lam t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_Ac e lam (schy_sq e lam (&33 / &64)) = --(&1 / &8)` ASSUME_TAC THENL
   [SUBGOAL_THEN `schy_Ac e lam (schy_sq e lam (&33 / &64)) =
                  schy_f1 e lam (schy_sq e lam (&33 / &64))` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t <= schy_sq e lam (&65 / &128) ==> schy_Ac e lam t = schy_f1 e lam t`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[schy_f1; schy_ta; schy_sq] THEN
    SUBGOAL_THEN `sqrt(e - lam / &2) pow 2 = e - lam / &2 /\
                  sqrt(e - &33 / &64 * lam) pow 2 = e - &33 / &64 * lam` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((e - lam / &2) - (e - &33 / &64 * lam)) / lam = (&1 / &8) pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[POW_2_SQRT_ABS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = schy_sq e lam (&33 / &64)` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `schy_Ac e lam (schy_sq e lam (&33 / &64)) = --(&1 / &8)`)) THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SCHY_AC_INC THEN ASM_REAL_ARITH_TAC);;

let SCHY_BEC_LIP = prove
 (`!e lam P a b. &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ (!t. abs(schy_becd e lam t) <= P)
                 ==> abs(schy_bec e lam a - schy_bec e lam b) <= P * abs(a - b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v. u <= v ==> abs(schy_bec e lam v - schy_bec e lam u) <= P * (v - u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`schy_bec e lam`; `schy_becd e lam`; `u:real`; `v:real`]
      REAL_MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(v - u) = v - u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a <= b` THENL
   [SUBGOAL_THEN `abs(a - b) = b - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `abs(a - b) = a - b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:real`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let SCHY_PROFILE_GT = prove
 (`!t. &17 / &32 < t ==> &1 / &32 < sch_cap_profile t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t <= &5 / &8` THENL
   [ASM_SIMP_TAC[SCH_CAP_PROFILE_TIP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - b) * (t - &5 / &8)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The polar part is injective: two strip points with the same B0 lie on   *)
(* one hyperbola z1 z2 = const, and the height z1^2 - G is strictly        *)
(* increasing along it when the blend bec is Lipschitz with a small        *)
(* constant times wq^2 (a pure real lemma).                                *)

let SCHY_HYP_INJ = prove
 (`!x x' w w' b1 b1' beta lam P wq se.
     &0 < se /\ se / &2 <= x /\ se / &2 <= x' /\
     x * w = x' * w' /\
     x pow 2 - ((&1 - b1) * w pow 2 + b1 * lam * beta pow 2) =
     x' pow 2 - ((&1 - b1') * w' pow 2 + b1' * lam * beta pow 2) /\
     &0 <= b1 /\ b1 <= &1 /\ abs(b1 - b1') <= P * abs(x - x') /\
     &0 <= lam * beta pow 2 /\ lam * beta pow 2 <= wq pow 2 /\ abs w' < wq /\
     P * wq pow 2 <= se / &4
     ==> x = x' /\ w = w'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x = x':real` ASSUME_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `x * w = x' * w':real` THEN ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < se`; `se / &2 <= x'`] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(x - x')) ==> x = x'`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x pow 2 - x' pow 2) * (x pow 2 + (&1 - b1) * w' pow 2) =
                x pow 2 * ((b1 - b1') * (lam * beta pow 2 - w' pow 2))` MP_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`x * w = x' * w':real`;
      `x pow 2 - ((&1 - b1) * w pow 2 + b1 * lam * beta pow 2) =
       x' pow 2 - ((&1 - b1') * w' pow 2 + b1' * lam * beta pow 2)`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `abs(x pow 2 - x' pow 2) = abs(x - x') * (x + x')` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x pow 2 - x' pow 2 = (x - x') * (x + x')`; REAL_ABS_MUL] THEN
    AP_TERM_TAC THEN MAP_EVERY (MP_TAC o ASSUME)
     [`&0 < se`; `se / &2 <= x`; `se / &2 <= x'`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - b1) * w' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(ASSUME `b1 <= &1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x pow 2 + (&1 - b1) * w' pow 2) = x pow 2 + (&1 - b1) * w' pow 2`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    MP_TAC(ASSUME `&0 <= (&1 - b1) * w' pow 2`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(lam * beta pow 2 - w' pow 2) <= wq pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `w' pow 2 <= wq pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      MP_TAC(ASSUME `abs w' < wq`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `w':real` REAL_LE_POW_2) THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`&0 <= lam * beta pow 2`; `lam * beta pow 2 <= wq pow 2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = abs(x - x')` THEN
  ABBREV_TAC `W = x pow 2 + (&1 - b1) * w' pow 2` THEN
  ABBREV_TAC `A = abs(b1 - b1')` THEN
  ABBREV_TAC `D = abs(lam * beta pow 2 - w' pow 2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x pow 2 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MP_TAC(ASSUME `&0 <= (&1 - b1) * w' pow 2`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= D /\ &0 <= x pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "D" THEN REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * D <= (P * u) * wq pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P * u) * wq pow 2 <= u * (se / &4)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(P * u) * q = u * (P * q)`] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `&0 < u`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 * (A * D) <= x pow 2 * (u * (se / &4))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`A * D <= (P * u) * wq pow 2`; `(P * u) * wq pow 2 <= u * (se / &4)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `se * x pow 2 <= (x + x') * W` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`&0 < se`; `se / &2 <= x`; `se / &2 <= x'`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u * (se * x pow 2) <= u * ((x + x') * W)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `&0 < u`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u * (se * x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < se`; `se / &2 <= x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [`u * (se * x pow 2) <= u * ((x + x') * W)`;
    `x pow 2 * (A * D) <= x pow 2 * (u * (se / &4))`] THEN
  UNDISCH_TAC `(u * (x + x')) * W = x pow 2 * (A * D)` THEN
  REAL_ARITH_TAC);;

(* The model point of the strip determines the strip parameter: polar part *)
(* by SCHY_HYP_INJ, tip part by the monotone A coordinate and B0, mixed     *)
(* case by SCHY_MA_MB or by the size of the A coordinate.                   *)

let SCHY_MM_MAMA = prove
 (`!(c':real^2->real^2) e lam P wq (z:real^2) z'.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     (!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b) /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\
     z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
     sqrt e / &2 <= z$1 /\ sqrt e / &2 <= z'$1 /\
     schy_ma c' e lam (schy_bec e lam) z = schy_ma c' e lam (schy_bec e lam) z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z':real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^2)$1 /\ &0 < (z':real^2)$1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`sqrt e / &2 <= (z:real^2)$1`; `sqrt e / &2 <= (z':real^2)$1`; `&0 < sqrt e`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_B0 c' e z = schy_B0 c' e z' /\
                schy_Ya c' e lam (schy_bec e lam) z = schy_Ya c' e lam (schy_bec e lam) z'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_ma c' e lam (schy_bec e lam) z = schy_ma c' e lam (schy_bec e lam) z'` THEN
    REWRITE_TAC[schy_ma; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(z:real^2)$1`; `(z':real^2)$1`; `(z:real^2)$2`; `(z':real^2)$2`;
                `schy_bec e lam ((z:real^2)$1)`; `schy_bec e lam ((z':real^2)$1)`;
                `schy_B0 c' e z`; `lam:real`; `P:real`; `wq:real`; `sqrt e`] SCHY_HYP_INJ) THEN
  ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2]] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [SUBGOAL_THEN `--(&2 * (z:real^2)$1 * z$2) = --(&2 * (z':real^2)$1 * z'$2)` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b
                                ==> a = b`) THEN
      ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
      UNDISCH_TAC `schy_B0 c' e z = schy_B0 c' e z'` THEN REWRITE_TAC[schy_B0];
      REAL_ARITH_TAC];
    UNDISCH_TAC `schy_Ya c' e lam (schy_bec e lam) z = schy_Ya c' e lam (schy_bec e lam) z'` THEN
    REWRITE_TAC[schy_Ya; schy_G] THEN
    REWRITE_TAC[ASSUME `schy_B0 c' e z = schy_B0 c' e z'`] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHY_BEC_LIP THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schy_B0] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG]]);;

let SCHY_MM_MBMB = prove
 (`!(c':real^2->real^2) e lam P wq (z:real^2) z'.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     (!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b) /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\
     z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
     sqrt e / &2 <= z$1 /\ sqrt e / &2 <= z'$1 /\
     schy_mb c' e (schy_Ac e lam) z = schy_mb c' e (schy_Ac e lam) z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z':real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^2)$1 /\ &0 < (z':real^2)$1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`sqrt e / &2 <= (z:real^2)$1`; `sqrt e / &2 <= (z':real^2)$1`; `&0 < sqrt e`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_Ac e lam ((z:real^2)$1) = schy_Ac e lam ((z':real^2)$1) /\
                schy_B0 c' e z = schy_B0 c' e z'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `schy_mb c' e (schy_Ac e lam) z = schy_mb c' e (schy_Ac e lam) z'` THEN
    REWRITE_TAC[schy_mb; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 * z$2 = (z':real^2)$1 * z'$2` ASSUME_TAC THENL
   [SUBGOAL_THEN `--(&2 * (z:real^2)$1 * z$2) = --(&2 * (z':real^2)$1 * z'$2)` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b
                                ==> a = b`) THEN
      ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
      UNDISCH_TAC `schy_B0 c' e z = schy_B0 c' e z'` THEN REWRITE_TAC[schy_B0];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$1 = (z':real^2)$1` ASSUME_TAC THENL
   [ASM_CASES_TAC `(z:real^2)$1 < (z':real^2)$1` THENL
     [MP_TAC(SPECL [`e:real`; `lam:real`; `(z:real^2)$1`; `(z':real^2)$1`] SCHY_AC_INC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `(z':real^2)$1 < (z:real^2)$1` THENL
       [MP_TAC(SPECL [`e:real`; `lam:real`; `(z':real^2)$1`; `(z:real^2)$1`] SCHY_AC_INC) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2)$2 = (z':real^2)$2` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2)$1 * z$2 = (z':real^2)$1 * z'$2` THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < (z':real^2)$1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2]);;

let SCHY_MM_MAMB = prove
 (`!(c':real^2->real^2) e lam P wq (z:real^2) z'.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     (!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b) /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\
     z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
     sqrt e / &2 <= z$1 /\ sqrt e / &2 <= z'$1 /\
     z$1 <= schy_sq e lam (&33 / &64) /\ schy_sq e lam (&33 / &64) < z'$1 /\
     schy_ma c' e lam (schy_bec e lam) z = schy_mb c' e (schy_Ac e lam) z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z':real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^2)$1 /\ &0 < (z':real^2)$1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`sqrt e / &2 <= (z:real^2)$1`; `sqrt e / &2 <= (z':real^2)$1`; `&0 < sqrt e`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(schy_B0 c' e z) <= &1 / &16` ASSUME_TAC THENL
   [REWRITE_TAC[schy_B0] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_B0 c' e z pow 2 <= &1 / &256` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(schy_B0 c' e z) pow 2 <= (&1 / &16) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam /\
                schy_sq e lam (&33 / &64) pow 2 = e - &33 / &64 * lam /\
                schy_ta e lam pow 2 = e - lam / &2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq; schy_ta] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `schy_sq e lam (&17 / &32) <= (z:real^2)$1` THENL
   [MATCH_MP_TAC SCHY_MM_MBMB THEN
    MAP_EVERY EXISTS_TAC [`c':real^2->real^2`; `e:real`; `lam:real`; `P:real`; `wq:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `schy_ma c' e lam (schy_bec e lam) z = schy_mb c' e (schy_Ac e lam) z'`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHY_MA_MB THEN
    SUBGOAL_THEN `schy_bec e lam ((z:real^2)$1) = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. schy_sq e lam (&17 / &32) <= t ==> schy_bec e lam t = &1`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2)$1 pow 2 <= e - &33 / &64 * lam /\
                  e - &17 / &32 * lam <= (z:real^2)$1 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `schy_sq e lam (&33 / &64) pow 2 = e - &33 / &64 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `schy_Ac e lam ((z:real^2)$1) = schy_f1 e lam ((z:real^2)$1)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!t. t <= schy_sq e lam (&65 / &128) ==> schy_Ac e lam t = schy_f1 e lam t`)
          (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[schy_f1] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `e / lam - &1 / &2 - (z:real^2)$1 pow 2 / lam =
                    (e - lam / &2 - z$1 pow 2) / lam` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `--(schy_Ya c' e lam (schy_bec e lam) z) =
                    (e - (z:real^2)$1 pow 2) / lam + schy_B0 c' e z pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[schy_Ya; schy_G] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `(e - (z:real^2)$1 pow 2) / lam <= &17 / &32` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ASSUME `schy_B0 c' e z pow 2 <= &1 / &256`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(schy_ma c' e lam (schy_bec e lam) z)$1 = (schy_mb c' e (schy_Ac e lam) z')$1`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[schy_ma; schy_mb; VECTOR_3] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `(z':real^2)$1`] SCHY_AC_LOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 / &8 < sqrt(sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) z)) -
                               schy_B0 c' e z pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN
    SUBGOAL_THEN `&1 / &32 < sch_cap_profile(--(schy_Ya c' e lam (schy_bec e lam) z))` MP_TAC THENL
     [MATCH_MP_TAC SCHY_PROFILE_GT THEN
      SUBGOAL_THEN `--(schy_Ya c' e lam (schy_bec e lam) z) =
                    (e - (z:real^2)$1 pow 2 + schy_G c' e lam (schy_bec e lam) z) / lam`
      SUBST1_TAC THENL
       [REWRITE_TAC[schy_Ya] THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= schy_G c' e lam (schy_bec e lam) z` MP_TAC THENL
       [REWRITE_TAC[schy_G] THEN
        MP_TAC(SPEC `(z:real^2)$1` (ASSUME `!t. &0 <= schy_bec e lam t /\ schy_bec e lam t <= &1`)) THEN
        STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
        TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]) THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&0 < lam`; `schy_bec e lam ((z:real^2)$1) <= &1`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^2)$1 pow 2 < e - &17 / &32 * lam` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `schy_sq e lam (&17 / &32) pow 2 = e - &17 / &32 * lam`)) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC;
      MP_TAC(ASSUME `schy_B0 c' e z pow 2 <= &1 / &256`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ASSUME `--(&1 / &8) <= schy_Ac e lam ((z':real^2)$1)`) THEN REAL_ARITH_TAC);;

let SCHY_MM_INJ = prove
 (`!(c':real^2->real^2) e lam P wq (z:real^2) z'.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     (!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b) /\
     &0 < wq /\ &100 * wq pow 2 <= lam /\
     z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
     sqrt e / &2 <= z$1 /\ sqrt e / &2 <= z'$1 /\
     (if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
      else schy_mb c' e (schy_Ac e lam) z) =
     (if z'$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z'
      else schy_mb c' e (schy_Ac e lam) z')
     ==> z = z'`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` THEN
  ASM_CASES_TAC `(z':real^2)$1 <= schy_sq e lam (&33 / &64)` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC SCHY_MM_MAMA;
    MATCH_MP_TAC SCHY_MM_MAMB;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHY_MM_MAMB;
    MATCH_MP_TAC SCHY_MM_MBMB] THEN
  MAP_EVERY EXISTS_TAC [`c':real^2->real^2`; `e:real`; `lam:real`; `P:real`; `wq:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHY_PROFILE_NORM = prove
 (`!m:real^3. m$1 pow 2 + m$2 pow 2 = sch_cap_profile(--(m$3)) ==> norm(sch5v_pr m) <= &1`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[vector_norm; sch5v_pr; DOT_2; VECTOR_2] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  MP_TAC(SPEC `--((m:real^3)$3)` SCHY_PROFILE_LE1) THEN
  UNDISCH_TAC `(m:real^3)$1 pow 2 + m$2 pow 2 = sch_cap_profile(--(m$3))` THEN
  REAL_ARITH_TAC);;

(* For t >= sqrt(e - 17/16 lam) the strip point is Theta of the model point  *)
(* K z (ma for t <= sq(33/64), mb beyond).                                    *)

let SCHY_GM_K = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq z.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     z IN schy_Q e lam wq /\ sqrt(e - &17 / &16 * lam) <= z$1
     ==> (if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
          else schy_mb c' e (schy_Ac e lam) z) IN sch5v_slab H /\
         schy_gm Theta c' e lam z = Theta (if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
          else schy_mb c' e (schy_Ac e lam) z) /\
         norm(sch5v_pr (if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
          else schy_mb c' e (schy_Ac e lam) z)) <= &1 /\
         abs((if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
          else schy_mb c' e (schy_Ac e lam) z)$3) <= &2 /\
         (schy_sq e lam (&7 / &8) < z$1 ==> -- &1 < (if z$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z
          else schy_mb c' e (schy_Ac e lam) z)$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "P2")
    (CONJUNCTS_THEN2 (LABEL_TAC "P3") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `abs(schy_B0 c' e z) <= &1 / &16` ASSUME_TAC THENL
   [REWRITE_TAC[schy_B0] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_B0 c' e z pow 2 <= &1 / &256 /\ (z:real^2)$2 pow 2 <= lam / &100`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `abs(schy_B0 c' e z) pow 2 <= (&1 / &16) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wq pow 2` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        MAP_EVERY (MP_TAC o ASSUME) [`abs((z:real^2)$2) < wq`] THEN REAL_ARITH_TAC;
        MP_TAC(ASSUME `&100 * wq pow 2 <= lam`) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&33 / &64)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&7 / &8)` THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_JUNCTION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`(schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
           (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 = &1`;
          `--(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3`;
          `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&7 / &8)`; `&5 <= H`] THEN
        REAL_ARITH_TAC;
        USE_THEN "P1" (fun th -> REWRITE_TAC[MP th (ASSUME
          `(z:real^2)$1 <= schy_sq e lam (&7 / &8)`)]) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SCHY_PROFILE_NORM THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN
        MP_TAC(ASSUME `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&7 / &8)`) THEN
        REAL_ARITH_TAC;
        MAP_EVERY (MP_TAC o ASSUME)
         [`--(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3`;
          `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&7 / &8)`] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_NOT_LE] THEN ASM_REWRITE_TAC[]];
      USE_THEN "P2" MP_TAC THEN ANTS_TAC THENL
       [MAP_EVERY (MP_TAC o ASSUME)
         [`~((z:real^2)$1 <= schy_sq e lam (&7 / &8))`;
          `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`;
          `(z:real^2)$1 <= schy_sq e lam (&33 / &64)`] THEN
        REAL_ARITH_TAC;
        STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SCHY_PROFILE_NORM THEN ASM_REWRITE_TAC[];
        MAP_EVERY (MP_TAC o ASSUME)
         [`--(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3`;
          `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)`] THEN
        REAL_ARITH_TAC;
        DISCH_TAC THEN REWRITE_TAC[schy_ma; VECTOR_3; schy_Ya] THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
        SUBGOAL_THEN `e - &7 / &8 * lam < (z:real^2)$1 pow 2` MP_TAC THENL
         [SUBGOAL_THEN `schy_sq e lam (&7 / &8) pow 2 = e - &7 / &8 * lam` (SUBST1_TAC o SYM) THENL
           [REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `schy_G c' e lam (schy_bec e lam) z <= lam / &8` MP_TAC THENL
         [REWRITE_TAC[schy_G] THEN
          MP_TAC(SPEC `(z:real^2)$1` (ASSUME
            `!t. &0 <= schy_bec e lam t /\ schy_bec e lam t <= &1`)) THEN
          ABBREV_TAC `b = schy_bec e lam ((z:real^2)$1)` THEN STRIP_TAC THEN
          SUBGOAL_THEN `(&1 - b) * (z:real^2)$2 pow 2 <= z$2 pow 2 /\
                        b * lam * schy_B0 c' e z pow 2 <= lam * schy_B0 c' e z pow 2`
          MP_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC(REAL_ARITH `&0 <= b * w ==> (&1 - b) * w <= w`) THEN
              MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
              MATCH_MP_TAC(REAL_ARITH `b * x <= &1 * x ==> b * x <= x`) THEN
              MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
              MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
              ASM_REAL_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `lam * schy_B0 c' e z pow 2 <= lam * (&1 / &256)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          MAP_EVERY (MP_TAC o ASSUME)
           [`(z:real^2)$2 pow 2 <= lam / &100`; `&0 < lam`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REAL_ARITH_TAC]];
    USE_THEN "P3" MP_TAC THEN ANTS_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME)
       [`~((z:real^2)$1 <= schy_sq e lam (&33 / &64))`;
        `schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64)`] THEN
      REAL_ARITH_TAC;
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCHY_PROFILE_NORM THEN ASM_REWRITE_TAC[];
      MAP_EVERY (MP_TAC o ASSUME)
       [`--(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3`;
        `(schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2)`] THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN REWRITE_TAC[schy_mb; VECTOR_3] THEN
      MP_TAC(SPECL [`e:real`; `lam:real`; `(z:real^2)$1`] SCHY_AC_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`~((z:real^2)$1 <= schy_sq e lam (&33 / &64))`;
          `schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64)`;
          `(z:real^2)$1 < schy_ta e lam + &1 / &16`] THEN
        REAL_ARITH_TAC;
        DISCH_TAC] THEN
      SUBGOAL_THEN `abs(schy_Ac e lam ((z:real^2)$1)) pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN
      MP_TAC(ASSUME `schy_B0 c' e z pow 2 <= &1 / &256`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]]);;

(* A model point of the chart with |pr y| <= 1 and |y3| <= 2 never         *)
(* projects to the right half of the box (generalizes SCHY_LAT_RIGHT).     *)

let SCHY_MODEL_RIGHT = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' y.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     norm(sch5v_pr y) <= &1 /\ abs(y$3) <= &2 /\
     &0 <= (sch5v_pr(Theta y))$1 /\
     (sch5v_pr(Theta y))$1 pow 2 + (sch5v_pr(Theta y))$2 pow 2 < &2 * e /\
     abs((sch5v_pr(Theta y))$2) + &2 * (&2 * B * lam + lam) < sqrt e
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  SUBGOAL_THEN `(c:real^2->real^2)(sch5v_pr y) IN
                  inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) \/
                (c:real^2->real^2)(sch5v_pr y) IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_UNION] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2 o MATCH_MP SCHY_CTX_J) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  SUBGOAL_THEN `dist(sch5v_pr((Theta:real^3->real^3) y),(c:real^2->real^2)(sch5v_pr y)) <
                &2 * B * lam + lam` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                   `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `y:real^3`] SCHY_THETA_DISP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    SUBGOAL_THEN `B * lam * abs((y:real^3)$3) <= B * lam * &2` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < lam`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * sqrt e < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(&4 * sqrt e) < abs r` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_SQUARE_ABS; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `x = sch5v_pr((Theta:real^3->real^3) y)` THEN
  SUBGOAL_THEN `norm(x:real^2) < &2 * sqrt e` ASSUME_TAC THENL
   [REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[DOT_2; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_OUT_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `e:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `x:real^2`;
                 `(c:real^2->real^2)(sch5v_pr y)`; `&2 * B * lam + lam`] SCHY_NEAR_J) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCHY_GM_INJ = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' ts wq P.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b) /\
     wq + &2 * (&2 * B * lam + lam) < sqrt e
     ==> !z z'. z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
                schy_gm Theta c' e lam z = schy_gm Theta c' e lam z' ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
    can (term_match [] `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H
                               (Theta:real^3->real^3) Theta'`) (concl th))) THEN
  ABBREV_TAC `zb = sqrt(e - &17 / &16 * lam)` THEN
  SUBGOAL_THEN `sqrt e / &2 <= zb /\ zb pow 2 = e - &17 / &16 * lam /\ zb < schy_sq e lam (&1) /\
                &0 < zb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zb" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z'. z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
                       zb <= z$1 /\ zb <= z'$1 /\
                       schy_gm Theta c' e lam z = schy_gm Theta c' e lam z' ==> z = z'`
  (LABEL_TAC "KK") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_K) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z':real^2`] SCHY_GM_K) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC SCHY_MM_INJ THEN
    MAP_EVERY EXISTS_TAC [`c':real^2->real^2`; `e:real`; `lam:real`; `P:real`; `wq:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`sqrt e / &2 <= zb`; `zb <= (z:real^2)$1`] THEN
      REAL_ARITH_TAC;
      MAP_EVERY (MP_TAC o ASSUME) [`sqrt e / &2 <= zb`; `zb <= (z':real^2)$1`] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `(Theta:real^3->real^3) (if (z:real^2)$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z else schy_mb c' e (schy_Ac e lam) z) = Theta (if (z':real^2)$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z' else schy_mb c' e (schy_Ac e lam) z')`
      MP_TAC THENL
       [UNDISCH_TAC `schy_gm (Theta:real^3->real^3) c' e lam z = schy_gm Theta c' e lam z'` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `Theta':real^3->real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z'. z IN schy_Q e lam wq /\ z' IN schy_Q e lam wq /\
                       z$1 < zb /\ schy_sq e lam (&7 / &8) < z'$1 /\
                       schy_gm Theta c' e lam z = schy_gm Theta c' e lam z' ==> F`
  (LABEL_TAC "X") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z':real^2`] SCHY_GM_K) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`zb < schy_sq e lam (&1)`; `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`;
        `schy_sq e lam (&7 / &8) < (z':real^2)$1`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `y = (if (z':real^2)$1 <= schy_sq e lam (&33 / &64) then schy_ma c' e lam (schy_bec e lam) z' else schy_mb c' e (schy_Ac e lam) z')` THEN
    REWRITE_TAC[ASSUME `schy_sq e lam (&7 / &8) < (z':real^2)$1`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `wq:real`; `z:real^2`] SCHY_BOXPT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME) [`(z:real^2)$1 < zb`; `zb < schy_sq e lam (&1)`] THEN
      REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `schy_gm Theta c' e lam z = schy_sbox z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`(z:real^2)$1 < zb`; `zb < schy_sq e lam (&1)`;
        `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Theta:real^3->real^3) y = schy_sbox z` ASSUME_TAC THENL
     [UNDISCH_TAC `schy_gm (Theta:real^3->real^3) c' e lam z = schy_gm Theta c' e lam z'` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= (z:real^2)$1` THENL
     [SUBGOAL_THEN `((Theta:real^3->real^3) y)$3 = e + lam * y$3` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!y. y IN sch5v_slab H ==> ((Theta:real^3->real^3) y)$3 = e + lam * y$3`)
          (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[schy_sbox; VECTOR_3] THEN
      SUBGOAL_THEN `(z:real^2)$1 pow 2 < zb pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `lam * -- &1 < lam * (y:real^3)$3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN
      MAP_EVERY (MP_TAC o ASSUME) [`zb pow 2 = e - &17 / &16 * lam`; `&0 < lam`] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_MODEL_RIGHT) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[SCHY_SBOX_VERT; VECTOR_2] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`~(&0 <= (z:real^2)$1)`; `(z:real^2)$1 pow 2 < e`; `(z:real^2)$2 pow 2 < lam / &50`;
        `abs((z:real^2)$2) < wq`; `wq + &2 * (&2 * B * lam + lam) < sqrt e`; `&0 < lam`;
        `&64 * lam < e`] THEN
      REWRITE_TAC[REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `zb <= (z:real^2)$1 /\ zb <= (z':real^2)$1` THENL
   [USE_THEN "KK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&7 / &8) /\ (z':real^2)$1 <= schy_sq e lam (&7 / &8)`
  THENL
   [SUBGOAL_THEN `schy_sbox z = schy_sbox z'` MP_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z:real^2`] SCHY_GM_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `z':real^2`] SCHY_GM_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[schy_sbox; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 < zb` THENL
   [USE_THEN "X" (MP_TAC o SPECL [`z:real^2`; `z':real^2`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`~((z:real^2)$1 <= schy_sq e lam (&7 / &8) /\ (z':real^2)$1 <= schy_sq e lam (&7 / &8))`;
      `(z:real^2)$1 < zb`; `zb < schy_sq e lam (&1)`;
      `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`] THEN
    REAL_ARITH_TAC;
    USE_THEN "X" (MP_TAC o SPECL [`z':real^2`; `z:real^2`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`~((z:real^2)$1 <= schy_sq e lam (&7 / &8) /\ (z':real^2)$1 <= schy_sq e lam (&7 / &8))`;
      `~(zb <= (z:real^2)$1 /\ zb <= (z':real^2)$1)`; `~((z:real^2)$1 < zb)`;
      `zb < schy_sq e lam (&1)`; `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Derivative tools for the transversality of the strip: chain rules for     *)
(* bec, bz and Ac usable by REAL_DIFF_TAC (side conditions through           *)
(* schy_hasd; the global rule list is restored at the end of this unit),     *)
(* components of Frechet derivatives as directional derivatives, locality.   *)
(* ------------------------------------------------------------------------- *)

let schy_hasd = new_definition
 `schy_hasd (h:real->real) h' x <=> (h has_real_derivative h') (atreal x)`;;

let SCHY_BEC_CHAIN = prove
 (`!e lam (g:real->real) g' x.
     (g has_real_derivative g') (atreal x)
     ==> schy_hasd (schy_bec e lam) (schy_becd e lam (g x)) (g x)
     ==> ((\x. schy_bec e lam (g x)) has_real_derivative (schy_becd e lam (g x) * g')) (atreal x)`,
  REWRITE_TAC[schy_hasd] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `schy_bec e lam`; `g':real`; `schy_becd e lam ((g:real->real) x)`;
                 `x:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let SCHY_BZ_CHAIN = prove
 (`!(c':real^2->real^2) e (g:real->real) g' x.
     (g has_real_derivative g') (atreal x)
     ==> schy_hasd (schy_bz c' e) (schy_bzd c' e (g x)) (g x)
     ==> ((\x. schy_bz c' e (g x)) has_real_derivative (schy_bzd c' e (g x) * g')) (atreal x)`,
  REWRITE_TAC[schy_hasd] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `schy_bz c' e`; `g':real`; `schy_bzd c' e ((g:real->real) x)`;
                 `x:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let SCHY_AC_CHAIN = prove
 (`!e lam (g:real->real) g' x.
     (g has_real_derivative g') (atreal x)
     ==> schy_hasd (schy_Ac e lam) (schy_Acd e lam (g x)) (g x)
     ==> ((\x. schy_Ac e lam (g x)) has_real_derivative (schy_Acd e lam (g x) * g')) (atreal x)`,
  REWRITE_TAC[schy_hasd] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `schy_Ac e lam`; `g':real`; `schy_Acd e lam ((g:real->real) x)`;
                 `x:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF] THEN REWRITE_TAC[REAL_MUL_SYM]);;

(* The three chain rules are added to the global rule list of REAL_DIFF_TAC  *)
(* here; the list is saved first and restored at the end of this unit, so no *)
(* other unit sees the extended list.                                        *)

let schy_saved_rdt = !real_differentiation_theorems;;

add_real_differentiation_theorems [SCHY_BEC_CHAIN; SCHY_BZ_CHAIN; SCHY_AC_CHAIN];;

let SCHY_DIRDERIV_COMP = prove
 (`!(f:real^2->real^N) z v i d.
     f differentiable (at z) /\ 1 <= i /\ i <= dimindex(:N) /\
     ((\t. (f(z + t % v))$i) has_real_derivative d) (atreal (&0))
     ==> (frechet_derivative f (at z) v)$i = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_FRECHET_DERIVATIVE_AT]) THEN
  REWRITE_TAC[LIFT_NUM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(lift o (\t. ((f:real^2->real^N)(z + t % v))$i) o drop) =
                (\x:real^N. lift(x$i)) o f o (\x:real^1. z + drop x % v)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(((\x:real^N. lift(x$i)) o (f:real^2->real^N) o (\x:real^1. z + drop x % v))
                 has_derivative
                 ((\x:real^N. lift(x$i)) o frechet_derivative f (at z) o (\h:real^1. drop h % v)))
                (at (vec 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\h:real^1. drop h % v:real^2) = (\h. vec 0 + drop h % v)` SUBST1_TAC THENL
         [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        MP_TAC(ISPECL [`\x:real^1. x`; `v:real^2`] LINEAR_VMUL_DROP) THEN
        REWRITE_TAC[LINEAR_ID];
        REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
        ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lift o (\t. ((f:real^2->real^N)(z + t % v))$i) o drop`;
                 `(\x:real^N. lift(x$i)) o frechet_derivative (f:real^2->real^N) (at z) o
                  (\h:real^1. drop h % v)`;
                 `\x:real^1. d % x`; `vec 0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[LIFT_DROP; DROP_CMUL; REAL_MUL_RID]);;

let SCHY_FD_LOCAL = prove
 (`!(f:real^M->real^N) g s x.
     open s /\ x IN s /\ (!y. y IN s ==> f y = g y) /\ f differentiable (at x)
     ==> g differentiable (at x) /\ frechet_derivative g (at x) = frechet_derivative f (at x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((g:real^M->real^N) has_derivative frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

let SCHY_YA_HYPDER = prove
 (`!(c':real^2->real^2) e lam t0 (z:real^2).
     &0 < lam /\ &2 * lam < e /\ lam <= &1 /\
     (!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)) /\
     abs(&2 * z$1 * z$2) <= t0
     ==> ((\t. schy_Ya c' e lam (schy_bec e lam) (z + t % vector[z$1; --(z$2)]))
          has_real_derivative
          ((&2 * z$1 pow 2 + &2 * (&1 - schy_bec e lam (z$1)) * z$2 pow 2 +
            z$1 * schy_becd e lam (z$1) * (z$2 pow 2 - lam * schy_B0 c' e z pow 2)) / lam))
         (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. schy_Ya c' e lam (schy_bec e lam) ((z:real^2) + t % vector[z$1; --(z$2)])) =
    (\t. ((z$1 + t * z$1) pow 2 - e -
          ((&1 - schy_bec e lam (z$1 + t * z$1)) * (z$2 - t * z$2) pow 2 +
           schy_bec e lam (z$1 + t * z$1) * lam *
           schy_bz c' e (--(&2 * (z$1 + t * z$1) * (z$2 - t * z$2))) pow 2)) / lam)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_Ya; schy_G; schy_B0; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_2; REAL_ARITH `z + t * --w = z - t * w`];
    ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  REWRITE_TAC[schy_hasd; schy_B0; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[REAL_ABS_NEG] THEN NO_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC);;

let SCHY_B0_DIRDER = prove
 (`!(c':real^2->real^2) e t0 (z:real^2) a.
     (!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau)) /\
     abs(&2 * z$1 * z$2) <= t0
     ==> ((\t. schy_B0 c' e (z + t % a)) has_real_derivative
          schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * (a$1 * z$2 + z$1 * a$2)))
         (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. schy_B0 c' e ((z:real^2) + t % a)) =
                (\t. schy_bz c' e (--(&2 * (z$1 + t * a$1) * (z$2 + t * a$2))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_B0; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
  REAL_DIFF_TAC THEN REWRITE_TAC[schy_hasd; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[REAL_ABS_NEG] THEN NO_TAC) THEN REAL_ARITH_TAC);;

let SCHY_AC_DIRDER = prove
 (`!e lam (z:real^2) a.
     &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ &0 < z$1
     ==> ((\t. schy_Ac e lam ((z + t % a)$1)) has_real_derivative
          schy_Acd e lam (z$1) * a$1) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_DIFF_TAC THEN REWRITE_TAC[schy_hasd; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN REAL_ARITH_TAC);;

(* On a piece U where the strip is Theta o K with F o K = 0: if             *)
(* DGam a + c X = 0 then c = 0 (apply DTheta' and DF; DF(DTheta' X) > 0 by  *)
(* SCHY_PHI_SIGN) and DK a = 0.                                             *)

let SCHY_TRANSV_C = prove
 (`!(v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam H (Theta:real^3->real^3) Theta'
    s1 rho1 rho2 (Gam:real^2->real^3) (K:real^2->real^3) U z a cc.
     schy_cd v B rho0 e c delta1 lam H Theta Theta' /\ &0 < s1 /\ s1 < &1 /\ &3 <= H /\
     &0 <= rho1 /\ rho1 < rho2 /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     open U /\ z IN U /\ Gam differentiable (at z) /\
     (!w. w IN U ==> K w IN sch5v_slab H /\ Gam w = Theta(K w) /\ schy_F(K w) = &0) /\
     (K z)$1 pow 2 + (K z)$2 pow 2 <= &1 /\ abs((K z)$3) <= H - &2 /\
     (--((K z)$3) < &7 / &8 \/ dist(Theta(K z),schy_lpt e) < rho2) /\
     frechet_derivative Gam (at z) a +
     cc % schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) (Gam z) = vec 0
     ==> cc = &0 /\ K differentiable (at z) /\ frechet_derivative K (at z) a = vec 0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  ABBREV_TAC `kin = schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)` THEN
  MP_TAC(ISPECL [`Theta:real^3->real^3`; `Theta':real^3->real^3`; `H:real`; `s1:real`;
                 `rho1:real`; `rho2:real`; `schy_lpt e`] SCHY_KIN_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(K:real^2->real^3) z IN sch5v_slab H /\ (Theta:real^3->real^3)(K z) = Gam z /\
                schy_F(K z) = &0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> can (term_match []
      `!w. w IN U ==> (K:real^2->real^3) w IN sch5v_slab H /\ P w`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Theta':real^3->real^3) differentiable (at ((Gam:real^2->real^3) z))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBST1_TAC(SYM(ASSUME `(Theta:real^3->real^3)((K:real^2->real^3) z) = Gam z`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^2->real^3) differentiable (at z) /\
                frechet_derivative K (at z) =
                frechet_derivative ((Theta':real^3->real^3) o (Gam:real^2->real^3)) (at z)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_FD_LOCAL THEN EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> can (term_match []
        `!w. w IN U ==> (K:real^2->real^3) w IN sch5v_slab H /\ P w`) (concl th))) THEN
      ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (K:real^2->real^3) (at z) =
                frechet_derivative (Theta':real^3->real^3) (at ((Gam:real^2->real^3) z)) o
                frechet_derivative Gam (at z)` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `frechet_derivative (K:real^2->real^3) (at z) =
                         frechet_derivative ((Theta':real^3->real^3) o (Gam:real^2->real^3)) (at z)`] THEN
    MATCH_MP_TAC SCHY_FD_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `frechet_derivative (K:real^2->real^3) (at z) =
     frechet_derivative ((Theta':real^3->real^3) o (Gam:real^2->real^3)) (at z)`)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `DT = frechet_derivative (Theta':real^3->real^3) (at ((Gam:real^2->real^3) z))` THEN
  SUBGOAL_THEN `linear(DT:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "DT" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = (DT:real^3->real^3)(schy_X v kin ((Gam:real^2->real^3) z))` THEN
  SUBGOAL_THEN `(DT:real^3->real^3)(frechet_derivative (Gam:real^2->real^3) (at z) a) + cc % W =
                vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th);
                                      GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LINEAR_0];
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (\y. lift(schy_F y)) (at ((K:real^2->real^3) z))` THEN
  SUBGOAL_THEN `linear(L:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable] THEN MESON_TAC[SCHY_F_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^3->real^1)((DT:real^3->real^3)
                  (frechet_derivative (Gam:real^2->real^3) (at z) a)) = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift(schy_F y)) differentiable (at ((K:real^2->real^3) z))` ASSUME_TAC THENL
     [REWRITE_TAC[differentiable] THEN MESON_TAC[SCHY_F_DERIV]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:real^2->real^3`; `\y:real^3. lift(schy_F y)`; `z:real^2`]
      SCHY_FD_COMPOSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(\w:real^2. vec 0):real^2->real^1`;
                   `(\y:real^3. lift(schy_F y)) o (K:real^2->real^3)`;
                   `U:real^2->bool`; `z:real^2`] SCHY_FD_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIFFERENTIABLE_CONST] THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> can (term_match []
        `!w. w IN U ==> (K:real^2->real^3) w IN sch5v_slab H /\ P w`) (concl th))) THEN
      ASM_SIMP_TAC[o_THM; LIFT_NUM];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C AP_THM `a:real^2`) THEN REWRITE_TAC[o_THM] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`;
                 `kin:real^3->real`; `(K:real^2->real^3) z`] SCHY_PHI_SIGN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`s1:real`; `H:real`] SCHY_KMOD_PROPS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(((K:real^2->real^3) z)$3) pow 2 <= (H - &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      REWRITE_TAC[REAL_POW2_ABS]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(Theta:real^3->real^3)((K:real^2->real^3) z) = Gam z`] THEN
  REWRITE_TAC[ASSUME `frechet_derivative (Theta':real^3->real^3) (at ((Gam:real^2->real^3) z)) = DT`;
              ASSUME `(DT:real^3->real^3)(schy_X v kin ((Gam:real^2->real^3) z)) = W`;
              ASSUME `frechet_derivative (\y. lift(schy_F y)) (at ((K:real^2->real^3) z)) = L`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `cc = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(L:real^3->real^1)((DT:real^3->real^3)
                    (frechet_derivative (Gam:real^2->real^3) (at z) a) + cc % W) = vec 0`
    MP_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_CMUL; DROP_VEC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    UNDISCH_TAC `&0 < drop((L:real^3->real^1) W)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  UNDISCH_TAC `(DT:real^3->real^3)(frechet_derivative (Gam:real^2->real^3) (at z) a) + cc % W =
               vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

(* The model maps are immersions: mb by its A and B coordinates; ma by B0  *)
(* (constant along the hyperbola) and the height along the hyperbola.      *)

let SCHY_IMM_MB = prove
 (`!(c':real^2->real^2) e lam t0 kap (z:real^2) a.
     &0 < lam /\ &2 * lam < e /\ lam <= &1 /\ &0 < z$1 /\ &0 < kap /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                kap <= abs(schy_bzd c' e tau)) /\
     abs(&2 * z$1 * z$2) <= t0 /\
     schy_mb c' e (schy_Ac e lam) differentiable (at z) /\
     frechet_derivative (schy_mb c' e (schy_Ac e lam)) (at z) a = vec 0
     ==> a = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_Acd e lam ((z:real^2)$1) * a$1 = &0 /\
                schy_bzd c' e (--(&2 * z$1 * z$2)) * --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2)) = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`schy_mb c' e (schy_Ac e lam)`; `z:real^2`; `a:real^2`; `1`;
                     `schy_Acd e lam ((z:real^2)$1) * (a:real^2)$1`] SCHY_DIRDERIV_COMP) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH; VEC_COMPONENT] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[schy_mb; VECTOR_3] THEN MATCH_MP_TAC SCHY_AC_DIRDER THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      MP_TAC(ISPECL [`schy_mb c' e (schy_Ac e lam)`; `z:real^2`; `a:real^2`; `2`;
                     `schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) *
                      --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2))`] SCHY_DIRDERIV_COMP) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH; VEC_COMPONENT] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[schy_mb; VECTOR_3] THEN MATCH_MP_TAC SCHY_B0_DIRDER THEN
        EXISTS_TAC `t0:real` THEN ASM_SIMP_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2)$1 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_Acd e lam ((z:real^2)$1) * (a:real^2)$1 = &0` THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    MP_TAC(CONJUNCT2(MP (SPEC `(z:real^2)$1` (ASSUME
      `!t. &0 < t ==> (schy_Ac e lam has_real_derivative schy_Acd e lam t) (atreal t) /\
                      &0 < schy_Acd e lam t`)) (ASSUME `&0 < (z:real^2)$1`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) = &0)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(MP (SPEC `--(&2 * (z:real^2)$1 * z$2)` (ASSUME
      `!tau. abs tau <= t0
             ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                 kap <= abs(schy_bzd c' e tau)`))
      (ONCE_REWRITE_RULE[GSYM REAL_ABS_NEG] (ASSUME `abs(&2 * (z:real^2)$1 * z$2) <= t0`)))) THEN
    MP_TAC(ASSUME `&0 < kap`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2)$2 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) *
                 --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2)) = &0` THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_MUL_LZERO; REAL_ADD_LID; REAL_NEG_EQ_0;
                    REAL_OF_NUM_EQ; ARITH_EQ] THEN
    MP_TAC(ASSUME `&0 < (z:real^2)$1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT]);;

let SCHY_IMM_MA = prove
 (`!(c':real^2->real^2) e lam t0 kap P wq (z:real^2) a.
     &0 < lam /\ &64 * lam < e /\ &16 * e < &1 /\ &0 < kap /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                kap <= abs(schy_bzd c' e tau)) /\
     abs(&2 * z$1 * z$2) <= t0 /\ abs(&2 * z$1 * z$2) < wq /\ abs(z$2) < wq /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     sqrt e / &2 <= z$1 /\
     schy_ma c' e lam (schy_bec e lam) differentiable (at z) /\
     frechet_derivative (schy_ma c' e lam (schy_bec e lam)) (at z) a = vec 0
     ==> a = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^2)$1` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME) [`&0 < sqrt e`; `sqrt e / &2 <= (z:real^2)$1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `DM = frechet_derivative (schy_ma c' e lam (schy_bec e lam)) (at z)` THEN
  SUBGOAL_THEN `linear(DM:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "DM" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v = vector[(z:real^2)$1; --(z$2)]:real^2` THEN
  ABBREV_TAC `N = &2 * (z:real^2)$1 pow 2 + &2 * (&1 - schy_bec e lam (z$1)) * z$2 pow 2 +
                  z$1 * schy_becd e lam (z$1) * (z$2 pow 2 - lam * schy_B0 c' e z pow 2)` THEN
  SUBGOAL_THEN `((DM:real^2->real^3) v)$3 = N / lam /\
                schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) *
                --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2)) = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "DM" THEN MATCH_MP_TAC SCHY_DIRDERIV_COMP THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REWRITE_TAC[schy_ma; VECTOR_3] THEN
      EXPAND_TAC "N" THEN EXPAND_TAC "v" THEN MATCH_MP_TAC SCHY_YA_HYPDER THEN
      EXISTS_TAC `t0:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`schy_ma c' e lam (schy_bec e lam)`; `z:real^2`; `a:real^2`; `2`;
                     `schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) *
                      --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2))`] SCHY_DIRDERIV_COMP) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH; VEC_COMPONENT] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[schy_ma; VECTOR_3] THEN MATCH_MP_TAC SCHY_B0_DIRDER THEN
        EXISTS_TAC `t0:real` THEN ASM_SIMP_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) = &0)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(MP (SPEC `--(&2 * (z:real^2)$1 * z$2)` (ASSUME
      `!tau. abs tau <= t0
             ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                 kap <= abs(schy_bzd c' e tau)`))
      (ONCE_REWRITE_RULE[GSYM REAL_ABS_NEG] (ASSUME `abs(&2 * (z:real^2)$1 * z$2) <= t0`)))) THEN
    MP_TAC(ASSUME `&0 < kap`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2)$1 * (z:real^2)$2 + z$1 * a$2 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_bzd c' e (--(&2 * (z:real^2)$1 * z$2)) *
                 --(&2 * ((a:real^2)$1 * z$2 + z$1 * a$2)) = &0` THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_NEG_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < N` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(schy_becd e lam ((z:real^2)$1) *
                      (z$2 pow 2 - lam * schy_B0 c' e z pow 2)) <= P * wq pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      SUBGOAL_THEN `(z:real^2)$2 pow 2 <= wq pow 2 /\
                    lam * schy_B0 c' e z pow 2 <= wq pow 2 /\
                    &0 <= lam * schy_B0 c' e z pow 2` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
          MP_TAC(ASSUME `abs((z:real^2)$2) < wq`) THEN REAL_ARITH_TAC;
          REWRITE_TAC[schy_B0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[REAL_ABS_NEG];
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          MP_TAC(ASSUME `&0 < lam`) THEN REAL_ARITH_TAC];
        MP_TAC(SPEC `(z:real^2)$2` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `--((z:real^2)$1 * (P * wq pow 2)) <=
                  z$1 * schy_becd e lam (z$1) * (z$2 pow 2 - lam * schy_B0 c' e z pow 2)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&0 < (z:real^2)$1`;
        `abs(schy_becd e lam ((z:real^2)$1) *
             (z$2 pow 2 - lam * schy_B0 c' e z pow 2)) <= P * wq pow 2`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2)$1 * (P * wq pow 2) <= z$1 * (sqrt e / &4) /\
                  z$1 * sqrt e <= z$1 * (&2 * z$1) /\
                  &0 <= (&1 - schy_bec e lam (z$1)) * z$2 pow 2 /\
                  &0 < z$1 * sqrt e` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `&0 < (z:real^2)$1`) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&0 < (z:real^2)$1`; `sqrt e / &2 <= (z:real^2)$1`] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MP_TAC(SPEC `(z:real^2)$1` (ASSUME
          `!t. &0 <= schy_bec e lam t /\ schy_bec e lam t <= &1`)) THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "N" THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`--((z:real^2)$1 * (P * wq pow 2)) <=
       z$1 * schy_becd e lam (z$1) * (z$2 pow 2 - lam * schy_B0 c' e z pow 2)`;
      `(z:real^2)$1 * (P * wq pow 2) <= z$1 * (sqrt e / &4)`;
      `(z:real^2)$1 * sqrt e <= z$1 * (&2 * z$1)`;
      `&0 <= (&1 - schy_bec e lam ((z:real^2)$1)) * z$2 pow 2`;
      `&0 < (z:real^2)$1 * sqrt e`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a = ((a:real^2)$1 / (z:real^2)$1) % (v:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
                                    VECTOR_2] THEN
    MP_TAC(ASSUME `(a:real^2)$1 * (z:real^2)$2 + z$1 * a$2 = &0`) THEN
    MP_TAC(ASSUME `&0 < (z:real^2)$1`) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `((a:real^2)$1 / (z:real^2)$1) * (N / lam) = &0` MP_TAC THENL
   [SUBGOAL_THEN `(DM:real^2->real^3)(((a:real^2)$1 / (z:real^2)$1) % v) =
                  ((a:real^2)$1 / z$1) % (DM:real^2->real^3) v` MP_TAC THENL
     [MATCH_MP_TAC LINEAR_CMUL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `a = ((a:real^2)$1 / (z:real^2)$1) % (v:real^2)`)] THEN
    REWRITE_TAC[ASSUME `(DM:real^2->real^3) a = vec 0`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$3`) THEN
    REWRITE_TAC[VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[ASSUME `((DM:real^2->real^3) v)$3 = N / lam`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `a = ((a:real^2)$1 / (z:real^2)$1) % (v:real^2)`)) THEN
  REWRITE_TAC[REAL_ENTIRE] THEN
  SUBGOAL_THEN `~(N / lam = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
  SUBGOAL_THEN `~((z:real^2)$1 = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ASSUME `&0 < (z:real^2)$1`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(a:real^2)$2 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^2)$1 * (z:real^2)$2 + z$1 * a$2 = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ENTIRE] THEN
    MP_TAC(ASSUME `&0 < (z:real^2)$1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT]);;

(* Transversality of the strip to the shear field X (hypothesis of          *)
(* SCHY_SHEAR): box part by the coordinates of sbox and X = e3, model parts *)
(* by SCHY_TRANSV_C and the immersions SCHY_IMM_MA / SCHY_IMM_MB.            *)

let SCHY_GM_TRANSV = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' s1 ds rho1 rho2 ts wq eps eps0 t0 kap P.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     (!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2) /\
     B * lam * H < rho2 / &2 /\
     &0 < eps /\ eps <= e /\ &0 < eps0 /\ eps0 <= e /\
     &8 * (wq + B * lam * H + ds + eps + eps0 + lam) <= rho1 /\
     wq + &2 * (B * lam * H + ds) < sqrt e /\
     &0 < kap /\ wq <= t0 /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                kap <= abs(schy_bzd c' e tau)) /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2)
     ==> !z a cc. z IN schy_Q e lam wq /\
                  frechet_derivative (schy_gm Theta c' e lam) (at z) a +
                  cc % schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))
                         (schy_gm Theta c' e lam z) = vec 0
                  ==> a = vec 0 /\ cc = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`] SCHY_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`] SCHY_GM_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CD_FACTS) THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `a:real^2`; `cc:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `z:real^2`] SCHY_Q_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_gm (Theta:real^3->real^3) c' e lam differentiable (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `schy_Q e lam wq` THEN
    ASM_REWRITE_TAC[SCHY_Q_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt e / &2 <= schy_sq e lam (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[schy_sq] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&1)` THENL
   [SUBGOAL_THEN `!w. w IN schy_Q e lam wq INTER {w:real^2 | w$1 < schy_sq e lam (&7 / &8)}
                     ==> schy_gm (Theta:real^3->real^3) c' e lam w = schy_sbox w` ASSUME_TAC THENL
     [X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                     `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                     `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `ts:real`; `wq:real`; `w:real^2`] SCHY_GM_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `z IN schy_Q e lam wq INTER {w:real^2 | w$1 < schy_sq e lam (&7 / &8)}`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`(z:real^2)$1 <= schy_sq e lam (&1)`; `schy_sq e lam (&1) < schy_sq e lam (&7 / &8)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `schy_sbox differentiable (at z)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[OPEN_UNIV; IN_UNIV; SCHY_SBOX_SMOOTH];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`schy_sbox`; `schy_gm (Theta:real^3->real^3) c' e lam`;
                   `schy_Q e lam wq INTER {w:real^2 | w$1 < schy_sq e lam (&7 / &8)}`;
                   `z:real^2`] SCHY_FD_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[SCHY_Q_OPEN; OPEN_HALFSPACE_COMPONENT_LT];
        X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]];
      STRIP_TAC] THEN
    SUBGOAL_THEN `schy_gm (Theta:real^3->real^3) c' e lam z = schy_sbox z` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`] SCHY_RHO_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) (schy_sbox z) =
                  basis 3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e) x = &0
             ==> schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e)) x = basis 3`)
        (concl th))) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                     `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                     `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `s1:real`; `ds:real`; `rho1:real`; `rho2:real`; `wq:real`;
                     `eps:real`; `eps0:real`; `z:real^2`; `&0`] SCHY_BOX_KIN0) THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_0] THEN REWRITE_TAC[schy_sh] THEN
      MP_TAC(SPEC `(z:real^2)$1` (ASSUME `!t. &0 <= schy_rho e lam eps t`)) THEN
      MP_TAC(ASSUME `&0 < eps0`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(frechet_derivative schy_sbox (at z) a)$1 = --((a:real^2)$1) /\
                  (frechet_derivative schy_sbox (at z) a)$2 = (a:real^2)$2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SCHY_DIRDERIV_COMP THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[schy_sbox; VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^2) = vec 0` ASSUME_TAC THENL
     [UNDISCH_TAC `frechet_derivative (schy_gm (Theta:real^3->real^3) c' e lam) (at z) a +
                   cc % schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))
                          (schy_gm Theta c' e lam z) = vec 0` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VEC_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frechet_derivative (schy_gm (Theta:real^3->real^3) c' e lam) (at z) a +
                 cc % schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))
                        (schy_gm Theta c' e lam z) = vec 0` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `frechet_derivative schy_sbox (at z)` LINEAR_0) THEN
    ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VECTOR_ADD_LID; VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH];
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `rho2:real`; `z:real^2`]
      SCHY_GM_MODEL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `m:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))] THEN
    ASM_CASES_TAC `(z:real^2)$1 <= schy_sq e lam (&17 / &32)` THENL
     [MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                     `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`;
                     `schy_gm (Theta:real^3->real^3) c' e lam`;
                     `schy_ma c' e lam (schy_bec e lam)`;
                     `schy_Q e lam wq INTER {w:real^2 | schy_sq e lam (&1) < w$1} INTER
                      {w:real^2 | w$1 < schy_sq e lam (&33 / &64)}`;
                     `z:real^2`; `a:real^2`; `cc:real`] SCHY_TRANSV_C) THEN
      ANTS_TAC THENL
       [ALL_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_IMM_MA THEN
        MAP_EVERY EXISTS_TAC [`c':real^2->real^2`; `e:real`; `lam:real`; `t0:real`;
                              `kap:real`; `P:real`; `wq:real`; `z:real^2`] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [MAP_EVERY (MP_TAC o ASSUME)
           [`abs(&2 * (z:real^2)$1 * z$2) < wq`; `wq <= t0`] THEN REAL_ARITH_TAC;
          MAP_EVERY (MP_TAC o ASSUME)
           [`sqrt e / &2 <= schy_sq e lam (&1)`;
            `~((z:real^2)$1 <= schy_sq e lam (&1))`] THEN REAL_ARITH_TAC]] THEN
      SUBGOAL_THEN `!w. w IN schy_Q e lam wq INTER {w:real^2 | schy_sq e lam (&1) < w$1} INTER
                        {w:real^2 | w$1 < schy_sq e lam (&33 / &64)}
                        ==> schy_ma c' e lam (schy_bec e lam) w IN sch5v_slab H /\
                            schy_gm Theta c' e lam w = Theta(schy_ma c' e lam (schy_bec e lam) w) /\
                            schy_F(schy_ma c' e lam (schy_bec e lam) w) = &0 /\
                            (schy_ma c' e lam (schy_bec e lam) w)$1 pow 2 +
                            (schy_ma c' e lam (schy_bec e lam) w)$2 pow 2 =
                            sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) w)$3)) /\
                            --(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) w)$3 /\
                            (schy_ma c' e lam (schy_bec e lam) w)$3 <= --(&1 / &2)`
      (LABEL_TAC "PW") THENL
       [X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `w:real^2`] SCHY_GM_PIECES) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[schy_F] THEN
        UNDISCH_TAC `(schy_ma c' e lam (schy_bec e lam) w)$1 pow 2 +
                     (schy_ma c' e lam (schy_bec e lam) w)$2 pow 2 =
                     sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) w)$3))` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "PW" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`~((z:real^2)$1 <= schy_sq e lam (&1))`; `(z:real^2)$1 <= schy_sq e lam (&17 / &32)`;
          `schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64)`] THEN
        REAL_ARITH_TAC;
        STRIP_TAC] THEN
      SUBGOAL_THEN `m = schy_ma c' e lam (schy_bec e lam) z` ASSUME_TAC THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) m = Theta(schy_ma c' e lam (schy_bec e lam) z)`
        MP_TAC THENL
         [UNDISCH_TAC `schy_gm (Theta:real^3->real^3) c' e lam z = Theta m` THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `Theta':real^3->real^3`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MP_TAC(ASSUME `&5 <= H`) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[SCHY_Q_OPEN] THEN
        MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
          REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`~((z:real^2)$1 <= schy_sq e lam (&1))`; `(z:real^2)$1 <= schy_sq e lam (&17 / &32)`;
          `schy_sq e lam (&17 / &32) < schy_sq e lam (&33 / &64)`] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
        USE_THEN "PW" (MP_TAC o SPEC `w:real^2`) THEN ASM_SIMP_TAC[];
        MP_TAC(SPEC `--((schy_ma c' e lam (schy_bec e lam) z)$3)` SCHY_PROFILE_LE1) THEN
        UNDISCH_TAC `(schy_ma c' e lam (schy_bec e lam) z)$1 pow 2 +
                     (schy_ma c' e lam (schy_bec e lam) z)$2 pow 2 =
                     sch_cap_profile(--((schy_ma c' e lam (schy_bec e lam) z)$3))` THEN
        REAL_ARITH_TAC;
        MAP_EVERY (MP_TAC o ASSUME)
         [`--(&5 / &4) < (schy_ma c' e lam (schy_bec e lam) z)$3`;
          `(schy_ma c' e lam (schy_bec e lam) z)$3 <= --(&1 / &2)`; `&5 <= H`] THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `--((m:real^3)$3) < &7 / &8 \/
                     dist(schy_gm (Theta:real^3->real^3) c' e lam z,schy_lpt e) < rho2` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `schy_gm (Theta:real^3->real^3) c' e lam z =
                      Theta(schy_ma c' e lam (schy_bec e lam) z)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[]];
     MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                     `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`;
                     `schy_gm (Theta:real^3->real^3) c' e lam`;
                     `schy_mb c' e (schy_Ac e lam)`;
                     `schy_Q e lam wq INTER {w:real^2 | schy_sq e lam (&17 / &32) < w$1}`;
                     `z:real^2`; `a:real^2`; `cc:real`] SCHY_TRANSV_C) THEN
      ANTS_TAC THENL
       [ALL_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_IMM_MB THEN
        MAP_EVERY EXISTS_TAC [`c':real^2->real^2`; `e:real`; `lam:real`; `t0:real`;
                              `kap:real`; `z:real^2`] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [MAP_EVERY (MP_TAC o ASSUME)
           [`sqrt e / &2 <= schy_sq e lam (&1)`; `&0 < sqrt e`;
            `~((z:real^2)$1 <= schy_sq e lam (&1))`] THEN REAL_ARITH_TAC;
          MAP_EVERY (MP_TAC o ASSUME)
           [`abs(&2 * (z:real^2)$1 * z$2) < wq`; `wq <= t0`] THEN REAL_ARITH_TAC]] THEN
      SUBGOAL_THEN `!w. w IN schy_Q e lam wq INTER {w:real^2 | schy_sq e lam (&17 / &32) < w$1}
                        ==> schy_mb c' e (schy_Ac e lam) w IN sch5v_slab H /\
                            schy_gm Theta c' e lam w = Theta(schy_mb c' e (schy_Ac e lam) w) /\
                            schy_F(schy_mb c' e (schy_Ac e lam) w) = &0 /\
                            (schy_mb c' e (schy_Ac e lam) w)$1 pow 2 +
                            (schy_mb c' e (schy_Ac e lam) w)$2 pow 2 =
                            sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) w)$3)) /\
                            --(&5 / &4) < (schy_mb c' e (schy_Ac e lam) w)$3 /\
                            (schy_mb c' e (schy_Ac e lam) w)$3 <= --(&1 / &2)`
      (LABEL_TAC "PWC") THENL
       [X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                     `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                     `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                     `Theta':real^3->real^3`; `ts:real`; `wq:real`; `w:real^2`] SCHY_GM_PIECES) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[schy_F] THEN
        UNDISCH_TAC `(schy_mb c' e (schy_Ac e lam) w)$1 pow 2 +
                     (schy_mb c' e (schy_Ac e lam) w)$2 pow 2 =
                     sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) w)$3))` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "PWC" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `~((z:real^2)$1 <= schy_sq e lam (&17 / &32))`) THEN REAL_ARITH_TAC;
        STRIP_TAC] THEN
      SUBGOAL_THEN `m = schy_mb c' e (schy_Ac e lam) z` ASSUME_TAC THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) m = Theta(schy_mb c' e (schy_Ac e lam) z)`
        MP_TAC THENL
         [UNDISCH_TAC `schy_gm (Theta:real^3->real^3) c' e lam z = Theta m` THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `Theta':real^3->real^3`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MP_TAC(ASSUME `&5 <= H`) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[SCHY_Q_OPEN] THEN
        REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `~((z:real^2)$1 <= schy_sq e lam (&17 / &32))`) THEN REAL_ARITH_TAC;
        X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
        USE_THEN "PWC" (MP_TAC o SPEC `w:real^2`) THEN ASM_SIMP_TAC[];
        MP_TAC(SPEC `--((schy_mb c' e (schy_Ac e lam) z)$3)` SCHY_PROFILE_LE1) THEN
        UNDISCH_TAC `(schy_mb c' e (schy_Ac e lam) z)$1 pow 2 +
                     (schy_mb c' e (schy_Ac e lam) z)$2 pow 2 =
                     sch_cap_profile(--((schy_mb c' e (schy_Ac e lam) z)$3))` THEN
        REAL_ARITH_TAC;
        MAP_EVERY (MP_TAC o ASSUME)
         [`--(&5 / &4) < (schy_mb c' e (schy_Ac e lam) z)$3`;
          `(schy_mb c' e (schy_Ac e lam) z)$3 <= --(&1 / &2)`; `&5 <= H`] THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `--((m:real^3)$3) < &7 / &8 \/
                     dist(schy_gm (Theta:real^3->real^3) c' e lam z,schy_lpt e) < rho2` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `schy_gm (Theta:real^3->real^3) c' e lam z =
                      Theta(schy_mb c' e (schy_Ac e lam) z)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The cancellation with explicit parameters.  The strip, the                *)
(* shear data and the field satisfy all hypotheses of SCHY_SHEAR; the new   *)
(* height hf + Tf has no critical point on Qc (SCHY_HS_NOCRIT), so          *)
(* SCHY_CRIT_SHEAR applies.  The saddle vec 0 = Gam(vec 0) lies in L.       *)
(* ------------------------------------------------------------------------- *)

let SCHY_CANCEL_CORE = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' S1 S2 (g1:real^3->real^3) g1' s1 ds rho1 rho2 ts wq wb
    eps eps0 dc t0 kap P.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\ closed S1 /\ closed S2 /\
     sch_neck g1 g1' /\ IMAGE g1 (sphere(vec 0,&1)) = S1 /\
     &0 < ds /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < s1 /\ s1 < &1 /\ &0 <= rho1 /\ rho1 < rho2 /\
     (!y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
          ==> dist(sch5v_pr y,--basis 1) < delta1) /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     (!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
     &0 < wq /\ wq <= ts /\ &100 * wq pow 2 <= lam /\
     (!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho2 / &2) /\
     B * lam * H < rho2 / &2 /\
     &0 < eps /\ eps <= e /\ eps <= lam / &100 /\ &0 < eps0 /\ eps0 <= e /\ eps0 <= lam / &100 /\
     &8 * (wq + B * lam * H + ds + eps + eps0 + lam) <= rho1 /\
     &2 * wq + &3 * (B * lam + lam) < rho0 / &2 /\
     &2 * wq + &3 * (B * lam + lam) < sqrt e /\
     wq + &2 * (B * lam * H + ds) < sqrt e /\
     wq + &2 * (&2 * B * lam + lam) < sqrt e /\
     (!z q. norm z <= &1 /\ dist(c z,q) < dc ==> q IN IMAGE c (ball(vec 0,&2))) /\
     (B + &2) * (&13 / &10 * lam) + B * (&2 * lam + (B + &2) * (&13 / &10 * lam)) +
     B * (&2 * lam) < dc /\
     &2 * lam + (B + &2) * (&13 / &10 * lam) < lam * H /\
     &0 < kap /\ wq <= t0 /\ t0 < ts /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                kap <= abs(schy_bzd c' e tau)) /\
     (!tau. abs tau <= t0 /\ ~(tau = &0) ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau) /\
     (!t. abs(schy_becd e lam t) <= P) /\ P * wq pow 2 <= sqrt e / &4 /\
     (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
     (!t. schy_psid e lam eps t < &0) /\ &0 < wb /\ wb < wq
     ==> ?Phi Phi' L. diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ compact L /\
                      (!x. ~(x IN L) ==> Phi x = x) /\ vec 0 IN L /\ vec 0 IN S1 /\
                      (!t. sch_crit (Phi o g1) t <=> sch_crit g1 t /\ ~(g1 t IN L))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `s1:real`; `rho1:real`; `rho2:real`] SCHY_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `eps0:real`; `wb:real`; `wq:real`]
    SCHY_TF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!a b. abs a < wq /\ abs b < wq /\ schy_bz c' e a = schy_bz c' e b ==> a = b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`schy_bz c' e`; `schy_bzd c' e`; `--t0`; `t0:real`; `kap:real`]
      SCHY_DERIV_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
        `!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                                  kap <= abs(schy_bzd c' e tau)`) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME) [`abs a < wq`; `abs b < wq`; `wq <= t0`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))`;
                 `schy_Q e lam wq`; `schy_Qc e lam wb`; `schy_gm (Theta:real^3->real^3) c' e lam`;
                 `schy_sh e lam eps eps0`; `schy_Tf e lam eps wb`; `S1:real^3->bool`]
    SCHY_SHEAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[SCHY_Q_OPEN];
      MATCH_MP_TAC SCHY_GM_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`;
                            `c:real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`;
                            `delta1:real`; `H:real`; `Theta':real^3->real^3`; `ts:real`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `eps0:real`; `wb:real`; `wq:real`]
        SCHY_TF_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `schy_Q e lam wq` o CONJUNCT1) THEN
      REWRITE_TAC[SCHY_Q_OPEN] THEN SIMP_TAC[];
      MP_TAC(SPECL [`e:real`; `lam:real`; `eps:real`; `eps0:real`; `wb:real`; `wq:real`]
        SCHY_TF_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `schy_Q e lam wq` o CONJUNCT1) THEN
      REWRITE_TAC[SCHY_Q_OPEN] THEN SIMP_TAC[];
      X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `S1:real^3->bool`; `S2:real^3->bool`]
        SCHY_GM_S1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&2 * wq + &3 * (B * lam + lam) < sqrt e`; `&0 < wq`; `&0 <= B * lam`; `&0 < lam`] THEN
        REAL_ARITH_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!z. ~(z IN schy_Qc e lam wb) ==> schy_Tf e lam eps wb z = &0`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCHY_GM_INJ THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`;
                            `c:real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`;
                            `delta1:real`; `H:real`; `Theta':real^3->real^3`; `ts:real`;
                            `P:real`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^2`; `t:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(s:real^2)$1 <= schy_sq e lam (&1)` THENL
       [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `S1:real^3->bool`; `S2:real^3->bool`; `s1:real`; `ds:real`;
                       `rho1:real`; `rho2:real`; `ts:real`; `wq:real`; `eps:real`; `eps0:real`]
          SCHY_GM_BOXCOL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o SPECL [`s:real^2`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `abs t < &2 * schy_sh e lam eps eps0 s`) THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `S1:real^3->bool`; `S2:real^3->bool`; `s1:real`;
                       `rho1:real`; `rho2:real`; `ts:real`; `wq:real`; `eps:real`; `eps0:real`;
                       `dc:real`] SCHY_GM_CHARTCOL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o SPECL [`s:real^2`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `~((s:real^2)$1 <= schy_sq e lam (&1))`) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC SCHY_GM_TRANSV THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`;
                            `c:real^2->real^2`; `B:real`; `rho0:real`; `delta1:real`;
                            `ds:real`; `ts:real`; `eps:real`; `eps0:real`;
                            `t0:real`; `kap:real`; `P:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `L:real^3->bool`] THEN
  SUBGOAL_THEN `vec 0:real^2 IN schy_Q e lam wq` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `schy_Qc e lam wb SUBSET schy_Q e lam wq`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_gm (Theta:real^3->real^3) c' e lam (vec 0) = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `vec 0:real^2`] SCHY_GM_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[VEC_COMPONENT] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[schy_sbox; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `schy_gm (Theta:real^3->real^3) c' e lam (vec 0) = vec 0`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `schy_gm (Theta:real^3->real^3) c' e lam (vec 0) = vec 0`)) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `S1:real^3->bool`; `S2:real^3->bool`]
      SCHY_GM_S1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&2 * wq + &3 * (B * lam + lam) < sqrt e`; `&0 < wq`; `&0 <= B * lam`; `&0 < lam`] THEN
      REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SCHY_CRIT_SHEAR THEN
    MAP_EVERY EXISTS_TAC [`g1':real^3->real^3`; `Phi':real^3->real^3`; `schy_Q e lam wq`;
                          `schy_Qc e lam wb`;
                          `schy_gm (Theta:real^3->real^3) c' e lam`;
                          `\z:real^2. schy_hf c' e lam z + schy_bw wb (z$2) * schy_rho e lam eps (z$1)`] THEN
    ASM_REWRITE_TAC[SCHY_Q_OPEN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCHY_GM_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`;
                            `c:real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`;
                            `delta1:real`; `H:real`; `Theta':real^3->real^3`; `ts:real`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `S1:real^3->bool`; `S2:real^3->bool`]
        SCHY_GM_S1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&2 * wq + &3 * (B * lam + lam) < sqrt e`; `&0 < wq`; `&0 <= B * lam`; `&0 < lam`] THEN
        REAL_ARITH_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPEC `schy_X v (schy_kin Theta Theta' H s1 rho1 rho2 (schy_lpt e))`
        SCH5V_FLOW_HEIGHT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `ts:real`; `wq:real`; `s:real^2`] SCHY_GM_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
      REWRITE_TAC[LIFT_DROP; schy_Tf];
      X_GEN_TAC `s:real^2` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`e:real`; `lam:real`; `wq:real`; `s:real^2`] SCHY_Q_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `schy_Qc e lam wb SUBSET schy_Q e lam wq`)) THEN ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
      MATCH_MP_TAC SCHY_HS_NOCRIT THEN
      MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `ts:real`; `t0:real`] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
          `!tau. abs tau < ts ==> schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\ P tau`)
          (concl th))) THEN ASM_SIMP_TAC[];
        CONJ_TAC THENL
         [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
            `!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                                      kap <= abs(schy_bzd c' e tau)`) (concl th))) THEN
          ASM_SIMP_TAC[];
          UNDISCH_TAC `(s:real^2) IN schy_Qc e lam wb` THEN
          REWRITE_TAC[schy_Qc; IN_ELIM_THM] THEN STRIP_TAC THEN
          SUBGOAL_THEN `abs(&2 * (s:real^2)$1 * s$2) <= &2 * (&1 / &2) * wb` MP_TAC THENL
           [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
            MAP_EVERY (MP_TAC o ASSUME)
             [`abs((s:real^2)$1) < &1 / &2`; `abs((s:real^2)$2) <= wb`] THEN REAL_ARITH_TAC;
            MAP_EVERY (MP_TAC o ASSUME) [`wb < wq`; `wq <= t0`] THEN REAL_ARITH_TAC]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Choices of the parameters and the H3 headline.  Helpers: a                *)
(* uniform neighbourhood dc of c(cball 1) inside c(ball 2), the continuity  *)
(* radius of c' at P0, the rho2 property of the chart, a bound on becd.     *)
(* ------------------------------------------------------------------------- *)

let SCHY_CHOICE_DC = prove
 (`!(c:real^2->real^2) c'.
     sch_ball c c'
     ==> ?dc. &0 < dc /\
              !z q. norm z <= &1 /\ dist(c z,q) < dc ==> q IN IMAGE c (ball(vec 0,&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball; diffeomorphism_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (c:real^2->real^2) (cball(vec 0,&1))`;
                 `(:real^2) DIFF IMAGE (c:real^2->real^2) (ball(vec 0,&2))`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; NOT_IN_EMPTY; IN_IMAGE;
                  IN_CBALL_0; IN_BALL_0] THEN
      MESON_TAC[REAL_ARITH `x <= &1 ==> x < &2`]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(c:real^2->real^2) z`; `q:real^2`] o check (fun th ->
      can (term_match [] `!x y. x IN s /\ y IN t ==> d <= dist(x:real^2,y)`) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
      ASM_REAL_ARITH_TAC]]);;

let SCHY_CHOICE_DELTA = prove
 (`!(c:real^2->real^2) c' e delta1.
     sch_ball c c' /\ c(--basis 1) = vector[--(sqrt e); &0] /\ &0 < delta1
     ==> ?dl. &0 < dl /\
              !w. w IN ball(vec 0,&2) /\ dist(c w,vector[--(sqrt e); &0]) < dl
                  ==> dist(w,--basis 1) < delta1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    GEN_REWRITE_RULE I [sch_ball] o check (fun th -> can (term_match []
      `sch_ball (c:real^2->real^2) c'`) (concl th))) THEN
  SUBGOAL_THEN `--basis 1 IN ball(vec 0:real^2,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2)(vector[--(sqrt e); &0]) = --basis 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `vector[--(sqrt e); &0]:real^2`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':real^2->real^2) continuous (at (vector[--(sqrt e); &0]))` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (c:real^2->real^2) (ball(vec 0,&2))` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `vector[--(sqrt e); &0]:real^2`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `delta1:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c':real^2->real^2)((c:real^2->real^2) w) = w` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x. x IN ball(vec 0:real^2,&2) ==> (c':real^2->real^2)(c x) = x`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SCHY_RHO2_PROP = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' dl rho2.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     (!w. w IN ball(vec 0,&2) /\ dist(c w,vector[--(sqrt e); &0]) < dl
          ==> dist(w,--basis 1) < delta1) /\
     &2 * rho2 <= dl /\ B * lam * H < rho2 / &2
     ==> !y. y IN sch5v_slab H /\ dist(Theta y,schy_lpt e) < rho2
             ==> dist(sch5v_pr y,--basis 1) < delta1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sch5v_slab H` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM; IN_BALL_0; sch5v_pr; vector_norm; DOT_2; VECTOR_2] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`; `rho0:real`; `e:real`; `c:real^2->real^2`;
                 `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `y:real^3`] SCHY_THETA_DISP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `B * lam * abs((y:real^3)$3) <= B * lam * H` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN sch5v_slab H` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Theta:real^3->real^3) y`; `schy_lpt e`] SCHY_PR_DIST) THEN
  SUBGOAL_THEN `sch5v_pr(schy_lpt e) = vector[--(sqrt e); &0]` SUBST1_TAC THENL
   [REWRITE_TAC[sch5v_pr; schy_lpt; VECTOR_3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(c:real^2->real^2)(sch5v_pr y)`; `sch5v_pr((Theta:real^3->real^3) y)`;
                 `vector[--(sqrt e); &0]:real^2`] DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(c:real^2->real^2)(sch5v_pr y)`; `sch5v_pr((Theta:real^3->real^3) y)`]
    DIST_SYM) THEN
  MP_TAC(ISPECL [`sch5v_pr((Theta:real^3->real^3) y)`; `(c:real^2->real^2)(sch5v_pr y)`]
    DIST_POS_LE) THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [`dist((Theta:real^3->real^3) y,schy_lpt e) < rho2`; `&2 * rho2 <= dl`;
    `B * lam * H < rho2 / &2`] THEN
  REAL_ARITH_TAC);;

let SCHY_BECD_BOUND = prove
 (`!e lam. &0 < lam /\ &2 * lam < e /\ lam <= &1
           ==> ?P. &0 < P /\ !t. abs(schy_becd e lam t) <= P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CFUN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`schy_bec e lam`; `schy_becd e lam`; `schy_sq e lam (&9 / &16)`;
                 `schy_sq e lam (&17 / &32)`] SCHY_DERIV_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC `t <= schy_sq e lam (&9 / &16) \/ schy_sq e lam (&17 / &32) <= t` THENL
   [SUBGOAL_THEN `schy_becd e lam t = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t <= schy_sq e lam (&9 / &16) \/ schy_sq e lam (&17 / &32) <= t
             ==> schy_becd e lam t = &0`) (concl th))) THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The inner choices: given the lam-free data (ts, t0, kap, dl, dc, ds, s1,  *)
(* d2) and lam small, choose P, eps1, wq, wb, eps, eps0 and apply the core. *)

let SCHY_CANCEL_INNER = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta' S1 S2 (g1:real^3->real^3) g1' ts t0 kap dl dc s1 ds d2.
     schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\ closed S1 /\ closed S2 /\
     sch_neck g1 g1' /\ IMAGE g1 (sphere(vec 0,&1)) = S1 /\
     &0 < ts /\
     (!tau. abs tau < ts
            ==> schy_gam e tau IN IMAGE c (ball(vec 0,&2)) /\
                c(c'(schy_gam e tau)) = schy_gam e tau /\
                c'(schy_gam e tau) IN sphere(vec 0,&1) /\
                (c'(schy_gam e tau))$1 < &0 /\
                dist(schy_gam e tau,vector[--(sqrt e); &0]) < rho0 / &2) /\
     &0 < t0 /\ t0 < ts /\ &0 < kap /\
     (!tau. abs tau <= t0
            ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                kap <= abs(schy_bzd c' e tau) /\ abs(schy_bzd c' e tau) <= &3 * kap /\
                abs(schy_bz c' e tau) <= &3 * kap * abs tau /\
                &0 <= schy_bz c' e tau * schy_bzd c' e tau * tau /\
                (~(tau = &0) ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau)) /\
     &0 < dl /\
     (!w. w IN ball(vec 0,&2) /\ dist(c w,vector[--(sqrt e); &0]) < dl
          ==> dist(w,--basis 1) < delta1) /\
     &0 < dc /\
     (!z q. norm z <= &1 /\ dist(c z,q) < dc ==> q IN IMAGE c (ball(vec 0,&2))) /\
     &0 < ds /\ ds <= dl / &192 /\ ds <= sqrt e / &8 /\
     &0 < s1 /\ s1 < &1 / &4 /\
     (!z. &1 <= norm z /\ norm z pow 2 < &1 + &2 * s1 ==> dist(c z,c(inv(norm z) % z)) < ds) /\
     &0 < d2 /\
     (!tau. abs tau < d2 ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < dl / &4) /\
     &2 * B + &8 <= H /\
     B * lam * H < dl / &4 /\ &48 * (B * lam * H + lam) <= dl / &4 /\
     &4 * (B * lam * H) < sqrt e /\ &12 * (B * lam + lam) < rho0 /\
     &12 * (B * lam + lam) < sqrt e /\
     (B + &2) * (&13 / &10 * lam) + B * (&2 * lam + (B + &2) * (&13 / &10 * lam)) +
     B * (&2 * lam) < dc /\
     &9 * kap pow 2 * lam <= &1
     ==> ?Phi Phi' L. diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ compact L /\
                      (!x. ~(x IN L) ==> Phi x = x) /\ vec 0 IN L /\ vec 0 IN S1 /\
                      (!t. sch_crit (Phi o g1) t <=> sch_crit g1 t /\ ~(g1 t IN L))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_CPAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_BECD_BOUND) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `P:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`e:real`; `lam:real`] SCHY_PSI_1D) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &1 / (&48 * kap + &1) /\ &0 < sqrt e / (&4 * P + &1) /\
                (&48 * kap + &1) * (&1 / (&48 * kap + &1)) = &1 /\
                (&4 * P + &1) * (sqrt e / (&4 * P + &1)) = sqrt e` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < kap`] THEN CONV_TAC REAL_FIELD;
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < P`] THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `wq = min (min t0 d2) (min (lam / &100) (min (&1 / (&48 * kap + &1))
                   (min (dl / &192) (min (sqrt e / &16) (min (rho0 / &16)
                   (sqrt e / (&4 * P + &1)))))))` THEN
  SUBGOAL_THEN `&0 < wq /\ wq <= t0 /\ wq <= d2 /\ wq <= lam / &100 /\
                wq <= &1 / (&48 * kap + &1) /\ wq <= dl / &192 /\ wq <= sqrt e / &16 /\
                wq <= rho0 / &16 /\ wq <= sqrt e / (&4 * P + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "wq" THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`&0 < t0`; `&0 < d2`; `&0 < lam`; `&0 < &1 / (&48 * kap + &1)`; `&0 < dl`;
      `&0 < sqrt e`; `&0 < rho0`; `&0 < sqrt e / (&4 * P + &1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eps = min (eps1 / &2) (min (lam / &100) (min e (dl / &192)))` THEN
  ABBREV_TAC `eps0 = min (lam / &100) (min e (dl / &192))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps < eps1 /\ eps <= lam / &100 /\ eps <= e /\ eps <= dl / &192 /\
                &0 < eps0 /\ eps0 <= lam / &100 /\ eps0 <= e /\ eps0 <= dl / &192`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN EXPAND_TAC "eps0" THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < eps1`; `&0 < lam`; `&0 < e`; `&0 < dl`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wq pow 2 <= wq * (lam / &100) /\ wq * (lam / &100) <= wq` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < wq`; `wq <= lam / &100`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `w * l <= w * &1 ==> w * l <= w`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < wq`; `lam <= &1`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wq pow 2 <= wq` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`wq pow 2 <= wq * (lam / &100)`; `wq * (lam / &100) <= wq`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&100 * wq pow 2 <= lam` ASSUME_TAC THENL
   [SUBGOAL_THEN `wq * (lam / &100) <= lam / &100` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `w * l <= &1 * l ==> w * l <= l`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MAP_EVERY (MP_TAC o ASSUME) [`wq <= lam / &100`; `lam <= &1`; `&0 < lam`] THEN
      REAL_ARITH_TAC;
      MP_TAC(ASSUME `wq pow 2 <= wq * (lam / &100)`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `P * wq pow 2 <= sqrt e / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `P * wq pow 2 <= P * wq /\ (&4 * P + &1) * wq <= sqrt e` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [SYM th]) o check (fun th ->
          concl th = `(&4 * P + &1) * (sqrt e / (&4 * P + &1)) = sqrt e`)) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        MAP_EVERY (MP_TAC o ASSUME) [`&0 < P`; `wq <= sqrt e / (&4 * P + &1)`] THEN
        REAL_ARITH_TAC];
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < P`; `&0 < wq`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. abs tau < wq
                      ==> abs(schy_bz c' e tau) <= &1 / &16 /\
                          lam * schy_bz c' e tau pow 2 <= wq pow 2`
  (LABEL_TAC "BZW") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `tau:real` (ASSUME
      `!tau. abs tau <= t0
             ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                 kap <= abs(schy_bzd c' e tau) /\ abs(schy_bzd c' e tau) <= &3 * kap /\
                 abs(schy_bz c' e tau) <= &3 * kap * abs tau /\
                 &0 <= schy_bz c' e tau * schy_bzd c' e tau * tau /\
                 (~(tau = &0) ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau)`))
      (MP (REAL_ARITH `abs tau < wq /\ wq <= t0 ==> abs tau <= t0`)
          (CONJ (ASSUME `abs tau < wq`) (ASSUME `wq <= t0`)))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN DISCH_TAC THEN
    SUBGOAL_THEN `kap * abs tau <= kap * wq` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      MAP_EVERY (MP_TAC o ASSUME) [`&0 < kap`; `abs tau < wq`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&48 * kap * wq <= &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&48 * kap + &1) * wq <= &1` MP_TAC THENL
       [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [SYM th]) o check (fun th ->
          concl th = `(&48 * kap + &1) * (&1 / (&48 * kap + &1)) = &1`)) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        MAP_EVERY (MP_TAC o ASSUME) [`&0 < kap`; `wq <= &1 / (&48 * kap + &1)`] THEN
        REAL_ARITH_TAC;
        MP_TAC(ASSUME `&0 < wq`) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME)
       [`abs(schy_bz c' e tau) <= &3 * kap * abs tau`; `kap * abs tau <= kap * wq`;
        `&48 * kap * wq <= &1`] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `schy_bz c' e tau pow 2 <= (&3 * kap * wq) pow 2` MP_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        REWRITE_TAC[REAL_ABS_POS] THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`abs(schy_bz c' e tau) <= &3 * kap * abs tau`; `kap * abs tau <= kap * wq`;
          `&0 < kap`; `&0 < wq`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x <= y ==> &0 <= y - x`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_MUL o
        CONJ (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < lam`))) THEN
      SUBGOAL_THEN `&0 <= (&1 - &9 * kap pow 2 * lam) * wq pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MP_TAC(ASSUME `&9 * kap pow 2 * lam <= &1`) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!tau. abs tau < wq ==> abs(schy_bz c' e tau) <= &1 / &16) /\
                (!tau. abs tau < wq ==> lam * schy_bz c' e tau pow 2 <= wq pow 2) /\
                (!tau. abs tau < wq ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < dl / &2 / &2) /\
                (!tau. abs tau <= t0
                       ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                           kap <= abs(schy_bzd c' e tau)) /\
                (!tau. abs tau <= t0 /\ ~(tau = &0)
                       ==> &0 < schy_bz c' e tau * schy_bzd c' e tau * tau) /\
                (!t. schy_psid e lam eps t < &0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN X_GEN_TAC `tau:real` THEN TRY DISCH_TAC THENL
     [USE_THEN "BZW" (MP_TAC o SPEC `tau:real`) THEN ASM_SIMP_TAC[];
      USE_THEN "BZW" (MP_TAC o SPEC `tau:real`) THEN ASM_SIMP_TAC[];
      MP_TAC(SPEC `tau:real` (ASSUME
        `!tau. abs tau < d2 ==> dist(schy_gam e tau,vector[--(sqrt e); &0]) < dl / &4`)) THEN
      ANTS_TAC THENL
       [MAP_EVERY (MP_TAC o ASSUME) [`abs tau < wq`; `wq <= d2`] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
        `!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                                  Q tau`) (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
        `!tau. abs tau <= t0 ==> (schy_bz c' e has_real_derivative schy_bzd c' e tau) (atreal tau) /\
                                  Q tau`) (concl th))) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H /\ dist((Theta:real^3->real^3) y,schy_lpt e) < dl / &2
                    ==> dist(sch5v_pr y,--basis 1) < delta1` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_RHO2_PROP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `r:real`; `C:real^3->bool`; `c:real^2->real^2`;
                          `c':real^2->real^2`;
                          `v:real^3->real^3`; `B:real`; `rho0:real`; `lam:real`;
                          `Theta':real^3->real^3`; `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`B * lam * H < dl / &4`; `&0 < dl`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * lam + (B + &2) * (&13 / &10 * lam) < lam * H` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * (&2 * B + &8) <= lam * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < lam`; `&0 <= B * lam`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `S1:real^3->bool`; `S2:real^3->bool`;
                 `g1:real^3->real^3`; `g1':real^3->real^3`; `s1:real`; `ds:real`;
                 `dl / &4`; `dl / &2`; `ts:real`; `wq:real`; `wq / &2`; `eps:real`;
                 `eps0:real`; `dc:real`; `t0:real`; `kap:real`; `P:real`] SCHY_CANCEL_CORE) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST (map (fun tms -> MAP_EVERY (MP_TAC o ASSUME) tms THEN REAL_ARITH_TAC)
   [[`s1 < &1 / &4`]; [`&0 < dl`]; [`wq <= t0`; `t0 < ts`]; [`B * lam * H < dl / &4`];
    [`wq <= dl / &192`; `&48 * (B * lam * H + lam) <= dl / &4`; `ds <= dl / &192`;
     `eps <= dl / &192`; `eps0 <= dl / &192`; `&0 < dl`];
    [`wq <= rho0 / &16`; `&12 * (B * lam + lam) < rho0`; `&0 < rho0`];
    [`wq <= sqrt e / &16`; `&12 * (B * lam + lam) < sqrt e`; `&0 < sqrt e`;
     `&0 <= B * lam`; `&0 < lam`];
    [`wq <= sqrt e / &16`; `&4 * (B * lam * H) < sqrt e`; `ds <= sqrt e / &8`; `&0 < sqrt e`];
    [`&0 < wq`]]));;

(* The H3 headline: for the data of the cancellation chart there is H0 such *)
(* that for every H >= H0 and every small lam, any chart Theta with the     *)
(* cancellation context and any neck g1 onto the lower part S1 of the slab  *)
(* configuration admit a global diffeomorphism Phi, the identity off a      *)
(* compact L containing the saddle vec 0 (which lies on S1), such that the  *)
(* critical points of Phi o g1 are those of g1 off L.                       *)

let SCHY_CANCEL_SHEAR_THM = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1.
     ?H0. &5 <= H0 /\
          !H. H0 <= H
              ==> ?lam1. &0 < lam1 /\
                    !lam (Theta:real^3->real^3) Theta' S1 S2 (g1:real^3->real^3) g1'.
                      lam < lam1 /\
                      schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta' /\
                      sch_slab_config (IMAGE g (sphere(vec 0,&1))) S1 S2 Theta /\
                      closed S1 /\ closed S2 /\
                      sch_neck g1 g1' /\ IMAGE g1 (sphere(vec 0,&1)) = S1
                      ==> ?Phi Phi' L. diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\
                                       compact L /\ (!x. ~(x IN L) ==> Phi x = x) /\
                                       vec 0 IN L /\ vec 0 IN S1 /\
                                       (!t. sch_crit (Phi o g1) t <=>
                                            sch_crit g1 t /\ ~(g1 t IN L))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `?lam0 H1 (Th:real^3->real^3) Th'.
                   schy_ctx g r e C c c' v B rho0 delta1 lam0 H1 Th Th'` THENL
   [ALL_TAC;
    EXISTS_TAC `&5` THEN REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `H:real` THEN DISCH_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `H:real`; `Theta:real^3->real^3`;
                          `Theta':real^3->real^3`] THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `lam0:real` (X_CHOOSE_THEN `H1:real`
    (X_CHOOSE_THEN `Th:real^3->real^3` (X_CHOOSE_TAC `Th':real^3->real^3`)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_cd] o check (fun th ->
    can (term_match [] `schy_cd (v:real^3->real^3) B rho0 e (c:real^2->real^2) delta1 lam0 H1
                               (Th:real^3->real^3) Th'`) (concl th))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam0:real`; `H1:real`; `Th:real^3->real^3`;
                 `Th':real^3->real^3`] SCHY_GAM_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `ts:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `ts:real`] SCHY_BZ_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> can (term_match []
      `!tau. abs tau < ts ==> schy_gam e tau IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\ P tau`)
      (concl th))) THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `kap:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `e:real`; `delta1:real`]
    SCHY_CHOICE_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`] SCHY_CHOICE_DC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dc:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt e` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ds = min (dl / &192) (sqrt e / &8)` THEN
  SUBGOAL_THEN `&0 < ds /\ ds <= dl / &192 /\ ds <= sqrt e / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < dl`; `&0 < sqrt e`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `ds:real`] SCHY_C_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`e:real`; `dl / &4`] SCHY_GAM_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `&0 < dl`) THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `&2 * B + &8` THEN CONJ_TAC THENL
   [MP_TAC(ASSUME `&0 <= B`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `H:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= B * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 <= B`; `&2 * B + &8 <= H`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K1 = (B + &2) * (&13 / &10) + B * (&2 + (B + &2) * (&13 / &10)) + B * &2` THEN
  SUBGOAL_THEN `&0 <= K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    SUBGOAL_THEN `&0 <= B * (&2 + (B + &2) * (&13 / &10))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(ASSUME `&0 <= B`) THEN
      SUBGOAL_THEN `&0 <= (B + &2) * (&13 / &10)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(ASSUME `&0 <= B`) THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MP_TAC(ASSUME `&0 <= B`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (dl / &4 / (B * H + &1))
               (min (dl / &4 / (&48 * (B * H + &1)))
               (min (sqrt e / (&4 * (B * H + &1)))
               (min (rho0 / (&12 * (B + &1)))
               (min (sqrt e / (&12 * (B + &1)))
               (min (dc / (K1 + &1)) (&1 / (&9 * kap pow 2 + &1)))))))` THEN
  SUBGOAL_THEN `&0 < B * H + &1 /\ &0 < &48 * (B * H + &1) /\ &0 < &4 * (B * H + &1) /\
                &0 < &12 * (B + &1) /\ &0 < K1 + &1 /\ &0 < &9 * kap pow 2 + &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `kap:real` REAL_LE_POW_2) THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 <= B * H`; `&0 <= B`; `&0 <= K1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY (MP_TAC o ASSUME) [`&0 < dl`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`lam:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                       `S1:real^3->bool`; `S2:real^3->bool`; `g1:real^3->real^3`;
                       `g1':real^3->real^3`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SCHY_CTX_BASIC o check (fun th -> can (term_match []
      `schy_ctx g r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
                (Theta:real^3->real^3) Theta'`) (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * (B * H + &1) < dl / &4 /\ lam * (&48 * (B * H + &1)) < dl / &4 /\
                lam * (&4 * (B * H + &1)) < sqrt e /\ lam * (&12 * (B + &1)) < rho0 /\
                lam * (&12 * (B + &1)) < sqrt e /\ lam * (K1 + &1) < dc /\
                lam * (&9 * kap pow 2 + &1) < &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ASSUME `lam < dl / &4 / (B * H + &1)`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < B * H + &1`];
      MP_TAC(ASSUME `lam < dl / &4 / (&48 * (B * H + &1))`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < &48 * (B * H + &1)`];
      MP_TAC(ASSUME `lam < sqrt e / (&4 * (B * H + &1))`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < &4 * (B * H + &1)`];
      MP_TAC(ASSUME `lam < rho0 / (&12 * (B + &1))`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < &12 * (B + &1)`];
      MP_TAC(ASSUME `lam < sqrt e / (&12 * (B + &1))`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < &12 * (B + &1)`];
      MP_TAC(ASSUME `lam < dc / (K1 + &1)`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < K1 + &1`];
      MP_TAC(ASSUME `lam < &1 / (&9 * kap pow 2 + &1)`) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < &9 * kap pow 2 + &1`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `v:real^3->real^3`; `B:real`;
                 `rho0:real`; `delta1:real`; `lam:real`; `H:real`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `S1:real^3->bool`; `S2:real^3->bool`;
                 `g1:real^3->real^3`; `g1':real^3->real^3`; `ts:real`; `t0:real`; `kap:real`;
                 `dl:real`; `dc:real`; `s1:real`; `ds:real`; `d2:real`] SCHY_CANCEL_INNER) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST (map (fun tms -> MAP_EVERY (MP_TAC o ASSUME) tms THEN REAL_ARITH_TAC)
   [[`lam * (B * H + &1) < dl / &4`; `&0 < lam`];
    [`lam * (&48 * (B * H + &1)) < dl / &4`];
    [`lam * (&4 * (B * H + &1)) < sqrt e`; `&0 < lam`];
    [`lam * (&12 * (B + &1)) < rho0`];
    [`lam * (&12 * (B + &1)) < sqrt e`];
    [`lam * (&9 * kap pow 2 + &1) < &1`; `&0 < lam`]] @
   [MP_TAC(ASSUME `lam * (K1 + &1) < dc`) THEN EXPAND_TAC "K1" THEN
    MP_TAC(ASSUME `&0 < lam`) THEN REAL_ARITH_TAC]));;

(* Restore the global rule list of REAL_DIFF_TAC extended above. *)

real_differentiation_theorems := schy_saved_rdt;;

