(* ========================================================================= *)
(* pc_p2a_l72g: O10 view-X form, part 1, multi-box compactness for MT Lemma  *)
(* 7.2.  The boxes of a p2a_cbox plus the box at the base point x (from      *)
(* p2a_bsmooth) carry box charts with uniform constants (p2aj_mb); a         *)
(* p2a_admx curve whose points lie in the boxes lies in boxes strictly below *)
(* their tops (P2AJ_STRICT_TOP); chart pieces in a box with a general top    *)
(* satisfy the displacement bound and stay in their chart (P2AJ_FE,          *)
(* P2AJ_STAY); along subsequences the chart curves of a piece converge       *)
(* uniformly (P2AJ_MB_PIECE_STEP).                                           *)
(* The first part: box charts with a general top, the strict-top cover, the  *)
(* multi-box datum.                                                          *)
(* ========================================================================= *)

needs "src/pc_p2a_l72e.ml";;

prioritize_real();;
type_invention_error := true;;

(* The displacement bound of a chart piece in a box chart with a general  *)
(* top b' (the region of the box is over (a',b']): the piece lies in an    *)
(* s-window (sa,sb) whose times are in (a',b'], and the L-integrand of the  *)
(* whole curve is bounded below by -sqrt(tau) Rm0.                          *)

let P2AJ_FE_POS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb Rm0 k s1 s2 sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!tau. &0 <= tau /\ tau <= b
            ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt gamma b tau) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> b' - T1 <= tt - s pow 2) /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)) IN cball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k))
     ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s2 pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s1 pow 2))) pow 2
         <= (s2 - s1) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ s2 <= sqrt b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `sa:real`; `sb:real`;
                 `cball((phi:A->real^N) k,&6 * (R:A->real) k)`; `lam:real`; `Rm:real`]
                P2AK_PIECE_SQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tt - s pow 2`; `y:real^N`; `u:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_sq]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `\v:real^1. vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at v)`;
                 `K:real->bool`; `s1:real`; `s2:real`] P2AK_FE_DISP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_integral (real_interval[s1 pow 2,s2 pow 2])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b)
                <= Lb + &2 * (sqrt b * Rm0) * (b - &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_INT_PIECE_UPPER THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM p2a_L_length] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm0)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Rm0:real`)) (concl th))) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 * Rm * (s2 - s1) <= b * Rm0 * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s2])
      (\s. norm(vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                  (at (lift s))) pow 2)
    <= &2 / lam * (Lb + &4 * b * sqrt b * Rm0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / lam * (real_integral (real_interval[s1 pow 2,s2 pow 2])
                             (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b) +
                           &2 * s2 pow 2 * Rm * (s2 - s1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s2 - s1) *
              real_integral (real_interval[s1,s2])
                (\s. norm(vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                            (at (lift s))) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The same with s1 >= 0, by continuity at s1.                              *)

let P2AJ_FE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb Rm0 k s1 s2 sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!tau. &0 <= tau /\ tau <= b
            ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt gamma b tau) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 <= s1 /\ s1 <= s2 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> b' - T1 <= tt - s pow 2) /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)) IN cball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k))
     ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s2 pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s1 pow 2))) pow 2
         <= (s2 - s1) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s1:real = s2` THENL
   [ASM_REWRITE_TAC[DIST_REFL; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `b:real`; `W:A->bool`; `a':real`; `b':real`;
                          `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_SCONT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\v. norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(drop v pow 2))) pow 2 -
         (s2 - drop v) * E`;
    `interval(lift s1,lift s2)`; `&0`] CONTINUOUS_LE_ON_CLOSURE) THEN
  SUBGOAL_THEN `closure(interval(lift s1,lift s2)) = interval[lift s1,lift s2]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN BETA_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL; LIFT_SUB; LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `gamma:real->A`; `Lb:real`; `Rm0:real`; `k:A`;
                   `s:real`; `s2:real`; `sa:real`; `sb:real`] P2AJ_FE_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(X_GEN_TAC `s':real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift s1`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[dist] THEN REAL_ARITH_TAC);;

(* Stay in the chart: started within R k of the chart centre, the piece    *)
(* stays in the chart, within r of its start, while (s1 - s0) E <= r^2.     *)

let P2AJ_STAY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb Rm0 k s0 s1 sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!tau. &0 <= tau /\ tau <= b
            ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt gamma b tau) /\
     p2a_L_length V tt gamma b <= Lb /\
     &0 <= Lb /\ k IN Fs /\ &0 <= s0 /\ s0 <= s1 /\ s1 pow 2 <= b /\ sa < s0 /\ s1 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s0 <= s /\ s <= s1 ==> b' - T1 <= tt - s pow 2) /\
     gamma(s0 pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
     dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s0 pow 2)),SND (chart_at (p2a_vatlas V b') k) k) < R k /\
     (s1 - s0) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= r pow 2
     ==> !s. s0 <= s /\ s <= s1
             ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                 dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s0 pow 2))) <= r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b' /\
                r <= (R:A->real) k /\
                cball((phi:A->real^N) k,&6 * R k) SUBSET IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AK_EXIT THEN
  MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `b:real`; `a':real`; `b':real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` THEN SIMP_TAC[p2a_admx];
    MATCH_MP_TAC P2AXR_ADMX_SCONT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `z:real^N`]
                  DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                  DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s':real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `tt:real`; `x:A`; `b:real`; `gamma:real->A`; `Lb:real`; `Rm0:real`; `k:A`;
                 `s0:real`; `s':real`; `sa:real`; `sb:real`] P2AJ_FE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `s1:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s':real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`;
                     `(phi:A->real^N)((gamma:real->A)(s pow 2))`] DIST_TRIANGLE) THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                    DIST_SYM) THEN
      MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s pow 2))`;
                     `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(s' - s0) * E <= r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s1 - s0) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Strict-top cover: if every point of a curve at a time in (0,tau0] lies  *)
(* in one of finitely many compact boxes C j over [a j,b j], then every     *)
(* point at a time tau in (0,tau0] lies in a box whose top b j is strictly  *)
(* above the time tt - tau (the curve is continuous in the slices, which    *)
(* are Hausdorff; times slightly before tau are later times).               *)

let P2AJ_STRICT_TOP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) tau0 n (C:num->A->bool) a b tau.
     (!t. hausdorff_space(p2a_vtop V t)) /\
     (!j. j < n ==> !s. a j <= s /\ s <= b j ==> compact_in (p2a_vtop V s) (C j)) /\
     (!tau. &0 <= tau /\ tau <= tau0 ==> gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
     (!tau1 O. &0 <= tau1 /\ tau1 <= tau0 /\ open_in (p2a_vtop V (tt - tau1)) O /\
               gamma tau1 IN O
               ==> ?d. &0 < d /\
                       !tau. &0 <= tau /\ tau <= tau0 /\ abs(tau - tau1) < d ==> gamma tau IN O) /\
     (!tau'. &0 < tau' /\ tau' <= tau0
             ==> ?j. j < n /\ a j <= tt - tau' /\ tt - tau' <= b j /\ gamma tau' IN C j) /\
     &0 < tau /\ tau <= tau0
     ==> ?j. j < n /\ a j <= tt - tau /\ tt - tau < b j /\ gamma tau IN C j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  (* each box excludes a left neighbourhood of tau *)
  SUBGOAL_THEN
   `!j:num. j < n
        ==> ?d. &0 < d /\
                !tau'. &0 <= tau' /\ tau' <= tau0 /\ tau - d < tau' /\ tau' < tau
                       ==> ~((a:num->real) j <= tt - tau' /\ tt - tau' <= (b:num->real) j /\
                             (gamma:real->A) tau' IN (C:num->A->bool) j)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "~")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(gamma:real->A) tau IN (C:num->A->bool) j` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `(a:num->real) j <= tt - tau` THEN ASM_REWRITE_TAC[] THENL
       [DISCH_TAC THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        TRY(DISCH_THEN(K ALL_TAC)) THEN EXISTS_TAC `(a:num->real) j - (tt - tau)` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]];
      TRY(DISCH_THEN(K ALL_TAC)) THEN
      ASM_CASES_TAC `(a:num->real) j <= tt - tau /\ tt - tau <= (b:num->real) j` THENL
       [ALL_TAC;
        (* the time is outside the box interval: a neighbourhood in time works *)
        ASM_CASES_TAC `(a:num->real) j <= tt - tau` THENL
         [EXISTS_TAC `tau:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
          EXISTS_TAC `(a:num->real) j - (tt - tau)` THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]]] THEN
      (* C j is closed in the slice at tt - tau, and the curve avoids it near tau *)
      FIRST_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
        can (find_term ((=) `(b:num->real) j`)) (concl th))) THEN
      SUBGOAL_THEN `closed_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) ((C:num->A->bool) j)` ASSUME_TAC THENL
       [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] o
          check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`tau:real`;
        `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) DIFF (C:num->A->bool) j`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau':real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dj:num->real` (LABEL_TAC "DJ")) THEN
  MP_TAC(REWRITE_RULE[FINITE_NUMSEG_LT; IN_ELIM_THM]
    (ISPECL [`\j:num. min ((dj:num->real) j) tau`; `{j:num | j < n}`] P2AK_FINITE_POS_LB)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "DJ" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `d <= tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `0 < n` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
        can (find_term ((=) `C:num->A->bool`)) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC)] THEN
      UNDISCH_TAC `j0 < n:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau - d / &2` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
    can (find_term ((=) `C:num->A->bool`)) (concl th) &&
    can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "DJ" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau - d / &2` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Box data are monotone in the radius, the lower and upper metric bounds    *)
(* and the curvature bound.                                                  *)

let P2AJ_BXD_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm r' lam' Gm' Rm'.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\
     &0 < r' /\ r' <= r /\ &0 < lam' /\ lam' <= lam /\ Gm <= Gm' /\ Rm <= Rm'
     ==> p2ak_bxd V W a' b' C T1 Fs R r' lam' Gm' Rm'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ak_bxd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`; `u:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^N`; `u:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lam' * norm(u:real^N) pow 2 <= lam * norm u pow 2 /\
                Gm * norm u pow 2 <= Gm' * norm u pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Multi-box data: boxes j < n (from a p2a_cbox) and the box j = n at the   *)
(* base point x (a = b = tt, C = {x}, from p2a_bsmooth).  Each box j has a  *)
(* region W j over (A0 j,b j] with A0 j + eta <= a j, its compact C j over  *)
(* [a j,b j], and box charts for the times [a j - eta / 2,b j] with uniform  *)
(* constants r, lam, Gm, Rm.                                                  *)

let p2aj_mb = new_definition
 `p2aj_mb (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
          (tt:real) (x:A) (n:num) (W:num->A->bool) (A0:num->real) (a:num->real)
          (b:num->real) (C:num->A->bool) (eta:real) (Fs:num->A->bool) (R:num->A->real)
          (r:real) (lam:real) (Gm:real) (Rm:real) <=>
    p2a_svs V /\ p2a_atlas_lc V /\ &0 < eta /\ &0 < r /\ &0 < lam /\ &0 <= Gm /\ &0 <= Rm /\
    a n = tt /\ b n = tt /\ C n = {x} /\
    (!j. j <= n
         ==> a j <= b j /\ A0 j + eta <= a j /\
             p2ak_bxd V (W j) (A0 j) (b j) (C j) (b j - a j + eta / &2) (Fs j) (R j)
                      r lam Gm Rm /\
             !s. a j <= s /\ s <= b j ==> compact_in (p2a_vtop V s) (C j))`;;

let P2AJ_MB_EXISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) K.
     p2a_svs V /\ p2a_atlas_lc V /\ x IN topspace(p2a_vtop V tt) /\
     p2a_bsmooth V x tt /\ p2a_cbox V K
     ==> ?n W A0 a b C eta Fs R r lam Gm Rm.
           p2aj_mb V tt x n W A0 a b C eta Fs R r lam Gm Rm /\
           !t y. y IN K t ==> ?j. j < n /\ a j <= t /\ t <= b j /\ y IN C j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_cbox]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `W0:num->A->bool`
    (X_CHOOSE_THEN `C0:num->A->bool` (X_CHOOSE_THEN `a0:num->real`
    (X_CHOOSE_THEN `b0:num->real` (X_CHOOSE_THEN `eta0:real` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_bsmooth]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Wx:A->bool` (X_CHOOSE_THEN `ax:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `W = \j. if j < n then (W0:num->A->bool) j else Wx` THEN
  ABBREV_TAC `C = \j. if j < n then (C0:num->A->bool) j else {x:A}` THEN
  ABBREV_TAC `a = \j. if j < n then (a0:num->real) j else tt` THEN
  ABBREV_TAC `b = \j. if j < n then (b0:num->real) j else tt` THEN
  ABBREV_TAC `eta = min eta0 (tt - ax)` THEN
  ABBREV_TAC `A0 = \j. if j < n then (a0:num->real) j - eta0 else ax` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= eta0 /\ eta <= tt - ax` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the facts of each box *)
  SUBGOAL_THEN
   `!j. j <= n
        ==> (a:num->real) j <= b j /\ (A0:num->real) j + eta <= a j /\
            (C:num->A->bool) j SUBSET (W:num->A->bool) j /\
            p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (W j) (A0 j) (b j) /\
            (!s. a j <= s /\ s <= b j ==> compact_in (p2a_vtop V s) (C j))`
  (LABEL_TAC "BOX") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"; "A0"; "C"; "W"] THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_region")) (concl th) &&
        can (find_term ((=) `W0:num->A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL; SING_SUBSET] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `s:real = tt` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[COMPACT_IN_SING]]];
    ALL_TAC] THEN
  (* box charts for each box *)
  SUBGOAL_THEN
   `!j. j <= n
        ==> ?Fs R r lam Gm Rm.
              p2ak_bxd (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((W:num->A->bool) j) ((A0:num->real) j) ((b:num->real) j)
                       ((C:num->A->bool) j) (b j - (a:num->real) j + eta / &2)
                       Fs R r lam Gm Rm`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "BOX" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P2AK_BXD_EXISTS THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:num->A->bool` (X_CHOOSE_THEN `R:num->A->real`
    (X_CHOOSE_THEN `rj:num->real` (X_CHOOSE_THEN `lj:num->real`
    (X_CHOOSE_THEN `gj:num->real` (X_CHOOSE_THEN `mj:num->real` (LABEL_TAC "BX"))))))) THEN
  (* uniform constants *)
  SUBGOAL_THEN `!j. j <= n ==> &0 < (rj:num->real) j /\ &0 < (lj:num->real) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "BX" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[p2ak_bxd]];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[FINITE_NUMSEG_LE; IN_ELIM_THM]
    (ISPECL [`\j:num. min ((rj:num->real) j) ((lj:num->real) j)`; `{j:num | j <= n}`]
            P2AK_FINITE_POS_LB)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(REWRITE_RULE[FINITE_NUMSEG_LE; IN_ELIM_THM]
    (ISPECL [`\j:num. max ((gj:num->real) j) ((mj:num->real) j)`; `{j:num | j <= n}`]
            UPPER_BOUND_FINITE_SET_REAL)) THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:real`) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                        `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                        `R:num->A->real`; `r0:real`; `r0:real`; `abs M0`; `abs M0`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2aj_mb] THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    SUBGOAL_THEN `(a:num->real) n = tt /\ (b:num->real) n = tt /\ (C:num->A->bool) n = {x}`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "C"] THEN REWRITE_TAC[LT_REFL]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "BOX" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AJ_BXD_MONO THEN
    MAP_EVERY EXISTS_TAC [`(rj:num->real) j`; `(lj:num->real) j`; `(gj:num->real) j`;
                          `(mj:num->real) j`] THEN
    CONJ_TAC THENL [USE_THEN "BX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r0:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:A`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `K:real->A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"; "C"] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The multi-box piece step (pigeonhole over the box charts at the start of *)
(* a piece, stay-in-chart, displacement bound, Arzela-Ascoli).              *)
(* ------------------------------------------------------------------------- *)

(* The L-integrand of a curve covered by the boxes (times in [a j,b j]) is  *)
(* at least -sqrt(tau) Rm (P2AK_BXD_LINT_LOWER in the box; tau = 0 is      *)
(* trivial).                                                                 *)

let P2AJ_MB_LINT_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gamma:real->A) tau0 tau.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\
     (!tau. &0 < tau /\ tau <= tau0
            ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau <= b j /\ gamma tau IN C j) /\
     &0 <= tau /\ tau <= tau0
     ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt gamma tau0 tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tau = &0` THENL
   [ASM_REWRITE_TAC[p2a_L_integrand; SQRT_0; REAL_MUL_LZERO; REAL_NEG_0; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~(tau = &0)` THEN UNDISCH_TAC `&0 <= tau` THEN UNDISCH_TAC `tau <= tau0` THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC P2AK_BXD_LINT_LOWER THEN
  MAP_EVERY EXISTS_TAC [`(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                        `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                        `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`;
                        `Gm:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* An open s-window around [p,q] whose times stay in (A0,b'], given that     *)
(* tt - p^2 is strictly below the top b' (or the top is at least tt).        *)

let P2AJ_WINDOW = prove
 (`!tt A0 b' p q.
     &0 <= p /\ p <= q /\ A0 < tt - q pow 2 /\ (tt - p pow 2 < b' \/ tt <= b')
     ==> ?sa sb. sa < p /\ q < sb /\
                 !s. sa < s /\ s < sb ==> A0 < tt - s pow 2 /\ tt - s pow 2 <= b'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `?sb. q < sb /\ &0 < sb /\ sb pow 2 = tt - A0` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sqrt(tt - A0)` THEN
    SUBGOAL_THEN `q pow 2 < tt - A0 /\ &0 <= tt - A0` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN
    SUBGOAL_THEN `q < sqrt(tt - A0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs s < sb ==> A0 < tt - s pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s pow 2 < sb pow 2` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `tt <= b'` THENL
   [MAP_EVERY EXISTS_TAC [`--(sb / &2)`; `sb:real`] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tt - p pow 2 < b' /\ &0 < tt - b'` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?sa. &0 < sa /\ sa pow 2 = tt - b'` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sqrt(tt - b')` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sa < p` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    SUBGOAL_THEN `p pow 2 <= sa pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `sa pow 2 < s pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* Multi-box piece property: along sub, the chart curves of gs on [p,q]     *)
(* converge uniformly in a box chart of some box j <= nb whose region      *)
(* window contains [p,q].                                                    *)

let p2aj_pp = new_definition
 `p2aj_pp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
          (tt:real) (nb:num) (W:num->A->bool) (A0:num->real) (b:num->real)
          (gs:num->real->A) (Fs:num->A->bool) (R:num->A->real) (p:real) (q:real)
          (sub:num->num) <=>
    ?j. j <= nb /\
        (?sa sb. sa < p /\ q < sb /\
                 !s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 <= b j) /\
        p2ak_pp V (W j) (b j) gs (Fs j) (R j) p q sub`;;

let P2AJ_PP_SUBSEQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt nb W A0 b (gs:num->real->A) Fs R p q sub t.
     p2aj_pp V tt nb W A0 b gs Fs R p q sub /\ p3_subseq t
     ==> p2aj_pp V tt nb W A0 b gs Fs R p q (sub o t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2aj_pp] THEN STRIP_TAC THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AK_PP_SUBSEQ THEN ASM_REWRITE_TAC[]]);;

(* One box, a fixed chart k at the start p of every curve, a window and the  *)
(* time bound T1 on [p,q]: along a subsequence the chart curves converge     *)
(* uniformly on [p,q] (stay-in-chart, displacement bound, Arzela-Ascoli).    *)

let P2AJ_BOX_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (g:num->real->A) Lb Rm0 k p q sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 <= Lb /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!n. p2a_admx V tt x b (g n) /\ p2a_L_length V tt (g n) b <= Lb /\
          (!tau. &0 <= tau /\ tau <= b
                 ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt (g n) b tau) /\
          g n (p pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
          dist(SND (chart_at (p2a_vatlas V b') k) (g n (p pow 2)),SND (chart_at (p2a_vatlas V b') k) k) < R k) /\
     k IN Fs /\ &0 <= p /\ p < q /\ q pow 2 <= b /\ sa < p /\ q < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. p <= s /\ s <= q ==> b' - T1 <= tt - s pow 2) /\
     (q - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= r pow 2
     ==> ?t. p3_subseq t /\ p2ak_pp V W b' g Fs R p q t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b' /\ r <= (R:A->real) k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* each curve stays in the chart ball *)
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= q
          ==> (g:num->real->A) n (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(g n (s pow 2)),phi(g n (p pow 2))) <= r`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `Lb:real`; `Rm0:real`;
                   `k:A`; `p:real`; `q:real`; `sa:real`; `sb:real`] P2AJ_STAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= q
          ==> dist((phi:A->real^N) k,phi((g:num->real->A) n (s pow 2))) <= &2 * (R:A->real) k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`;
                   `(phi:A->real^N)((g:num->real->A) n (s pow 2))`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`]
                  DIST_SYM) THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((g:num->real->A) n (s pow 2))`;
                   `(phi:A->real^N)((g:num->real->A) n (p pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the displacement bound *)
  SUBGOAL_THEN
   `!n s s'. p <= s /\ s <= s' /\ s' <= q
             ==> dist((phi:A->real^N)((g:num->real->A) n (s' pow 2)),phi(g n (s pow 2))) pow 2
                 <= (s' - s) * E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    SUBGOAL_THEN `&0 <= s /\ sa < s /\ s' < sb /\ s' pow 2 <= b` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!u. s <= u /\ u <= s' ==> b' - T1 <= tt - u pow 2` ASSUME_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `q:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. s <= u /\ u <= s'
          ==> (g:num->real->A) n (u pow 2) IN U INTER W /\
              (phi:A->real^N)(g n (u pow 2)) IN cball(phi k,&6 * (R:A->real) k)`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `u:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r:real`)) (concl th) &&
        can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[IN_CBALL] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `u:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * (R:A->real) k`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `Lb:real`; `Rm0:real`;
                   `k:A`; `s:real`; `s':real`; `sa:real`; `sb:real`] P2AJ_FE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Arzela-Ascoli for the chart curves on [p,q] *)
  MP_TAC(ISPECL [`\n v. (phi:A->real^N)((g:num->real->A) n (drop v pow 2))`;
                 `interval[lift p,lift q]`; `norm((phi:A->real^N) k) + &2 * (R:A->real) k`]
                ARZELA_ASCOLI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * (R:A->real) k`)) (concl th))) THEN
      ASM_REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `e pow 2 / (E + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(s - y) * E < e pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e pow 2 / (E + &1) * E` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < e pow 2 / (E + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `e pow 2 / (E + &1) * E = e pow 2 - e pow 2 / (E + &1)` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(E + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN
    SUBGOAL_THEN `dist((phi:A->real^N)((g:num->real->A) n (s pow 2)),phi(g n (y pow 2))) pow 2
                  < e pow 2` MP_TAC THENL
     [ASM_CASES_TAC `s <= y` THENL
       [SUBGOAL_THEN `abs(s - y) = y - s` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`; `y:real`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `abs(s - y) = s - y` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real`; `s:real`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
    SIMP_TAC[REAL_ABS_DIST; REAL_ARITH `abs e = e <=> &0 <= e`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t2:num->num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `t2:num->num` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[p3_subseq]; ALL_TAC] THEN
  REWRITE_TAC[p2ak_pp] THEN
  MAP_EVERY EXISTS_TAC [`k:A`; `Y:real^1->real^N`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `dist((phi:A->real^N) k,(Y:real^1->real^N)(lift s)) - &2 * (R:A->real) k`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPECL [`N:num`; `lift s`])) THEN
    REWRITE_TAC[GE; LE_REFL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(t2:num->num) N`; `s:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&2 * (R:A->real) k`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(t2:num->num) n`; `s:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `lift s`]) THEN
    ASM_REWRITE_TAC[GE; IN_INTERVAL_1; LIFT_DROP; dist]]);;

(* The multi-box piece step: along a further subsequence the chart curves  *)
(* on [p,q] converge in a box chart (pigeonhole over the finitely many box  *)
(* charts (j,k) at the start; the start p = 0 uses the box at x).           *)

let P2AJ_MB_PIECE_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 p q r0.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     &0 <= p /\ p < q /\ q pow 2 <= tau0 /\ q pow 2 - p pow 2 <= eta / &2 /\
     (q - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= r pow 2 /\
     p3_subseq r0
     ==> ?t. p3_subseq t /\ p2aj_pp V tt nb W A0 b gs Fs R p q (r0 o t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  (* finitely many box charts *)
  SUBGOAL_THEN `FINITE {z:num#A | FST z <= nb /\ SND z IN (Fs:num->A->bool) (FST z)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{j:num | j <= nb} CROSS UNIONS (IMAGE (Fs:num->A->bool) {j | j <= nb})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CROSS THEN REWRITE_TAC[FINITE_NUMSEG_LE; FINITE_UNIONS] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[p2ak_bxd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  (* the start box and chart of each curve *)
  SUBGOAL_THEN
   `!n. ?z:num#A.
          FST z <= nb /\ SND z IN (Fs:num->A->bool) (FST z) /\
          (a:num->real) (FST z) <= tt - p pow 2 /\
          (tt - p pow 2 < (b:num->real) (FST z) \/ tt <= b (FST z)) /\
          (gs:num->real->A) ((r0:num->num) n) (p pow 2) IN
            FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (b (FST z))) (SND z)) INTER
            (W:num->A->bool) (FST z) /\
          dist(SND(chart_at (p2a_vatlas V (b (FST z))) (SND z)) (gs (r0 n) (p pow 2)),
               SND(chart_at (p2a_vatlas V (b (FST z))) (SND z)) (SND z))
          < (R:num->A->real) (FST z) (SND z)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN
     `?j. j <= nb /\ (a:num->real) j <= tt - p pow 2 /\
          (tt - p pow 2 < (b:num->real) j \/ tt <= b j) /\
          (gs:num->real->A) ((r0:num->num) n) (p pow 2) IN (C:num->A->bool) j`
    (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THENL
     [FIRST_ASSUM(MP_TAC o SPEC `(r0:num->num) n` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
      ASM_CASES_TAC `p = &0` THENL
       [EXISTS_TAC `nb:num` THEN
        SUBGOAL_THEN `p pow 2 = &0` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        ASM_REWRITE_TAC[LE_REFL; IN_SING; REAL_SUB_RZERO; REAL_LE_REFL];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p pow 2` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
        can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN
          UNDISCH_TAC `~(p = &0)` THEN UNDISCH_TAC `&0 <= p` THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j < nb:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
      not(is_forall(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(gs:num->real->A) ((r0:num->num) n) (p pow 2)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `(C:num->A->bool) j`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(j:num,k:A)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `jk:num->num#A` (LABEL_TAC "JK")) THEN
  MP_TAC(ISPECL [`jk:num->num#A`;
                 `{z:num#A | FST z <= nb /\ SND z IN (Fs:num->A->bool) (FST z)}`] P2AK_PIGEON) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
      USE_THEN "JK" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[IN_ELIM_THM] o ONCE_REWRITE_RULE[EXISTS_PAIR_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `t1:num->num`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!n. (a:num->real) j <= tt - p pow 2 /\ (tt - p pow 2 < (b:num->real) j \/ tt <= b j) /\
        (gs:num->real->A) ((r0:num->num) ((t1:num->num) n)) (p pow 2) IN
          FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (b j)) (k:A)) INTER (W:num->A->bool) j /\
        dist(SND(chart_at (p2a_vatlas V (b j)) k) (gs (r0 (t1 n)) (p pow 2)),
             SND(chart_at (p2a_vatlas V (b j)) k) k) < (R:num->A->real) j k`
  (LABEL_TAC "ST") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "JK" (MP_TAC o SPEC `(t1:num->num) n`) THEN
    SUBGOAL_THEN `(jk:num->num#A) ((t1:num->num) n) = (j,k)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ST" (MP_TAC o SPEC `0`) THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "ST" (MP_TAC o SPEC `0`) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `p pow 2 <= q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:real`; `(A0:num->real) j`; `(b:num->real) j`; `p:real`; `q:real`]
                P2AJ_WINDOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa:real` (X_CHOOSE_THEN `sb:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= q
                    ==> (b:num->real) j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 <= q pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `g = \n. (gs:num->real->A) ((r0:num->num) ((t1:num->num) n))` THEN
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 ((g:num->real->A) n) /\ p2a_L_length V tt (g n) tau0 <= Lb /\
        (!tau. &0 <= tau /\ tau <= tau0
               ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt (g n) tau0 tau) /\
        g n (p pow 2) IN FST(chart_at (p2a_vatlas V ((b:num->real) j)) (k:A)) INTER
                         (W:num->A->bool) j /\
        dist(SND(chart_at (p2a_vatlas V (b j)) k) (g n (p pow 2)),
             SND(chart_at (p2a_vatlas V (b j)) k) k) < (R:num->A->real) j k`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN BETA_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `(r0:num->num) ((t1:num->num) n)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    USE_THEN "ST" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau':real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
      can (find_term ((=) `C:num->A->bool`)) (concl th) &&
      can (find_term ((=) `t1:num->num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`; `g:num->real->A`; `Lb:real`; `Rm:real`;
                 `k:A`; `p:real`; `q:real`; `sa:real`; `sb:real`] P2AJ_BOX_STEP) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(t1:num->num) o (t2:num->num)` THEN
  ASM_SIMP_TAC[P2AK_SUBSEQ_O] THEN
  REWRITE_TAC[p2aj_pp] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_pp")) (concl th))) THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[p2ak_pp; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Multi-box compactness (P2AJ_MB_LIMIT), the cover of the limit by the     *)
(* boxes, its chart structure on pieces of a subsequence and its continuity *)
(* in the slice topologies (P2AJ_MB_CONT).                                  *)
(* ------------------------------------------------------------------------- *)

(* A uniform mesh h for the pieces: h E <= r^2 (stay-in-chart) and         *)
(* 2 S h <= eta / 2 (the time span of a piece is at most eta / 2).          *)

let P2AJ_MESH = prove
 (`!S E r eta. &0 < S /\ &0 <= E /\ &0 < r /\ &0 < eta
               ==> ?M h. 1 <= M /\ &0 < h /\ S / &M = h /\ &M * h = S /\
                         h * E <= r pow 2 /\ &2 * S * h <= eta / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `(S * E) / r pow 2 + (&4 * S pow 2) / eta` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `&0 <= (S * E) / r pow 2 /\ &0 <= (&4 * S pow 2) / eta` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= m + 1 /\ &0 < &(m + 1) /\ (S * E) / r pow 2 <= &(m + 1) /\
                (&4 * S pow 2) / eta <= &(m + 1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THENL [ARITH_TAC; ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `S * E <= &(m + 1) * r pow 2 /\ &4 * S pow 2 <= &(m + 1) * eta`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(S * E) / r pow 2 <= &(m + 1)` THEN
    UNDISCH_TAC `(&4 * S pow 2) / eta <= &(m + 1)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`m + 1`; `S / &(m + 1)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[];
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    SUBGOAL_THEN `S / &(m + 1) * E = (S * E) / &(m + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&2 * S * S / &(m + 1) = (&2 * S pow 2) / &(m + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* The chart facts of a box chart of the multi-box datum.                   *)

let P2AJ_MB_CHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm j k.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ j <= nb /\ k IN Fs j
     ==> p2a_region V (W j) (A0 j) (b j) /\ A0 j < b j /\
         (FST(chart_at (p2a_vatlas V (b j)) k),SND(chart_at (p2a_vatlas V (b j)) k))
           IN p2a_vatlas V (b j) /\
         k IN FST(chart_at (p2a_vatlas V (b j)) k) /\ &0 < r /\ r <= R j k /\
         cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&6 * R j k) SUBSET
         IMAGE (SND(chart_at (p2a_vatlas V (b j)) k))
               (FST(chart_at (p2a_vatlas V (b j)) k) INTER W j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2ak_bxd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[PAIR] THEN ASM_REAL_ARITH_TAC);;

(* A sequence in a region chart whose chart images converge to y0 converges *)
(* in the slice topology to chart_inv y0.                                    *)

let P2AJ_CHART_SLICE_LIM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' U (phi:A->real^N) t (z:num->A) y0.
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ a' < t /\ t <= b' /\
     y0 IN IMAGE phi (U INTER W) /\ (!n. z n IN U INTER W) /\
     ((\n. phi(z n)) --> y0) sequentially
     ==> chart_inv (U INTER W,phi) y0 IN topspace(p2a_vtop V t) /\
         !O. open_in (p2a_vtop V t) O /\ chart_inv (U INTER W,phi) y0 IN O
             ==> ?N. !n. N <= n ==> z n IN O`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `y0:real^N`] P2A_CHART_PIECE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2A_REGION_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `t:real`; `O:A->bool`; `y0:real^N`] P2A_CHART_INV_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o REWRITE_RULE[LIM_SEQUENTIALLY] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((z:num->A) n)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `O:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `(z:num->A) n`] P2A_REGION_CHART_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* Multi-box compactness: a subsequence converging at every backward time   *)
(* in the slice topology (partition of [0,sqrt tau0] with mesh h, iterated  *)
(* piece steps, the limit at a time is chart_inv of the chart limit).        *)

let P2AJ_MB_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j)
     ==> ?sub gamma.
           p3_subseq sub /\ gamma (&0) = x /\
           (!tau. &0 <= tau /\ tau <= tau0
                  ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                      !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                          ==> ?N. !n. N <= n ==> gs (sub n) tau IN O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt tau0` THEN
  SUBGOAL_THEN `&0 < S /\ S pow 2 = tau0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`S:real`; `E:real`; `r:real`; `eta:real`] P2AJ_MESH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC)) THEN
  (* the pieces *)
  MP_TAC(ISPECL [`\i sub. p2aj_pp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt nb (W:num->A->bool) (A0:num->real) (b:num->real)
                            (gs:num->real->A) (Fs:num->A->bool) (R:num->A->real)
                            (&i * h) (&(SUC i) * h) sub`; `M:num`] P2AK_SUBSEQ_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AJ_PP_SUBSEQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `r0:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= &i * h /\ &i * h < &(SUC i) * h /\ &(SUC i) * h <= S`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&M * h = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `i < M:num` THEN ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2AJ_MB_PIECE_STEP THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a:num->real`; `C:num->A->bool`; `eta:real`; `r:real`;
                          `lam:real`; `Gm:real`; `Rm:real`; `Lb:real`; `tau0:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `S pow 2 = tau0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(&(SUC i) * h) pow 2 - (&i * h) pow 2 = h * (&(SUC i) * h + &i * h)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * S * h` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * S * h = h * (&2 * S)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ARITH `(&i + &1) * h - &i * h = h`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= tau0
          ==> ?y:A. y IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
                    !O. open_in (p2a_vtop V (tt - tau)) O /\ y IN O
                        ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O`
  MP_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real`; `M:num`; `sqrt tau`] P2AK_PARTITION_INDEX) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE] THEN UNDISCH_TAC `sqrt tau0 = S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aj_pp")) (concl th))) THEN
    ASM_REWRITE_TAC[p2aj_pp; p2ak_pp] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `sa:real` (X_CHOOSE_THEN `sb:real` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `Y:real^1->real^N` STRIP_ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(sqrt tau) pow 2 = tau` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `(A0:num->real) j < tt - tau /\ tt - tau <= (b:num->real) j`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift(sqrt tau)) IN
                  IMAGE (phi:A->real^N) (U INTER (W:num->A->bool) j)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `cball((phi:A->real^N) k,&2 * (R:num->A->real) j k)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                   `U:A->bool`; `phi:A->real^N`; `tt - tau`;
                   `\n. (gs:num->real->A) ((sub:num->num) n) tau`;
                   `(Y:real^1->real^N)(lift(sqrt tau))`] P2AJ_CHART_SLICE_LIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `sqrt tau`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `sub:num->num`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "distance"))
                  (concl th)))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `sqrt tau`]) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN
    EXISTS_TAC `chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N)
                          ((Y:real^1->real^N)(lift(sqrt tau)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `gamma = \tau. @y:A. y IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
                   !O. open_in (p2a_vtop V (tt - tau)) O /\ y IN O
                       ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O` THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= tau0
          ==> (gamma:real->A) tau IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
              !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                  ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN EXPAND_TAC "gamma" THEN
    CONV_TAC SELECT_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `gamma:real->A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. hausdorff_space(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs]; ALL_TAC] THEN
  MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - &0)`;
                        `\n. (gs:num->real->A) ((sub:num->num) n) (&0)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. (gs:num->real->A) ((sub:num->num) n) (&0) = x /\
                    x IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - &0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The limit is covered by the boxes (non-strictly): the boxes of the      *)
(* curves recur along a subsequence (pigeonhole), and C j is closed.        *)

let P2AJ_LIM_COVER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) tau0 sub gamma tau.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ p3_subseq sub /\
     (!n tau. &0 < tau /\ tau <= tau0
              ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau <= b j /\ gs n tau IN C j) /\
     gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
     (!O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
          ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 < tau /\ tau <= tau0
     ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau <= b j /\ gamma tau IN C j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN `!n. ?j. j < nb /\ (a:num->real) j <= tt - tau /\ tt - tau <= (b:num->real) j /\
                        (gs:num->real->A) ((sub:num->num) n) tau IN (C:num->A->bool) j`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(sub:num->num) n`; `tau:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
      can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `jf:num->num` (LABEL_TAC "JF")) THEN
  MP_TAC(ISPECL [`jf:num->num`; `{j:num | j < nb}`] P2AK_PIGEON) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "JF" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. (gs:num->real->A) ((sub:num->num) ((t:num->num) n)) tau IN
                    (C:num->A->bool) j /\
                    (a:num->real) j <= tt - tau /\ tt - tau <= (b:num->real) j`
  (LABEL_TAC "GT") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "JF" (MP_TAC o SPEC `(t:num->num) n`) THEN
    SUBGOAL_THEN `(jf:num->num) ((t:num->num) n) = j` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "GT" (STRIP_ASSUME_TAC o SPEC `0`) THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) ((C:num->A->bool) j)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) DIFF (C:num->A->bool) j` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(t:num->num) N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:num`)) (concl th))) THEN
  SUBGOAL_THEN `N <= (t:num->num) N` (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPEC `t:num->num` MONOTONE_BIGGER) THEN
    ANTS_TAC THENL [UNDISCH_TAC `p3_subseq (t:num->num)` THEN REWRITE_TAC[p3_subseq]; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "GT" (MP_TAC o SPEC `N:num`) THEN SIMP_TAC[]);;

(* Slice convergence passes to subsequences.                                 *)

let P2AJ_SLICE_SUBSEQ = prove
 (`!top (z:num->A) y (t:num->num).
     p3_subseq t /\ (!O. open_in top O /\ y IN O ==> ?N. !n. N <= n ==> z n IN O)
     ==> !O. open_in top O /\ y IN O ==> ?N. !n. N <= n ==> z (t n) IN O`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t:num->num` MONOTONE_BIGGER) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p3_subseq (t:num->num)` THEN REWRITE_TAC[p3_subseq]; SIMP_TAC[]]);;

(* On a piece of a p2aj_pp subsequence the slice limit is in the box chart,  *)
(* its chart curve is the uniform chart limit (continuous), and the chart   *)
(* points converge.                                                          *)

let P2AJ_PP_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) sub gamma p q.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\
     p2aj_pp V tt nb W A0 b gs Fs R p q sub /\
     (!s. p <= s /\ s <= q
          ==> gamma(s pow 2) IN topspace(p2a_vtop V (tt - s pow 2)) /\
              !O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
                  ==> ?N. !n. N <= n ==> gs (sub n) (s pow 2) IN O)
     ==> ?j k. j <= nb /\
               (?sa sb. sa < p /\ q < sb /\
                        !s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 <= b j) /\
               k IN Fs j /\
               (!s. p <= s /\ s <= q
                    ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
                        dist(SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s pow 2)),
                             SND(chart_at (p2a_vatlas V (b j)) k) k) <= &2 * R j k) /\
               (\v. SND(chart_at (p2a_vatlas V (b j)) k) (gamma(drop v pow 2))) continuous_on
                 interval[lift p,lift q] /\
               (!s. p <= s /\ s <= q
                    ==> ((\n. SND(chart_at (p2a_vatlas V (b j)) k) (gs (sub n) (s pow 2))) -->
                         SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s pow 2))) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2aj_pp]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `sa:real` (X_CHOOSE_THEN `sb:real` STRIP_ASSUME_TAC))
    (MP_TAC o GEN_REWRITE_RULE I [p2ak_pp])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `Y:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:A`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (* the limit is chart_inv of the chart limit *)
  SUBGOAL_THEN
   `!s. p <= s /\ s <= q
        ==> (gamma:real->A)(s pow 2) IN U INTER (W:num->A->bool) j /\
            (phi:A->real^N)(gamma(s pow 2)) = (Y:real^1->real^N)(lift s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(A0:num->real) j < tt - s pow 2 /\ tt - s pow 2 <= (b:num->real) j`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift s) IN IMAGE (phi:A->real^N) (U INTER (W:num->A->bool) j)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `cball((phi:A->real^N) k,&2 * (R:num->A->real) j k)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                   `U:A->bool`; `phi:A->real^N`; `tt - s pow 2`;
                   `\n. (gs:num->real->A) ((sub:num->num) n) (s pow 2)`;
                   `(Y:real^1->real^N)(lift s)`] P2AJ_CHART_SLICE_LIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `sub:num->num`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "distance"))
                  (concl th)))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN
    SUBGOAL_THEN `(gamma:real->A)(s pow 2) =
                  chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N) ((Y:real^1->real^N)(lift s))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)`;
                            `\n. (gs:num->real->A) ((sub:num->num) n) (s pow 2)`] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                   `U:A->bool`; `phi:A->real^N`; `(Y:real^1->real^N)(lift s)`]
                  P2A_CHART_PIECE_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_CBALL] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `Y:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_REWRITE_TAC[]]);;

(* The limit curve is continuous in the slice topologies (a piece around     *)
(* each time along a further subsequence, P2AJ_PP_LIMIT, P2A_CHART_INV_NBHD). *)

let P2AJ_MB_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma
    tau1 O.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 <= tau1 /\ tau1 <= tau0 /\ open_in (p2a_vtop V (tt - tau1)) O /\ gamma tau1 IN O
     ==> ?d. &0 < d /\
             !tau. &0 <= tau /\ tau <= tau0 /\ abs(tau - tau1) < d ==> gamma tau IN O`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tau1 /\ sqrt tau1 <= sqrt tau0 /\ sqrt tau1 pow 2 = tau1 /\
                &0 < sqrt tau0 /\ sqrt tau0 pow 2 = tau0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt tau0` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `s0 = sqrt tau1` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(SPECL [`S:real`; `E:real`; `r:real`; `eta:real`] P2AJ_MESH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `p = max (&0) (s0 - h / &2)` THEN
  ABBREV_TAC `p' = min S (s0 + h / &2)` THEN
  SUBGOAL_THEN `&0 <= p /\ p <= s0 /\ s0 <= p' /\ p < p' /\ p' <= S /\ p' - p <= h`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p' pow 2 <= tau0 /\ p' pow 2 - p pow 2 <= eta / &2 /\ (p' - p) * E <= r pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `S pow 2 = tau0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `p' pow 2 - p pow 2 = (p' - p) * (p' + p)` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * S * h` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * S * h = h * (&2 * S)`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `p:real`; `p':real`;
                 `sub:num->num`] P2AJ_MB_PIECE_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `(sub:num->num) o (t:num->num)`;
                 `gamma:real->A`; `p:real`; `p':real`] P2AJ_PP_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s pow 2 /\ s pow 2 <= tau0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN UNDISCH_TAC `S pow 2 = tau0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)`;
                   `\m. (gs:num->real->A) ((sub:num->num) m) (s pow 2)`;
                   `(gamma:real->A)(s pow 2)`; `t:num->num`] P2AJ_SLICE_SUBSEQ) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(A0:num->real) j < tt - tau1 /\ tt - tau1 <= (b:num->real) j` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau1 IN U INTER (W:num->A->bool) j` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `U:A->bool`; `phi:A->real^N`; `tt - tau1`; `O:A->bool`;
                 `(phi:A->real^N)((gamma:real->A) tau1)`] P2A_CHART_INV_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N) (phi((gamma:real->A) tau1)) =
                  gamma tau1` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(A0:num->real) j`; `(b:num->real) j`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_on")) (concl th))) THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift s0`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `r1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 (h / &2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(sqrt tau - s0) < min d1 (h / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - tau1))` THEN CONJ_TAC THENL
     [EXPAND_TAC "s0" THEN MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau pow 2 = tau /\ sqrt tau <= S` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN UNDISCH_TAC `sqrt tau0 = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= sqrt tau /\ sqrt tau <= p'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((gamma:real->A) tau)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `O:A->bool`)) (concl th) &&
    can (find_term ((=) `r1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN U INTER (W:num->A->bool) j` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `U:A->bool`; `phi:A->real^N`; `(gamma:real->A) tau`] P2A_REGION_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The limit lies in boxes strictly below their tops, and the multi-box     *)
(* piece limit (P2AJ_MB_PIECE_LIMIT, the analogue of P2AK_SB_PIECE_LIMIT    *)
(* for every short piece of [0,sqrt tau0]).                                 *)
(* ------------------------------------------------------------------------- *)

(* The limit lies in boxes strictly below their tops (P2AJ_STRICT_TOP with  *)
(* the cover P2AJ_LIM_COVER and the continuity P2AJ_MB_CONT).               *)

let P2AJ_LIM_STRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma tau.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 < tau /\ tau <= tau0
     ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gamma tau IN C j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  MATCH_MP_TAC P2AJ_STRICT_TOP THEN
  MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tau0:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AJ_MB_CONT THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                          `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                          `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                          `Rm:real`; `gs:num->real->A`; `Lb:real`; `sub:num->num`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AJ_LIM_COVER THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `x:A`; `W:num->A->bool`; `A0:num->real`; `eta:real`;
                          `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                          `Rm:real`; `gs:num->real->A`; `tau0:real`; `sub:num->num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `v:real`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPEC `v:real` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]]);;

(* The box and chart at the start p of a piece of the limit: for p = 0 the  *)
(* box at x, otherwise a box strictly below its top.                         *)

let P2AJ_START_BOX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gamma:real->A) tau0 p.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ gamma (&0) = x /\
     (!tau. &0 < tau /\ tau <= tau0
            ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gamma tau IN C j) /\
     &0 <= p /\ p pow 2 <= tau0
     ==> ?j k. j <= nb /\ k IN Fs j /\ a j <= tt - p pow 2 /\
               (tt - p pow 2 < b j \/ tt <= b j) /\
               gamma(p pow 2) IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
               dist(SND(chart_at (p2a_vatlas V (b j)) k) (gamma(p pow 2)),
                    SND(chart_at (p2a_vatlas V (b j)) k) k) < R j k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN
   `?j. j <= nb /\ (a:num->real) j <= tt - p pow 2 /\
        (tt - p pow 2 < (b:num->real) j \/ tt <= b j) /\
        (gamma:real->A)(p pow 2) IN (C:num->A->bool) j`
  (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THENL
   [ASM_CASES_TAC `p = &0` THENL
     [EXISTS_TAC `nb:num` THEN
      SUBGOAL_THEN `p pow 2 = &0` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      ASM_REWRITE_TAC[LE_REFL; IN_SING; REAL_SUB_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      UNDISCH_TAC `~(p = &0)` THEN UNDISCH_TAC `&0 <= p` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < nb:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A)(p pow 2)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term ((=) `(C:num->A->bool) j`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:A`] THEN ASM_REWRITE_TAC[]);;

(* The piece limit in one box with a general top: started in the R k ball  *)
(* of a chart at the limit point, the curves eventually stay in the chart   *)
(* (within 2 R k) with the displacement bound, the limit stays in the chart *)
(* with chart convergence and the displacement bound.                       *)

let P2AJ_BOX_PIECE_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (gs:num->real->A) Lb Rm0 sub
    (gamma:real->A) k p p' sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 <= Lb /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!n. p2a_admx V tt x b (gs (sub n)) /\ p2a_L_length V tt (gs (sub n)) b <= Lb /\
          (!tau. &0 <= tau /\ tau <= b
                 ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt (gs (sub n)) b tau)) /\
     (!s. p <= s /\ s <= p'
          ==> gamma(s pow 2) IN topspace(p2a_vtop V (tt - s pow 2)) /\
              !O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
                  ==> ?N. !n. N <= n ==> gs (sub n) (s pow 2) IN O) /\
     k IN Fs /\ gamma(p pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
     dist(SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2)),SND (chart_at (p2a_vatlas V b') k) k) < R k /\
     &0 <= p /\ p < p' /\ p' pow 2 <= b /\ sa < p /\ p' < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. p <= s /\ s <= p' ==> b' - T1 <= tt - s pow 2) /\
     (p' - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= r pow 2
     ==> ?N0.
           (!n s. N0 <= n /\ p <= s /\ s <= p'
                  ==> gs (sub n) (s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                      dist(SND (chart_at (p2a_vatlas V b') k) (gs (sub n) (s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k) /\
           (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
                     ==> dist(SND (chart_at (p2a_vatlas V b') k) (gs (sub n) (s' pow 2)),
                              SND (chart_at (p2a_vatlas V b') k) (gs (sub n) (s pow 2))) pow 2
                         <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
           (!s. p <= s /\ s <= p'
                ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                    dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k /\
                    ((\n. SND (chart_at (p2a_vatlas V b') k) (gs (sub n) (s pow 2))) --> SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)))
                    sequentially) /\
           (!s s'. p <= s /\ s <= s' /\ s' <= p'
                   ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) pow 2
                       <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `p':real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> &0 <= s pow 2 /\ s pow 2 <= b /\ b' - T1 <= tt - s pow 2 /\
            a' < tt - s pow 2 /\ tt - s pow 2 <= b'`
  (LABEL_TAC "FACTS") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) &&
        can (find_term ((=) `p':real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* eventually the curves start in the radius R k ball of the chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `tt - p pow 2`; `(gamma:real->A)(p pow 2)`;
                 `\n. (gs:num->real->A) ((sub:num->num) n) (p pow 2)`] P2AK_CHART_CONV) THEN
  ANTS_TAC THENL
   [USE_THEN "FACTS" (MP_TAC o SPEC `p:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `(R:A->real) k - dist((phi:A->real^N)((gamma:real->A)(p pow 2)),phi k)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0" o BETA_RULE)) THEN EXISTS_TAC `N0:num` THEN
  SUBGOAL_THEN
   `!n. N0 <= n ==> (gs:num->real->A) ((sub:num->num) n) (p pow 2) IN U INTER W /\
                    dist((phi:A->real^N)(gs (sub n) (p pow 2)),phi k) < (R:A->real) k`
  (LABEL_TAC "START") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`;
                   `(phi:A->real^N)((gamma:real->A)(p pow 2))`; `(phi:A->real^N) k`]
                  DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* stay in the chart *)
  SUBGOAL_THEN
   `!n s. N0 <= n /\ p <= s /\ s <= p'
          ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(gs (sub n) (s pow 2)),phi(gs (sub n) (p pow 2))) <= r`
  (LABEL_TAC "STAY") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    USE_THEN "START" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(gs:num->real->A) ((sub:num->num) n)`; `Lb:real`;
                   `Rm0:real`; `k:A`; `p:real`; `p':real`; `sa:real`; `sb:real`] P2AJ_STAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. N0 <= n /\ p <= s /\ s <= p'
          ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(gs (sub n) (s pow 2)),phi k) <= &2 * (R:A->real) k`
  (LABEL_TAC "IN2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "STAY" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "START" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s pow 2))`;
                   `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`;
                   `(phi:A->real^N) k`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the displacement bound for the curves *)
  SUBGOAL_THEN
   `!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
             ==> dist((phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s' pow 2)),
                      phi(gs (sub n) (s pow 2))) pow 2 <= (s' - s) * E`
  (LABEL_TAC "FE") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    SUBGOAL_THEN `&0 <= s /\ sa < s /\ s' < sb /\ s' pow 2 <= b` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!u. s <= u /\ u <= s' ==> b' - T1 <= tt - u pow 2` ASSUME_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      USE_THEN "FACTS" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. s <= u /\ u <= s'
          ==> (gs:num->real->A) ((sub:num->num) n) (u pow 2) IN U INTER W /\
              (phi:A->real^N)(gs (sub n) (u pow 2)) IN cball(phi k,&6 * (R:A->real) k)`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      USE_THEN "IN2" (MP_TAC o SPECL [`n:num`; `u:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (u pow 2))`]
                    DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(gs:num->real->A) ((sub:num->num) n)`; `Lb:real`;
                   `Rm0:real`; `k:A`; `s:real`; `s':real`; `sa:real`; `sb:real`] P2AJ_FE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the limit curve on [p,p'] *)
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> (gamma:real->A)(s pow 2) IN U INTER W /\
            dist((phi:A->real^N)(gamma(s pow 2)),phi k) <= &2 * (R:A->real) k /\
            ((\n. phi((gs:num->real->A) ((sub:num->num) n) (s pow 2))) --> phi(gamma(s pow 2)))
            sequentially`
  (LABEL_TAC "LIM") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "FACTS" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIMs"))] THEN
    SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN {y | y IN U INTER W /\
                    (phi:A->real^N) y IN cball(phi k,&2 * (R:A->real) k)}` MP_TAC THENL
     [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                     `(phi:A->real^N) k`; `&2 * (R:A->real) k`; `tt - s pow 2`]
                    P2AK_CHART_CBALL_CLOSED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      USE_THEN "LIMs" (MP_TAC o SPEC
        `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)) DIFF
         {y | y IN U INTER W /\ (phi:A->real^N) y IN cball(phi k,&2 * (R:A->real) k)}`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N + N0:num`) THEN
      REWRITE_TAC[ARITH_RULE `N <= N + N0:num`; IN_DIFF; IN_ELIM_THM; IN_CBALL] THEN
      USE_THEN "IN2" (MP_TAC o SPECL [`N + N0:num`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `N0 <= N + N0:num`]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) (N + N0)) (s pow 2))`]
                    DIST_SYM) THEN
      MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_CBALL] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `tt - s pow 2`; `(gamma:real->A)(s pow 2)`;
                   `\n. (gs:num->real->A) ((sub:num->num) n) (s pow 2)`] P2AK_CHART_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the displacement bound for the limit *)
  MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (s' - s) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dist((phi:A->real^N)((gamma:real->A)(s' pow 2)),phi(gamma(s pow 2))) <=
                sqrt((s' - s) * E)` MP_TAC THENL
   [REWRITE_TAC[dist] THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s' pow 2)) -
                    phi(gs (sub n) (s pow 2))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
       [USE_THEN "LIM" (MP_TAC o SPEC `s':real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "LIM" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM dist] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN USE_THEN "FE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((s' - s) * E) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[DIST_POS_LE];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

(* The multi-box piece limit: for every short piece [p,p'] the limit and the *)
(* curves (eventually) lie in one box chart, with chart convergence and the  *)
(* displacement bounds (the analogue of P2AK_SB_PIECE_LIMIT).                *)

let P2AJ_MB_PIECE_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma p p'.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\ gamma (&0) = x /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 <= p /\ p < p' /\ p' pow 2 <= tau0 /\ p' pow 2 - p pow 2 <= eta / &2 /\
     (p' - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= r pow 2
     ==> ?j k N0.
           j <= nb /\ k IN Fs j /\
           (?sa sb. sa < p /\ p' < sb /\
                    !s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 <= b j) /\
           (!s. p <= s /\ s <= p' ==> b j - (b j - a j + eta / &2) <= tt - s pow 2) /\
           (!n s. N0 <= n /\ p <= s /\ s <= p'
                  ==> gs (sub n) (s pow 2) IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
                      dist(SND(chart_at (p2a_vatlas V (b j)) k) (gs (sub n) (s pow 2)),
                           SND(chart_at (p2a_vatlas V (b j)) k) k) <= &2 * R j k) /\
           (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
                     ==> dist(SND(chart_at (p2a_vatlas V (b j)) k) (gs (sub n) (s' pow 2)),
                              SND(chart_at (p2a_vatlas V (b j)) k) (gs (sub n) (s pow 2))) pow 2
                         <= (s' - s) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm))) /\
           (!s. p <= s /\ s <= p'
                ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
                    dist(SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s pow 2)),
                         SND(chart_at (p2a_vatlas V (b j)) k) k) <= &2 * R j k /\
                    ((\n. SND(chart_at (p2a_vatlas V (b j)) k) (gs (sub n) (s pow 2))) -->
                     SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s pow 2))) sequentially) /\
           (!s s'. p <= s /\ s <= s' /\ s' <= p'
                   ==> dist(SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s' pow 2)),
                            SND(chart_at (p2a_vatlas V (b j)) k) (gamma(s pow 2))) pow 2
                       <= (s' - s) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN `p pow 2 <= p' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!tau. &0 < tau /\ tau <= tau0
                      ==> ?j. j < nb /\ (a:num->real) j <= tt - tau /\
                              tt - tau < (b:num->real) j /\
                              (gamma:real->A) tau IN (C:num->A->bool) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AJ_LIM_STRICT THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `x:A`; `W:num->A->bool`; `A0:num->real`; `eta:real`;
                          `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                          `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`;
                          `sub:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gamma:real->A`; `tau0:real`; `p:real`] P2AJ_START_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:real`; `(A0:num->real) j`; `(b:num->real) j`; `p:real`; `p':real`]
                P2AJ_WINDOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa:real` (X_CHOOSE_THEN `sb:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= p'
                    ==> (b:num->real) j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 <= p' pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`; `gs:num->real->A`; `Lb:real`;
                 `Rm:real`; `sub:num->num`; `gamma:real->A`; `k:A`; `p:real`; `p':real`;
                 `sa:real`; `sb:real`] P2AJ_BOX_PIECE_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `(sub:num->num) n` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                            `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                            `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th) &&
        can (find_term ((=) `C:num->A->bool`)) (concl th) &&
        can (find_term ((=) `sub:num->num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:A`; `N0:num`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distances in a region chart at a single time.  The open submanifold W of *)
(* the slice at b' with the pullback of the slice metric at t is isometric  *)
(* to W in the slice at t (P2AJ_REG_ISO); hence segments in a region chart  *)
(* bound the slice distance (P2AJ_SEG_DIST), and a curve leaving a chart    *)
(* ball is long (P2AJ_REGION_FIRST_EXIT), so points at a small slice        *)
(* distance are chart-close (P2AJ_DIST_CHART_CLOSE).                        *)
(* ------------------------------------------------------------------------- *)

(* Curves of an open submanifold are curves of the manifold, with the same  *)
(* length, and conversely (P2AJ_C1_RESTRICT and P2AJ_LENGTH_RESTRICT are   *)
(* copies of P2AP_C1_CURVE_RESTRICT and P2AP_LENGTH_RESTRICT of pc_p2a_par, *)
(* whose closure is not loaded here).                                        *)

let P2AJ_C1_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_c1_curve (top,atlas) gamma a b /\
         (!t. t IN real_interval[a,b] ==> gamma t IN W)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (gamma:real->A) t IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gamma:real->A)
                   (topspace (subtopology euclideanreal (real_interval[a,b]))) SUBSET W` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W:A->bool,phi:A->real^N)`) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[FST; SND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

let P2AJ_C1_TO_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. t IN real_interval[a,b] ==> gamma t IN W)
     ==> mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,psi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

let P2AJ_LENGTH_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_length (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b =
         mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AJ_C1_RESTRICT) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top /\ gamma t IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN restrict_atlas atlas W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U INTER W:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The distance of a manifold is at most that of an open submanifold.       *)

let P2AJ_DIST_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) x y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     mfd_joinable (subtopology top W,restrict_atlas atlas W) x y
     ==> mfd_joinable (top,atlas) x y /\
         mfd_dist (top,atlas) g x y <=
         mfd_dist (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!gamma:real->A.
      mfd_c1_curve (subtopology (top:A topology) W,
                    restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W) gamma (&0) (&1) /\
      gamma(&0) = x /\ gamma(&1) = y
      ==> mfd_joinable (top,atlas) x y /\
          mfd_dist (top,atlas) (g:A->real^N^N) x y <=
          mfd_length (restrict_atlas atlas W) (restrict_metric atlas W g) gamma (&0) (&1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AJ_C1_RESTRICT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] P2AJ_LENGTH_RESTRICT) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_joinable] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_joinable")) (concl th) &&
    not(is_forall(concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_length (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W)
                  (restrict_metric atlas W (g:A->real^N^N)) (gamma0:real->A) (&0) (&1)` THEN
    EXISTS_TAC `gamma0:real->A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `gamma:real->A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* Smooth identity maps restrict to open submanifolds.                     *)

let P2AJ_SMOOTH_MAP_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (atlas':((A->bool)#(A->real^N))->bool) W.
     smooth_manifold_atlas top atlas /\ mfd_smooth_map atlas atlas' W (\y:A. y)
     ==> mfd_smooth_map (restrict_atlas atlas W) (restrict_atlas atlas' W) W (\y:A. y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`V1:A->bool`; `p1:A->real^N`; `V2:A->bool`; `p2:A->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U1:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))
    (X_CHOOSE_THEN `U2:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U1:A->bool`; `p1:A->real^N`; `U2:A->bool`; `p2:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x:A | x IN (U1 INTER W) INTER W /\ x IN U2 INTER W} =
                {x | x IN U1 INTER W /\ x IN U2}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC
    (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT] SMOOTH_MAP_ON_EQ) th)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `p1:A->real^N`; `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]);;

(* A region gives a diffeomorphism (the identity) of the open submanifolds W *)
(* of the slices at b' and at t.                                             *)

let P2AJ_REGION_DIFFEO_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' t.
     p2a_region V W a' b' /\ a' < t /\ t <= b'
     ==> smooth_manifold_atlas (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) /\ smooth_manifold_atlas (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) /\
         mfd_diffeo (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))) (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))) (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  SUBGOAL_THEN `topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) = W /\ topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) = W` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mfd_diffeo] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_diffeo] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT];
    MATCH_MP_TAC P2AJ_SMOOTH_MAP_RESTRICT THEN EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AJ_SMOOTH_MAP_RESTRICT THEN EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t` THEN
    ASM_REWRITE_TAC[]]);;

(* The isometry: W in the slice at b' with the pullback of the slice metric *)
(* at t is isometric (by the identity) to W in the slice at t; in a region  *)
(* chart the pulled back metric is p2a_rlocal at t.                         *)

let P2AJ_REG_ISO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' t.
     p2a_svs V /\ p2a_region V W a' b' /\ a' < t /\ t <= b' /\ ~(W = {})
     ==> mfd_isometry ((subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)),(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))) (mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))) ((subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)),(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)) (\y:A. y) (\y. y) /\
         riemannian_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))) /\ riemannian_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)) /\
         riemannian_metric (p2a_vatlas V t) (p2a_vmetric V t) /\
         (!U (phi:A->real^N) x.
            (U,phi) IN p2a_vatlas V b' /\ x IN U INTER W
            ==> metric_local (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (U INTER W,phi) (mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))) (phi x) =
                p2a_rlocal V W b' (U INTER W,phi) t (phi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`]
                P2AJ_REGION_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (p2a_vmetric V t)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN REWRITE_TAC[p2a_svs] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `t:real`) THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `\y:A. y`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (x:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi':A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) /\
                (U' INTER W:A->bool,phi':A->real^N) IN (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN CONJ_TAC THENL
     [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `U':A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN U' INTER W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `\y:A. y`; `\y:A. y`; `(restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))`;
                 `U INTER W:A->bool`; `phi:A->real^N`; `U' INTER W:A->bool`; `phi':A->real^N`;
                 `x:A`] MFD_PULLBACK_METRIC_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `t:real`; `(U':A->bool,phi':A->real^N)`; `x:A`] P2A_RLOCAL_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FST] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(phi':A->real^N) o (\y:A. y) o chart_inv (U INTER W,phi:A->real^N) =
                chart_trans (U INTER W,phi) (U',phi')` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `chart_trans (U INTER W,phi:A->real^N) (U',phi':A->real^N) (phi x) = phi' x`
  SUBST1_TAC THENL
   [REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'`; `U:A->bool`; `phi:A->real^N`;
                   `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (U' INTER W,phi':A->real^N) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)) (phi' x) =
                metric_local (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (U',phi') (p2a_vmetric V t) (phi' x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    REFL_TAC]);;

(* The single-time distance bound in a region chart: points of a segment in *)
(* the chart image are at slice distance at most sqrt(Gm) times their chart *)
(* distance (the segment curve, P2AJ_REG_ISO, P2AJ_DIST_RESTRICT).           *)

let P2AJ_SEG_DIST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' U (phi:A->real^N) t z1 z2 lam Gm.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < t /\ t <= b' /\ segment[z1,z2] SUBSET IMAGE phi (U INTER W) /\ &0 <= lam /\
     (!y v. y IN segment[z1,z2]
            ==> lam * norm v pow 2 <= v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) /\
                v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) <= Gm * norm v pow 2)
     ==> mfd_joinable (p2a_vtop V t,p2a_vatlas V t)
                      (chart_inv (U INTER W,phi) z1) (chart_inv (U INTER W,phi) z2) /\
         mfd_dist (p2a_vtop V t,p2a_vatlas V t) (p2a_vmetric V t)
                  (chart_inv (U INTER W,phi) z1) (chart_inv (U INTER W,phi) z2)
         <= sqrt Gm * dist(z1,z2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(W:A->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`z1:real^N`; `z2:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2AJ_REG_ISO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`]
                P2AJ_REGION_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the segment curve in the region manifold *)
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `U INTER W:A->bool`; `phi:A->real^N`; `z1:real^N`; `z2:real^N`]
                GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `U INTER W:A->bool`; `phi:A->real^N`;
                 `z1:real^N`; `z2:real^N`; `lam:real`; `Gm:real`; `segment[z1:real^N,z2]`]
                GRGD_SEGMENT_LENGTH_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?x:A. x IN U INTER W /\ (phi:A->real^N) x = (y:real^N)` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `metric_local (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (U INTER W,phi:A->real^N) (mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))) (phi x) =
                  p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) t (phi(x:A))` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `g0 = \u. chart_inv (U INTER W:A->bool,phi:A->real^N) (z1 + u % (z2 - z1))` THEN
  SUBGOAL_THEN `(g0:real->A) (&0) = chart_inv (U INTER W,phi:A->real^N) z1 /\
                g0 (&1) = chart_inv (U INTER W,phi) z2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g0" THEN REWRITE_TAC[] THEN CONJ_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `g0:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "g0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable ((subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)),(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))) (chart_inv (U INTER W,phi:A->real^N) z1)
                                         (chart_inv (U INTER W,phi) z2)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `g0:real->A` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g0" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g0:real->A) (&0) IN topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) /\ g0 (&1) IN topspace (subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `&0`; `&1`] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    EXPAND_TAC "g0" THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))`; `\y:A. y`; `\y:A. y`]
                MFD_DIST_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`chart_inv (U INTER W,phi:A->real^N) z1`;
                             `chart_inv (U INTER W,phi:A->real^N) z2`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `W:A->bool`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`;
                 `chart_inv (U INTER W,phi:A->real^N) z1`;
                 `chart_inv (U INTER W,phi:A->real^N) z2`] P2AJ_DIST_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* First exit from a region chart ball: a C^1 curve of the slice at t that  *)
(* leaves the chart ball of radius r has length at least sqrt(c) r (the    *)
(* curve up to the first exit lies in W; GRGD_CHART_LENGTH_LOWER in the     *)
(* region manifold through the isometry, as in GRGD_FIRST_EXIT).            *)

let P2AJ_REGION_FIRST_EXIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' U (phi:A->real^N) t (gamma:real->A) r c C.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < t /\ t <= b' /\
     mfd_c1_curve (p2a_vtop V t,p2a_vatlas V t) gamma (&0) (&1) /\
     gamma(&0) IN U INTER W /\ &0 < r /\
     cball(phi(gamma(&0)),r) SUBSET IMAGE phi (U INTER W) /\ &0 <= c /\
     (!y v. y IN cball(phi(gamma(&0)),r)
            ==> c * norm v pow 2 <= v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) /\
                v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) <= C * norm v pow 2) /\
     (?u. u IN real_interval[&0,&1] /\
          ~(gamma u IN U INTER W /\ phi(gamma u) IN ball(phi(gamma(&0)),r)))
     ==> sqrt c * r <= mfd_length (p2a_vatlas V t) (p2a_vmetric V t) gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(W:A->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2AJ_REG_ISO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`]
                P2AJ_REGION_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `t:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),
                                p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (gamma:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t,p2a_vatlas V t) (gamma:real->A) (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  (* the open chart ball in the slice *)
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)
            {z:A | z IN U INTER W /\ (phi:A->real^N) z IN ball(phi(gamma(&0)),r)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN `{z:A | z IN U INTER W /\ (phi:A->real^N) z IN ball(phi(gamma(&0)),r)} =
                  {z | z IN U /\ phi z IN ball(phi(gamma(&0)),r)} INTER W` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `gamma:real->A`;
                 `{z:A | z IN U INTER W /\ (phi:A->real^N) z IN ball(phi(gamma(&0)),r)}`]
                GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN EXISTS_TAC `u:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  (* the closed chart ball contains the curve up to t1 *)
  SUBGOAL_THEN
   `(gamma:real->A) t1 IN
    {y | y IN U INTER W /\ (phi:A->real^N) y IN cball(phi(gamma(&0)),r)}`
  MP_TAC THENL
   [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AK_CHART_CBALL_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `t1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `r <= dist((phi:A->real^N)((gamma:real->A)(&0)),phi(gamma t1))` ASSUME_TAC THENL
   [UNDISCH_TAC `~((gamma:real->A) t1 IN U INTER W /\
                   (phi:A->real^N)(gamma t1) IN ball(phi(gamma(&0)),r))` THEN
    ASM_REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curve on [0,t1] in the region manifold *)
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,t1]
        ==> (gamma:real->A) u IN U INTER W /\
            (phi:A->real^N)(gamma u) IN cball(phi(gamma(&0)),r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `v:real = t1` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t1:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t,p2a_vatlas V t) (gamma:real->A) (&0) t1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve ((subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)),(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))) (gamma:real->A) (&0) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AJ_C1_TO_RESTRICT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t1:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve ((subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)),(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))) (gamma:real->A) (&0) t1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gamma:real->A) = (\y:A. y) o gamma` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC GRGD_ISOMETRY_C1 THEN
    MAP_EVERY EXISTS_TAC [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `gamma:real->A`; `&0`; `t1:real`;
                 `U INTER W:A->bool`; `phi:A->real^N`; `c:real`; `C:real`;
                 `cball((phi:A->real^N)((gamma:real->A)(&0)),r)`]
                GRGD_CHART_LENGTH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:A. x IN U INTER W /\ (phi:A->real^N) x = y`
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `metric_local (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (U INTER W,phi:A->real^N) (mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))) (phi x) =
                  p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) t (phi(x:A))` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool))`; `(mfd_pullback_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (W:A->bool)) (restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool)) (\y:A. y) (restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)))`; `(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool))`; `(restrict_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (W:A->bool) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t))`; `\y:A. y`; `\y:A. y`;
                 `gamma:real->A`; `&0`; `t1:real`] GRGD_ISOMETRY_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\y:A. y) o (gamma:real->A) = gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `W:A->bool`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`;
                 `gamma:real->A`; `&0`; `t1:real`] P2AJ_LENGTH_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`;
                 `gamma:real->A`; `&0`; `t1:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t`;
                 `gamma:real->A`; `t1:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sqrt c`; `r:real`;
                 `dist((phi:A->real^N)((gamma:real->A)(&0)),phi(gamma t1))`] REAL_LE_LMUL) THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* Small slice distance stays in the region chart ball: at distance less    *)
(* than sqrt(c) r from z the points are in the chart ball of radius r.     *)

let P2AJ_DIST_CHART_CLOSE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' U (phi:A->real^N) t (z:A) w r c C.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < t /\ t <= b' /\ z IN U INTER W /\ &0 < r /\
     cball(phi z,r) SUBSET IMAGE phi (U INTER W) /\ &0 <= c /\
     (!y v. y IN cball(phi z,r)
            ==> c * norm v pow 2 <= v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) /\
                v dot (p2a_rlocal V W b' (U INTER W,phi) t y ** v) <= C * norm v pow 2) /\
     mfd_joinable (p2a_vtop V t,p2a_vatlas V t) z w /\
     mfd_dist (p2a_vtop V t,p2a_vatlas V t) (p2a_vmetric V t) z w < sqrt c * r
     ==> w IN U INTER W /\ phi w IN ball(phi z,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  UNDISCH_TAC `mfd_dist (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t,p2a_vatlas V t) (p2a_vmetric V t) (z:A) w <
               sqrt c * r` THEN
  REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[mfd_dist] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_joinable] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_joinable")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_length (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (p2a_vmetric V t) (gamma0:real->A) (&0) (&1)` THEN
    EXISTS_TAC `gamma0:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AJ_REGION_FIRST_EXIT THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Clause (b2) of Lemma 7.2, the uniform convergence of the subsequence in  *)
(* the slice distances (uniform chart convergence on short pieces,          *)
(* P2AJ_UNIF_CONV, and the chart segment bound P2AJ_SEG_DIST).              *)
(* ------------------------------------------------------------------------- *)

(* Finitely many eventual properties hold eventually together.               *)

let P2AJ_EVENTUALLY_FINITE = prove
 (`!(P:num->num->bool) M.
     (!i. i < M ==> ?N. !n. N <= n ==> P i n)
     ==> ?N. !n. N <= n ==> !i. i < M ==> P i n`,
  GEN_TAC THEN INDUCT_TAC THENL [REWRITE_TAC[LT] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "SUC")) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `M < SUC M`] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num = M` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN ASM_ARITH_TAC]);;

(* Pointwise convergence with uniform Hoelder-1/2 bounds is uniform on a    *)
(* compact interval (a finite grid).                                         *)

let P2AJ_UNIF_CONV = prove
 (`!(Yn:num->real->real^N) (Y:real->real^N) p q E N0.
     p <= q /\ &0 <= E /\
     (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= q
               ==> dist(Yn n s',Yn n s) pow 2 <= (s' - s) * E) /\
     (!s s'. p <= s /\ s <= s' /\ s' <= q ==> dist(Y s',Y s) pow 2 <= (s' - s) * E) /\
     (!s. p <= s /\ s <= q ==> ((\n. Yn n s) --> Y s) sequentially)
     ==> !e. &0 < e ==> ?N. !n s. N <= n /\ p <= s /\ s <= q ==> dist(Yn n s,Y s) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ d * E < (e / &3) pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (e / &3) pow 2 /\ &0 < E + &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `(e / &3) pow 2 / (E + &1)` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(e / &3) pow 2 / (E + &1) * (E + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* small steps give small displacements *)
  SUBGOAL_THEN `!z1 z2:real^N u. &0 <= u /\ u <= d /\ dist(z1,z2) pow 2 <= u * E
                                 ==> dist(z1,z2) < e / &3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `u * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the grid *)
  MP_TAC(SPEC `(q - p) / d` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `m0:num`) THEN
  SUBGOAL_THEN `?M. 1 <= M /\ &0 < &M /\ (q - p) / &M <= d` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `m0 + 1` THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &(m0 + 1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `(q - p) / d <= &m0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 < d * &1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?hh. (q - p) / &M = hh /\ &0 <= hh /\ &M * hh = q - p /\ hh <= d`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(q - p) / &M` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < SUC M ==> p <= p + &m * hh /\ p + &m * hh <= q` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> p <= p + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      SUBGOAL_THEN `&m * hh <= &M * hh` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `m < SUC M` THEN ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m n. dist((Yn:num->real->real^N) n (p + &m * hh),
                              (Y:real->real^N)(p + &m * hh)) < e / &3`; `SUC M`]
                P2AJ_EVENTUALLY_FINITE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p + &m * hh` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
  EXISTS_TAC `N0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N0 <= n:num /\ N1 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m < SUC M /\ p + &m * hh <= s /\ s <= p + &m * hh + hh`
  (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `p:real = q` THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[ARITH_RULE `0 < SUC M`; REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`q - p`; `M:num`; `s - p`] P2AK_PARTITION_INDEX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `i:num` THEN
    CONJ_TAC THENL [UNDISCH_TAC `i < M:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `s - p <= &(SUC i) * hh` THEN UNDISCH_TAC `&i * hh <= s - p` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `q:real`)) (concl th) && can (find_term ((=) `hh:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `g = p + &m * hh` THEN
  SUBGOAL_THEN `dist((Yn:num->real->real^N) n s,Yn n g) < e / &3 /\
                dist(Yn n g,(Y:real->real^N) g) < e / &3 /\
                dist(Y g,Y s) < e / &3` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s - g` THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N0:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N1:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s - g` THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not(can (find_term ((=) `N0:num`)) (concl th)) &&
        can (find_term ((=) `Y:real->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "real_pow")) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Yn:num->real->real^N) n s`; `(Yn:num->real->real^N) n g`;
                 `(Y:real->real^N) s`] DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(Yn:num->real->real^N) n g`; `(Y:real->real^N) g`;
                 `(Y:real->real^N) s`] DIST_TRIANGLE) THEN
  REAL_ARITH_TAC);;

(* The metric bounds of a box chart for the times [a j - eta / 2,b j].     *)

let P2AJ_MB_CHART_BOUNDS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm j k.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ j <= nb /\ k IN Fs j
     ==> !t z u. a j - eta / &2 <= t /\ t <= b j /\
                 z IN cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&6 * R j k)
                 ==> lam * norm u pow 2 <=
                     u dot (p2a_rlocal V (W j) (b j)
                              (FST(chart_at (p2a_vatlas V (b j)) k) INTER W j,
                               SND(chart_at (p2a_vatlas V (b j)) k)) t z ** u) /\
                     u dot (p2a_rlocal V (W j) (b j)
                              (FST(chart_at (p2a_vatlas V (b j)) k) INTER W j,
                               SND(chart_at (p2a_vatlas V (b j)) k)) t z ** u)
                     <= Gm * norm u pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2ak_bxd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`; `u:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^N`; `u:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* On a short piece the curves converge uniformly in the slice distances    *)
(* (uniform chart convergence, P2AJ_UNIF_CONV, and P2AJ_SEG_DIST).           *)

let P2AJ_PIECE_DIST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma p p'.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\ gamma (&0) = x /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 <= p /\ p < p' /\ p' pow 2 <= tau0 /\ p' pow 2 - p pow 2 <= eta / &2 /\
     (p' - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= r pow 2
     ==> !e. &0 < e
             ==> ?N. !n s. N <= n /\ p <= s /\ s <= p'
                           ==> mfd_dist (p2a_vtop V (tt - s pow 2),p2a_vatlas V (tt - s pow 2))
                                        (p2a_vmetric V (tt - s pow 2))
                                        (gs (sub n) (s pow 2)) (gamma(s pow 2)) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP P2AJ_MB_PIECE_LIMIT th) THEN STRIP_ASSUME_TAC th) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `N0:num`
    STRIP_ASSUME_TAC))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n s. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s pow 2))`;
                 `\s. (phi:A->real^N)((gamma:real->A)(s pow 2))`; `p:real`; `p':real`;
                 `E:real`; `N0:num`] P2AJ_UNIF_CONV) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (sqrt Gm + &1)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `Gm:real` SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
  EXISTS_TAC `N0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N0 <= n:num /\ N1 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N0:num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(A0:num->real) j < tt - s pow 2 /\ tt - s pow 2 <= (b:num->real) j /\
                (a:num->real) j - eta / &2 <= tt - s pow 2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eta:real`)) (concl th) &&
      can (find_term ((=) `p':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z1 = (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s pow 2))` THEN
  ABBREV_TAC `z2 = (phi:A->real^N)((gamma:real->A)(s pow 2))` THEN
  SUBGOAL_THEN `segment[z1:real^N,z2] SUBSET cball((phi:A->real^N) k,&2 * (R:num->A->real) j k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CBALL; IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball((phi:A->real^N) k,&2 * (R:num->A->real) j k) SUBSET
                cball(phi k,&6 * R j k)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `U:A->bool`; `phi:A->real^N`; `tt - s pow 2`; `z1:real^N`; `z2:real^N`;
                 `lam:real`; `Gm:real`] P2AJ_SEG_DIST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N) z1 =
                (gs:num->real->A) ((sub:num->num) n) (s pow 2) /\
                chart_inv (U INTER W j,phi) z2 = (gamma:real->A)(s pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["z1"; "z2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(A0:num->real) j`; `(b:num->real) j`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sqrt Gm * dist(z1:real^N,z2)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sqrt Gm` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt Gm * e / (sqrt Gm + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    SUBGOAL_THEN `&0 < sqrt Gm + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `x * y / z = (x * y) / z`] THEN
    ASM_REAL_ARITH_TAC]);;

(* (b2): the subsequence converges uniformly in the slice distances.         *)

let P2AJ_B2 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\ gamma (&0) = x /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O)
     ==> !e. &0 < e
             ==> ?N. !n. N <= n
                     ==> !tau. &0 <= tau /\ tau <= tau0
                               ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                            (p2a_vmetric V (tt - tau))
                                            (gs (sub n) tau) (gamma tau) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt tau0` THEN
  SUBGOAL_THEN `&0 < S /\ S pow 2 = tau0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`S:real`; `E:real`; `r:real`; `eta:real`] P2AJ_MESH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\i n. !s. &i * h <= s /\ s <= &(SUC i) * h
               ==> mfd_dist (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2),p2a_vatlas V (tt - s pow 2))
                            (p2a_vmetric V (tt - s pow 2))
                            ((gs:num->real->A) ((sub:num->num) n) (s pow 2))
                            ((gamma:real->A)(s pow 2)) < e`; `M:num`]
   P2AJ_EVENTUALLY_FINITE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &i * h /\ &i * h < &(SUC i) * h /\ &(SUC i) * h <= S`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&M * h = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `i < M:num` THEN ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                   `gamma:real->A`; `&i * h`; `&(SUC i) * h`] P2AJ_PIECE_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `S pow 2 = tau0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(&(SUC i) * h) pow 2 - (&i * h) pow 2 = h * (&(SUC i) * h + &i * h)`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * S * h` THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * S * h = h * (&2 * S)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ARITH `(&i + &1) * h - &i * h = h`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real`; `M:num`; `sqrt tau`] P2AK_PARTITION_INDEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN UNDISCH_TAC `sqrt tau0 = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sqrt tau`) THEN ASM_SIMP_TAC[SQRT_POW_2]);;

