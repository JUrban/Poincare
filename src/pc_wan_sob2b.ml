(* ========================================================================= *)
(* pc_wan_sob2b: limits in W^(1,2). Closure and lower semicontinuity of the  *)
(* Dirichlet integral under L^2_loc limits (WAN_DIR_LSC), weak convergence   *)
(* of the weak partials (WAN_WEAK_PARTIALS_CONV), the metric forms           *)
(* WAN_GDIR_LSC and WAN_RADON_RIESZ_G, and the Lipschitz chain rule          *)
(* WAN_CHAIN_LIP_W12.                                                        *)
(* Tool: a Mazur lemma in L^2 proved from the parallelogram law and         *)
(* RIESZ_FISCHER (convex combinations of tails of a bounded sequence of     *)
(* d-tuples converge strongly), which replaces weak compactness.            *)
(* Statement constants: pc_wan_defs, pc_wan_p4defs.                          *)
(* ========================================================================= *)

needs "src/pc_wan_sob2c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Convex combinations of tails, supported in an index set S, and the sum   *)
(* of squared L^2 norms of d-tuples.                                         *)
(* ------------------------------------------------------------------------- *)

let wan_tcc = new_definition
 `wan_tcc (S:num->bool) n N (lam:num->real) <=>
    n <= N /\ (!m. &0 <= lam m) /\ (!m. ~(m IN S /\ n <= m /\ m <= N) ==> lam m = &0) /\
    sum(n..N) lam = &1`;;

let wan_tcomb = new_definition
 `wan_tcomb n N (lam:num->real) (g:num->num->real^M->real^K) =
    \i x. vsum(n..N) (\m. lam m % g m i x)`;;

let wan_qf = new_definition
 `wan_qf (s:real^M->bool) d (FF:num->real^M->real^K) =
    sum(1..d) (\i. drop(integral s (\x. lift(norm(FF i x) pow 2))))`;;

let WAN_TCOMB_LSPACE = prove
 (`!(s:real^M->bool) n N lam (g:num->num->real^M->real^K) i.
     (!m. g m i IN lspace s (&2)) ==> wan_tcomb n N lam g i IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_tcomb] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LSPACE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC LSPACE_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let WAN_QF_POS = prove
 (`!(s:real^M->bool) d (FF:num->real^M->real^K).
     (!i. 1 <= i /\ i <= d ==> FF i IN lspace s (&2)) ==> &0 <= wan_qf s d FF`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_qf] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(FF:num->real^M->real^K) i`; `s:real^M->bool`] WAN_SOB_LNORM2_SQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_LE_POW_2]);;

let WAN_QF_COMPONENT_LE = prove
 (`!(s:real^M->bool) d (FF:num->real^M->real^K) i.
     (!i. 1 <= i /\ i <= d ==> FF i IN lspace s (&2)) /\ 1 <= i /\ i <= d
     ==> lnorm s (&2) (FF i) pow 2 <= wan_qf s d FF`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_qf] THEN
  MP_TAC(ISPECL [`(FF:num->real^M->real^K) i`; `s:real^M->bool`] WAN_SOB_LNORM2_SQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`{i:num}`; `1..d`;
                 `\i. drop(integral s (\x. lift(norm((FF:num->real^M->real^K) i x) pow 2)))`]
                SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SUBSET; IN_SING; IN_NUMSEG; IN_DIFF] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(FF:num->real^M->real^K) j`; `s:real^M->bool`] WAN_SOB_LNORM2_SQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_LE_POW_2]);;

let WAN_NORM_PARALLELOGRAM = prove
 (`!a b:real^K. norm(a - b) pow 2 =
                &2 * norm a pow 2 + &2 * norm b pow 2 - &4 * norm(inv(&2) % (a + b)) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
                                  DOT_LADD; DOT_RADD] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let WAN_QF_PARALLELOGRAM = prove
 (`!(s:real^M->bool) d (FF:num->real^M->real^K) GG.
     (!i. 1 <= i /\ i <= d ==> FF i IN lspace s (&2) /\ GG i IN lspace s (&2))
     ==> wan_qf s d (\i x. FF i x - GG i x) =
         &2 * wan_qf s d FF + &2 * wan_qf s d GG -
         &4 * wan_qf s d (\i x. inv(&2) % (FF i x + GG i x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_qf] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm((FF:num->real^M->real^K) i x) pow 2)) integrable_on s /\
    (\x. lift(norm((GG:num->real^M->real^K) i x) pow 2)) integrable_on s /\
    (\x. lift(norm(inv(&2) % ((FF:num->real^M->real^K) i x + GG i x)) pow 2)) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LSPACE_CMUL THEN
    MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[ETA_AX; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[WAN_NORM_PARALLELOGRAM] THEN
  REWRITE_TAC[LIFT_SUB; LIFT_ADD; LIFT_CMUL] THEN
  SUBGOAL_THEN
   `integral s (\x. &2 % lift(norm((FF:num->real^M->real^K) i x) pow 2) +
                    &2 % lift(norm((GG:num->real^M->real^K) i x) pow 2) -
                    &4 % lift(norm(inv(&2) % (FF i x + GG i x)) pow 2)) =
    &2 % integral s (\x. lift(norm(FF i x) pow 2)) +
    &2 % integral s (\x. lift(norm(GG i x) pow 2)) -
    &4 % integral s (\x. lift(norm(inv(&2) % (FF i x + GG i x)) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    REWRITE_TAC[DROP_SUB; DROP_ADD; DROP_CMUL]]);;

let WAN_INFINITE_UNBOUNDED = prove
 (`!S n. INFINITE (S:num->bool) ==> ?m. m IN S /\ n <= m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
  EXISTS_TAC `(r:num->num) n` THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (r:num->num) (:num) = S` THEN SET_TAC[];
    MP_TAC(SPEC `r:num->num` MONOTONE_BIGGER) THEN ASM_SIMP_TAC[]]);;

let WAN_TCC_MONO = prove
 (`!(S:num->bool) n n' N lam.
     n <= n' /\ wan_tcc S n' N lam
     ==> wan_tcc S n N lam /\
         (!g:num->num->real^M->real^K. wan_tcomb n' N lam g = wan_tcomb n N lam g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_tcc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "V") ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!m. m IN n..N /\ ~(m IN n'..N) ==> (lam:num->real) m = &0` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN USE_THEN "V" MATCH_MP_TAC THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN USE_THEN "V" MATCH_MP_TAC THEN
    ASM_MESON_TAC[LE_TRANS];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC SUM_SUPERSET THEN REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_SIMP_TAC[] THEN
    ASM_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[wan_tcomb; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[SUBSET_NUMSEG] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN ASM_ARITH_TAC]);;

let WAN_TCC_SINGLE = prove
 (`!(S:num->bool) n m.
     m IN S /\ n <= m
     ==> wan_tcc S n m (\k. if k = m then &1 else &0) /\
         (!g:num->num->real^M->real^K.
            wan_tcomb n m (\k. if k = m then &1 else &0) g = g m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_tcc; wan_tcomb] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[LE_REFL];
    GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^M`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum(n..m) (\k. if k = m then (g:num->num->real^M->real^K) m i x else vec 0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
      REWRITE_TAC[VSUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[LE_REFL]]]);;

let WAN_TCC_MID = prove
 (`!(S:num->bool) n n' N N' lam lam'.
     n <= n' /\ wan_tcc S n N lam /\ wan_tcc S n' N' lam'
     ==> wan_tcc S n (MAX N N') (\m. inv(&2) * (lam m + lam' m)) /\
         (!g:num->num->real^M->real^K.
            wan_tcomb n (MAX N N') (\m. inv(&2) * (lam m + lam' m)) g =
            (\i x. inv(&2) % (wan_tcomb n N lam g i x + wan_tcomb n' N' lam' g i x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_tcc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "V") ASSUME_TAC)))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "V'") ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `(!m. m IN n..MAX N N' /\ ~(m IN n..N) ==> (lam:num->real) m = &0) /\
    (!m. m IN n..MAX N N' /\ ~(m IN n'..N') ==> (lam':num->real) m = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "V" MATCH_MP_TAC; USE_THEN "V'" MATCH_MP_TAC] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n..N SUBSET n..MAX N N' /\ n'..N' SUBSET n..MAX N N'` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(lam:num->real) m = &0 /\ (lam':num->real) m = &0`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THENL [USE_THEN "V" MATCH_MP_TAC; USE_THEN "V'" MATCH_MP_TAC] THEN
    UNDISCH_TAC `~(m IN (S:num->bool) /\ n <= m /\ m <= MAX N N')` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_LMUL; SUM_ADD_NUMSEG] THEN
    SUBGOAL_THEN `sum(n..MAX N N') lam = sum(n..N) lam /\ sum(n..MAX N N') lam' = sum(n'..N') lam'`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[wan_tcomb; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VECTOR_ADD_RDISTRIB; VSUM_LMUL; VSUM_ADD_NUMSEG] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* The Mazur lemma: for a sequence of d-tuples of L^2(s) maps with          *)
(* sum of squared norms <= M along an infinite index set S, convex          *)
(* combinations of tails (supported in S) form a Cauchy sequence for the     *)
(* quadratic form, hence converge to a d-tuple h with wan_qf s d h <= M.     *)
(* ------------------------------------------------------------------------- *)

let WAN_MAZUR_SET = prove
 (`!(s:real^M->bool) (S:num->bool) (g:num->num->real^M->real^K) d M n.
     INFINITE S /\
     (!m i. 1 <= i /\ i <= d ==> g m i IN lspace s (&2)) /\
     (!m. m IN S ==> wan_qf s d (g m) <= M)
     ==> ~({wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam} = {}) /\
         (!x. x IN {wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam}
              ==> &0 <= x) /\
         inf {wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam} <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`S:num->bool`; `n:num`] WAN_INFINITE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`S:num->bool`; `n:num`; `m:num`] WAN_TCC_SINGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o ISPEC `g:num->num->real^M->real^K`)) THEN
  SUBGOAL_THEN
   `wan_qf s d ((g:num->num->real^M->real^K) m) IN
    {wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `\k:num. if k = m then &1 else &0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN {wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
              wan_tcc S n N lam} ==> &0 <= x`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_QF_POS THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_TCOMB_LSPACE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`&0`; `wan_qf s d ((g:num->num->real^M->real^K) m)`] THEN
  ASM_SIMP_TAC[]);;

let WAN_MAZUR_CHOICE = prove
 (`!(s:real^M->bool) (S:num->bool) (g:num->num->real^M->real^K) d M n e.
     INFINITE S /\
     (!m i. 1 <= i /\ i <= d ==> g m i IN lspace s (&2)) /\
     (!m. m IN S ==> wan_qf s d (g m) <= M) /\ &0 < e
     ==> ?N lam. wan_tcc S n N lam /\
                 wan_qf s d (wan_tcomb n N lam g) <
                 inf {wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam} + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:real^M->bool`; `S:num->bool`; `g:num->num->real^M->real^K`;
                `d:num`; `M:real`; `n:num`] WAN_MAZUR_SET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
                   wan_tcc S n N lam}`;
                 `inf {wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
                       wan_tcc S n N lam} + e`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LT_ADDR]];
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `N0:num` (X_CHOOSE_THEN `lam0:num->real` STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N0:num`; `lam0:num->real`] THEN ASM_MESON_TAC[]]);;

let WAN_MAZUR_SEQ = prove
 (`!(s:real^M->bool) (S:num->bool) (g:num->num->real^M->real^K) d M.
     INFINITE S /\
     (!m i. 1 <= i /\ i <= d ==> g m i IN lspace s (&2)) /\
     (!m. m IN S ==> wan_qf s d (g m) <= M)
     ==> ?N lam.
           (!n. wan_tcc S n (N n) (lam n)) /\
           (!n. wan_qf s d (wan_tcomb n (N n) (lam n) g) <= M + inv(&n + &1)) /\
           (!e. &0 < e
                ==> ?K. !n m. K <= n /\ n <= m
                              ==> wan_qf s d (\i x. wan_tcomb n (N n) (lam n) g i x -
                                                    wan_tcomb m (N m) (lam m) g i x) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `dd = \n. inf {wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
                  wan_tcc S n N lam}` THEN
  SUBGOAL_THEN
   `!n. ~({wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
            wan_tcc S n N lam} = {}) /\
        (!x. x IN {wan_qf s d (wan_tcomb n N lam g) | N,lam | wan_tcc S n N lam}
             ==> &0 <= x) /\
        (dd:num->real) n <= M`
  (LABEL_TAC "SET") THENL
   [GEN_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_MAZUR_SET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n N lam. wan_tcc S n N lam
              ==> (dd:num->real) n <= wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K))`
  (LABEL_TAC "LB") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN
    USE_THEN "SET" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPEC `{wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) | N,lam |
                   wan_tcc S n N lam}` INF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `lam:num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= (dd:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INF THEN
    USE_THEN "SET" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (dd:num->real) n <= dd(SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
    USE_THEN "SET" (MP_TAC o SPEC `SUC n`) THEN
    USE_THEN "SET" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `lam:num->real` STRIP_ASSUME_TAC)) THEN
      MP_TAC(SPECL [`S:num->bool`; `n:num`; `SUC n`; `N:num`; `lam:num->real`]
                   WAN_TCC_MONO) THEN
      ASM_REWRITE_TAC[ARITH_RULE `n <= SUC n`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`N:num`; `lam:num->real`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?N lam. wan_tcc S n N lam /\
                wan_qf s d (wan_tcomb n N lam (g:num->num->real^M->real^K)) <
                (dd:num->real) n + inv(&n + &1)`
  MP_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_MAZUR_CHOICE THEN EXISTS_TAC `M:real` THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`N:num->num`; `lam:num->num->real`] THEN STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N:num->num`; `lam:num->num->real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(dd:num->real) n + inv(&n + &1)` THEN ASM_REWRITE_TAC[REAL_LE_RADD] THEN
    USE_THEN "SET" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `dd:num->real` CONVERGENT_REAL_BOUNDED_MONOTONE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `abs M` THEN GEN_TAC THEN
    USE_THEN "SET" (MP_TAC o SPEC `x:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> concl th = `!n. &0 <= (dd:num->real) n`)) THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `l:real`)] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &8` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:num`) THEN
  MP_TAC(SPEC `e / &8` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K1 + K2:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(&n + &1) < e / &8 /\ inv(&m + &1) < e / &8` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&K2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((dd:num->real) n - l) < e / &8 /\ abs(dd m - l) < e / &8`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`S:num->bool`; `n:num`; `m:num`; `(N:num->num) n`; `(N:num->num) m`;
                `(lam:num->num->real) n`; `(lam:num->num->real) m`] WAN_TCC_MID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o ISPEC `g:num->num->real^M->real^K`)) THEN
  REMOVE_THEN "LB" (MP_TAC o SPECL [`n:num`; `MAX ((N:num->num) n) (N m)`;
                                 `\k. inv(&2) * ((lam:num->num->real) n k + lam m k)`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `d:num`;
                 `wan_tcomb n ((N:num->num) n) ((lam:num->num->real) n)
                    (g:num->num->real^M->real^K)`;
                 `wan_tcomb m ((N:num->num) m) ((lam:num->num->real) m)
                    (g:num->num->real^M->real^K)`] WAN_QF_PARALLELOGRAM) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TCOMB_LSPACE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term ((=) `inv(&n + &1)`)) (concl th) && is_forall(concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    can (find_term ((=) `inv(&n + &1)`)) (concl th) && is_forall(concl th))) THEN
  REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

let WAN_QF_LNORM = prove
 (`!(s:real^M->bool) d (FF:num->real^M->real^K).
     (!i. 1 <= i /\ i <= d ==> FF i IN lspace s (&2))
     ==> wan_qf s d FF = sum(1..d) (\i. lnorm s (&2) (FF i) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_qf] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN ASM_SIMP_TAC[]);;

let WAN_MAZUR = prove
 (`!(s:real^M->bool) (S:num->bool) (g:num->num->real^M->real^K) d M.
     INFINITE S /\
     (!m i. 1 <= i /\ i <= d ==> g m i IN lspace s (&2)) /\
     (!m. m IN S ==> wan_qf s d (g m) <= M)
     ==> ?N lam (h:num->real^M->real^K).
           (!n. wan_tcc S n (N n) (lam n)) /\
           (!i. 1 <= i /\ i <= d ==> h i IN lspace s (&2)) /\
           (!i. 1 <= i /\ i <= d
                ==> ((\n. lnorm s (&2) (\x. wan_tcomb n (N n) (lam n) g i x - h i x)) ---> &0)
                    sequentially) /\
           wan_qf s d h <= M`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_MAZUR_SEQ) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num->num` (X_CHOOSE_THEN `lam:num->num->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BD") (LABEL_TAC "CY"))))) THEN
  ABBREV_TAC `c = \n. wan_tcomb n ((N:num->num) n) ((lam:num->num->real) n)
                        (g:num->num->real^M->real^K)` THEN
  SUBGOAL_THEN `!n i. 1 <= i /\ i <= d ==> (c:num->num->real^M->real^K) n i IN lspace s (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_TCOMB_LSPACE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= d
        ==> ?hi. hi IN lspace s (&2) /\
                 ((\n. lnorm s (&2) (\x. (c:num->num->real^M->real^K) n i x - hi x)) ---> &0)
                 sequentially`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\n:num. (c:num->num->real^M->real^K) n i`; `&2`; `s:real^M->bool`]
                  RIESZ_FISCHER) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; ARITH] THEN ANTS_TAC THENL
     [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "CY" (fun th -> MP_TAC(MP (SPEC `e pow 2` th)
        (SPEC `2` (MATCH_MP REAL_POW_LT (ASSUME `&0 < e`))))) THEN
      DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN EXISTS_TAC `K:num` THEN
      SUBGOAL_THEN
       `!n m. K <= n /\ n <= m
              ==> lnorm s (&2) (\x. (c:num->num->real^M->real^K) n i x - c m i x) < e`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `wan_qf s d (\i x. (c:num->num->real^M->real^K) n i x - c m i x)` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`s:real^M->bool`; `d:num`;
                         `\i x. (c:num->num->real^M->real^K) n i x - c m i x`; `i:num`]
                        WAN_QF_COMPONENT_LE) THEN
          REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; ETA_AX];
          EXPAND_TAC "c" THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
      DISJ_CASES_TAC(ARITH_RULE `n:num <= m \/ m <= n`) THENL
       [ONCE_REWRITE_TAC[GSYM LNORM_NEG] THEN
        REWRITE_TAC[VECTOR_NEG_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `hi:real^M->real^K` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `hi:real^M->real^K` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN REWRITE_TAC[GE] THEN
      DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x < e ==> abs x < e`) THEN
      MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_SIMP_TAC[REAL_POS; ETA_AX]];
    DISCH_THEN(X_CHOOSE_THEN `h:num->real^M->real^K` (LABEL_TAC "H") o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  SUBGOAL_THEN `!n. (c:num->num->real^M->real^K) n = wan_tcomb n (N n) (lam n) g`
  (LABEL_TAC "C") THENL [EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N:num->num`; `lam:num->num->real`; `h:num->real^M->real^K`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "H" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "H" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `1 <= i /\ i <= d`)) THEN
    USE_THEN "C" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. wan_qf s d ((c:num->num->real^M->real^K) n) - inv(&n + &1)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `d:num`; `h:num->real^M->real^K`] WAN_QF_LNORM) THEN
    ANTS_TAC THENL [USE_THEN "H" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. sum(1..d) (\i. lnorm s (&2) ((c:num->num->real^M->real^K) n i) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_QF_LNORM THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN
    USE_THEN "H" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `1 <= i`) (ASSUME `i:num <= d`))) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    USE_THEN "BD" (MP_TAC o SPEC `n:num`) THEN
    USE_THEN "C" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC]);;



(* ------------------------------------------------------------------------- *)
(* Linear combinations of weak partials, pairing with test functions under  *)
(* L^2 convergence on a compact support, tail convex combinations of an     *)
(* L^2_loc convergent sequence, and lower semicontinuity of the Dirichlet   *)
(* integral (DIR_LSC).                                                       *)
(* ------------------------------------------------------------------------- *)

let WAN_WPD_VSUM_S = prove
 (`!(s:real^N->bool) i (u:A->real^N->real^K) v t.
     FINITE t /\ (!m. m IN t ==> wan_wpd s i (u m) (v m))
     ==> wan_wpd s i (\x. vsum t (\m. u m x)) (\x. vsum t (\m. v m x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY; WAN_WPD_ZERO] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `(u:A->real^N->real^K) a`;
                 `(v:A->real^N->real^K) a`;
                 `\x. vsum t (\m. (u:A->real^N->real^K) m x)`;
                 `\x. vsum t (\m. (v:A->real^N->real^K) m x)`] WAN_WPD_ADD) THEN
  ASM_SIMP_TAC[ETA_AX]);;

let WAN_VSUM_CMUL_LSPACE = prove
 (`!(s:real^N->bool) (f:num->real^N->real^K) (c:num->real) a b.
     (!m. a <= m /\ m <= b ==> f m IN lspace s (&2))
     ==> (\x. vsum(a..b) (\m. c m % f m x)) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC LSPACE_CMUL THEN
  ASM_SIMP_TAC[ETA_AX]);;

let WAN_LNORM2_SUBSET_LE = prove
 (`!(s:real^N->bool) k (f:real^N->real^K).
     f IN lspace s (&2) /\ lebesgue_measurable k /\ k SUBSET s
     ==> lnorm k (&2) f <= lnorm s (&2) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) IN lspace k (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[LNORM_POS_LE; WAN_SOB_LNORM2_SQ; ARITH] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2]);;

let WAN_LNORM2_SUBSET_CONV = prove
 (`!(s:real^N->bool) k (f:num->real^N->real^K) g.
     (!n. f n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     lebesgue_measurable k /\ k SUBSET s /\
     ((\n. lnorm s (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> ((\n. lnorm k (&2) (\x. f n x - g x)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (f:num->real^N->real^K) n x - g x) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_REWRITE_TAC[]]);;

let WAN_PAIR_CONV_K = prove
 (`!(s:real^N->bool) k (psi:real^N->real) (f:num->real^N->real^K) g B.
     compact k /\ k SUBSET s /\ (\x. lift(psi x)) continuous_on (:real^N) /\
     (!x. ~(x IN k) ==> psi x = &0) /\ (!x. abs(psi x) <= B) /\
     (!n. f n IN lspace k (&2)) /\ g IN lspace k (&2) /\
     ((\n. lnorm k (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> ((\n. integral s (\x. psi x % f n x)) --> integral s (\x. psi x % g x))
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!FF:real^N->real^K. FF IN lspace k (&2)
                  ==> (\x. psi x % FF x) integrable_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_LLOC_PAIRING THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[SUBSET_REFL; WAN_LSPACE2_IMP_LLOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!FF:real^N->real^K. integral s (\x. psi x % FF x) = integral k (\x. psi x % FF x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN k` THENL
     [SUBGOAL_THEN `(x:real^N) IN s` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. B * drop(integral k (\x. lift(norm((f:num->real^N->real^K) n x - g x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. (f:num->real^N->real^K) n x - g x) IN lspace k (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift(norm((f:num->real^N->real^K) n x - g x))) integrable_on k`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x. (f:num->real^N->real^K) n x - g x`; `k:real^N->bool`; `&1`]
                    WAN_L2_L1_BOUND) THEN
      ASM_SIMP_TAC[MEASURABLE_COMPACT; REAL_LT_01];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. psi x % (f:num->real^N->real^K) n x) integrable_on k /\
                  (\x. psi x % (g:real^N->real^K) x) integrable_on k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_SUB] THEN REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral k (\x. lift(B * norm((f:num->real^N->real^K) n x - g x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. B * drop(integral k (\x. lift(norm((f:num->real^N->real^K) n x - g x)))))
     ---> &0) sequentially`
  MP_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(SPEC `B:real` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN
    MP_TAC(ISPECL [`\n x. (f:num->real^N->real^K) n x - g x`; `k:real^N->bool`]
                  WAN_L2_TO_L1_CONV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. lnorm k (&2) (\x. (f:num->real^N->real^K) n x - g x) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x. (f:num->real^N->real^K) n x - g x`; `k:real^N->bool`]
                    WAN_SOB_LNORM2_SQ) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
      REWRITE_TAC[];
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `&0 = &0 pow 2`] THEN
      MATCH_MP_TAC REALLIM_POW THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM]]);;

let WAN_TCOMB_L2_CONV = prove
 (`!(k:real^N->bool) (u:num->real^N->real^K) v (S:num->bool) (N:num->num) lam.
     (!m. u m IN lspace k (&2)) /\ v IN lspace k (&2) /\
     (!n. wan_tcc S n (N n) (lam n)) /\
     ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially
     ==> ((\n. lnorm k (&2) (\x. vsum(n..N n) (\m. lam n m % u m x) - v x)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  SUBGOAL_THEN `!n. sum(n..N n) ((lam:num->num->real) n) = &1 /\ (!m. &0 <= lam n m)`
  ASSUME_TAC THENL [ASM_MESON_TAC[wan_tcc]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x. vsum(n..N n) (\m. (lam:num->num->real) n m % (u:num->real^N->real^K) m x) - v x =
          vsum(n..N n) (\m. lam n m % (u m x - v x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG] THEN REWRITE_TAC[VSUM_RMUL; ETA_AX] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. (\x. (u:num->real^N->real^K) m x - v x) IN lspace k (&2)` ASSUME_TAC
  THENL [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
         ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m. (\x. (lam:num->num->real) n m % ((u:num->real^N->real^K) m x - v x)) IN lspace k (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= e / &2 /\ &0 < e ==> abs x < e`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(n..N n) (\m. lnorm k (&2) (\x. (lam:num->num->real) n m %
                                                ((u:num->real^N->real^K) m x - v x)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real^N->bool`; `&2`;
                    `\m x. (lam:num->num->real) n m % ((u:num->real^N->real^K) m x - v x)`;
                    `n..(N:num->num) n`] VSUM_LNORM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_ARITH `&1 <= &2`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(n..N n) (\m. (lam:num->num->real) n m * (e / &2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`] THEN
    SUBGOAL_THEN `&0 <= (lam:num->num->real) n m` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e / &2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[SUM_RMUL; ETA_AX] THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL]]);;


(* ------------------------------------------------------------------------- *)
(* DIR_LSC: an L^2_loc limit of a W^{1,2} sequence with bounded Dirichlet   *)
(* integrals is W^{1,2} with Dirichlet integral at most the bound.  Mazur:  *)
(* tail convex combinations of the weak partials converge in L^2(s); the    *)
(* same combinations of the maps converge to v in L^2_loc; the weak         *)
(* identity passes to the limit on the support of each test function.       *)
(* ------------------------------------------------------------------------- *)

let WAN_MAZUR_WPD = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M (S:num->bool).
       open s /\ INFINITE S /\ (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\
       v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially)
       ==> ?NN lam (h:num->real^N->real^K).
             (!n. wan_tcc S n (NN n) (lam n)) /\
             (!i. 1 <= i /\ i <= dimindex(:N)
                  ==> h i IN lspace s (&2) /\ wan_wpd s i v (h i) /\
                      ((\n. lnorm s (&2)
                              (\x. vsum(n..NN n) (\m. lam n m % wan_wd s i (u m) x) -
                                   h i x)) ---> &0) sequentially) /\
             wan_qf s (dimindex(:N)) h <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `S:num->bool`;
                 `\m i. wan_wd s i ((u:num->real^N->real^K) m)`; `dimindex(:N)`; `M:real`]
                WAN_MAZUR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[WAN_WD_WORKS];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[wan_qf; GSYM wan_dir] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num` (X_CHOOSE_THEN `lam:num->num->real`
    (X_CHOOSE_THEN `h:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wan_tcomb]) THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= dimindex(:N)
          ==> wan_wpd s i
                (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                        (u:num->real^N->real^K) m x))
                (\x. vsum(n..NN n) (\m. lam n m % wan_wd s i (u m) x))`
  (LABEL_TAC "A") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_VSUM_S THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. compact k /\ k SUBSET s
        ==> ((\n. lnorm k (&2) (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                   (u:num->real^N->real^K) m x) - v x)) ---> &0) sequentially`
  (LABEL_TAC "B") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TCOMB_L2_CONV THEN
    EXISTS_TAC `S:num->bool` THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_W12_IMP_LSPACE];
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
      ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> wan_wpd s i (v:real^N->real^K) (h i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[wan_wpd] THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC] THEN
    X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. integral s (\x. wan_dpart i phi x %
                  vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                     (u:num->real^N->real^K) m x))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_PAIR_CONV_K THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `B:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC WAN_VSUM_CMUL_LSPACE THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_W12_IMP_LSPACE];
        CONJ_TAC THENL
         [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
          ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
          USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. --(integral s (\x. phi x %
                  vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                     wan_wd s i ((u:num->real^N->real^K) m) x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      USE_THEN "A" (fun th -> MP_TAC(MATCH_MP (SPEC `n:num` th)
        (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`)))) THEN
      REWRITE_TAC[wan_wpd] THEN
      DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_NEG THEN MATCH_MP_TAC WAN_PAIR_CONV_K THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `B:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!n. (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                   wan_wd s i ((u:num->real^N->real^K) m) x))
          IN lspace s (&2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_VSUM_CMUL_LSPACE THEN
      ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC WAN_LNORM2_SUBSET_CONV THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`NN:num->num`; `lam:num->num->real`; `h:num->real^N->real^K`] THEN
  ASM_SIMP_TAC[]);;

let WAN_DIR_LSC_THM = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M.
       open s /\ (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\
       v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially)
       ==> wan_w12 s v /\ wan_dir s v <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`;
                 `(:num)`] WAN_MAZUR_WPD) THEN
  ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num` (X_CHOOSE_THEN `lam:num->num->real`
    (X_CHOOSE_THEN `h:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `wan_w12 s (v:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `(h:num->real^N->real^K) i` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->real^K`; `h:num->real^N->real^K`]
                WAN_DIR_EQ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `wan_qf s (dimindex(:N)) (h:num->real^N->real^K) <= M` THEN
  REWRITE_TAC[wan_qf]);;

let WAN_DIR_LSC = prove
 (`!(n:N->bool) (kk:K->bool). WAN_DIR_LSC_STATEMENT n kk`,
  REWRITE_TAC[WAN_DIR_LSC_STATEMENT; WAN_DIR_LSC_THM]);;


(* ------------------------------------------------------------------------- *)
(* WEAK_PARTIALS_CONV: along the whole sequence the weak partials converge  *)
(* weakly in L^2(s) to those of the limit.  If not, a one-sided infinite    *)
(* set of indices stays e away; Mazur on that set gives tail convex          *)
(* combinations whose pairings stay e away, but they converge in L^2 to a   *)
(* weak partial of the limit, which is the chosen one a.e.                   *)
(* ------------------------------------------------------------------------- *)

let WAN_L2_DOT_BOUND = prove
 (`!(s:real^N->bool) (f:real^N->real^K) g.
     f IN lspace s (&2) /\ g IN lspace s (&2)
     ==> abs(drop(integral s (\x. lift(f x dot g x)))) <=
         lnorm s (&2) f * lnorm s (&2) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(norm((f:real^N->real^K) x) * norm((g:real^N->real^K) x)))
                integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
    MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. lift(norm((f:real^N->real^K) x) *
                                        norm((g:real^N->real^K) x))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[WAN_LSPACE2_DOT_INTEGRABLE; NORM_LIFT; LIFT_DROP;
                 NORM_CAUCHY_SCHWARZ_ABS];
    MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `&2`; `f:real^N->real^K`; `g:real^N->real^K`]
                  HOELDER_INEQUALITY) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

let WAN_L2_DOT_CONV = prove
 (`!(s:real^N->bool) (psi:real^N->real^K) (f:num->real^N->real^K) g.
     psi IN lspace s (&2) /\ (!n. f n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     ((\n. lnorm s (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> ((\n. drop(integral s (\x. lift(psi x dot f n x)))) --->
          drop(integral s (\x. lift(psi x dot g x)))) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. lnorm s (&2) (psi:real^N->real^K) *
                  lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x. lift((psi:real^N->real^K) x dot (f:num->real^N->real^K) n x)) integrable_on s /\
      (\x. lift(psi x dot (g:real^N->real^K) x)) integrable_on s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM DOT_RSUB] THEN
    MATCH_MP_TAC WAN_L2_DOT_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
      [GSYM(SPEC `lnorm s (&2) (psi:real^N->real^K)` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_DOT_VSUM_INTEGRAL = prove
 (`!(s:real^N->bool) (psi:real^N->real^K) (FF:num->real^N->real^K) (c:num->real) a b.
     psi IN lspace s (&2) /\ (!m. a <= m /\ m <= b ==> FF m IN lspace s (&2))
     ==> drop(integral s (\x. lift(psi x dot vsum(a..b) (\m. c m % FF m x)))) =
         sum(a..b) (\m. c m * drop(integral s (\x. lift(psi x dot FF m x))))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DOT_RSUM; FINITE_NUMSEG; DOT_RMUL; LIFT_SUM; o_DEF; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\m x. c m % lift((psi:real^N->real^K) x dot (FF:num->real^N->real^K) m x)`;
                 `s:real^N->bool`; `a..b`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_SIMP_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. lift((psi:real^N->real^K) x dot (FF:num->real^N->real^K) m x))
                integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]);;

let WAN_NOT_REALLIM_ONESIDED = prove
 (`!(a:num->real) l.
     ~((a ---> l) sequentially)
     ==> ?e S. &0 < e /\ INFINITE S /\
               ((!m. m IN S ==> e <= a m - l) \/ (!m. m IN S ==> e <= l - a m))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `INFINITE {m | e <= (a:num->real) m - l}` THENL
   [EXISTS_TAC `{m | e <= (a:num->real) m - l}` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `INFINITE {m | e <= l - (a:num->real) m}` THENL
   [EXISTS_TAC `{m | e <= l - (a:num->real) m}` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[INFINITE; num_FINITE; IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[INFINITE; num_FINITE; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o SPEC `N1 + N2 + 1`) THEN
  ASM_MESON_TAC[REAL_ARITH `~(abs(x - l) < e) ==> e <= x - l \/ e <= l - x`;
                ARITH_RULE `N1 + N2 + 1 <= n ==> ~(n <= N1) /\ ~(n <= N2)`]);;

let WAN_TCC_LOWER = prove
 (`!(S:num->bool) n N lam (x:num->real) e.
     wan_tcc S n N lam /\ (!m. m IN S ==> e <= x m)
     ==> e <= sum(n..N) (\m. lam m * x m)`,
  REWRITE_TAC[wan_tcc] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(n..N) (\m. lam m * e)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_RMUL; ETA_AX] THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `(m:num) IN S` THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `(lam:num->real) m = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]]]);;

let WAN_TCC_AFFINE = prove
 (`!(S:num->bool) n N lam (x:num->real) c.
     wan_tcc S n N lam
     ==> sum(n..N) (\m. lam m * (x m - c)) = sum(n..N) (\m. lam m * x m) - c /\
         sum(n..N) (\m. lam m * (c - x m)) = c - sum(n..N) (\m. lam m * x m)`,
  REWRITE_TAC[wan_tcc] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG; SUM_RMUL; ETA_AX] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

let WAN_TCC_CONTRA = prove
 (`!(S:num->bool) (NN:num->num) (lam:num->num->real) (a:num->real) (J:num->real) l e.
     &0 < e /\ (!n. wan_tcc S n (NN n) (lam n)) /\
     (!n. J n = sum(n..NN n) (\m. lam n m * a m)) /\
     ((!m. m IN S ==> e <= a m - l) \/ (!m. m IN S ==> e <= l - a m))
     ==> ~((J ---> l) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SIDE")))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:num` (MP_TAC o SPEC `K:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:num->bool`; `K:num`; `(NN:num->num) K`; `(lam:num->num->real) K`;
                 `a:num->real`; `l:real`] WAN_TCC_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "SIDE" STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:num->bool`; `K:num`; `(NN:num->num) K`; `(lam:num->num->real) K`;
                   `\m. (a:num->real) m - l`; `e:real`] WAN_TCC_LOWER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`S:num->bool`; `K:num`; `(NN:num->num) K`; `(lam:num->num->real) K`;
                   `\m. l - (a:num->real) m`; `e:real`] WAN_TCC_LOWER) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


let WAN_WEAK_PARTIALS_CONV_THM = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M psi i.
       open s /\ (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\
       v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       psi IN lspace s (&2) /\ 1 <= i /\ i <= dimindex(:N)
       ==> wan_w12 s v /\
           ((\n. integral s (\x. lift(psi x dot wan_wd s i (u n) x))) -->
            integral s (\x. lift(psi x dot wan_wd s i v x))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (v:real^N->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`]
                  WAN_DIR_LSC_THM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `((\n. drop(integral s (\x. lift(psi x dot
                wan_wd s i ((u:num->real^N->real^K) n) x)))) --->
     drop(integral s (\x. lift(psi x dot wan_wd s i (v:real^N->real^K) x)))) sequentially`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_NOT_REALLIM_ONESIDED) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `S:num->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SIDE"))))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`;
                 `S:num->bool`] WAN_MAZUR_WPD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num` (X_CHOOSE_THEN `lam:num->num->real`
    (X_CHOOSE_THEN `h:num->real^N->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (MP_TAC o SPEC `i:num`) ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                 wan_wd s i ((u:num->real^N->real^K) m) x)) IN lspace s (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_VSUM_CMUL_LSPACE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. drop(integral s (\x. lift(psi x dot vsum(n..NN n) (\m. (lam:num->num->real) n m %
                  wan_wd s i ((u:num->real^N->real^K) m) x)))) =
        sum(n..NN n) (\m. lam n m *
                  drop(integral s (\x. lift(psi x dot wan_wd s i (u m) x))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_DOT_VSUM_INTEGRAL THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. drop(integral s (\x. lift(psi x dot vsum(n..NN n) (\m. (lam:num->num->real) n m %
                  wan_wd s i ((u:num->real^N->real^K) m) x))))) --->
     drop(integral s (\x. lift(psi x dot wan_wd s i (v:real^N->real^K) x)))) sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `drop(integral s (\x. lift(psi x dot wan_wd s i (v:real^N->real^K) x))) =
      drop(integral s (\x. lift(psi x dot (h:num->real^N->real^K) i x)))`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (v:real^N->real^K) x =
                                   (h:num->real^N->real^K) i x)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[ETA_AX];
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real^K`;
                   `\n x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                           wan_wd s i ((u:num->real^N->real^K) m) x)`;
                   `(h:num->real^N->real^K) i`] WAN_L2_DOT_CONV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:num->bool`; `NN:num->num`; `lam:num->num->real`;
                 `\m. drop(integral s (\x. lift(psi x dot
                        wan_wd s i ((u:num->real^N->real^K) m) x)))`;
                 `\n. drop(integral s (\x. lift(psi x dot vsum(n..NN n)
                        (\m. (lam:num->num->real) n m %
                             wan_wd s i ((u:num->real^N->real^K) m) x))))`;
                 `drop(integral s (\x. lift(psi x dot wan_wd s i (v:real^N->real^K) x)))`;
                 `e:real`] WAN_TCC_CONTRA) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let WAN_WEAK_PARTIALS_CONV = prove
 (`!(n:N->bool) (kk:K->bool). WAN_WEAK_PARTIALS_CONV_STATEMENT n kk`,
  REWRITE_TAC[WAN_WEAK_PARTIALS_CONV_STATEMENT; WAN_WEAK_PARTIALS_CONV_THM]);;


(* ------------------------------------------------------------------------- *)
(* The ambient metric G: entries and operator norm bounded by the quadratic *)
(* form bound (symmetric G), measurability and L^2 membership of G(f) H,    *)
(* pointwise limits of G(u_n) w.                                             *)
(* ------------------------------------------------------------------------- *)

let WAN_QF_BOUND_POS = prove
 (`!(A:real^K^K) B. (!w. abs(w dot (A ** w)) <= B * norm w pow 2) ==> &0 <= B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^K`) THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_POW_ONE; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let WAN_SYM_QF_ENTRY = prove
 (`!(A:real^K^K) B i j.
     transp A = A /\ (!w. abs(w dot (A ** w)) <= B * norm w pow 2) /\
     1 <= i /\ i <= dimindex(:K) /\ 1 <= j /\ j <= dimindex(:K)
     ==> abs(A$i$j) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^K^K)$i$j = (basis i:real^K) dot (A ** basis j)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`] (INST_TYPE [`:K`,`:N`] NORM_BASIS)) THEN
  MP_TAC(ISPECL [`j:num`] (INST_TYPE [`:K`,`:N`] NORM_BASIS)) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`basis j:real^K`,`y:real^K`) THEN SPEC_TAC(`basis i:real^K`,`x:real^K`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^K) dot (A ** x) = x dot (A ** y)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x + y:real^K) pow 2 + norm(x - y) pow 2 = &4` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B * norm(x + y:real^K) pow 2 + B * norm(x - y) pow 2 = &4 * B` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x + y:real^K` o check (is_forall o concl)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x - y:real^K` o check (is_forall o concl)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_SYM_QF_OPBOUND = prove
 (`!(A:real^K^K) B.
     transp A = A /\ (!w. abs(w dot (A ** w)) <= B * norm w pow 2)
     ==> !w. norm(A ** w) <= &(dimindex(:K)) * &(dimindex(:K)) * B * norm w`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\i. abs(((A:real^K^K) ** w)$i))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\i. &(dimindex(:K)) * B * norm(w:real^K))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((A:real^K^K)$i) * norm(w:real^K)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:K)) (\j. abs((A:real^K^K)$i$j))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:K)) (\j. B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC WAN_SYM_QF_ENTRY THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

let WAN_GMUL_MEASURABLE = prove
 (`!(G:real^K->real^K^K) (f:real^N->real^K) (FF:real^N->real^K) s.
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     f measurable_on s /\ FF measurable_on s
     ==> (\x. G(f x) ** FF x) measurable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. pastecart ((f:real^N->real^K) x) ((FF:real^N->real^K) x)`;
                 `\z:real^(K,K)finite_sum. (G:real^K->real^K^K)(fstcart z) ** sndcart z`;
                 `s:real^N->bool`] MEASURABLE_ON_COMPOSE_CONTINUOUS_0) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; SNDCART_VEC;
              MATRIX_VECTOR_MUL_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(K,K)finite_sum. (G:real^K->real^K^K)(fstcart z) ** sndcart z) =
    (\z. (\(m:real^(K,K)finite_prod) (x:real^K). matrify m ** x)
           ((((vectorize:real^K^K->real^(K,K)finite_prod) o G) o fstcart) z) (sndcart z))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC BILINEAR_CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL; ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX]]);;

let WAN_GMUL_LSPACE = prove
 (`!(G:real^K->real^K^K) C (f:real^N->real^K) (H:real^N->real^K) s.
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y w. norm(G y ** w) <= C * norm w) /\ f measurable_on s /\ H IN lspace s (&2)
     ==> (\x. G(f x) ** H x) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                 `\x. (G:real^K->real^K^K)((f:real^N->real^K) x) ** (H:real^N->real^K) x`;
                 `\x. C % (H:real^N->real^K) x`] LSPACE_BOUNDED_MEASURABLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_GMUL_MEASURABLE THEN ASM_MESON_TAC[WAN_LSPACE_MEASURABLE];
    MATCH_MP_TAC LSPACE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * norm((H:real^N->real^K) x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC]);;

let WAN_G_PTWISE_LIM = prove
 (`!(G:real^K->real^K^K) (f:num->real^K) y w.
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (f --> y) sequentially
     ==> ((\n. G(f n) ** w) --> G y ** w) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\n. (vectorize:real^K^K->real^(K,K)finite_prod)(G((f:num->real^K) n))) -->
     vectorize(G(y:real^K))) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)`;
                   `sequentially`; `f:num->real^K`; `y:real^K`] LIM_CONTINUOUS_FUNCTION) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K)` THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV; o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\(m:real^(K,K)finite_prod) (x:real^K). matrify m ** x`;
                 `\n. (vectorize:real^K^K->real^(K,K)finite_prod)(G((f:num->real^K) n))`;
                 `\n:num. (w:real^K)`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod)(G(y:real^K))`; `w:real^K`]
                LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[LIM_CONST; BILINEAR_MATRIX_VECTOR_MUL; MATRIFY_VECTORIZE]);;


(* ------------------------------------------------------------------------- *)
(* Limits of the two G-weighted pairings used in GDIR_LSC and RADON_RIESZ_G *)
(* (b the weak partial of the limit, a_n those of the sequence):            *)
(*   int b.G(u_n)b -> int b.G(v)b   (dominated convergence),                *)
(*   int b.G(u_n)a_n -> int b.G(v)b (weak convergence of a_n plus           *)
(*   G(u_n)b -> G(v)b in L^2).                                              *)
(* ------------------------------------------------------------------------- *)

let WAN_GDIR_TERM1_LIM = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) B C (u:num->real^N->real^K) v S
    (b:real^N->real^K).
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\
     (!y w. norm(G y ** w) <= C * norm w) /\
     (!n. u n measurable_on s) /\ v measurable_on s /\
     negligible S /\ (!x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
     b IN lspace s (&2)
     ==> ((\n. integral s (\x. lift(b x dot (G(u n x) ** b x)))) -->
          integral s (\x. lift(b x dot (G(v x) ** b x)))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. lift((b:real^N->real^K) x dot
               ((G:real^K->real^K^K)((u:num->real^N->real^K) n x) ** b x))`;
    `\x. lift((b:real^N->real^K) x dot
             ((G:real^K->real^K^K)((v:real^N->real^K) x) ** b x))`;
    `\x. lift(B * norm((b:real^N->real^K) x) pow 2)`;
    `s:real^N->bool`; `S:real^N->bool`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_GMUL_LSPACE THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`sequentially`; `\p q:real^K. lift(p dot q)`;
                     `\n:num. (b:real^N->real^K) x`;
                     `\n. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                          (b:real^N->real^K) x`;
                     `(b:real^N->real^K) x`;
                     `(G:real^K->real^K^K)((v:real^N->real^K) x) ** (b:real^N->real^K) x`]
                    LIM_BILINEAR) THEN
      REWRITE_TAC[LIM_CONST; BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC WAN_G_PTWISE_LIM THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]]);;

let WAN_LIFT_NORM_POW2_NULL = prove
 (`!(f:num->real^K). (f --> vec 0) sequentially
                     ==> ((\n. lift(norm(f n) pow 2)) --> vec 0) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\n. norm((f:num->real^K) n)) ---> &0) sequentially` MP_TAC THENL
   [REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM] THEN
    ONCE_REWRITE_TAC[GSYM LIM_NULL_NORM] THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP REALLIM_POW) THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM]);;

let WAN_GDIFF_L2_NULL = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) C (u:num->real^N->real^K) v S
    (b:real^N->real^K).
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y w. norm(G y ** w) <= C * norm w) /\
     (!n. u n measurable_on s) /\ v measurable_on s /\
     negligible S /\ (!x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
     b IN lspace s (&2)
     ==> ((\n. lnorm s (&2) (\x. G(u n x) ** b x - G(v x) ** b x)) ---> &0)
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) ** (b:real^N->real^K) x -
             G((v:real^N->real^K) x) ** b x) IN lspace s (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC WAN_GMUL_LSPACE THEN EXISTS_TAC `C:real` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) ** (b:real^N->real^K) x -
           G((v:real^N->real^K) x) ** b x`; `s:real^N->bool`] WAN_LNORM2_NULL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\n x. lift(norm((G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                     (b:real^N->real^K) x - G((v:real^N->real^K) x) ** b x) pow 2)`;
    `\x:real^N. lift(&0)`;
    `\x. lift((&2 * C) pow 2 * norm((b:real^N->real^K) x) pow 2)`;
    `s:real^N->bool`; `S:real^N->bool`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_NORM] THEN
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^K) <= c /\ norm(b:real^K) <= c ==> norm(a - b) <= &2 * c`) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_NUM] THEN
      MATCH_MP_TAC WAN_LIFT_NORM_POW2_NULL THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
        [VECTOR_ARITH `vec 0:real^K = (G:real^K->real^K^K)((v:real^N->real^K) x) **
                                      (b:real^N->real^K) x - G(v x) ** b x`] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      MATCH_MP_TAC WAN_G_PTWISE_LIM THEN ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[LIFT_NUM; INTEGRAL_0] THEN
    REWRITE_TAC[REAL_TENDSTO; o_DEF; DROP_VEC]]);;

let WAN_GDIR_TERM2_LIM = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) C (u:num->real^N->real^K) v M S i.
     open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y. transp(G y) = G y) /\ (!y w. norm(G y ** w) <= C * norm w) /\
     (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
     (!k. compact k /\ k SUBSET s
          ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
     negligible S /\ (!x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
     1 <= i /\ i <= dimindex(:N)
     ==> ((\n. integral s (\x. lift(wan_wd s i v x dot
                                     (G(u n x) ** wan_wd s i (u n) x)))) -->
          integral s (\x. lift(wan_wd s i v x dot (G(v x) ** wan_wd s i v x))))
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (v:real^N->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`]
                  WAN_DIR_LSC_THM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd s i (v:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_wd s i ((u:num->real^N->real^K) n) IN lspace s (&2)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n measurable_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_W12_IMP_LSPACE; WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^K) measurable_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  ABBREV_TAC `b = wan_wd s i (v:real^N->real^K)` THEN
  SUBGOAL_THEN
   `(\x. (G:real^K->real^K^K)((v:real^N->real^K) x) ** (b:real^N->real^K) x)
    IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_GMUL_LSPACE THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) ** (b:real^N->real^K) x -
             G((v:real^N->real^K) x) ** b x) IN lspace s (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC WAN_GMUL_LSPACE THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x. (b:real^N->real^K) x dot ((G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                                   wan_wd s i (u n) x) =
          (G((v:real^N->real^K) x) ** b x) dot wan_wd s i (u n) x +
          (G(u n x) ** b x - G(v x) ** b x) dot wan_wd s i (u n) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; DOT_LSUB] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (b:real^N->real^K) x dot ((G:real^K->real^K^K)((v:real^N->real^K) x) ** b x) =
        (G(v x) ** b x) dot b x`
  (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN MATCH_ACCEPT_TAC DOT_SYM; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral s (\x. lift(((G:real^K->real^K^K)((v:real^N->real^K) x) **
                               (b:real^N->real^K) x) dot
                              wan_wd s i ((u:num->real^N->real^K) n) x +
                              (G(u n x) ** b x - G(v x) ** b x) dot wan_wd s i (u n) x)) =
        integral s (\x. lift((G(v x) ** b x) dot wan_wd s i (u n) x)) +
        integral s (\x. lift((G(u n x) ** b x - G(v x) ** b x) dot wan_wd s i (u n) x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRAL_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_RID] THEN
  MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`;
                   `\x. (G:real^K->real^K^K)((v:real^N->real^K) x) ** (b:real^N->real^K) x`;
                   `i:num`] WAN_WEAK_PARTIALS_CONV_THM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. lnorm s (&2) (\x. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                                    (b:real^N->real^K) x - G((v:real^N->real^K) x) ** b x) *
                  sqrt M` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[NORM_1] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (\x. (G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                                  (b:real^N->real^K) x - G((v:real^N->real^K) x) ** b x) *
                lnorm s (&2) (wan_wd s i (u n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_L2_DOT_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`wan_wd s i ((u:num->real^N->real^K) n)`; `s:real^N->bool`]
                  WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(u:num->real^N->real^K) n`; `i:num`]
                  WAN_WD_SQ_LE_DIR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lnorm s (&2) (wan_wd s i ((u:num->real^N->real^K) n)) =
                  sqrt(lnorm s (&2) (wan_wd s i (u n)) pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
      MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wan_dir s ((u:num->real^N->real^K) n)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `C:real`; `u:num->real^N->real^K`;
                 `v:real^N->real^K`; `S:real^N->bool`; `b:real^N->real^K`]
                WAN_GDIFF_L2_NULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sqrt M` o MATCH_MP REALLIM_RMUL) THEN
  REWRITE_TAC[REAL_MUL_LZERO; TENDSTO_REAL; o_DEF; LIFT_NUM]);;


(* ------------------------------------------------------------------------- *)
(* GDIR_LSC and RADON_RIESZ_G.  With a_n, b the weak partials of u_n, v:    *)
(*   a.G a - (a-b).G(a-b) = 2 b.G a - b.G b   (G symmetric),                *)
(* so gdir(u_n) - Q_n -> gdir(v) with Q_n = sum int (a_n-b).G(u_n)(a_n-b)   *)
(* (WAN_GDIR_CORE).  Q_n >= 0 gives lower semicontinuity; if moreover       *)
(* gdir(u_n) -> gdir(v) then Q_n -> 0, and G >= lam I bounds lam times      *)
(* dir(u_n - v) by Q_n.                                                      *)
(* ------------------------------------------------------------------------- *)

let WAN_GDOT_INTEGRABLE = prove
 (`!(G:real^K->real^K^K) C (f:real^N->real^K) s.
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y w. norm(G y ** w) <= C * norm w) /\ f measurable_on s
     ==> !(FF:real^N->real^K) (H:real^N->real^K).
           FF IN lspace s (&2) /\ H IN lspace s (&2)
           ==> (\x. lift(FF x dot (G(f x) ** H x))) integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_GMUL_LSPACE THEN EXISTS_TAC `C:real` THEN
  ASM_REWRITE_TAC[]);;

let WAN_PSD_EXPAND = prove
 (`!(A:real^K^K) a b.
     transp A = A
     ==> a dot (A ** a) - (a - b) dot (A ** (a - b)) =
         &2 * (b dot (A ** a)) - b dot (A ** b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_LSUB; DOT_RSUB] THEN
  SUBGOAL_THEN `(a:real^K) dot ((A:real^K^K) ** b) = b dot (A ** a)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC DOT_SYM;
    REAL_ARITH_TAC]);;

let WAN_INTEGRAL_LIN3 = prove
 (`!(f1:real^N->real^1) f2 g1 g2 c s.
     f1 integrable_on s /\ f2 integrable_on s /\ g1 integrable_on s /\ g2 integrable_on s /\
     (!x. x IN s ==> drop(f1 x) - drop(f2 x) = c * drop(g1 x) - drop(g2 x))
     ==> drop(integral s f1) - drop(integral s f2) =
         c * drop(integral s g1) - drop(integral s g2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM DROP_SUB; GSYM DROP_CMUL; GSYM INTEGRAL_SUB; GSYM INTEGRAL_CMUL;
               INTEGRABLE_CMUL] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  ASM_SIMP_TAC[GSYM DROP_EQ; DROP_SUB; DROP_CMUL]);;

let WAN_GDIR_CORE = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:num->real^N->real^K) v M B S.
     open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\ (!y. transp(G y) = G y) /\
     (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
     (!k. compact k /\ k SUBSET s
          ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
     negligible S /\ (!x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially)
     ==> wan_w12 s v /\
         (!n i. 1 <= i /\ i <= dimindex(:N)
                ==> (\x. lift((wan_wd s i (u n) x - wan_wd s i v x) dot
                              (G(u n x) ** (wan_wd s i (u n) x - wan_wd s i v x))))
                    integrable_on s) /\
         ((\n. wan_gdir s G (u n) -
               sum(1..dimindex(:N))
                  (\i. drop(integral s (\x. lift((wan_wd s i (u n) x - wan_wd s i v x) dot
                         (G(u n x) ** (wan_wd s i (u n) x - wan_wd s i v x)))))))
          ---> wan_gdir s G v) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (v:real^N->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`]
                  WAN_DIR_LSC_THM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `C = &(dimindex(:K)) * &(dimindex(:K)) * B` THEN
  SUBGOAL_THEN `!y w. norm((G:real^K->real^K^K) y ** w) <= C * norm w` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^K->real^K^K) y`; `B:real`] WAN_SYM_QF_OPBOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^K`) THEN EXPAND_TAC "C" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= dimindex(:N)
          ==> wan_wd s i ((u:num->real^N->real^K) n) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N) ==> wan_wd s i (v:real^N->real^K) IN lspace s (&2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n measurable_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_W12_IMP_LSPACE; WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^K) measurable_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. wan_wd s i ((u:num->real^N->real^K) n) x -
                   wan_wd s i (v:real^N->real^K) x) IN lspace s (&2)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n (FF:real^N->real^K) (H:real^N->real^K).
      FF IN lspace s (&2) /\ H IN lspace s (&2)
      ==> (\x. lift(FF x dot ((G:real^K->real^K^K)((u:num->real^N->real^K) n x) ** H x)))
          integrable_on s`
  (LABEL_TAC "GI") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `C:real`; `(u:num->real^N->real^K) n`;
                   `s:real^N->bool`] WAN_GDOT_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`FF:real^N->real^K`; `H:real^N->real^K`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "GI" (MATCH_MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[wan_gdir] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. sum(1..dimindex(:N))
          (\i. &2 * drop(integral s (\x. lift(wan_wd s i (v:real^N->real^K) x dot
                  ((G:real^K->real^K^K)((u:num->real^N->real^K) n x) **
                   wan_wd s i (u n) x)))) -
               drop(integral s (\x. lift(wan_wd s i v x dot (G(u n x) ** wan_wd s i v x)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_LIN3 THEN REPEAT CONJ_TAC THENL
     [USE_THEN "GI" (MATCH_MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[ETA_AX];
      USE_THEN "GI" (MATCH_MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[ETA_AX];
      USE_THEN "GI" (MATCH_MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[ETA_AX];
      USE_THEN "GI" (MATCH_MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC WAN_PSD_EXPAND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = &2 * x - x`] THEN
  MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_LMUL THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `C:real`;
                   `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`; `S:real^N->bool`;
                   `i:num`] WAN_GDIR_TERM2_LIM) THEN
    ASM_REWRITE_TAC[REAL_TENDSTO; o_DEF];
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `B:real`; `C:real`;
                   `u:num->real^N->real^K`; `v:real^N->real^K`; `S:real^N->bool`;
                   `wan_wd s i (v:real^N->real^K)`] WAN_GDIR_TERM1_LIM) THEN
    ASM_SIMP_TAC[REAL_TENDSTO; o_DEF]]);;


let WAN_GDIR_LSC_THM = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:num->real^N->real^K) v M E.
       open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
       (?B. !y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\
       (!y. transp(G y) = G y) /\ (!y w. &0 <= w dot (G y ** w)) /\
       (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       (?S. negligible S /\ !x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
       (!n. wan_gdir s G (u n) <= E)
       ==> wan_w12 s v /\ wan_gdir s G v <= E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `u:num->real^N->real^K`;
                 `v:real^N->real^K`; `M:real`; `B:real`; `S:real^N->bool`]
                WAN_GDIR_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC
   `\n. wan_gdir s G ((u:num->real^N->real^K) n) -
        sum(1..dimindex(:N))
           (\i. drop(integral s (\x. lift((wan_wd s i (u n) x - wan_wd s i (v:real^N->real^K) x)
                   dot ((G:real^K->real^K^K)(u n x) **
                        (wan_wd s i (u n) x - wan_wd s i v x))))))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= E /\ &0 <= q ==> x - q <= E`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP]);;

let WAN_GDIR_LSC = prove
 (`!(n:N->bool) (kk:K->bool). WAN_GDIR_LSC_STATEMENT n kk`,
  REWRITE_TAC[WAN_GDIR_LSC_STATEMENT; WAN_GDIR_LSC_THM]);;

let WAN_RADON_RIESZ_G_THM = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:num->real^N->real^K) v M lam.
       open s /\ ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
       (?B. !y w. abs(w dot (G y ** w)) <= B * norm w pow 2) /\
       (!y. transp(G y) = G y) /\ &0 < lam /\
       (!y w. lam * norm w pow 2 <= w dot (G y ** w)) /\
       (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
       (?S. negligible S /\ !x. x IN s DIFF S ==> ((\n. u n x) --> v x) sequentially) /\
       ((\n. wan_gdir s G (u n)) ---> wan_gdir s G v) sequentially
       ==> wan_w12 s v /\
           ((\n. wan_dir s (\x. u n x - v x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `u:num->real^N->real^K`;
                 `v:real^N->real^K`; `M:real`; `B:real`; `S:real^N->bool`]
                WAN_GDIR_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\n. sum(1..dimindex(:N))
           (\i. drop(integral s (\x. lift((wan_wd s i ((u:num->real^N->real^K) n) x -
                                         wan_wd s i (v:real^N->real^K) x) dot
                   ((G:real^K->real^K^K)(u n x) **
                    (wan_wd s i (u n) x - wan_wd s i v x))))))) ---> &0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`sequentially`; `\n. wan_gdir s G ((u:num->real^N->real^K) n)`;
      `\n. wan_gdir s G ((u:num->real^N->real^K) n) -
           sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift((wan_wd s i (u n) x -
                                            wan_wd s i (v:real^N->real^K) x) dot
                      ((G:real^K->real^K^K)(u n x) **
                       (wan_wd s i (u n) x - wan_wd s i v x))))))`;
      `wan_gdir s G (v:real^N->real^K)`; `wan_gdir s G (v:real^N->real^K)`] REALLIM_SUB) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ARITH `a - (a - q):real = q`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. wan_wd s i ((u:num->real^N->real^K) n) x -
                   wan_wd s i (v:real^N->real^K) x) IN lspace s (&2)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[REAL_POS; ETA_AX; WAN_WD_WORKS];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. inv lam *
        sum(1..dimindex(:N))
           (\i. drop(integral s (\x. lift((wan_wd s i ((u:num->real^N->real^K) n) x -
                                         wan_wd s i (v:real^N->real^K) x) dot
                   ((G:real^K->real^K^K)(u n x) **
                    (wan_wd s i (u n) x - wan_wd s i v x))))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(SPEC `inv lam` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(u:num->real^N->real^K) n`; `v:real^N->real^K`]
                WAN_W12_SUB_WD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:num->real^N->real^K) n x - (v:real^N->real^K) x`;
                 `\i x. wan_wd s i ((u:num->real^N->real^K) n) x -
                        wan_wd s i (v:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv lam * (lam * sum(1..dimindex(:N))
       (\i. drop(integral s (\x. lift(norm(wan_wd s i ((u:num->real^N->real^K) n) x -
                                          wan_wd s i (v:real^N->real^K) x) pow 2)))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_wd s i ((u:num->real^N->real^K) n) x -
                   wan_wd s i (v:real^N->real^K) x) pow 2)) integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP]);;

let WAN_RADON_RIESZ_G = prove
 (`!(n:N->bool) (kk:K->bool). WAN_RADON_RIESZ_G_STATEMENT n kk`,
  REWRITE_TAC[WAN_RADON_RIESZ_G_STATEMENT; WAN_RADON_RIESZ_G_THM]);;


(* ------------------------------------------------------------------------- *)
(* Mollified Lipschitz maps R^K -> R^L: same Lipschitz constant, uniform    *)
(* approximation within L e, derivative bounded by the Lipschitz constant.  *)
(* ------------------------------------------------------------------------- *)

let WAN_MOLL_LIP_VEC = prove
 (`!e (P:real^K->real^L) L.
     &0 < e /\ (!y z. norm(P y - P z) <= L * norm(y - z))
     ==> !x y. norm(wan_moll e P x - wan_moll e P y) <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c. (\z. (P:real^K->real^L)(z + c)) continuous_on (:real^K)` ASSUME_TAC
  THENL
   [GEN_TAC THEN MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN EXISTS_TAC `L:real` THEN
    MAP_EVERY X_GEN_TAC [`a:real^K`; `b:real^K`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a + c:real^K`; `b + c:real^K`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[VECTOR_ARITH `(x + c) - (y + c):real^N = x - y`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^K->real^L) continuous_on (:real^K)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^K`) THEN REWRITE_TAC[VECTOR_ADD_RID; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `P:real^K->real^L`; `y - x:real^K`; `x:real^K`]
                WAN_MOLL_TRANSLATE) THEN
  REWRITE_TAC[VECTOR_ARITH `x + y - x:real^N = y`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `wan_moll e (P:real^K->real^L) x - wan_moll e (\z. P(z + (y - x))) x =
    wan_moll e (\z. P z - P(z + (y - x))) x`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_moll; wan_kconv; VECTOR_SUB_LDISTRIB] THEN
    MP_TAC(ISPECL [`\z. wan_mke e (x - z) % (P:real^K->real^L) z`;
                   `\z. wan_mke e (x - z) % (P:real^K->real^L) (z + (y - x))`;
                   `(:real^K)`] INTEGRAL_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
       [MP_TAC(ISPECL [`wan_mke e:real^K->real`; `P:real^K->real^L`; `x:real^K`]
                      WAN_KCONV_INTEGRABLE);
        MP_TAC(ISPECL [`wan_mke e:real^K->real`; `\z. (P:real^K->real^L) (z + (y - x))`;
                       `x:real^K`] WAN_KCONV_INTEGRABLE)] THEN
      ASM_SIMP_TAC[WAN_MKE_TEST; WAN_CONTINUOUS_LLOC];
      REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_MOLL_NORM_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `z:real^K` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^K`; `z + (y - x):real^K`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[VECTOR_ARITH `z - (z + (y - x)):real^N = x - y`]]);;

let WAN_MOLL_LIP_APPROX = prove
 (`!e (P:real^K->real^L) L.
     &0 < e /\ &0 <= L /\ (!y z. norm(P y - P z) <= L * norm(y - z))
     ==> !x. norm(wan_moll e P x - P x) <= L * e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(P:real^K->real^L) continuous_on (:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `P:real^K->real^L`; `x:real^K`] WAN_MOLL_SUB) THEN
  ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`e:real`; `x:real^K`] WAN_MKE_INTEGRAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^K) (\y. (L * e) % lift(wan_mke e (x - y:real^K))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MP_TAC(ISPECL [`wan_mke e:real^K->real`; `\y. (P:real^K->real^L) y - P x`;
                     `x:real^K`] WAN_KCONV_INTEGRABLE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[WAN_MKE_TEST] THEN
      MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `lift(&1)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_MUL; DROP_CMUL; LIFT_DROP] THEN
      SUBGOAL_THEN `&0 <= wan_mke e (x - y:real^K)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[WAN_MKE_POS]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
      ASM_CASES_TAC `e <= norm(x - y:real^K)` THENL
       [ASM_SIMP_TAC[WAN_MKE_ZERO; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * norm(y - x:real^K)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC]];
    MP_TAC(ISPECL [`\y. lift(wan_mke e (x - y:real^K))`; `L * e`; `(:real^K)`]
                  INTEGRAL_CMUL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift(&1)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let WAN_LIP_DERIV_BOUND_VEC = prove
 (`!(f:real^K->real^L) L x h.
     (!y z. norm(f y - f z) <= L * norm(y - z)) /\ f differentiable at x
     ==> norm(frechet_derivative f (at x) h) <= L * norm h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_DIFF_QUOT_LIMIT o
    REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o SPEC `h:real^K`) THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. (&n + &1) % ((f:real^K->real^L)(x + inv(&n + &1) % h) - f x)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[NORM_MUL] THEN
  MP_TAC(SPEC `n:num` WAN_INV_N1_BOUNDS) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x + inv(&n + &1) % h:real^K`; `x:real^K`]) THEN
  REWRITE_TAC[VECTOR_ARITH `(x + h) - x:real^K = h`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `&0 <= &n + &1`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &1) * L * inv(&n + &1) * norm(h:real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `(&n + &1) * inv(&n + &1) = &1` THEN CONV_TAC REAL_RING]);;

let WAN_C1_DIFFERENTIABLE = prove
 (`!(P:real^K->real^L).
     continuously_differentiable 1 (:real^K) P ==> !y. P differentiable at y`,
  GEN_TAC THEN REWRITE_TAC[ONE; continuously_differentiable; IN_UNIV; WITHIN_UNIV] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^K` THEN REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `(f':real^K->real^K->real^L) y` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* CHAIN_LIP_W12: Lipschitz chain rule with the energy bound L^2 dir(u).    *)
(* Mollify P (WAN_CHAIN_W12 applies, derivatives bounded by L), pass to the *)
(* limit with DIR_LSC (the mollified compositions converge uniformly).      *)
(* ------------------------------------------------------------------------- *)

let WAN_CHAIN_LIP_W12_THM = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (P:real^K->real^L) L.
       open s /\ bounded s /\ wan_w12 s u /\
       (!y z. norm(P y - P z) <= L * norm(y - z))
       ==> wan_w12 s (\x. P(u x)) /\
           wan_dir s (\x. P(u x)) <= L pow 2 * wan_dir s u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`basis 1:real^K`; `vec 0:real^K`]) THEN
    SIMP_TAC[VECTOR_SUB_RZERO; NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
    MP_TAC(ISPEC `(P:real^K->real^L) (basis 1) - P(vec 0)` NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^K->real^L) continuous_on (:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) measurable_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^K) (wan_moll (inv(&n + &1)) (P:real^K->real^L)) /\
        (!y z. norm(wan_moll (inv(&n + &1)) P y - wan_moll (inv(&n + &1)) P z) <=
               L * norm(y - z)) /\
        (!y. norm(wan_moll (inv(&n + &1)) P y - P y) <= L * inv(&n + &1))`
  (LABEL_TAC "Q") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC];
      MATCH_MP_TAC WAN_MOLL_LIP_VEC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_MOLL_LIP_APPROX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. continuously_differentiable 1 (:real^K) (wan_moll (inv(&n + &1)) (P:real^K->real^L)) /\
        (!y h. norm(frechet_derivative (wan_moll (inv(&n + &1)) P) (at y) h) <= L * norm h) /\
        (!y. onorm(frechet_derivative (wan_moll (inv(&n + &1)) P) (at y)) <= L)`
  (LABEL_TAC "D") THENL
   [GEN_TAC THEN USE_THEN "Q" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN
     `continuously_differentiable 1 (:real^K) (wan_moll (inv(&n + &1)) (P:real^K->real^L))`
    ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
    MP_TAC(ISPEC `wan_moll (inv(&n + &1)) (P:real^K->real^L)` WAN_C1_DIFFERENTIABLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "DF") THEN
    SUBGOAL_THEN
     `!y h. norm(frechet_derivative (wan_moll (inv(&n + &1)) (P:real^K->real^L)) (at y) h) <=
            L * norm h`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_LIP_DERIV_BOUND_VEC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^K` THEN
    MP_TAC(ISPEC `frechet_derivative (wan_moll (inv(&n + &1)) (P:real^K->real^L)) (at y)`
                 ONORM) THEN
    ANTS_TAC THENL
     [USE_THEN "DF" (MP_TAC o SPEC `y:real^K`) THEN
      REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN SIMP_TAC[has_derivative];
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_w12 s (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x)) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd s i (\x. wan_moll (inv(&n + &1)) P (u x))
                   (\x. frechet_derivative (wan_moll (inv(&n + &1)) P) (at (u x))
                          (wan_wd s i u x)))`
  (LABEL_TAC "C") THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`s:real^N->bool`; `u:real^N->real^K`;
                  `wan_moll (inv(&n + &1)) (P:real^K->real^L)`]
      (REWRITE_RULE[WAN_CHAIN_W12_STATEMENT]
        (ISPECL [`(:N)`; `(:K)`; `(:L)`] WAN_CHAIN_W12))) THEN
    ANTS_TAC THENL
     [USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_dir s (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x)) <=
        L pow 2 * wan_dir s u`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "C" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[wan_dir; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`;
                   `\x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x)`;
                   `\x. frechet_derivative (wan_moll (inv(&n + &1)) (P:real^K->real^L))
                          (at ((u:real^N->real^K) x)) (wan_wd s i u x)`] WAN_WD_UNIQUE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral s (\x. lift(L pow 2 *
                   norm(wan_wd s i (u:real^N->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
      EXISTS_TAC
       `{x | x IN s /\
             ~(wan_wd s i (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L)
                                 ((u:real^N->real^K) x)) x =
               frechet_derivative (wan_moll (inv(&n + &1)) P) (at (u x))
                 (wan_wd s i u x))}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; LIFT_DROP] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN
         `wan_wd s i (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L)
                            ((u:real^N->real^K) x)) x =
          frechet_derivative (wan_moll (inv(&n + &1)) P) (at (u x)) (wan_wd s i u x)`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_REWRITE_TAC[NORM_POS_LE]];
      MP_TAC(ISPECL [`\x. lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2)`; `L pow 2`;
                     `s:real^N->bool`] INTEGRAL_CMUL) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[DROP_CMUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (P:real^K->real^L) ((u:real^N->real^K) x)) IN lspace s (&2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `measurable(s:real^N->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_OPEN]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                   `\x. (P:real^K->real^L) ((u:real^N->real^K) x)`;
                   `\x. lift(norm((P:real^K->real^L)(vec 0)) +
                             L * norm((u:real^N->real^K) x))`]
                  LSPACE_BOUNDED_MEASURABLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MEASURABLE_COMPOSE_CONT THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC LSPACE_ADD THEN
      ASM_SIMP_TAC[LSPACE_CONST; REAL_POS] THEN MATCH_MP_TAC LSPACE_CMUL THEN
      MATCH_MP_TAC LSPACE_NORM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`(u:real^N->real^K) x`; `vec 0:real^K`] o
        check (fun th -> is_forall(concl th) &&
                         length(fst(strip_forall(concl th))) = 2 &&
                         can (find_term ((=) `P:real^K->real^L`)) (concl th))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO] THEN
      MATCH_ACCEPT_TAC(NORM_ARITH
       `norm(a - b:real^L) <= c ==> norm(a) <= abs(norm(b) + c)`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. compact k /\ k SUBSET s
        ==> ((\n. lnorm k (&2)
                  (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x) -
                       P(u x))) ---> &0) sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `measurable(k:real^N->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_COMPACT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. (\x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x) - P(u x))
          IN lspace k (&2)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN
      USE_THEN "C" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. measure(k:real^N->bool) rpow (inv(&2)) * (L * inv(&n + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= L * inv(&n + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`k:real^N->bool`; `&2`; `lift(L * inv(&n + &1))`] LNORM_CONST) THEN
      ASM_SIMP_TAC[NORM_LIFT; REAL_ARITH `&0 < &2`;
                   REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^N->bool` THEN
      ASM_SIMP_TAC[REAL_POS; NEGLIGIBLE_EMPTY; DIFF_EMPTY; LSPACE_CONST; NORM_LIFT;
                   REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      USE_THEN "Q" (MP_TAC o SPEC `(u:real^N->real^K) x` o CONJUNCT2 o CONJUNCT2 o
                    SPEC `n:num`) THEN REWRITE_TAC[];
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
        [REAL_ARITH `&0 = measure(k:real^N->bool) rpow (inv(&2)) * (L * &0)`] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `\n x. wan_moll (inv(&n + &1)) (P:real^K->real^L) ((u:real^N->real^K) x)`;
                 `\x. (P:real^K->real^L) ((u:real^N->real^K) x)`;
                 `L pow 2 * wan_dir s (u:real^N->real^K)`] WAN_DIR_LSC_THM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WAN_CHAIN_LIP_W12 = prove
 (`!(n:N->bool) (kk:K->bool) (ll:L->bool). WAN_CHAIN_LIP_W12_STATEMENT n kk ll`,
  REWRITE_TAC[WAN_CHAIN_LIP_W12_STATEMENT; WAN_CHAIN_LIP_W12_THM]);;

