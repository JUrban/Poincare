(* ========================================================================= *)
(* Unit pc_p3_c171a: MT Prop 17.1, the counterexample                       *)
(* package.  One counterexample instance p3h_inst (a history in the setting *)
(* of 17.1 at its first bad time ts with the worst bad point x), the        *)
(* sequence predicate p3h_cexseq (instances with R(x) -> infinity, the      *)
(* Thm 10.2 ball bounds, no Lemma 17.7 configuration and no fresh cap near  *)
(* x for large indices) and its passage to subsequences; canonical          *)
(* neighbourhoods above 2 R(x) at all times <= ts (P3H_171_CANON_ABOVE);    *)
(* abs Rm from R under pinching (P3H_RM_FROM_R).  The notions are the plain *)
(* p3_canon_at and rfs_canonical_assumption.  Also used by pc_rfa_171u.     *)
(* ========================================================================= *)

needs "src/pc_p3_c172a.ml";;
needs "src/pc_p3_assembly.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_p2c_l112.ml";;
needs "src/pc_rfa_pinchrm.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The step function at the bad time, times of slices, and canonical         *)
(* neighbourhoods above c R(x), c >= 2, at all times s <= ts (before ts by   *)
(* the truncation, at ts by the choice of the worst bad point).              *)
(* ------------------------------------------------------------------------- *)

let P3H_STEPF_AT_BAD = prove
 (`!i rs' r' ts s (hs:(A)rfs_history).
     p3_seq_ok rs' /\ rs' (SUC i) = r' /\ p3_T i <= ts /\ ts < rfs_horizon hs /\
     rfs_horizon hs <= p3_T (SUC i) /\ s <= ts
     ==> p3_stepf rs' ts = r' /\ r' <= p3_stepf rs' s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3_step ts = SUC i` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3_STEP_GE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_stepf rs' ts = r'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3_stepf]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P3_STEPF_MONO THEN ASM_REWRITE_TAC[]);;

let P3H_TOPSPACE_TIME_POS = prove
 (`!(hs:(A)rfs_history) s y. y IN topspace(rfs_top_at hs s) ==> &0 <= s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_top_at; rfs_live] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

let P3H_171_CANON_ABOVE = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) r' ts x c.
     &2 <= c /\ rs' (SUC i) = r' /\ &0 < r' /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
     inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
     (!y. y IN topspace(rfs_top_at hs ts) /\
          &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
          ==> p3_canon_at (rfs_view hs) C eps y ts)
     ==> !y s. s <= ts /\ y IN topspace(rfs_top_at hs s) /\
               c * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) s y
               ==> p3_canon_at (rfs_view hs) C eps y s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(r' pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x <=
                c * rfs_vscalar (rfs_view hs) ts x /\
                &2 * rfs_vscalar (rfs_view hs) ts x <= c * rfs_vscalar (rfs_view hs) ts x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = ts` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = ts`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s < ts` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd)
                   (hs:(A)rfs_history)`) THEN
  REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `rs':num->real`; `r':real`; `ts:real`; `s:real`;
                 `hs:(A)rfs_history`] P3H_STEPF_AT_BAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  UNDISCH_TAC `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts)
                 C eps (p3_stepf rs')` THEN
  REWRITE_TAC[P3H_TRUNC_CANON_BAD] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[p3h_bad; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_TOPSPACE_TIME_POS THEN
    MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `y:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(p3_stepf rs' s pow 2) <= inv(r' pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(p3_stepf rs' s pow 2) <= rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One counterexample instance, and abs Rm from R under pinching.            *)
(* ------------------------------------------------------------------------- *)

let p3h_inst = new_definition
 `p3h_inst (C:real,eps:real,hf:real->real->real,md:real->real,g0:real^3->real^3^3,A0:real)
           (i:num) (rs:num->real,ks:num->real,ds:num->real)
           (dlt:real,r':real,rs':num->real,ks':num->real,dd:num->real,
            hs:(A)rfs_history,ts:real,x:A) <=>
    &2 <= C /\ &0 < eps /\ rs' (SUC i) = r' /\ &0 < r' /\
    p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
    p3_T i <= ts /\ ts < rfs_horizon hs /\
    rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
    x IN topspace(rfs_top_at hs ts) /\
    inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
    (!y. y IN topspace(rfs_top_at hs ts) /\
         &2 * rfs_vscalar (rfs_view hs) ts x <= rfs_vscalar (rfs_view hs) ts y
         ==> p3_canon_at (rfs_view hs) C eps y ts)`;;

let P3H_RM_FROM_R = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !(hs:(A)rfs_history) s y K Q.
            rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ &0 <= s /\
            y IN topspace(rfs_top_at hs s) /\ &1 <= Q /\ &0 <= K /\
            rfs_vscalar (rfs_view hs) s y <= K * Q
            ==> p3_vrm (rfs_view hs) s y <= (&2 * K + &12 + &2 * exp(&4)) * Q`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `s:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[rfs_view; rfs_pinched] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                 `rfs_metric_at (hs:(A)rfs_history) s`; `s:real`; `y:A`] RFA_PINCH_RM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--(&6) <= mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s y` THEN
    REWRITE_TAC[rfs_pinched_at] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_LE_NEG2] THEN
    SUBGOAL_THEN `&0 < &4 * s + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y <= K * Q` THEN
  REWRITE_TAC[rfs_vscalar; rfs_view; p3_vrm; rfs_vatlas; rfs_vmetric] THEN
  SUBGOAL_THEN `&0 <= exp(&4)` MP_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K * Q` MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&4) <= exp(&4) * Q` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The counterexample sequence as one predicate, and subsequences.           *)
(* ------------------------------------------------------------------------- *)

let p3h_cexseq = new_definition
 `p3h_cexseq (C:real,eps:real,hf:real->real->real,md:real->real,g0:real^3->real^3^3,A0:real)
             (i:num) (rs:num->real,ks:num->real,ds:num->real)
             (dlt:num->real,r:num->real,rs':num->num->real,ks':num->num->real,
              dd:num->num->real,hs:num->(A)rfs_history,ts:num->real,x:num->A) <=>
    &0 < p3_T i /\
    (!a. p3h_inst (C,eps,hf,md,g0,A0) i (rs,ks,ds)
           (dlt a,r a,rs' a,ks' a,dd a,hs a,ts a,x a)) /\
    (!B. ?N. !a. N <= a ==> B < rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
    (!A. &0 < A
         ==> ?D N. &0 <= D /\
                   !a z. N <= a /\
                         z IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a))))
                         ==> rfs_vscalar (rfs_view (hs a)) (ts a) z <=
                             D * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) /\
    (!Ap Dp tp. &0 < Ap /\ &0 < Dp /\ &0 < tp
       ==> ?N. !a. N <= a
               ==> ~(?y k j.
                       y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                              (Ap * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                       1 <= k /\ k <= hs_count (hs a) /\ j IN ev_index(hs_event (hs a) k) /\
                       ts a - tp * inv(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)) <=
                       hs_time (hs a) k /\
                       hs_time (hs a) k < ts a /\
                       y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1)) /\
                       p3_flowline (hs a) y (hs_time (hs a) k) (ts a) /\
                       (!s. hs_time (hs a) k <= s /\ s <= ts a
                            ==> rfs_vscalar (rfs_view (hs a)) s y <=
                                Dp * rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
    (!A. &0 < A
         ==> ?N. !a. N <= a
                 ==> ~(?k j y. 1 <= k /\ k <= hs_count (hs a) /\
                               j IN ev_index(hs_event (hs a) k) /\
                               hs_time (hs a) k = ts a /\
                               y IN rfs_vball (rfs_view (hs a)) (ts a) (x a)
                                      (A * inv(sqrt(rfs_vscalar (rfs_view (hs a)) (ts a) (x a)))) /\
                               y IN IMAGE (ev_capm (hs_event (hs a) k) j) (cball(vec 0,&1))))`;;

let P3H_SUBSEQ_GE = prove
 (`!sub. p3_subseq sub ==> !n. n <= sub n`,
  GEN_TAC THEN REWRITE_TAC[p3_subseq] THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `SUC n`]) THEN ASM_ARITH_TAC);;

let P3H_CEXSEQ_SUBSEQ = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt r rs' ks' dd (hs:num->(A)rfs_history) ts x sub.
     p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dlt,r,rs',ks',dd,hs,ts,x) /\ p3_subseq sub
     ==> p3h_cexseq (C,eps,hf,md,g0,A0) i (rs,ks,ds)
           (dlt o sub,r o sub,rs' o sub,ks' o sub,dd o sub,hs o sub,ts o sub,x o sub)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3h_cexseq; o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INST")
      (CONJUNCTS_THEN2 (LABEL_TAC "QINF") (CONJUNCTS_THEN2 (LABEL_TAC "BALL")
        (CONJUNCTS_THEN2 (LABEL_TAC "H17") (LABEL_TAC "HF"))))))
    (LABEL_TAC "SUB")) THEN
  USE_THEN "SUB" (LABEL_TAC "GE" o MATCH_MP P3H_SUBSEQ_GE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `B:real` THEN USE_THEN "QINF" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GE" (ACCEPT_TAC o SPEC `a:num`);
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "BALL" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `z:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GE" (ACCEPT_TAC o SPEC `a:num`);
    MAP_EVERY X_GEN_TAC [`Ap:real`; `Dp:real`; `tp:real`] THEN STRIP_TAC THEN
    USE_THEN "H17" (fun th -> MP_TAC(MP (SPECL [`Ap:real`; `Dp:real`; `tp:real`] th)
      (CONJ (ASSUME `&0 < Ap`) (CONJ (ASSUME `&0 < Dp`) (ASSUME `&0 < tp`))))) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GE" (ACCEPT_TAC o SPEC `a:num`);
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "HF" (fun th -> MP_TAC(MP (SPEC `A:real` th) (ASSUME `&0 < A`))) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GE" (ACCEPT_TAC o SPEC `a:num`)]);;

