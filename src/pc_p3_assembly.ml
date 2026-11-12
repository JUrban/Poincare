(* ========================================================================= *)
(* Unit pc_p3_assembly: the assembly of the Part 3 proof.                  *)
(* D2: MT Thm 15.9 in continuation form from Props 16.1 and 17.1, Lemma    *)
(* 15.11, the flow extension and Lemma 17.12 (sequence recursion with the  *)
(* redefinition of MT p. 409, inner loop over surgeries bounded by Lemma   *)
(* 17.12, outer induction over the intervals [T_i, T_(i+1)]).  D1: the     *)
(* existence part of RFS_EXTINCTION_STATEMENT from Thm 15.9, the start, the *)
(* Part 4 interface, scaling and orientability.  D3: the combination       *)
(* P3_RFS_EXTINCTION.                                                      *)
(*                                                                         *)
(* Sections: A1-A9, D2, D1, D3.                                            *)
(* ========================================================================= *)

needs "src/pc_p3_core.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_rfs_top.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A1. Time steps T_j = 2^j/32 and step functions.                         *)
(* ------------------------------------------------------------------------- *)

let P3_T_EXISTS = prove
 (`!t. ?j. t < p3_T j`,
  GEN_TAC THEN REWRITE_TAC[p3_T] THEN
  MP_TAC(SPECL [`&2`; `&32 * t`] REAL_ARCH_POW) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &32`] THEN ASM_REAL_ARITH_TAC);;

let P3_STEP = prove
 (`!t. t < p3_T(p3_step t) /\ !m. m < p3_step t ==> ~(t < p3_T m)`,
  GEN_TAC THEN REWRITE_TAC[p3_step] THEN
  MP_TAC(ISPEC `\j. (t:real) < p3_T j` MINIMAL) THEN
  REWRITE_TAC[P3_T_EXISTS] THEN SIMP_TAC[]);;

let P3_T_MONO = prove
 (`!m n. m <= n ==> p3_T m <= p3_T n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_T] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &32`] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3_T_POS = prove
 (`!j. &0 < p3_T j`,
  GEN_TAC THEN REWRITE_TAC[p3_T] THEN
  SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2 /\ &0 < &32`]);;

let P3_STEP_LE = prove
 (`!t j. t < p3_T j ==> p3_step t <= j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` P3_STEP) THEN ASM_MESON_TAC[]);;

let P3_STEP_MONO = prove
 (`!s t. s <= t ==> p3_step s <= p3_step t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3_STEP_LE THEN
  MP_TAC(SPEC `t:real` P3_STEP) THEN ASM_REAL_ARITH_TAC);;

let P3_STEP_GE = prove
 (`!t j. p3_T j <= t ==> SUC j <= p3_step t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC j <= n <=> ~(n <= j)`] THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` P3_STEP) THEN
  MP_TAC(SPECL [`p3_step t`; `j:num`] P3_T_MONO) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3_SEQ_MONO = prove
 (`!s. p3_seq_ok s ==> !m n. m <= n ==> s n <= s m`,
  GEN_TAC THEN REWRITE_TAC[p3_seq_ok] THEN STRIP_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LE_EXISTS] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let P3_STEPF_POS = prove
 (`!s t. p3_seq_ok s ==> &0 < p3_stepf s t`,
  SIMP_TAC[p3_seq_ok; p3_stepf]);;

let P3_STEPF_MONO = prove
 (`!s a b. p3_seq_ok s /\ a <= b ==> p3_stepf s b <= p3_stepf s a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_stepf] THEN
  MP_TAC(SPEC `s:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P3_STEP_MONO THEN ASM_REWRITE_TAC[]);;

(* The step function of a parameter                                         *)
(* sequence starting at eps stays below eps (the rp bound of Lemma 15.11).  *)

let P3_STEPF_LE_EPS = prove
 (`!rs eps. p3_seq_ok rs /\ rs 0 = eps ==> !t. p3_stepf rs t <= eps`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  GEN_TAC THEN REWRITE_TAC[p3_stepf] THEN
  MP_TAC(SPEC `rs:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_0]);;

(* ------------------------------------------------------------------------- *)
(* A2. Extensions of histories: reflexive, transitive, same initial data.  *)
(* ------------------------------------------------------------------------- *)

let RFS_EXTENDS_REFL = prove
 (`!hs:(A)rfs_history. rfs_extends hs hs`,
  REWRITE_TAC[rfs_extends; rfs_horizon; LE_REFL; REAL_LE_REFL]);;

let RFS_EXTENDS_TRANS = prove
 (`!h1 h2 h3:(A)rfs_history.
        rfs_extends h1 h2 /\ rfs_extends h2 h3 ==> rfs_extends h1 h3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_extends; rfs_horizon] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_count (h1:(A)rfs_history) <= hs_count (h3:(A)rfs_history)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hs_time (h2:(A)rfs_history) (hs_count (h1:(A)rfs_history) + 1) <=
    hs_time (h3:(A)rfs_history) (hs_count h1 + 1)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `hs_count (h1:(A)rfs_history) + 1 <= hs_count (h2:(A)rfs_history)`
    THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `hs_count (h1:(A)rfs_history) + 1` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `hs_event (h3:(A)rfs_history)`)) (concl th) = false &&
                         can (find_term ((=) `hs_top (h3:(A)rfs_history)`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      SUBGOAL_THEN `hs_count (h1:(A)rfs_history) = hs_count (h2:(A)rfs_history)`
      SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[REAL_LE_TRANS];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k <= hs_count (h2:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `hs_time (h1:(A)rfs_history) (k + 1) <= hs_time (h2:(A)rfs_history) (k + 1)`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `k + 1 <= hs_count (h1:(A)rfs_history)` THENL
       [ASM_MESON_TAC[REAL_LE_REFL];
        SUBGOAL_THEN `k = hs_count (h1:(A)rfs_history)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    ASM_MESON_TAC[REAL_LTE_TRANS];
    ASM_MESON_TAC[LE_TRANS]]);;

let RFS_EXTENDS_INITIAL = prove
 (`!hs hs':(A)rfs_history.
        rfs_history_ok hs /\ rfs_extends hs hs'
        ==> hs_top hs' 0 = hs_top hs 0 /\ hs_atlas hs' 0 = hs_atlas hs 0 /\
            hs_metric hs' 0 (&0) = hs_metric hs 0 (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_history_ok; rfs_extends] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o
    check (fun th -> can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  REWRITE_TAC[LE_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o
    check (fun th -> can (find_term ((=) `hs_time (hs:(A)rfs_history)`)) (concl th) &&
                     not (can (find_term ((=) `hs_top (hs:(A)rfs_history)`)) (concl th)))) THEN
  ASM_REWRITE_TAC[LE_0; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* A3. Times, slabs and views: an extension has the same view before the   *)
(* earlier horizon, so the truncated views agree.                          *)
(* ------------------------------------------------------------------------- *)

let RFS_TIME_MONO_ADD = prove
 (`!hs:(A)rfs_history d j.
        rfs_history_ok hs /\ j + d <= hs_count hs + 1
        ==> hs_time hs j <= hs_time hs (j + d)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (j + d)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    DISCH_THEN(MP_TAC o SPEC `j + d:num`) THEN REWRITE_TAC[GSYM ADD1] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let RFS_TIME_MONO = prove
 (`!hs:(A)rfs_history j k.
        rfs_history_ok hs /\ j <= k /\ k <= hs_count hs + 1
        ==> hs_time hs j <= hs_time hs k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - j:num`; `j:num`] RFS_TIME_MONO_ADD) THEN
  ASM_SIMP_TAC[ARITH_RULE `(j:num) <= k ==> j + (k - j) = k`]);;

let RFS_SLAB_UNIQUE = prove
 (`!hs:(A)rfs_history t k.
        rfs_history_ok hs /\ k <= hs_count hs /\
        hs_time hs k <= t /\ t < hs_time hs (k + 1)
        ==> rfs_slab hs t = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_slab] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `k':num` THEN BETA_TAC THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k + 1`; `k':num`] RFS_TIME_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k' + 1`; `k:num`] RFS_TIME_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let RFS_SLAB = prove
 (`!hs:(A)rfs_history t.
        rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
        ==> rfs_slab hs t <= hs_count hs /\
            hs_time hs (rfs_slab hs t) <= t /\ t < hs_time hs (rfs_slab hs t + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?k. k <= hs_count (hs:(A)rfs_history) /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?j. t < hs_time (hs:(A)rfs_history) j /\ !m. m < j ==> ~(t < hs_time hs m)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM num_WOP] THEN EXISTS_TAC `hs_count (hs:(A)rfs_history) + 1` THEN
      ASM_MESON_TAC[rfs_horizon];
      ALL_TAC] THEN
    ASM_CASES_TAC `j = 0` THENL
     [UNDISCH_TAC `t < hs_time (hs:(A)rfs_history) j` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `j - 1` THEN
    SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(j:num) - 1 <= n <=> j <= n + 1`] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history) + 1`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_horizon];
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`; `k:num`] RFS_SLAB_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let RFS_EXTENDS_HORIZON = prove
 (`!hs hs':(A)rfs_history.
        rfs_history_ok hs' /\ rfs_extends hs hs' ==> rfs_horizon hs <= rfs_horizon hs'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hs_time (hs':(A)rfs_history) (hs_count (hs:(A)rfs_history) + 1)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_horizon] THEN MATCH_MP_TAC RFS_TIME_MONO THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RFS_EXTENDS_AT = prove
 (`!hs hs':(A)rfs_history t.
        rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
        t < rfs_horizon hs
        ==> rfs_top_at hs' t = rfs_top_at hs t /\
            rfs_atlas_at hs' t = rfs_atlas_at hs t /\
            rfs_metric_at hs' t = rfs_metric_at hs t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`] RFS_EXTENDS_HORIZON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live; GSYM rfs_horizon] THEN
  ASM_CASES_TAC `&0 <= t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t < rfs_horizon (hs':(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) t` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_slab (hs':(A)rfs_history) t = k` SUBST1_TAC THENL
   [MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `k + 1 <= hs_count (hs:(A)rfs_history)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `k = hs_count (hs:(A)rfs_history)` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `t < hs_time (hs:(A)rfs_history) (hs_count hs + 1)` THEN
      UNDISCH_TAC `rfs_horizon (hs:(A)rfs_history) <= hs_time (hs':(A)rfs_history) (hs_count hs + 1)` THEN
      REWRITE_TAC[rfs_horizon] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFS_EXTENDS_TRUNC = prove
 (`!hs hs':(A)rfs_history tau.
        rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
        tau <= rfs_horizon hs
        ==> rfs_trunc (rfs_view hs') tau = rfs_trunc (rfs_view hs) tau`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_view; rfs_trunc; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN ABS_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `t:real`] RFS_EXTENDS_AT) THEN
  ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* A4. Locality in time: the strong canonical neighbourhood assumption and *)
(* noncollapsing pass to truncations (they only read times up to t).       *)
(* ------------------------------------------------------------------------- *)

let RFS_STRONG_CANONICAL_TRUNC = prove
 (`!TM AT G C eps (x:A) t U tau.
        t < tau /\ rfs_strong_canonical (TM,AT,G) C eps x t U
        ==> rfs_strong_canonical (rfs_trunc (TM,AT,G) tau) C eps x t U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_trunc; rfs_strong_canonical] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') ==> (a \/ b) ==> (a' \/ b)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_strong_neck (TM,AT,G) eps (x:A) t e` THEN
  REWRITE_TAC[rfs_strong_neck; rfs_evolving_neck; rfs_persists; rfs_close_fam] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                ((G:real->A->real^3^3) t) x`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s < tau` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `t + s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                       ((G:real->A->real^3^3) t) x < tau`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                     ((G:real->A->real^3^3) t) x <= &0`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let RFS_CANON_TRUNC = prove
 (`!TM AT G C eps rp tau.
        rfs_canonical_assumption (TM:real->A topology,AT,G) C eps rp
        ==> rfs_canonical_assumption (rfs_trunc (TM,AT,G) tau) C eps rp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_trunc; rfs_canonical_assumption] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
  ASM_CASES_TAC `t < tau` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `U:A->bool`) THEN EXISTS_TAC `U:A->bool` THEN
  MP_TAC(REWRITE_RULE[rfs_trunc] RFS_STRONG_CANONICAL_TRUNC) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFS_NONCOLL_TRUNC = prove
 (`!TM AT G (kp:real->real) r0 tau.
        rfs_noncollapsed (TM:real->A topology,AT,G) kp r0
        ==> rfs_noncollapsed (rfs_trunc (TM,AT,G) tau) kp r0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfs_trunc; rfs_noncollapsed; rfs_parabolic_exists; rfs_persists;
              rfs_vball] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN
  ASM_CASES_TAC `t < tau` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `!s. s <= t ==> s < tau` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `r:real`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `kp:real->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* The canonical neighbourhood assumption with                             *)
(* the volume clause (p3_canonv_assumption) and noncollapsing without the  *)
(* exemption (p3_noncoll_all) pass to truncations in the same way; the     *)
(* strong neck alternative is the first part of RFS_STRONG_CANONICAL_TRUNC. *)

let RFS_STRONG_NECK_TRUNC = prove
 (`!TM AT G eps (x:A) t e tau.
        t < tau /\ rfs_strong_neck (TM,AT,G) eps x t e
        ==> rfs_strong_neck (rfs_trunc (TM,AT,G) tau) eps x t e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_trunc] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_strong_neck (TM,AT,G) eps (x:A) t e` THEN
  REWRITE_TAC[rfs_strong_neck; rfs_evolving_neck; rfs_persists; rfs_close_fam] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                ((G:real->A->real^3^3) t) x`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s < tau` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `t + s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                       ((G:real->A->real^3^3) t) x < tau`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                     ((G:real->A->real^3^3) t) x <= &0`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let P3_STRONG_CANONV_TRUNC = prove
 (`!TM AT G C eps (x:A) t U tau.
        t < tau /\ p3_strong_canonv (TM,AT,G) C eps x t U
        ==> p3_strong_canonv (rfs_trunc (TM,AT,G) tau) C eps x t U`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[p3_strong_canonv; p3_comp_vol] THEN
  REWRITE_TAC[rfs_trunc; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') ==> (a \/ b) ==> (a' \/ b)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(REWRITE_RULE[rfs_trunc] RFS_STRONG_NECK_TRUNC) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3_CANONV_TRUNC = prove
 (`!TM AT G C eps rp tau.
        p3_canonv_assumption (TM:real->A topology,AT,G) C eps rp
        ==> p3_canonv_assumption (rfs_trunc (TM,AT,G) tau) C eps rp`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3_canonv_assumption; p3_canonv_at; rfs_trunc; rfs_vtop; rfs_vscalar] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
  ASM_CASES_TAC `t < tau` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `U:A->bool`) THEN EXISTS_TAC `U:A->bool` THEN
  MP_TAC(REWRITE_RULE[rfs_trunc] P3_STRONG_CANONV_TRUNC) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3_NONCOLL_ALL_TRUNC = prove
 (`!TM AT G (kp:real->real) r0 tau.
        p3_noncoll_all (TM:real->A topology,AT,G) kp r0
        ==> p3_noncoll_all (rfs_trunc (TM,AT,G) tau) kp r0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3_noncoll_all; p3_noncoll_at; rfs_trunc; rfs_vtop; rfs_vatlas;
              rfs_vmetric; rfs_parabolic_exists; rfs_persists; rfs_vball] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
  ASM_CASES_TAC `t < tau` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `!s. s <= t ==> s < tau` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `kp:real->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o SPEC `r:real`) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A5. Transfer to extensions, the upgrade of one step (Props 16.1 and     *)
(* 17.1 at step i give p3_step_closed), finite minima, sequence extension. *)
(* 17.1 gives the canonv assumption, 16.1 then p3_noncoll_all; the other   *)
(* conjuncts of p3_inv follow by weakening (pc_p3_defs).                   *)
(* ------------------------------------------------------------------------- *)

let P3_TRANSFER = prove
 (`!C eps hf md g0 A0 rs ks dd (hs:(A)rfs_history) hs' tau.
        p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\ rfs_history_ok hs' /\
        rfs_extends hs hs' /\ tau <= rfs_horizon hs
        ==> rfs_canonical_assumption (rfs_trunc (rfs_view hs') tau) C eps (p3_stepf rs) /\
            rfs_noncollapsed (rfs_trunc (rfs_view hs') tau) (p3_stepf ks) eps /\
            p3_canonv_assumption (rfs_trunc (rfs_view hs') tau) C eps (p3_stepf rs) /\
            p3_noncoll_all (rfs_trunc (rfs_view hs') tau) (p3_stepf ks) eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_inv; p3_struct] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `tau:real`]
         RFS_EXTENDS_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `rfs_canonical_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs)` THEN
  UNDISCH_TAC `rfs_noncollapsed (rfs_view (hs:(A)rfs_history)) (p3_stepf ks) eps` THEN
  UNDISCH_TAC `p3_canonv_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs)` THEN
  UNDISCH_TAC `p3_noncoll_all (rfs_view (hs:(A)rfs_history)) (p3_stepf ks) eps` THEN
  REWRITE_TAC[rfs_view] THEN
  MESON_TAC[RFS_CANON_TRUNC; RFS_NONCOLL_TRUNC; P3_CANONV_TRUNC; P3_NONCOLL_ALL_TRUNC]);;

let P3_UPGRADE = prove
 (`!(u:A->bool) C eps hf md g0 A0 i rsi ksi dsi rs ks dd dseq dfun.
        (!j. j <= i ==> rsi j = rs j /\ ksi j = ks j /\ dsi j = dseq j) /\
        p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok dd /\ p3_seq_ok dseq /\
        (!j. dd j <= dseq (SUC j)) /\
        dseq (SUC i) <= dfun (rs (SUC i)) /\
        p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rsi,ksi,dsi) (ks (SUC i)) dfun /\
        p3_canon_prop u (C,eps,hf,md,g0,A0) i (rsi,ksi,dsi) (rs (SUC i)) (dseq (SUC i))
        ==> p3_step_closed u (C,eps,hf,md,g0,A0) (rs,ks,dd) i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agree") (CONJUNCTS_THEN2 (LABEL_TAC "rs")
    (CONJUNCTS_THEN2 (LABEL_TAC "ks") (CONJUNCTS_THEN2 (LABEL_TAC "dd")
      (CONJUNCTS_THEN2 (LABEL_TAC "dseq") (CONJUNCTS_THEN2 (LABEL_TAC "le")
        (CONJUNCTS_THEN2 (LABEL_TAC "dfun")
          (CONJUNCTS_THEN2 (LABEL_TAC "nc") (LABEL_TAC "cn"))))))))) THEN
  REWRITE_TAC[p3_step_closed] THEN X_GEN_TAC `hs:(A)rfs_history` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!dlt. dseq (SUC i) <= dlt
          ==> p3_step_hyp (C,eps,hf,md,g0,A0) i (rsi,ksi,dsi) dlt (rs,ks,dd)
                          (hs:(A)rfs_history)`
  (LABEL_TAC "hyp") THENL
   [X_GEN_TAC `dlt:real` THEN DISCH_TAC THEN REWRITE_TAC[p3_step_hyp] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!j. (dd:num->real) j <= dseq j` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(dseq:num->real) (SUC j)` THEN
      USE_THEN "le" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "dseq" (MP_TAC o REWRITE_RULE[p3_seq_ok]) THEN SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN USE_THEN "agree" (MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN USE_THEN "agree" (MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dseq:num->real) (SUC i)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dd:num->real) i` THEN
      CONJ_TAC THENL
       [USE_THEN "dd" (MP_TAC o REWRITE_RULE[p3_seq_ok]) THEN SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dseq:num->real) (SUC i)` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3_canonv_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs)`
  ASSUME_TAC THENL
   [USE_THEN "cn" (MP_TAC o SPECL [`rs:num->real`; `ks:num->real`; `dd:num->real`;
                                   `hs:(A)rfs_history`] o REWRITE_RULE[p3_canon_prop]) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "hyp" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3_noncoll_all (rfs_view (hs:(A)rfs_history)) (p3_stepf ks) eps`
  ASSUME_TAC THENL
   [USE_THEN "nc" (MP_TAC o SPECL [`(rs:num->real) (SUC i)`; `rs:num->real`;
                                   `ks:num->real`; `dd:num->real`;
                                   `hs:(A)rfs_history`] o REWRITE_RULE[p3_noncoll_prop]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "rs" (MP_TAC o REWRITE_RULE[p3_seq_ok]) THEN SIMP_TAC[];
      USE_THEN "agree" (MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
      USE_THEN "rs" (MP_TAC o REWRITE_RULE[p3_seq_ok]) THEN SIMP_TAC[];
      USE_THEN "hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p3_inv] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3_CANONV_ASSUMPTION_IMP; MATCH_MP_TAC P3_NONCOLL_ALL_IMP] THEN
  ASM_REWRITE_TAC[]);;

let P3_FINITE_MIN = prove
 (`!(f:num->real) n.
        (!j. j <= n ==> &0 < f j) ==> ?m. &0 < m /\ !j. j <= n ==> m <= f j`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `inf (IMAGE (f:num->real) (0..n))` THEN
  MP_TAC(ISPEC `IMAGE (f:num->real) (0..n)` INF_FINITE) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY; LT;
           FORALL_IN_IMAGE; IN_IMAGE; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[]);;

let P3_SEQ_UPTO_EXTEND = prove
 (`!s s' i x.
        p3_seq_upto i s /\ (!j. j <= i ==> s' j = s j) /\ s' (SUC i) = x /\
        &0 < x /\ x <= s i
        ==> p3_seq_upto (SUC i) s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_seq_upto] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j = SUC i` THENL
   [ASM_REWRITE_TAC[LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:num) <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(j:num) = i` THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `SUC j <= i /\ j < i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A6. The parameter sequences: course-of-values recursion through Skolem  *)
(* functions of the step results.                                          *)
(* ------------------------------------------------------------------------- *)

let P3_DIAG_AGREE = prove
 (`!s:num->num->real.
        (!n j. j <= SUC n ==> s (SUC n) j = s n j)
        ==> !n j. j <= SUC n ==> s n j = s j j`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "f1") THEN
  SUBGOAL_THEN `!d n j. j <= SUC n ==> (s:num->num->real) (n + d) j = s n j`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(s:num->num->real) (n + d) j` THEN
    CONJ_TAC THENL
     [USE_THEN "f1" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = SUC n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "f1" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - j:num`; `j:num`; `j:num`]) THEN
    REWRITE_TAC[ARITH_RULE `(j:num) <= SUC j`] THEN
    SUBGOAL_THEN `(j:num) + (n - j) = n` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let P3_DIAG_OK = prove
 (`!s:num->num->real.
        (!n. p3_seq_upto (SUC n) (s n)) /\
        (!n j. j <= SUC n ==> s (SUC n) j = s n j)
        ==> p3_seq_ok (\j. s j j)`,
  GEN_TAC THEN REWRITE_TAC[p3_seq_ok; p3_seq_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v") (LABEL_TAC "a")) THEN
  X_GEN_TAC `j:num` THEN
  USE_THEN "a" (MP_TAC o SPECL [`j:num`; `SUC j`]) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  USE_THEN "v" (MP_TAC o SPECL [`j:num`; `j:num`]) THEN
  REWRITE_TAC[ARITH_RULE `(j:num) <= SUC j /\ j < SUC j`] THEN SIMP_TAC[]);;

let P3_SEQ_RECURSION = prove
 (`!(P:num->(num->real)->(num->real)->(num->real)->real->real->real->bool) r0 k0 d0.
     &0 < r0 /\ &0 < k0 /\ &0 < d0 /\
     (!i rs ks ds.
        1 <= i /\ rs 0 = r0 /\ ks 0 = k0 /\ ds 0 = d0 /\
        p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds
        ==> ?r k d. &0 < r /\ r <= rs i /\ &0 < k /\ k <= ks i /\
                    &0 < d /\ d <= ds i /\ P i rs ks ds r k d)
     ==> ?rs ks ds.
           p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok ds /\
           rs 0 = r0 /\ ks 0 = k0 /\ ds 0 = d0 /\
           !i. 1 <= i
               ==> ?rsi ksi dsi.
                     (!j. j <= i ==> rsi j = rs j /\ ksi j = ks j /\ dsi j = ds j) /\
                     rsi 0 = r0 /\ ksi 0 = k0 /\ dsi 0 = d0 /\
                     p3_seq_upto i rsi /\ p3_seq_upto i ksi /\ p3_seq_upto i dsi /\
                     P i rsi ksi dsi (rs (SUC i)) (ks (SUC i)) (ds (SUC i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num->(num->real)->(num->real)->(num->real)->real`
    (X_CHOOSE_THEN `K:num->(num->real)->(num->real)->(num->real)->real`
      (X_CHOOSE_THEN `D:num->(num->real)->(num->real)->(num->real)->real`
        (LABEL_TAC "step")))) THEN
  MP_TAC(ISPECL
   [`(\j:num. r0:real),(\j:num. k0:real),(\j:num. d0:real)`;
    `\(st:(num->real)#(num->real)#(num->real)) (n:num).
       (\j. if j = SUC(SUC n)
            then (R:num->(num->real)->(num->real)->(num->real)->real)
                   (SUC n) (FST st) (FST(SND st)) (SND(SND st))
            else FST st j),
       (\j. if j = SUC(SUC n)
            then (K:num->(num->real)->(num->real)->(num->real)->real)
                   (SUC n) (FST st) (FST(SND st)) (SND(SND st))
            else FST(SND st) j),
       (\j. if j = SUC(SUC n)
            then (D:num->(num->real)->(num->real)->(num->real)->real)
                   (SUC n) (FST st) (FST(SND st)) (SND(SND st))
            else SND(SND st) j)`]
   num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:num->(num->real)#(num->real)#(num->real)`
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `RS = \n. FST((S:num->(num->real)#(num->real)#(num->real)) n)` THEN
  ABBREV_TAC `KS = \n. FST(SND((S:num->(num->real)#(num->real)#(num->real)) n))` THEN
  ABBREV_TAC `DS = \n. SND(SND((S:num->(num->real)#(num->real)#(num->real)) n))` THEN
  SUBGOAL_THEN
   `((RS:num->num->real) 0 = \j:num. (r0:real)) /\
    ((KS:num->num->real) 0 = \j:num. (k0:real)) /\
    ((DS:num->num->real) 0 = \j:num. (d0:real)) /\
    (!n. RS (SUC n) =
         (\j. if j = SUC(SUC n)
              then (R:num->(num->real)->(num->real)->(num->real)->real)
                     (SUC n) (RS n) (KS n) (DS n) else RS n j)) /\
    (!n. KS (SUC n) =
         (\j. if j = SUC(SUC n)
              then (K:num->(num->real)->(num->real)->(num->real)->real)
                     (SUC n) (RS n) (KS n) (DS n) else KS n j)) /\
    (!n. DS (SUC n) =
         (\j. if j = SUC(SUC n)
              then (D:num->(num->real)->(num->real)->(num->real)->real)
                     (SUC n) (RS n) (KS n) (DS n) else DS n j))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["RS"; "KS"; "DS"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n j. j <= SUC n ==> (RS:num->num->real) (SUC n) j = RS n j) /\
    (!n j. j <= SUC n ==> (KS:num->num->real) (SUC n) j = KS n j) /\
    (!n j. j <= SUC n ==> (DS:num->num->real) (SUC n) j = DS n j)`
  (CONJUNCTS_THEN2 (LABEL_TAC "a1") (CONJUNCTS_THEN2 (LABEL_TAC "a2") (LABEL_TAC "a3")))
  THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(j = SUC(SUC n))` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (RS:num->num->real) n 0 = r0 /\ (KS:num->num->real) n 0 = k0 /\
        (DS:num->num->real) n 0 = d0 /\
        p3_seq_upto (SUC n) (RS n) /\ p3_seq_upto (SUC n) (KS n) /\
        p3_seq_upto (SUC n) (DS n)`
  (LABEL_TAC "v") THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[p3_seq_upto; REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    USE_THEN "step" (MP_TAC o SPECL [`SUC n`; `(RS:num->num->real) n`;
                                     `(KS:num->num->real) n`; `(DS:num->num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "a1" (MP_TAC o SPECL [`n:num`; `0`]) THEN ASM_SIMP_TAC[LE_0];
      USE_THEN "a2" (MP_TAC o SPECL [`n:num`; `0`]) THEN ASM_SIMP_TAC[LE_0];
      USE_THEN "a3" (MP_TAC o SPECL [`n:num`; `0`]) THEN ASM_SIMP_TAC[LE_0];
      MATCH_MP_TAC P3_SEQ_UPTO_EXTEND THEN
      MAP_EVERY EXISTS_TAC
       [`(RS:num->num->real) n`;
        `(R:num->(num->real)->(num->real)->(num->real)->real)
           (SUC n) ((RS:num->num->real) n) ((KS:num->num->real) n) ((DS:num->num->real) n)`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "a1" (fun th -> MESON_TAC[th]);
      MATCH_MP_TAC P3_SEQ_UPTO_EXTEND THEN
      MAP_EVERY EXISTS_TAC
       [`(KS:num->num->real) n`;
        `(K:num->(num->real)->(num->real)->(num->real)->real)
           (SUC n) ((RS:num->num->real) n) ((KS:num->num->real) n) ((DS:num->num->real) n)`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "a2" (fun th -> MESON_TAC[th]);
      MATCH_MP_TAC P3_SEQ_UPTO_EXTEND THEN
      MAP_EVERY EXISTS_TAC
       [`(DS:num->num->real) n`;
        `(D:num->(num->real)->(num->real)->(num->real)->real)
           (SUC n) ((RS:num->num->real) n) ((KS:num->num->real) n) ((DS:num->num->real) n)`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "a3" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\j. (RS:num->num->real) j j`; `\j. (KS:num->num->real) j j`;
    `\j. (DS:num->num->real) j j`] THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3_DIAG_OK THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC P3_DIAG_OK THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC P3_DIAG_OK THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. i = SUC n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `i - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "v" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN
   `(RS:num->num->real) (SUC(SUC n)) (SUC(SUC n)) =
      (R:num->(num->real)->(num->real)->(num->real)->real) (SUC n) (RS n) (KS n) (DS n) /\
    (KS:num->num->real) (SUC(SUC n)) (SUC(SUC n)) =
      (K:num->(num->real)->(num->real)->(num->real)->real) (SUC n) (RS n) (KS n) (DS n) /\
    (DS:num->num->real) (SUC(SUC n)) (SUC(SUC n)) =
      (D:num->(num->real)->(num->real)->(num->real)->real) (SUC n) (RS n) (KS n) (DS n)`
  (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "a1" (MP_TAC o SPECL [`SUC n`; `SUC(SUC n)`]) THEN
    USE_THEN "a2" (MP_TAC o SPECL [`SUC n`; `SUC(SUC n)`]) THEN
    USE_THEN "a3" (MP_TAC o SPECL [`SUC n`; `SUC(SUC n)`]) THEN
    REWRITE_TAC[LE_REFL] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(RS:num->num->real) n`; `(KS:num->num->real) n`; `(DS:num->num->real) n`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `RS:num->num->real` P3_DIAG_AGREE) THEN
    MP_TAC(SPEC `KS:num->num->real` P3_DIAG_AGREE) THEN
    MP_TAC(SPEC `DS:num->num->real` P3_DIAG_AGREE) THEN
    ASM_SIMP_TAC[];
    USE_THEN "step" (MP_TAC o SPECL [`SUC n`; `(RS:num->num->real) n`;
                                     `(KS:num->num->real) n`; `(DS:num->num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A7. One advance inside [T_i, T_(i+1)]: Ricci flow extension, or surgery *)
(* (Lemma 15.11), then the step closure.  The surgery input has the rp     *)
(* bound of Lemma 15.11, supplied from rs 0 = eps (A7 to A9, D2).          *)
(* ------------------------------------------------------------------------- *)

let P3_ADVANCE = prove
 (`!(u:A->bool) (FR:(real->real)->(A)rfs_history->bool) C eps hf md g0 A0 rs ks dd i d11 (hs:(A)rfs_history).
     P3_FLOW_EXTENSION_STATEMENT u /\
     (!dl (h:(A)rfs_history) h'.
        FR dl h /\ rfs_extends h h' /\ hs_count h' = hs_count h ==> FR dl h') /\
     (!rp dl kp (h:(A)rfs_history) Tb.
        FR dl h /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h /\
        rfs_canonical_assumption (rfs_view h) C eps rp /\
        rfs_noncollapsed (rfs_view h) kp eps /\
        (!t. &0 <= t ==> &0 < kp t /\ dl t <= d11) /\
        (!t. &0 <= t ==> rp t <= eps) /\
        rfs_slab_maximal h (hs_count h) /\ rfs_horizon h < Tb
        ==> ?h'. rfs_extends h h' /\ hs_count h' = SUC(hs_count h) /\
                 hs_time h' (SUC(hs_count h)) = rfs_horizon h /\
                 rfs_horizon h < rfs_horizon h' /\ rfs_horizon h' <= Tb /\
                 p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h' /\ FR dl h') /\
     p3_step_closed u (C,eps,hf,md,g0,A0) (rs,ks,dd) i /\
     (!t. &0 <= t ==> p3_stepf dd t <= d11) /\
     FR (p3_stepf dd) hs /\ p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
     p3_T i <= rfs_horizon hs /\ rfs_horizon hs < p3_T (SUC i) /\ rs 0 = eps
     ==> ?hs'. rfs_extends hs hs' /\ FR (p3_stepf dd) hs' /\
               p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs' /\
               rfs_horizon hs < rfs_horizon hs' /\ rfs_horizon hs' <= p3_T (SUC i) /\
               (rfs_horizon hs' = p3_T (SUC i) \/ hs_count hs' = SUC(hs_count hs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "flow") (CONJUNCTS_THEN2 (LABEL_TAC "fr")
    (CONJUNCTS_THEN2 (LABEL_TAC "surg")
    (CONJUNCTS_THEN2 (LABEL_TAC "up") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!h h':(A)rfs_history.
      p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h /\ p3_T i <= rfs_horizon h /\
      rfs_extends h h' /\
      p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd) h' /\
      rfs_horizon h < rfs_horizon h' /\ rfs_horizon h' <= p3_T (SUC i)
      ==> p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h'`
  (LABEL_TAC "U") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "up" (MATCH_MP_TAC o REWRITE_RULE[p3_step_closed]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P3_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `dd:num->real`; `h:(A)rfs_history`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd)
                   (h':(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:(A)rfs_history.
      FR (p3_stepf dd) h /\
      p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h /\ p3_T i <= rfs_horizon h /\
      rfs_horizon h < p3_T (SUC i) /\ rfs_slab_maximal h (hs_count h)
      ==> ?h'. rfs_extends h h' /\ FR (p3_stepf dd) h' /\
               p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h' /\
               rfs_horizon h < rfs_horizon h' /\ rfs_horizon h' <= p3_T (SUC i) /\
               hs_count h' = SUC(hs_count h)`
  (LABEL_TAC "S") THENL
   [REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3_inv]
      (ASSUME `p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) (h:(A)rfs_history)`)) THEN
    USE_THEN "surg" (MP_TAC o SPECL [`p3_stepf rs`; `p3_stepf dd`; `p3_stepf ks`;
                                     `h:(A)rfs_history`; `p3_T (SUC i)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[P3_STEPF_POS; P3_STEPF_LE_EPS]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h':(A)rfs_history` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `h':(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "U" MATCH_MP_TAC THEN EXISTS_TAC `h:(A)rfs_history` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `rfs_slab_maximal (hs:(A)rfs_history) (hs_count hs)` THENL
   [USE_THEN "S" (MP_TAC o SPEC `hs:(A)rfs_history`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd) (hs:(A)rfs_history)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p3_inv]; ALL_TAC] THEN
  USE_THEN "flow" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
     `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs`; `p3_stepf dd`;
     `hs:(A)rfs_history`; `p3_T (SUC i)`] o
     REWRITE_RULE[P3_FLOW_EXTENSION_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:(A)rfs_history` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) (h1:(A)rfs_history)` ASSUME_TAC
  THENL
   [USE_THEN "U" MATCH_MP_TAC THEN EXISTS_TAC `hs:(A)rfs_history` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(FR:(real->real)->(A)rfs_history->bool) (p3_stepf dd) h1` ASSUME_TAC THENL
   [USE_THEN "fr" MATCH_MP_TAC THEN EXISTS_TAC `hs:(A)rfs_history` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i)` THENL
   [EXISTS_TAC `h1:(A)rfs_history` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_slab_maximal (h1:(A)rfs_history) (hs_count h1)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i) \/
                   rfs_slab_maximal h1 (hs_count h1)`) THEN
    REWRITE_TAC[ASSUME `~(rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i))`];
    ALL_TAC] THEN
  USE_THEN "S" (MP_TAC o SPEC `h1:(A)rfs_history`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:(A)rfs_history` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h2:(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFS_EXTENDS_TRANS THEN EXISTS_TAC `h1:(A)rfs_history` THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A8. The inner loop: advances until T_(i+1), terminated by the bound of  *)
(* Lemma 17.12 on the number of surgeries.                                 *)
(* ------------------------------------------------------------------------- *)

let P3_LOOP = prove
 (`!(u:A->bool) (FR:(real->real)->(A)rfs_history->bool) C eps hf md g0 A0 rs ks dd i d11 N top0 atlas0 g00.
     P3_FLOW_EXTENSION_STATEMENT u /\
     (!dl (h:(A)rfs_history) h'.
        FR dl h /\ rfs_extends h h' /\ hs_count h' = hs_count h ==> FR dl h') /\
     (!rp dl kp (h:(A)rfs_history) Tb.
        FR dl h /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h /\
        rfs_canonical_assumption (rfs_view h) C eps rp /\
        rfs_noncollapsed (rfs_view h) kp eps /\
        (!t. &0 <= t ==> &0 < kp t /\ dl t <= d11) /\
        (!t. &0 <= t ==> rp t <= eps) /\
        rfs_slab_maximal h (hs_count h) /\ rfs_horizon h < Tb
        ==> ?h'. rfs_extends h h' /\ hs_count h' = SUC(hs_count h) /\
                 hs_time h' (SUC(hs_count h)) = rfs_horizon h /\
                 rfs_horizon h < rfs_horizon h' /\ rfs_horizon h' <= Tb /\
                 p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h' /\ FR dl h') /\
     p3_step_closed u (C,eps,hf,md,g0,A0) (rs,ks,dd) i /\
     (!t. &0 <= t ==> p3_stepf dd t <= d11) /\
     (!h:(A)rfs_history.
        hs_top h 0 = top0 /\ hs_atlas h 0 = atlas0 /\ hs_metric h 0 (&0) = g00 /\
        p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd) h /\
        FR (p3_stepf dd) h /\
        rfs_horizon h <= p3_T (SUC i)
        ==> hs_count h <= N) /\
     rs 0 = eps
     ==> !n (hs:(A)rfs_history).
           FR (p3_stepf dd) hs /\
           p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\ p3_T i <= rfs_horizon hs /\
           hs_top hs 0 = top0 /\ hs_atlas hs 0 = atlas0 /\
           hs_metric hs 0 (&0) = g00 /\ N < hs_count hs + n
           ==> ?hs'. rfs_extends hs hs' /\ FR (p3_stepf dd) hs' /\
                     p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs' /\
                     p3_T (SUC i) <= rfs_horizon hs'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "flow") (CONJUNCTS_THEN2 (LABEL_TAC "fr")
    (CONJUNCTS_THEN2 (LABEL_TAC "surg")
    (CONJUNCTS_THEN2 (LABEL_TAC "up") (CONJUNCTS_THEN2 (LABEL_TAC "d11")
      (CONJUNCTS_THEN2 (LABEL_TAC "bound") (LABEL_TAC "rs0"))))))) THEN
  INDUCT_TAC THEN X_GEN_TAC `hs:(A)rfs_history` THEN STRIP_TAC THEN
  (ASM_CASES_TAC `p3_T (SUC i) <= rfs_horizon (hs:(A)rfs_history)` THENL
    [EXISTS_TAC `hs:(A)rfs_history` THEN ASM_REWRITE_TAC[RFS_EXTENDS_REFL];
     ALL_TAC] THEN
   SUBGOAL_THEN `rfs_horizon (hs:(A)rfs_history) < p3_T (SUC i)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `hs_count (hs:(A)rfs_history) <= N` ASSUME_TAC THENL
    [USE_THEN "bound" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) (hs:(A)rfs_history)` THEN
       REWRITE_TAC[p3_inv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       ASM_REAL_ARITH_TAC];
     ALL_TAC])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `FR:(real->real)->(A)rfs_history->bool`; `C:real`; `eps:real`;
    `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`;
    `ks:num->real`; `dd:num->real`; `i:num`; `d11:real`; `hs:(A)rfs_history`]
    P3_ADVANCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "flow" ACCEPT_TAC; USE_THEN "fr" ACCEPT_TAC;
           USE_THEN "surg" ACCEPT_TAC;
           USE_THEN "up" ACCEPT_TAC; USE_THEN "d11" ACCEPT_TAC;
           USE_THEN "rs0" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:(A)rfs_history` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_inv; p3_struct] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `h1:(A)rfs_history`] RFS_EXTENDS_INITIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i)` THENL
   [EXISTS_TAC `h1:(A)rfs_history` THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `hs_count (h1:(A)rfs_history) = SUC(hs_count (hs:(A)rfs_history))`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i) \/
                   hs_count h1 = SUC(hs_count (hs:(A)rfs_history))`) THEN
    REWRITE_TAC[ASSUME `~(rfs_horizon (h1:(A)rfs_history) = p3_T (SUC i))`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h1:(A)rfs_history`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:(A)rfs_history` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h2:(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFS_EXTENDS_TRANS THEN EXISTS_TAC `h1:(A)rfs_history` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A9. The key step: from T_i to T_(i+1), with the lower bounds for Lemma  *)
(* 17.12 from the step functions.                                          *)
(* ------------------------------------------------------------------------- *)

let P3_KEY_STEP = prove
 (`!(u:A->bool) (FR:(real->real)->(A)rfs_history->bool) C eps hf md g0 A0 rs ks dd i d11 d1712.
     P3_FLOW_EXTENSION_STATEMENT u /\
     (!dl (h:(A)rfs_history) h'.
        FR dl h /\ rfs_extends h h' /\ hs_count h' = hs_count h ==> FR dl h') /\
     (!rp dl kp (h:(A)rfs_history) Tb.
        FR dl h /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h /\
        rfs_canonical_assumption (rfs_view h) C eps rp /\
        rfs_noncollapsed (rfs_view h) kp eps /\
        (!t. &0 <= t ==> &0 < kp t /\ dl t <= d11) /\
        (!t. &0 <= t ==> rp t <= eps) /\
        rfs_slab_maximal h (hs_count h) /\ rfs_horizon h < Tb
        ==> ?h'. rfs_extends h h' /\ hs_count h' = SUC(hs_count h) /\
                 hs_time h' (SUC(hs_count h)) = rfs_horizon h /\
                 rfs_horizon h < rfs_horizon h' /\ rfs_horizon h' <= Tb /\
                 p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h' /\ FR dl h') /\
     p3_step_closed u (C,eps,hf,md,g0,A0) (rs,ks,dd) i /\
     p3_hfun C hf /\ p3_seq_ok rs /\ p3_seq_ok dd /\
     (!t. &0 <= t ==> p3_stepf dd t <= d11) /\
     (!t. &0 <= t ==> p3_stepf dd t <= d1712) /\
     (!top0 atlas0 g00 Tb rmin dmin hmin.
        &0 < rmin /\ &0 < dmin /\ &0 < hmin
        ==> ?N. !rp dl (h:(A)rfs_history).
                  hs_top h 0 = top0 /\ hs_atlas h 0 = atlas0 /\
                  hs_metric h 0 (&0) = g00 /\
                  p3_struct (C,eps,hf,md,g0,A0) (rp,dl) h /\
                  FR dl h /\
                  rfs_horizon h <= Tb /\
                  (!t. &0 <= t ==> dl t <= d1712) /\
                  (!t. &0 <= t /\ t < Tb
                       ==> rmin <= rp t /\ dmin <= dl t /\
                           hmin <= p3_hscale hf rp dl t)
                  ==> hs_count h <= N) /\
     rs 0 = eps
     ==> !hs:(A)rfs_history.
           FR (p3_stepf dd) hs /\
           p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\ p3_T i <= rfs_horizon hs
           ==> ?hs'. rfs_extends hs hs' /\ FR (p3_stepf dd) hs' /\
                     p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs' /\
                     p3_T (SUC i) <= rfs_horizon hs'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "flow") (CONJUNCTS_THEN2 (LABEL_TAC "fr")
    (CONJUNCTS_THEN2 (LABEL_TAC "surg")
    (CONJUNCTS_THEN2 (LABEL_TAC "up") (CONJUNCTS_THEN2 (LABEL_TAC "hf")
      (CONJUNCTS_THEN2 (LABEL_TAC "rs") (CONJUNCTS_THEN2 (LABEL_TAC "dd")
        (CONJUNCTS_THEN2 (LABEL_TAC "d11") (CONJUNCTS_THEN2 (LABEL_TAC "d1712")
          (CONJUNCTS_THEN2 (LABEL_TAC "l1712") (LABEL_TAC "rs0"))))))))))) THEN
  X_GEN_TAC `hs:(A)rfs_history` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!j. &0 < (rs:num->real) j) /\ (!j. &0 < (dd:num->real) j)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p3_seq_ok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. (hf:real->real->real) ((dd:num->real) j * (rs:num->real) j) (dd j)`;
                 `SUC i`] P3_FINITE_MIN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "hf" (MP_TAC o SPECL [`(dd:num->real) j * (rs:num->real) j`;
                                   `(dd:num->real) j`] o REWRITE_RULE[p3_hfun]) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    DISCH_THEN(X_CHOOSE_THEN `hmin:real` STRIP_ASSUME_TAC)] THEN
  USE_THEN "l1712" (MP_TAC o SPECL [`hs_top (hs:(A)rfs_history) 0`;
     `hs_atlas (hs:(A)rfs_history) 0`; `hs_metric (hs:(A)rfs_history) 0 (&0)`;
     `p3_T (SUC i)`; `(rs:num->real) (SUC i)`; `(dd:num->real) (SUC i)`; `hmin:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MP_TAC(ISPECL [`u:A->bool`; `FR:(real->real)->(A)rfs_history->bool`; `C:real`; `eps:real`;
     `hf:real->real->real`;
     `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`;
     `ks:num->real`; `dd:num->real`; `i:num`; `d11:real`; `N:num`;
     `hs_top (hs:(A)rfs_history) 0`; `hs_atlas (hs:(A)rfs_history) 0`;
     `hs_metric (hs:(A)rfs_history) 0 (&0)`] P3_LOOP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "flow" ACCEPT_TAC; USE_THEN "fr" ACCEPT_TAC;
      USE_THEN "surg" ACCEPT_TAC;
      USE_THEN "up" ACCEPT_TAC; USE_THEN "d11" ACCEPT_TAC;
      ALL_TAC; USE_THEN "rs0" ACCEPT_TAC] THEN
    X_GEN_TAC `h:(A)rfs_history` THEN STRIP_TAC THEN
    USE_THEN "N" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p3_stepf rs`; `p3_stepf dd`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p3_step t <= SUC i` ASSUME_TAC THENL
     [MATCH_MP_TAC P3_STEP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p3_stepf; p3_hscale] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `rs:num->real` P3_SEQ_MONO) THEN ASM_SIMP_TAC[];
      MP_TAC(SPEC `dd:num->real` P3_SEQ_MONO) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`SUC N`; `hs:(A)rfs_history`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* D2. MT Thm 15.9 in continuation form from its parts.                    *)
(* ------------------------------------------------------------------------- *)

let P3_THM_15_9_FROM_PARTS_FR = prove
 (`!(u:A->bool) (FR:(real->real)->(A)rfs_history->bool).
     P3_PROP_16_1_STATEMENT u /\ P3_PROP_17_1_STATEMENT u /\
     (?g0 A0 md eps11 d11.
        p3_std_initial g0 A0 /\ p3_modulus md /\ &0 < eps11 /\ &0 < d11 /\
        !eps C. &0 < eps /\ eps <= eps11 /\ &1 < C
          ==> ?hf. p3_hfun C hf /\
                !rp dl kp (hs:(A)rfs_history) Tb.
                   FR dl hs /\
                   p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                   rfs_canonical_assumption (rfs_view hs) C eps rp /\
                   rfs_noncollapsed (rfs_view hs) kp eps /\
                   (!t. &0 <= t ==> &0 < kp t /\ dl t <= d11) /\
                   (!t. &0 <= t ==> rp t <= eps) /\
                   rfs_slab_maximal hs (hs_count hs) /\ rfs_horizon hs < Tb
                   ==> ?hs'. rfs_extends hs hs' /\
                             hs_count hs' = SUC(hs_count hs) /\
                             hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
                             rfs_horizon hs < rfs_horizon hs' /\ rfs_horizon hs' <= Tb /\
                             p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs' /\
                             FR dl hs') /\
     (!dl (h:(A)rfs_history) h'.
        FR dl h /\ rfs_extends h h' /\ hs_count h' = hs_count h ==> FR dl h') /\
     P3_FLOW_EXTENSION_STATEMENT u /\
     (!C eps hf md g0 A0.
        &1 < C /\ &0 < eps /\ p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
        ==> ?d1712. &0 < d1712 /\
              !top0 atlas0 g00 Tb rmin dmin hmin.
                 &0 < rmin /\ &0 < dmin /\ &0 < hmin
                 ==> ?N. !rp dl (hs:(A)rfs_history).
                           hs_top hs 0 = top0 /\ hs_atlas hs 0 = atlas0 /\
                           hs_metric hs 0 (&0) = g00 /\
                           p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                           FR dl hs /\
                           rfs_horizon hs <= Tb /\
                           (!t. &0 <= t ==> dl t <= d1712) /\
                           (!t. &0 <= t /\ t < Tb
                                ==> rmin <= rp t /\ dmin <= dl t /\
                                    hmin <= p3_hscale hf rp dl t)
                           ==> hs_count hs <= N)
     ==> ?eps1. &0 < eps1 /\
           !eps. &0 < eps /\ eps <= eps1
             ==> ?C hf md g0 A0.
                   &1 < C /\ p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
                   !kappa0. &0 < kappa0
                     ==> ?rs ks ds.
                           p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok ds /\
                           rs 0 = eps /\ ks 0 = kappa0 /\
                           !dd (hs:(A)rfs_history).
                              p3_seq_ok dd /\ (!j. dd j <= ds j) /\
                              FR (p3_stepf dd) hs /\
                              p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
                              p3_T 1 <= rfs_horizon hs
                              ==> !Tb. ?hs'. rfs_extends hs hs' /\
                                             FR (p3_stepf dd) hs' /\
                                             p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs' /\
                                             Tb <= rfs_horizon hs'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P3_PROP_16_1_STATEMENT; P3_PROP_17_1_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps16:real` (X_CHOOSE_THEN `d16:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p16")))))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps17:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p17")))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g0:real^3->real^3^3` (X_CHOOSE_THEN `A0:real`
          (X_CHOOSE_THEN `md:real->real` (X_CHOOSE_THEN `eps11:real`
            (X_CHOOSE_THEN `d11:real`
              (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
                (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
                  (LABEL_TAC "l1511"))))))))))
        (CONJUNCTS_THEN2 (LABEL_TAC "fr")
          (CONJUNCTS_THEN2 (LABEL_TAC "flow") (LABEL_TAC "l1712")))))) THEN
  EXISTS_TAC `min eps11 (min eps16 eps17)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps11 /\ eps <= eps16 /\ eps <= eps17` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "p17" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `d17:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q17"))))) THEN
  USE_THEN "l1511" (MP_TAC o SPECL [`eps:real`; `C:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hf:real->real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "surg"))) THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `hf:real->real->real`; `md:real->real`;
                        `g0:real^3->real^3^3`; `A0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "l1712" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
     `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1712:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q1712"))) THEN
  X_GEN_TAC `kappa0:real` THEN DISCH_TAC THEN
  ABBREV_TAC `d0 = min d16 (min d17 (min d11 d1712))` THEN
  SUBGOAL_THEN `&0 < d0 /\ d0 <= d16 /\ d0 <= d17 /\ d0 <= d11 /\ d0 <= d1712`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\i (rsi:num->real) (ksi:num->real) (dsi:num->real) (r:real) (k:real) (d:real).
       ?dfun. d <= dfun r /\
              p3_noncoll_prop (u:A->bool) (C,eps,hf,md,g0,A0) i (rsi,ksi,dsi) k dfun /\
              p3_canon_prop (u:A->bool) (C,eps,hf,md,g0,A0) i (rsi,ksi,dsi) r d`;
    `eps:real`; `kappa0:real`; `d0:real`] P3_SEQ_RECURSION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `rsi:num->real`; `ksi:num->real`; `dsi:num->real`] THEN
    STRIP_TAC THEN
    USE_THEN "p16" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
       `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `rsi:num->real`; `ksi:num->real`;
                               `dsi:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `dfun:real->real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "q17" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`;
       `md:real->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `rsi:num->real`; `ksi:num->real`;
                               `dsi:num->real`; `kappa:real`; `dfun:real->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real` (X_CHOOSE_THEN `dnew:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r':real`; `kappa:real`; `dnew:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dfun:real->real) r'` THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `dfun:real->real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:num->real` (X_CHOOSE_THEN `ks:num->real`
    (X_CHOOSE_THEN `dseq:num->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (LABEL_TAC "seqs")))))))))) THEN
  MAP_EVERY EXISTS_TAC [`rs:num->real`; `ks:num->real`;
                        `\j. (dseq:num->real) (SUC j)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p3_seq_ok (\j. (dseq:num->real) (SUC j))` (fun th -> REWRITE_TAC[th])
  THENL
   [UNDISCH_TAC `p3_seq_ok (dseq:num->real)` THEN REWRITE_TAC[p3_seq_ok] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`dd:num->real`; `hs:(A)rfs_history`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. (dd:num->real) j <= d0` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dd:num->real) 0` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `dd:num->real` P3_SEQ_MONO) THEN ASM_SIMP_TAC[LE_0]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dseq:num->real) (SUC 0)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `dseq:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`; `SUC 0`]) THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. &0 <= t ==> p3_stepf dd t <= d11) /\ (!t. &0 <= t ==> p3_stepf dd t <= d1712)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3_stepf] THEN ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i ==> p3_step_closed (u:A->bool) (C,eps,hf,md,g0,A0) (rs,ks,dd) i`
  (LABEL_TAC "closed") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "seqs" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rsi:num->real` (X_CHOOSE_THEN `ksi:num->real`
      (X_CHOOSE_THEN `dsi:num->real` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC P3_UPGRADE THEN
    MAP_EVERY EXISTS_TAC [`rsi:num->real`; `ksi:num->real`; `dsi:num->real`;
                          `dseq:num->real`; `dfun:real->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i (h:(A)rfs_history).
      1 <= i /\ FR (p3_stepf dd) h /\
      p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h /\ p3_T i <= rfs_horizon h
      ==> ?h'. rfs_extends h h' /\ FR (p3_stepf dd) h' /\
               p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h' /\
               p3_T (SUC i) <= rfs_horizon h'`
  (LABEL_TAC "key") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `FR:(real->real)->(A)rfs_history->bool`; `C:real`;
       `eps:real`; `hf:real->real->real`;
       `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`;
       `ks:num->real`; `dd:num->real`; `i:num`; `d11:real`; `d1712:real`]
       P3_KEY_STEP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "flow" ACCEPT_TAC;
        USE_THEN "fr" ACCEPT_TAC;
        USE_THEN "surg" ACCEPT_TAC;
        USE_THEN "closed" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "q1712" ACCEPT_TAC;
        ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?h':(A)rfs_history.
          rfs_extends hs h' /\ FR (p3_stepf dd) h' /\
          p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) h' /\
          p3_T (SUC m) <= rfs_horizon h'`
  (LABEL_TAC "outer") THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `hs:(A)rfs_history` THEN
      ASM_REWRITE_TAC[RFS_EXTENDS_REFL; GSYM ONE];
      FIRST_X_ASSUM(X_CHOOSE_THEN `h1:(A)rfs_history` STRIP_ASSUME_TAC) THEN
      USE_THEN "key" (MP_TAC o SPECL [`SUC m`; `h1:(A)rfs_history`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `h2:(A)rfs_history` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `h2:(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RFS_EXTENDS_TRANS]];
    ALL_TAC] THEN
  X_GEN_TAC `Tb:real` THEN
  MP_TAC(SPEC `Tb:real` P3_T_EXISTS) THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  USE_THEN "outer" (X_CHOOSE_THEN `h':(A)rfs_history` STRIP_ASSUME_TAC o SPEC `m:num`) THEN
  EXISTS_TAC `h':(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `SUC m`] P3_T_MONO) THEN
  ANTS_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The extra invariant passes to extensions with the same events.          *)

let P3_EXTRA_EXTENDS_SAME = prove
 (`!dl (hs:(A+num#num#real^3)rfs_history) hs'.
        p3_extra dl hs /\ rfs_extends hs hs' /\ hs_count hs' = hs_count hs
        ==> p3_extra dl hs'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_extra; rfs_extends] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `hs_top (hs':(A+num#num#real^3)rfs_history) k = hs_top hs k`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]];
    SUBGOAL_THEN
     `hs_top (hs':(A+num#num#real^3)rfs_history) k = hs_top hs k /\
      hs_top hs' (k - 1) = hs_top hs (k - 1) /\
      hs_time hs' k = hs_time hs k /\ hs_event hs' k = hs_event hs k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `k - 1 <= k`; LE_TRANS]; ASM_SIMP_TAC[]]]);;

(* MT Thm 15.9 on the history carrier with the extra invariant:             *)
(* the instance FR = p3_extra of the generic assembly.                       *)

let P3_THM_15_9_FROM_PARTS = prove
 (`!u:A->bool.
     P3_PROP_16_1_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_17_1_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_15_11_STATEMENT u /\
     P3_FLOW_EXTENSION_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_17_12_STATEMENT u
     ==> P3_THM_15_9_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_LEMMA_15_11_STATEMENT; P3_LEMMA_17_12_STATEMENT;
              P3_THM_15_9_STATEMENT] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`(:A+num#num#real^3)`;
                       `p3_extra:(real->real)->(A+num#num#real^3)rfs_history->bool`]
    P3_THM_15_9_FROM_PARTS_FR) THEN
  ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC P3_EXTRA_EXTENDS_SAME);;

(* ------------------------------------------------------------------------- *)
(* D1. The invariant implies rfs_controlled; the existence part of         *)
(* RFS_EXTINCTION_STATEMENT.                                               *)
(* ------------------------------------------------------------------------- *)

let P3_INV_CONTROLLED = prove
 (`!C eps hf md gst ast rs ks dd (hs:(A)rfs_history).
        p3_hfun C hf /\ p3_inv (C,eps,hf,md,gst,ast) (rs,ks,dd) hs
        ==> rfs_controlled (C,eps)
              (p3_stepf rs,p3_stepf dd,p3_stepf ks,
               p3_hscale hf (p3_stepf rs) (p3_stepf dd)) hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_inv; p3_struct; rfs_controlled; rfs_params] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < p3_stepf rs t /\ &0 < p3_stepf dd t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P3_STEPF_POS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[p3_hfun]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p3_stepf dd t * p3_stepf rs t`; `p3_stepf dd t`] o
      check (fun th -> can (find_term ((=) `hf:real->real->real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; p3_hscale] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN
    MATCH_MP_TAC P3_STEPF_MONO THEN ASM_REWRITE_TAC[]]);;

let RFS_EXTINCTION_FROM_P3 = prove
 (`!u:A->bool.
        P3_THM_15_9_STATEMENT u /\ P3_START_STATEMENT u /\
        P4_EXTINCTION_STATEMENT u /\ P2_NORMALIZE_STATEMENT u /\
        SMT_ORIENTABLE_STATEMENT u (:3)
        ==> RFS_EXTINCTION_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_THM_15_9_STATEMENT; P3_START_STATEMENT; RFS_EXTINCTION_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "thm")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `kappa0:real` (X_CHOOSE_THEN `eps2:real` (X_CHOOSE_THEN `b0:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "start")))))))
      (CONJUNCTS_THEN2 (LABEL_TAC "p4")
         (CONJUNCTS_THEN2 (LABEL_TAC "norm") (LABEL_TAC "orient"))))) THEN
  X_GEN_TAC `eps0:real` THEN DISCH_TAC THEN
  ABBREV_TAC `eps = min eps0 (min eps1 eps2)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps0 /\ eps <= eps1 /\ eps <= eps2` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "thm" (MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `hf:real->real->real`
    (X_CHOOSE_THEN `md:real->real` (X_CHOOSE_THEN `gst:real^3->real^3^3`
      (X_CHOOSE_THEN `ast:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `kappa0:real`)))))))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:num->real` (X_CHOOSE_THEN `ks:num->real`
    (X_CHOOSE_THEN `ds:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))))))))) THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `dl0:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `dd = \j. min dl0 ((ds:num->real) j)` THEN
  SUBGOAL_THEN `p3_seq_ok dd /\ (!j. dd j <= (ds:num->real) j) /\
                (!t. p3_stepf dd t <= dl0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[p3_seq_ok]) THEN
    REWRITE_TAC[p3_seq_ok; p3_stepf] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
          check (fun th -> can (find_term ((=) `ds:num->real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_orientable (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [USE_THEN "orient" (MP_TAC o REWRITE_RULE[SMT_ORIENTABLE_STATEMENT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "norm" (MP_TAC o SPECL [`top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] o
    REWRITE_RULE[P2_NORMALIZE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric atlas (\x:A. q %% (g:A->real^3^3) x)` ASSUME_TAC
  THENL [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "start" (MP_TAC o SPECL
   [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `gst:real^3->real^3^3`; `ast:real`; `rs:num->real`; `ks:num->real`;
    `dd:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `\x:A. q %% (g:A->real^3^3) x`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hs0:(A+num#num#real^3)rfs_history`
    (X_CHOOSE_THEN `iota:A->A+num#num#real^3`
      (X_CHOOSE_THEN `iota':A+num#num#real^3->A` STRIP_ASSUME_TAC))) THEN
  USE_THEN "p4" (MP_TAC o SPECL [`top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `\x:A. q %% (g:A->real^3^3) x`] o
    REWRITE_RULE[P4_EXTINCTION_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Text:real` (LABEL_TAC "text")) THEN
  REMOVE_THEN "ext" (MP_TAC o SPECL [`dd:num->real`; `hs0:(A+num#num#real^3)rfs_history`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `Text + &1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `hs:(A+num#num#real^3)rfs_history` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`hs:(A+num#num#real^3)rfs_history`; `p3_stepf rs`; `p3_stepf dd`;
    `p3_stepf ks`; `p3_hscale hf (p3_stepf rs) (p3_stepf dd)`; `q:real`;
    `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_history_ok (hs0:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_inv (C,eps,hf,md,gst,ast) (rs,ks,dd)
                   (hs0:(A+num#num#real^3)rfs_history)` THEN
    REWRITE_TAC[p3_inv; p3_struct] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs0:(A+num#num#real^3)rfs_history`;
                 `hs:(A+num#num#real^3)rfs_history`] RFS_EXTENDS_INITIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3_INV_CONTROLLED THEN
    MAP_EVERY EXISTS_TAC [`md:real->real`; `gst:real^3->real^3^3`; `ast:real`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `rfs_initial (top,atlas) (\x:A. q %% (g:A->real^3^3) x)
                   (hs0:(A+num#num#real^3)rfs_history) iota iota'` THEN
    ASM_REWRITE_TAC[rfs_initial];
    UNDISCH_TAC `p3_inv (C,eps,hf,md,gst,ast) (rs,ks,dd)
                   (hs:(A+num#num#real^3)rfs_history)` THEN
    REWRITE_TAC[p3_inv; p3_struct] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "text" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `gst:real^3->real^3^3`; `ast:real`; `rs:num->real`; `ks:num->real`;
      `dd:num->real`; `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_initial (top,atlas) (\x:A. q %% (g:A->real^3^3) x)
                     (hs0:(A+num#num#real^3)rfs_history) iota iota'` THEN
      ASM_REWRITE_TAC[rfs_initial];
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* D3. The combination: RFS_EXTINCTION_STATEMENT from the core Part 3      *)
(* statements, the Part 4 interface and the inputs.                        *)
(* ------------------------------------------------------------------------- *)

let P3_RFS_EXTINCTION = prove
 (`!u:A->bool.
        P3_PROP_16_1_STATEMENT (:A+num#num#real^3) /\
        P3_PROP_17_1_STATEMENT (:A+num#num#real^3) /\
        P3_LEMMA_15_11_STATEMENT u /\
        P3_FLOW_EXTENSION_STATEMENT (:A+num#num#real^3) /\
        P3_LEMMA_17_12_STATEMENT u /\
        P3_START_STATEMENT u /\ P4_EXTINCTION_STATEMENT u /\
        P2_NORMALIZE_STATEMENT u /\ SMT_ORIENTABLE_STATEMENT u (:3)
        ==> RFS_EXTINCTION_STATEMENT u`,
  MESON_TAC[P3_THM_15_9_FROM_PARTS; RFS_EXTINCTION_FROM_P3]);;

