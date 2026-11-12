(* ========================================================================= *)
(* Unit pc_p3_s16lim (Part 3 proofs; Ch 16, fourth unit of Prop 16.5): the   *)
(* setting of MT Lemma 16.8.  Saturation of goodness over subsequences       *)
(* (P3N_SATURATE), limits of the rescaled caps as partial standard flows     *)
(* (P3N_LIMIT_STEP), curvature on windows (Lemma 11.2, P3N_WINDOW_CURV), the *)
(* contradiction sequence p3n_seq with the cutoff tc, the persistence of big *)
(* balls through events (P3N_BIG_PERSIST, from Claim 16.10), and the window  *)
(* lemma for the rescaled coordinate flows (P3N_WINDOW).                     *)
(*                                                                           *)
(* First saturation, limits and windows; then the contradiction sequence,    *)
(* persistence and window closeness.                                         *)
(* ========================================================================= *)

needs "src/pc_p3_s16end.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Saturation over subsequences.  For a property good s b of                 *)
(* index sequences s and levels b (inherited by eventual subsequences and   *)
(* downward closed in b), some subsequence k of any s0 reaches a level L    *)
(* (good below L) that no further subsequence improves (P3N_SATURATE), by  *)
(* the diagonal argument SUBSEQUENCE_DIAGONALIZATION_LEMMA.                 *)
(* ========================================================================= *)

let p3n_esub = new_definition
 `p3n_esub (s':num->num) (s:num->num) <=>
    ?N0. !j. N0 <= j ==> ?j'. j <= j' /\ s' j = s j'`;;

let p3n_tsup = new_definition
 `p3n_tsup (good:(num->num)->real->bool) th (s:num->num) =
    sup ({&0} UNION {b | &0 <= b /\ b <= th /\ good s b})`;;

let p3n_tsup2 = new_definition
 `p3n_tsup2 (good:(num->num)->real->bool) th (s:num->num) =
    sup {p3n_tsup good th s' | p3n_esub s' s}`;;

let P3N_ESUB_REFL = prove
 (`!s. p3n_esub s s`,
  REWRITE_TAC[p3n_esub] THEN MESON_TAC[LE_REFL]);;

let P3N_ESUB_TRANS = prove
 (`!s1 s2 s3. p3n_esub s1 s2 /\ p3n_esub s2 s3 ==> p3n_esub s1 s3`,
  REWRITE_TAC[p3n_esub] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `N1:num`) (X_CHOOSE_TAC `N2:num`)) THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j1:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j2:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let P3N_ESUB_O = prove
 (`!r k. (!m n. m < n ==> k m < k n) ==> p3n_esub (r o k) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3n_esub; o_THM] THEN EXISTS_TAC `0` THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXISTS_TAC `(k:num->num) j` THEN
  REWRITE_TAC[] THEN MP_TAC(ISPEC `k:num->num` MONOTONE_BIGGER) THEN ASM_SIMP_TAC[]);;

let P3N_ESUB_SUBSEQ = prove
 (`!r s:num->num.
     p3n_esub s r
     ==> ?k. (!m n. m < n ==> k m < k n) /\ p3n_esub (r o k) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_esub] THEN DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  SUBGOAL_THEN `?pk:num->num. !j. N0 <= j ==> j <= pk j /\ (s:num->num) j = (r:num->num) (pk j)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `N0 <= j` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(pk:num->num) N0`; `\x j. (pk:num->num) (MAX (SUC j + N0) (x + 1))`]
                num_RECURSION) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num->num` THEN
  SUBGOAL_THEN `!j. ?j'. j <= j' /\ N0 <= j' /\ (k:num->num) j = pk j'` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `N0:num` THEN ASM_REWRITE_TAC[LE_0; LE_REFL];
      EXISTS_TAC `MAX (SUC j + N0) ((k:num->num) j + 1)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `a = MAX (SUC j + N0) ((k:num->num) j + 1)` THEN
    SUBGOAL_THEN `N0 <= a /\ (k:num->num) j + 1 <= a` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th ->
      can (find_term (fun t -> t = `pk:num->num`)) (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `k:num->num`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> t = `k:num->num`)) (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> t = `pk:num->num`)) (concl th))) THEN
    EXISTS_TAC `j':num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j':num` o check (fun th ->
      can (find_term (fun t -> t = `pk:num->num`)) (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `k:num->num`)) (concl th)))) THEN
    ASM_SIMP_TAC[]]);;

let P3N_TSUP_FACTS = prove
 (`!(good:(num->num)->real->bool) th s.
     &0 <= th
     ==> &0 <= p3n_tsup good th s /\ p3n_tsup good th s <= th /\
         (!b. &0 <= b /\ b <= th /\ good s b ==> b <= p3n_tsup good th s) /\
         ((!b b'. good s b /\ b' <= b ==> good s b')
          ==> !b. &0 <= b /\ b < p3n_tsup good th s ==> good s b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p3n_tsup] THEN
  ABBREV_TAC `S = {&0} UNION {b | &0 <= b /\ b <= th /\ (good:(num->num)->real->bool) s b}` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (&0) IN S /\ (!x. x IN S ==> x <= th) /\
                (!b. &0 <= b /\ b <= th /\ (good:(num->num)->real->bool) s b ==> b IN S) /\
                (!x. x IN S ==> x = &0 \/ good s x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_UNION; IN_SING; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[IN_UNION; IN_SING];
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b. !x. x IN S ==> x <= b` ASSUME_TAC THENL
   [EXISTS_TAC `th:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `b:real`] SUP_APPROACH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      can (find_term (fun t -> t = `good:(num->num)->real->bool`)) (concl th) &&
      can (find_term (fun t -> t = `\/`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `b < x` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let P3N_TSUP_MONO = prove
 (`!(good:(num->num)->real->bool) th s s'.
     &0 <= th /\ (!s s' b. good s b /\ p3n_esub s' s ==> good s' b) /\ p3n_esub s' s
     ==> p3n_tsup good th s <= p3n_tsup good th s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3n_tsup] THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[IN_UNION; IN_SING];
    REWRITE_TAC[SUBSET; IN_UNION; IN_SING; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    EXISTS_TAC `th:real` THEN REWRITE_TAC[IN_UNION; IN_SING; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3N_TSUP2_FACTS = prove
 (`!(good:(num->num)->real->bool) th.
     &0 <= th /\ (!s s' b. good s b /\ p3n_esub s' s ==> good s' b)
     ==> (!s. p3n_tsup good th s <= p3n_tsup2 good th s /\ p3n_tsup2 good th s <= th) /\
         (!s s'. p3n_esub s' s ==> p3n_tsup good th s' <= p3n_tsup2 good th s) /\
         (!s s'. p3n_esub s' s ==> p3n_tsup2 good th s' <= p3n_tsup2 good th s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. ~({p3n_tsup (good:(num->num)->real->bool) th s' | p3n_esub s' s} = {}) /\
                    (?b. !x. x IN {p3n_tsup good th s' | p3n_esub s' s} ==> x <= b) /\
                    (!x. x IN {p3n_tsup good th s' | p3n_esub s' s} ==> x <= th)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`p3n_tsup (good:(num->num)->real->bool) th s`; `s:num->num`] THEN
      REWRITE_TAC[P3N_ESUB_REFL];
      EXISTS_TAC `th:real` THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`good:(num->num)->real->bool`; `th:real`; `s':num->num`] P3N_TSUP_FACTS) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`good:(num->num)->real->bool`; `th:real`; `s':num->num`] P3N_TSUP_FACTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. p3n_esub s' s
                       ==> p3n_tsup (good:(num->num)->real->bool) th s' <= p3n_tsup2 good th s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p3n_tsup2] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P3N_ESUB_REFL];
      REWRITE_TAC[p3n_tsup2] THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_MESON_TAC[]];
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [p3n_tsup2] THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s'':num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC P3N_ESUB_TRANS THEN
    EXISTS_TAC `s':num->num` THEN ASM_REWRITE_TAC[]]);;

let P3N_SATURATE = prove
 (`!(good:(num->num)->real->bool) th.
     &0 <= th /\ (!s s' b. good s b /\ p3n_esub s' s ==> good s' b) /\
     (!s b b'. good s b /\ b' <= b ==> good s b')
     ==> !s0:num->num. ?k:num->num L. (!m n:num. m < n ==> k m < k n) /\ &0 <= L /\ L <= th /\
                    (!b. &0 <= b /\ b < L ==> good (s0 o k) b) /\
                    (!s' b. p3n_esub s' (s0 o k) /\ &0 <= b /\ b <= th /\ good s' b
                            ==> b <= L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s0:num->num` THEN
  MP_TAC(ISPECL [`good:(num->num)->real->bool`; `th:real`] P3N_TSUP2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\i (r:num->num). p3n_tsup2 (good:(num->num)->real->bool) th r - inv(&i + &1)
                                 <= p3n_tsup good th r`
         SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN
      MP_TAC(ISPECL [`{p3n_tsup (good:(num->num)->real->bool) th s' | p3n_esub s' r}`;
                     `p3n_tsup2 (good:(num->num)->real->bool) th r - inv(&i + &1)`]
                    SUP_APPROACH) THEN
      REWRITE_TAC[GSYM p3n_tsup2] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
          MAP_EVERY EXISTS_TAC [`p3n_tsup (good:(num->num)->real->bool) th r`; `r:num->num`] THEN
          REWRITE_TAC[P3N_ESUB_REFL];
          EXISTS_TAC `th:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `p3n_tsup2 (good:(num->num)->real->bool) th r` THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC(REAL_ARITH `&0 < e ==> x - e < x`) THEN
          REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[EXISTS_IN_GSPEC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':num->num` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`r:num->num`; `s':num->num`] P3N_ESUB_SUBSEQ) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:num->num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `p3n_tsup (good:(num->num)->real->bool) th s' <= p3n_tsup good th ((r:num->num) o (k:num->num))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC P3N_TSUP_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p3n_tsup2 (good:(num->num)->real->bool) th ((r:num->num) o (k:num->num)) <= p3n_tsup2 good th r`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC P3N_ESUB_O THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `N:num`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `p3n_esub ((r:num->num) o (k2:num->num)) ((r:num->num) o (k1:num->num))` ASSUME_TAC THENL
       [REWRITE_TAC[p3n_esub; o_THM] THEN EXISTS_TAC `N:num` THEN X_GEN_TAC `j:num` THEN
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
          can (find_term (fun t -> t = `k2:num->num`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `p3n_tsup (good:(num->num)->real->bool) th ((r:num->num) o (k1:num->num)) <=
                    p3n_tsup good th ((r:num->num) o (k2:num->num))` ASSUME_TAC THENL
       [MATCH_MP_TAC P3N_TSUP_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p3n_tsup2 (good:(num->num)->real->bool) th ((r:num->num) o (k2:num->num)) <=
                    p3n_tsup2 good th ((r:num->num) o (k1:num->num))` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:num->num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num->num` THEN
  EXISTS_TAC `p3n_tsup (good:(num->num)->real->bool) th ((s0:num->num) o (k:num->num))` THEN
  MP_TAC(ISPECL [`good:(num->num)->real->bool`; `th:real`; `(s0:num->num) o (k:num->num)`]
                P3N_TSUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `p3n_tsup2 (good:(num->num)->real->bool) th ((s0:num->num) o (k:num->num)) <=
                p3n_tsup good th ((s0:num->num) o (k:num->num))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `p3n_tsup2 (good:(num->num)->real->bool) th ((s0:num->num) o (k:num->num)) -
                 p3n_tsup good th ((s0:num->num) o (k:num->num))` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "real_inv")) (concl th))) THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD;
        REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p3n_tsup (good:(num->num)->real->bool) th s'` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`good:(num->num)->real->bool`; `th:real`; `s':num->num`] P3N_TSUP_FACTS) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3n_tsup2 (good:(num->num)->real->bool) th ((s0:num->num) o (k:num->num))` THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Comparable metrics have comparable distances                              *)
(* (P3N_DIST_COMPARE, from MFD_LENGTH_METRIC_COMPARE) and the same          *)
(* completeness (P3N_COMPLETE_COMPARE: closed balls of g' sit in larger     *)
(* closed balls of g).                                                       *)
(* ========================================================================= *)

let P3N_DIST_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' c x y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g' /\ &0 < c /\
     (!z v. z IN topspace top ==> v dot (g' z ** v) <= c * (v dot (g z ** v))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g' x y <= sqrt c * mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[mfd_joinable];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN X_GEN_TAC `L:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g':A->real^N^N) gamma (&0) (&1)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g':A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_LENGTH_METRIC_COMPARE THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                     (gamma:real->A) (&0) (&1)` THEN
      REWRITE_TAC[mfd_c1_curve; continuous_map; TOPSPACE_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]]]);;

let P3N_COMPLETE_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g' /\ &0 < c /\
     (!z v. z IN topspace top ==> v dot (g z ** v) <= c * (v dot (g' z ** v))) /\
     mfd_complete (top,atlas) g
     ==> mfd_complete (top,atlas) g'`,
  REWRITE_TAC[mfd_complete] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x (sqrt c * r)` THEN
  ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt c * mfd_dist (top,atlas) (g':A->real^N^N) x y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3N_DIST_COMPARE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]]);;

(* ========================================================================= *)
(* A limit flow on R^3 from g0 with bounded curvature on each                *)
(* [0,t1] is a partial standard flow (P3N_LIMIT_PSTD): the flow-from pieces *)
(* glue (PDE_RFF_UNION) and each slice is complete because it is            *)
(* exp-comparable to g0 (RFA_LMETRIC_EQUIV0 with Ric <= 2 |Rm| g,          *)
(* P3N_COMPLETE_COMPARE).                                                    *)
(* ========================================================================= *)

let P3N_RFF_LFROM = prove
 (`!b (g:real->real^3->real^3^3).
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b g
     ==> rfa_lfrom (:real^3) (&0) b g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((:real^3),(\x:real^3. x)) IN open_set_atlas (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES]; ALL_TAC] THEN
  REWRITE_TAC[rfa_lfrom] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `b:real`;
                   `g:real->real^3->real^3^3`; `((:real^3),(\x:real^3. x))`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
    REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; IMAGE_ID; ETA_AX];
    UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b
                   (g:real->real^3->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `((:real^3),(\x:real^3. x))` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; IMAGE_ID];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b
                   (g:real->real^3->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from] THEN
    DISCH_THEN(MP_TAC o SPEC `((:real^3),(\x:real^3. x))` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; IMAGE_ID] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
      `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `e:real`;
                          `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_REFL; REAL_SUB_LZERO] THEN
    ASM_MESON_TAC[IN_UNIV]]);;

let P3N_LIMIT_PSTD = prove
 (`!g0 A0 L (g:real->real^3->real^3^3).
     p3_std_initial g0 A0 /\ &0 < L /\ g (&0) = g0 /\
     (!b. &0 < b /\ b < L
          ==> ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b g) /\
     (!t1. t1 < L
           ==> ?K. !t x. &0 <= t /\ t <= t1
                         ==> mfd_rm_norm (open_set_atlas (:real^3)) (g t) x <= K)
     ==> p3_partial_std g0 L g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_partial_std] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_RFF_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ABBREV_TAC `b = (t + L) / &2` THEN
  SUBGOAL_THEN `&0 < b /\ t < b /\ b < L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b
                  (g:real->real^3->real^3^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  ABBREV_TAC `Kr = &2 * abs K` THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < b
                    ==> riemannian_metric (open_set_atlas (:real^3)) ((g:real->real^3->real^3^3) s)`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `b:real`;
                   `g:real->real^3->real^3^3`; `s:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y v. exp(--(&2 * Kr * (t - &0))) * (v dot ((g:real->real^3->real^3^3) (&0) y ** v)) <=
          v dot (g t y ** v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `&0`; `b:real`; `g:real->real^3->real^3^3`; `y:real^3`;
                   `t:real`; `Kr:real`] RFA_LMETRIC_EQUIV0) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P3N_RFF_LFROM; IN_UNIV] THEN
      CONJ_TAC THENL [EXPAND_TAC "Kr" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `w:real^3`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `(g:real->real^3->real^3^3) s`; `y:real^3`; `w:real^3`]
                    P2AP_MFD_RICCI_ABS) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[P3N_EUCL_ATLAS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
        USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[RFB_OPEN_SET_MFD_RICCI; OPEN_UNIV; IN_UNIV; DIMINDEX_3] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(REAL_ARITH `&2 * c <= b ==> x <= &2 * c ==> x <= b`) THEN
      SUBGOAL_THEN `&0 <= w dot ((g:real->real^3->real^3^3) s y ** w)` ASSUME_TAC THENL
       [MATCH_MP_TAC RFA_METRIC_QPOS THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[IN_UNIV] THEN
        USE_THEN "rm" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[riemannian_metric; RFB_OPEN_SET_ATLAS_CASES] THEN
        DISCH_THEN(MP_TAC o SPEC `((:real^3),(\x:real^3. x))`) THEN
        REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; IMAGE_ID];
        ALL_TAC] THEN
      SUBGOAL_THEN `mfd_rm_norm (open_set_atlas (:real^3)) ((g:real->real^3->real^3^3) s) y *
                    (w dot (g s y ** w)) <= abs K * (w dot (g s y ** w))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= abs K`) THEN
        USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "Kr" THEN REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P3N_COMPLETE_COMPARE THEN
  MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `exp(&2 * Kr * t)`] THEN
  REWRITE_TAC[P3N_EUCL_ATLAS; REAL_EXP_POS_LT; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[p3_std_initial];
    USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * Kr * t) * exp(--(&2 * Kr * t)) *
                (v dot ((g0:real^3->real^3^3) y ** v))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                  REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[])];
    ASM_MESON_TAC[p3_std_initial]]);;

(* ========================================================================= *)
(* Curvature bounds pass to C^2 limits (P3N_SEC_LIMIT, by                    *)
(* LCK_CURVATURE_STABILITY at the point with the limit's own curvature), and *)
(* the rescaled pullback of a slice by a parametrisation has sectional       *)
(* curvatures bounded by the rescaled curvature norm (P3N_PULLBACK_SEC_LE). *)
(* ========================================================================= *)

let P3N_SEC_LIMIT = prove
 (`!U (G0:real^N->real^N^N) y K.
     metric_field U G0 /\ y IN U /\
     (!eta. &0 < eta
            ==> ?H. metric_field U H /\ lck_dist2 2 G0 H y < eta pow 2 /\
                    !u v. ~collinear {vec 0,u,v} ==> abs(lsectional H y u v) <= K)
     ==> !u v. ~collinear {vec 0,u,v} ==> abs(lsectional G0 y u v) <= K`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_LE_EPS THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sqrt(lrm_deriv_norm2 0 (G0:real^N->real^N^N) y)`; `a:real`]
                LCK_CURVATURE_STABILITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^N->real^N^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "st" (MP_TAC o SPECL [`U:real^N->bool`; `G0:real^N->real^N^N`;
                                 `H:real^N->real^N^N`; `y:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] RFA_RMD_POS) THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let P3N_PULLBACK_SEC_LE = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) Q y u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s /\ &0 < Q /\ ~collinear {vec 0,u,v}
     ==> abs(lsectional (\z. Q %% rfs_pullback atlas e g z) y u v) <=
         mfd_rm_norm atlas g (e y) / Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `rfs_pullback atlas (e:real^3->A) g`; `Q:real`; `y:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < Q ==> abs Q = Q`; REAL_LE_DIV2_EQ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`; `u:real^3`; `v:real^3`]
                APX_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`] APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`N:real^3->bool`; `N':real^3->bool`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e`;
                 `h':real^3->real^3`] P2AP_DIFFEO_DERIV_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e)
                    (at y)` THEN
  SUBGOAL_THEN `(D:real^3->real^3) (vec 0) = vec 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
  UNDISCH_TAC `~collinear {vec 0,u:real^3,v}` THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th -> is_forall(concl th) &&
      not (can (find_term (fun t -> t = `D:real^3->real^3`)) (concl th)))) THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LINEAR_CMUL]]);;

(* ========================================================================= *)
(* Events and persistence.  A set open before an event, kept                 *)
(* by it and missing the cut spheres is open after it (P3N_EVENT_KEEP).     *)
(* If an open set of a stage persists up to tt (exclusive) but not beyond,  *)
(* then tt is an event time at which the set is not kept                    *)
(* (P3N_FIRST_FAILURE).                                                      *)
(* ========================================================================= *)

let P3N_EVENT_KEEP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev W.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     smooth_manifold_atlas topX atlasX /\ open_in topX W /\
     DISJOINT W (mfd_cut_spheres (ev_index ev) (ev_neck ev)) /\ W SUBSET topspace topY
     ==> open_in topY W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                 `ev_index (ev:(A)rfs_event)`; `ev_neck (ev:(A)rfs_event)`;
                 `ev_capp (ev:(A)rfs_event)`; `ev_capm (ev:(A)rfs_event)`; `W:A->bool`]
                APX_CUT_SUBDIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC
     `DISJOINT (W:A->bool) (mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event)))` THEN
    SET_TAC[];
    STRIP_TAC] THEN
  UNDISCH_TAC `(W:A->bool) SUBSET topspace topY` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P3N_FIRST_FAILURE = prove
 (`!(hs:(A)rfs_history) k W tt.
     rfs_history_ok hs /\ k <= hs_count hs /\ open_in (hs_top hs k) W /\
     hs_time hs k < tt /\ tt < rfs_horizon hs /\
     (!t. hs_time hs k < t /\ t < tt ==> rfs_persists (rfs_view hs) W (hs_time hs k) t) /\
     ~(?d. &0 < d /\ rfs_persists (rfs_view hs) W (hs_time hs k) (tt + d))
     ==> ?j. k < j /\ j <= hs_count hs /\ hs_time hs j = tt /\
             open_in (hs_top hs (j - 1)) W /\
             ~(W SUBSET topspace (hs_top hs j) /\
               DISJOINT W (mfd_cut_spheres (ev_index (hs_event hs j))
                                           (ev_neck (hs_event hs j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN SIMP_TAC[rfs_history_ok];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `j = rfs_slab (hs:(A)rfs_history) tt` THEN STRIP_TAC THEN
  SUBGOAL_THEN `k <= j:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `j + 1`; `k:num`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the persistence of W on the slab j from a time t0 >= max(t_j,..) *)
  SUBGOAL_THEN
   `open_in (hs_top (hs:(A)rfs_history) j) W
    ==> ?d. &0 < d /\ rfs_persists (rfs_view hs) W (hs_time hs k) (tt + d)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `(hs_time (hs:(A)rfs_history) (j + 1) - tt) / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < tt` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th))) THEN
      ASM_REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `j:num`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_space")) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `hs_time (hs:(A)rfs_history) j < tt` THENL
   [(* tt inside the slab: W is open in stage j *)
    UNDISCH_TAC `~(?d. &0 < d /\ rfs_persists (rfs_view (hs:(A)rfs_history)) (W:A->bool) (hs_time hs k) (tt + d))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ABBREV_TAC `t0 = (max (hs_time (hs:(A)rfs_history) j) (hs_time hs k) + tt) / &2` THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) j <= t0 /\ hs_time hs k < t0 /\ t0 < tt`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th))) THEN
    ASM_REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `j:num`; `t0:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) j = tt` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k < j:num` ASSUME_TAC THENL
   [REWRITE_TAC[LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= j /\ j - 1 <= hs_count (hs:(A)rfs_history) /\ j - 1 + 1 = j`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (j - 1)) W` ASSUME_TAC THENL
   [ABBREV_TAC `t0 = (max (hs_time (hs:(A)rfs_history) (j - 1)) (hs_time hs k) + tt) / &2` THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (j - 1) < tt` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - 1`; `j:num`] APX_HS_TIME_MONO) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (j - 1) <= t0 /\ hs_time hs k < t0 /\ t0 < tt`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th))) THEN
    ASM_REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - 1`; `t0:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(?d. &0 < d /\ rfs_persists (rfs_view (hs:(A)rfs_history)) (W:A->bool) (hs_time hs k) (tt + d))` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  MATCH_MP_TAC P3N_EVENT_KEEP THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (j - 1)`; `hs_atlas (hs:(A)rfs_history) (j - 1)`;
                        `hs_metric (hs:(A)rfs_history) (j - 1)`; `tt:real`;
                        `hs_atlas (hs:(A)rfs_history) j`; `hs_metric (hs:(A)rfs_history) j`;
                        `hs_event (hs:(A)rfs_history) j`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `j:num`] P3S_STAGE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The setting of Lemma 16.8.  For a history hs with cap                     *)
(* coordinates Phi at the event time ts and scale Q = h^-2: the rescaled    *)
(* coordinate flow p3n_cfl (normalized time s, real time ts + s / Q), the   *)
(* persistence time p3n_ptime of the core ball (capped at th), the          *)
(* goodness of level b for the ball of radius m + 1 with curvature constant *)
(* K (p3n_gat: persistence and abs Rm <= K Q while s <= b, s < T), and     *)
(* its sequence form p3n_good (uniform K, eventually in the index for each *)
(* m), which is inherited by eventual subsequences and downward closed.    *)
(* ========================================================================= *)

let p3n_cfl = new_definition
 `p3n_cfl (hs:(A)rfs_history) (Phi:real^3->A) ts Q s =
    \y. Q %% rfs_pullback (rfs_vatlas (rfs_view hs) (ts + s / Q)) Phi
                          (rfs_vmetric (rfs_view hs) (ts + s / Q)) y`;;

let p3n_ptime = new_definition
 `p3n_ptime (g0:real^3->real^3^3) (hs:(A)rfs_history) (Phi:real^3->A) ts Q mstar th =
    sup ({&0} UNION
         {s | &0 <= s /\ s <= th /\
              rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < mstar})
                           ts (ts + s / Q)})`;;

let p3n_gat = new_definition
 `p3n_gat (g0:real^3->real^3^3) (hs:(A)rfs_history) (Phi:real^3->A) ts Q tp K (m:num) b <=>
    !s. &0 <= s /\ s <= b /\ s < tp
        ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < &m + &1})
                         ts (ts + s / Q) /\
            !y. y IN IMAGE Phi {x | p3_std_dist g0 x < &m + &1}
                ==> p3_vrm (rfs_view hs) (ts + s / Q) y <= K * Q`;;

let p3n_good = new_definition
 `p3n_good (g0:real^3->real^3^3) (hs:num->(A)rfs_history) (Phi:num->real^3->A) ts Q Tf
           (s:num->num) b <=>
    ?K. !m. ?N. !j. N <= j
                    ==> p3n_gat g0 (hs (s j)) (Phi (s j)) (ts (s j)) (Q (s j)) (Tf (s j)) K m b`;;

let P3N_GOOD_INHERIT = prove
 (`!g0 (hs:num->(A)rfs_history) Phi ts Q Tf s s' b.
     p3n_good g0 hs Phi ts Q Tf s b /\ p3n_esub s' s ==> p3n_good g0 hs Phi ts Q Tf s' b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_good; p3n_esub] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `K:real` ASSUME_TAC) (X_CHOOSE_TAC `N0:num`)) THEN
  EXISTS_TAC `K:real` THEN X_GEN_TAC `m:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `m:num`) THEN
  EXISTS_TAC `MAX N0 N` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term (fun t -> t = `N0:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let P3N_GOOD_MONO = prove
 (`!g0 (hs:num->(A)rfs_history) Phi ts Q Tf s b b'.
     p3n_good g0 hs Phi ts Q Tf s b /\ b' <= b ==> p3n_good g0 hs Phi ts Q Tf s b'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_good; p3n_gat] THEN STRIP_TAC THEN
  EXISTS_TAC `K:real` THEN X_GEN_TAC `m:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `m:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real`) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let P3N_GOOD_SATURATE = prove
 (`!g0 (hs:num->(A)rfs_history) Phi ts Q Tf th (s0:num->num).
     &0 <= th
     ==> ?k:num->num L. (!m n:num. m < n ==> k m < k n) /\ &0 <= L /\ L <= th /\
               (!b. &0 <= b /\ b < L ==> p3n_good g0 hs Phi ts Q Tf (s0 o k) b) /\
               (!s' b. p3n_esub s' (s0 o k) /\ &0 <= b /\ b <= th /\
                       p3n_good g0 hs Phi ts Q Tf s' b ==> b <= L)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p3n_good (g0:real^3->real^3^3) (hs:num->(A)rfs_history) Phi ts Q Tf`;
                 `th:real`] P3N_SATURATE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[P3N_GOOD_INHERIT]; MESON_TAC[P3N_GOOD_MONO]];
    DISCH_THEN(MP_TAC o SPEC `s0:num->num`) THEN REWRITE_TAC[]]);;

(* ========================================================================= *)
(* From a limit flow on [0,L) with locally uniform curvature                 *)
(* bounds (passed from the approximants) to a standard flow agreeing with   *)
(* it on [0,L) (P3N_GSTAR: P3N_SEC_LIMIT, P3N_LIMIT_PSTD, P2_STD_EXTEND).   *)
(* ========================================================================= *)

let P3N_OSA_RIEM = prove
 (`!G:real^N->real^N^N.
     riemannian_metric (open_set_atlas (:real^N)) G ==> metric_field (:real^N) G`,
  GEN_TAC THEN REWRITE_TAC[riemannian_metric; RFB_OPEN_SET_ATLAS_CASES] THEN
  DISCH_THEN(MP_TAC o SPEC `((:real^N),(\x:real^N. x))`) THEN
  REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; IMAGE_ID]);;

let P3N_GSTAR = prove
 (`P2_STD_EXTEND_STATEMENT
   ==> !g0 A0 L (g:real->real^3->real^3^3).
         p3_std_initial g0 A0 /\ &0 < L /\ g (&0) = g0 /\
         (!b. &0 < b /\ b < L
              ==> ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) b g) /\
         (!t1. t1 < L
               ==> ?Kc. !s y. &0 <= s /\ s <= t1
                          ==> ?U. open U /\ y IN U /\
                                  !eta. &0 < eta
                                        ==> ?H. metric_field U H /\
                                                lck_dist2 2 (g s) H y < eta pow 2 /\
                                                !u v. ~collinear {vec 0,u,v}
                                                      ==> abs(lsectional H y u v) <= Kc)
         ==> ?G. p3_std_flow g0 (&1) G /\ (!t x. &0 <= t /\ t < L ==> G t x = g t x)`,
  REWRITE_TAC[P2_STD_EXTEND_STATEMENT] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_LIMIT_PSTD THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t1:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kc:real` (LABEL_TAC "kc")) THEN
  EXISTS_TAC `Kc:real` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (:real^3) ((g:real->real^3->real^3^3) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_OSA_RIEM THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`;
                   `(s + L) / &2`; `g:real->real^3->real^3^3`; `s:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  USE_THEN "kc" (MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(g:real->real^3->real^3^3) s`; `y:real^3`; `Kc:real`]
                P3N_SEC_LIMIT) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

(* ========================================================================= *)
(* A parametrisation of a slice stays a parametrisation of the               *)
(* later slices while its image persists (P3N_PARAM_LATER, regular-view     *)
(* conjunct 5 and APX_PARAM_TRANSFER).                                       *)
(* ========================================================================= *)

let P3N_PARAM_LATER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U (Phi:real^3->A) a b.
     p2c_regular_view V /\ smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     mfd_param (rfs_vtop V a) (rfs_vatlas V a) U Phi /\ open U /\
     a < b /\ rfs_persists V (IMAGE Phi U) a b
     ==> mfd_param (rfs_vtop V b) (rfs_vatlas V b) U Phi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) a) (IMAGE (Phi:real^3->A) U)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a`;
                          `U:real^3->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`IMAGE (Phi:real^3->A) U`; `a:real`; `b:real`] o last o
              CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas
                  (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b) (rfs_vatlas V b)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (IMAGE (Phi:real^3->A) U) a b` THEN
    REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIV:A->bool`; `UNIV:A->bool`] APX_PARAM_TRANSFER) THEN
  REWRITE_TAC[APX_PARAM_TRANSFER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) a`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) a`;
    `IMAGE (Phi:real^3->A) U`;
    `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b`;
    `IMAGE (Phi:real^3->A) U`; `\y:A. y`; `\y:A. y`; `U:real^3->bool`; `Phi:real^3->A`]) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* ========================================================================= *)
(* The limit step of Lemma 16.8 (P3N_LIMIT_STEP).  If the cap sequence is    *)
(* good below L > 0 along D (and its persistence times stay above every      *)
(* b < L), Prop 5.14 (P2C_PROP_5_14) gives a subsequence converging on [0,L) *)
(* to a flow g from g0; its curvature is locally bounded (P3N_SEC_LIMIT), so *)
(* it is a partial standard flow and extends to a standard flow              *)
(* G (P3N_GSTAR); the rescaled flows converge to G on compact subsets of     *)
(* [0,L).                                                                    *)
(* ========================================================================= *)

let P3N_GAT_FACTS = prove
 (`!g0 (hs:(A)rfs_history) Phi ts Q tp K m b s.
     p2c_regular_view (rfs_view hs) /\ &0 < Q /\
     smooth_manifold_atlas (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts) /\
     mfd_param (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts)
               {x | p3_std_dist g0 x < &m + &1} Phi /\
     open {x | p3_std_dist g0 x < &m + &1} /\ ~({x | p3_std_dist g0 x < &m + &1} = {}) /\
     p3n_gat g0 hs Phi ts Q tp K m b /\ &0 <= s /\ s <= b /\ s < tp
     ==> mfd_param (rfs_vtop (rfs_view hs) (ts + s / Q)) (rfs_vatlas (rfs_view hs) (ts + s / Q))
                   {x | p3_std_dist g0 x < &m + &1} Phi /\
         smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s / Q))
                               (rfs_vatlas (rfs_view hs) (ts + s / Q)) /\
         riemannian_metric (rfs_vatlas (rfs_view hs) (ts + s / Q))
                           (rfs_vmetric (rfs_view hs) (ts + s / Q)) /\
         metric_field {x | p3_std_dist g0 x < &m + &1} (p3n_cfl hs Phi ts Q s) /\
         (!y u v. y IN {x | p3_std_dist g0 x < &m + &1} /\ ~collinear {vec 0,u,v}
                  ==> abs(lsectional (p3n_cfl hs Phi ts Q s) y u v) <= K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Wm = {x | p3_std_dist g0 x < &m + &1}` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o REWRITE_RULE[p3n_gat]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q))
              (rfs_vatlas (rfs_view hs) (ts + s / Q)) Wm (Phi:real^3->A) /\
    smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s / Q))
                          (rfs_vatlas (rfs_view hs) (ts + s / Q))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
    SUBGOAL_THEN `ts < ts + s / Q` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> t < t + x`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3N_PARAM_LATER THEN EXISTS_TAC `ts:real` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE (Phi:real^3->A) Wm)
                     ts (ts + s / Q)` THEN
      REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(MP_TAC o SPEC `ts + s / Q`) THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas (rfs_view (hs:(A)rfs_history)) (ts + s / Q))
                                  (rfs_vmetric (rfs_view hs) (ts + s / Q))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~(Wm:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^3`) THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `ts + s / Q`; `(Phi:real^3->A) w`]
                  P2C_REGULAR_SLICE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                   `rfs_vatlas (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                   `Wm:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p3n_cfl] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[p3n_cfl] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (rfs_view (hs:(A)rfs_history)) (ts + s / Q) ((Phi:real^3->A) y) / Q` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[p3_vrm] THEN MATCH_MP_TAC P3N_PULLBACK_SEC_LE THEN
      MAP_EVERY EXISTS_TAC [`rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                            `Wm:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(Phi:real^3->A) y` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "p3_vrm")) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]]]);;

let P3N_SLICE_PARAM = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q g xl W phi.
     p2c_slice_limit_with V x t Q (euclidean,open_set_atlas (:real^3)) g xl W phi
     ==> !n. mfd_param (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) (W n) (phi n)`,
  REWRITE_TAC[p2c_slice_limit_with; mfd_param] THEN MESON_TAC[]);;

let P3N_OSA_CHART_INV = prove
 (`chart_inv ((:real^N),(\x:real^N. x)) = \x. x`,
  REWRITE_TAC[FUN_EQ_THM; chart_inv; IN_UNIV] THEN MESON_TAC[]);;

let P3N_FLOW_LIMIT_CL = prove
 (`!(hs:num->(A)rfs_history) x t Q J (g:real->real^3->real^3^3) xl W (phi:num->real^3->A).
     p2c_flow_limit_with (\n. rfs_view (hs n)) x t Q J (euclidean,open_set_atlas (:real^3))
                         g xl W phi
     ==> !a b K m e. real_interval[a,b] SUBSET J /\ compact K /\ &0 < e
           ==> ?k0. !k s y. k0 <= k /\ a <= s /\ s <= b /\ y IN K
                      ==> lck_dist2 m (g s) (p3n_cfl (hs k) (phi k) (t k) (Q k) s) y < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flow_limit_with; COMPACT_IN_EUCLIDEAN] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `K:real^3->bool`; `m:num`; `e:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  REWRITE_TAC[P3N_OSA_CHART_INV; p3n_cfl] THEN
  SUBGOAL_THEN `(phi:num->real^3->A) k o (\x:real^3. x) = phi k` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; SIMP_TAC[]]);;

let P3N_LIMIT_STEP = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT
     ==> !md g0 A0 (hs:num->(A)rfs_history) k i dl hh Phi xi ts Q Tf D L.
           p3_modulus md /\ p3_std_initial g0 A0 /\
           (!n. rfs_history_ok (hs n) /\ 1 <= k n /\ k n <= hs_count (hs n) /\
                hs_time (hs n) (k n) = ts n /\
                &0 < dl n (ts n) /\ dl n (ts n) <= inv(&n + &1) /\
                &0 < hh n (ts n) /\ inv(hh n (ts n) pow 2) = Q n /\
                p3_cap_param (md,g0,A0) (dl n,hh n) (hs n) (k n) (i n) (Phi n) (xi n)) /\
           (!m n. m < n ==> D m < D n) /\ &0 < L /\
           (!b. &0 <= b /\ b < L ==> p3n_good g0 hs Phi ts Q Tf D b) /\
           (!b. b < L ==> ?N. !j. N <= j ==> b < Tf (D j))
           ==> ?sub:num->num G. (!m n:num. m < n ==> sub m < sub n) /\ p3_std_flow g0 (&1) G /\
                 !a b K m e. &0 <= a /\ a <= b /\ b < L /\ compact K /\ &0 < e
                   ==> ?N. !j:num s y. N <= j /\ a <= s /\ s <= b /\ y IN K
                              ==> lck_dist2 m (G s)
                                    (p3n_cfl (hs (D (sub j))) (Phi (D (sub j)))
                                             (ts (D (sub j))) (Q (D (sub j))) s) y < e`,
  GEN_TAC THEN REWRITE_TAC[P2C_PROP_5_14_STATEMENT; P2C_HISTORY_REGULAR_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "514") (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (LABEL_TAC "ext"))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "good") (LABEL_TAC "tf"))))))) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. hs_time ((hs:num->(A)rfs_history) n) ((k:num->num) n) = (ts:num->real) n /\
                    inv((hh:num->real->real) n (ts n) pow 2) = (Q:num->real) n`
  (LABEL_TAC "eqs") THENL [USE_THEN "H" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (Q:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "eqs" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
    USE_THEN "H" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the time-0 slice limit along D *)
  SUBGOAL_THEN
   `p2c_slice_limit_with (\n. rfs_view ((hs:num->(A)rfs_history) (D n)))
      (\n. (Phi:num->real^3->A) (D n) (vec 0)) (\n. (ts:num->real) (D n)) (\n. (Q:num->real) (D n))
      (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
      (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (D n))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
                   `\n. (hs:num->(A)rfs_history) ((D:num->num) n)`; `\n. (k:num->num) ((D:num->num) n)`;
                   `\n. (i:num->num) ((D:num->num) n)`; `\n. (dl:num->real->real) ((D:num->num) n)`;
                   `\n. (hh:num->real->real) ((D:num->num) n)`; `\n. (Phi:num->real^3->A) ((D:num->num) n)`;
                   `\n. (xi:num->real^3->real^3) ((D:num->num) n)`] P3N_SLICE0) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
      USE_THEN "H" (MP_TAC o SPEC `(D:num->num) n`) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&((D:num->num) n) + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `D:num->num`)) (concl th) &&
        not (can (find_term (fun t -> t = `m:num`)) (concl th)))) THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "eqs" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "514" (MP_TAC o ISPECL
   [`\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n))`;
    `\n. (Phi:num->real^3->A) ((D:num->num) n) (vec 0)`;
    `\n. (ts:num->real) ((D:num->num) n)`; `\n. (Q:num->real) ((D:num->num) n)`;
    `{s:real | &0 <= s /\ s < L}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
    `g0:real^3->real^3^3`; `vec 0:real^3`; `\m. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
    `\n. (Phi:num->real^3->A) ((D:num->num) n)`]) THEN
  ANTS_TAC THENL
  [(ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN BETA_TAC THEN USE_THEN "reg" MATCH_MP_TAC THEN
  USE_THEN "H" (fun th -> REWRITE_TAC[th]);
    MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b < a` THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[P2C_VIEW_EXPAND] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    (SUBGOAL_THEN `a / (Q:num->real) ((D:num->num) n) < b / Q (D n)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ b < L` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET {s:real | &0 <= s /\ s < L}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `a:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o SPEC `(b + L) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3n_good] THEN DISCH_THEN(X_CHOOSE_THEN `K:real` (MP_TAC o SPEC `m:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "tf" (MP_TAC o SPEC `(b + L) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `N1 + N2 + m:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3n_gat] THEN DISCH_THEN(LABEL_TAC "gat") THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP P3N_SLICE_PARAM) THEN
      BETA_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(hs:num->(A)rfs_history) ((D:num->num) n)`; `(k:num->num) ((D:num->num) n)`]
                    P3N_VIEW_AT_EVENT) THEN
      ANTS_TAC THENL [USE_THEN "H" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      USE_THEN "eqs" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n)))
                                ((ts:num->real) (D n))`;
                     `rfs_vatlas (rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n)))
                                ((ts:num->real) (D n))`;
                     `{x:real^3 | p3_std_dist g0 x < &n + &1}`;
                     `(Phi:num->real^3->A) ((D:num->num) n)`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((Phi:num->real^3->A) ((D:num->num) n)) {x:real^3 | p3_std_dist g0 x < &n + &1}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
      REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      USE_THEN "gat" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
      DISCH_THEN(MP_TAC o SPEC `ts ((D:num->num) n) + s / (Q:num->real) (D n)`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_REFL; REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MESON_TAC[OPEN_IN_SUBSET]]];
    USE_THEN "gat" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= a / (Q:num->real) ((D:num->num) n)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "gat" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p3_subseq; o_DEF]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P3N_FLOW_LIMIT_CL o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_flow_limit_with")) (concl th))) THEN
  DISCH_THEN(LABEL_TAC "CL") THEN
  REMOVE_THEN "CL" (LABEL_TAC "CL" o BETA_RULE) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ext" (MP_TAC o MATCH_MP P3N_GSTAR) THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `L:real`;
                             `g:real->real^3->real^3^3`]) THEN
  ANTS_TAC THENL
  [(ASM_REWRITE_TAC[] THEN CONJ_TAC) THENL
   [X_GEN_TAC `b:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_from")) (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
    ABBREV_TAC `b2 = (max t1 (&0) + L) / &2` THEN
    SUBGOAL_THEN `&0 <= b2 /\ t1 < b2 /\ b2 < L` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "b2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o SPEC `b2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[p3n_good]] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "gk")) THEN
  USE_THEN "tf" (MP_TAC o SPEC `b2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `K:real` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `p3_std_dist g0 (y:real^3)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < &m + &1}` THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3N_STD_WBALLS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num` o CONJUNCT1) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "CL" (MP_TAC o SPECL [`s:real`; `s:real`; `{y:real^3}`; `2`; `eta pow 2`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_SING; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_POW_LT]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    USE_THEN "gk" (MP_TAC o SPEC `m:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
    ABBREV_TAC `j = k0 + N1 + N2 + m:num` THEN
    EXISTS_TAC `p3n_cfl ((hs:num->(A)rfs_history) (D ((sub:num->num) j))) (Phi (D (sub j)))
                        ((ts:num->real) (D (sub j))) ((Q:num->real) (D (sub j))) s` THEN
  SUBGOAL_THEN `j <= (sub:num->num) j /\ k0 <= j /\ N1 <= sub j /\ N2 <= sub j /\ m <= sub j`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sub:num->num`)) (concl th) &&
      not (can (find_term (fun t -> t = `m':num`)) (concl th)) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    EXPAND_TAC "j" THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(hs:num->(A)rfs_history) (D ((sub:num->num) j))`;
                 `(Phi:num->real^3->A) (D ((sub:num->num) j))`; `(ts:num->real) (D ((sub:num->num) j))`;
                 `(Q:num->real) (D ((sub:num->num) j))`; `(Tf:num->real) (D ((sub:num->num) j))`;
                 `K:real`; `m:num`; `b2:real`; `s:real`] P3N_GAT_FACTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "reg" MATCH_MP_TAC THEN USE_THEN "H" (fun th -> REWRITE_TAC[th]);
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`(hs:num->(A)rfs_history) (D ((sub:num->num) j))`;
                     `(k:num->num) (D ((sub:num->num) j))`] P3N_VIEW_AT_EVENT) THEN
      ANTS_TAC THENL [USE_THEN "H" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      USE_THEN "eqs" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < &((sub:num->num) j) + &1}` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) j` o MATCH_MP P3N_SLICE_PARAM) THEN
        REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
        REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[];
      USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b2:real` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REMOVE_THEN "k0" (MP_TAC o SPECL [`j:num`; `s:real`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[IN_SING; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 3 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `G:real->real^3->real^3^3`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:real^3->bool`; `m:num`; `e:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "CL" (MP_TAC o SPECL [`a:real`; `b:real`; `K:real^3->bool`; `m:num`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G:real->real^3->real^3^3) s = g s` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The converse of P3N_PULLBACK_SEC_LE: bounds on the                        *)
(* sectional curvatures of the rescaled pullback bound the curvature norm   *)
(* of the slice at the image point (P3N_PULLBACK_RM_LE; the derivative of   *)
(* the chart representation is a linear isomorphism).                       *)
(* ========================================================================= *)

let P3N_PULLBACK_RM_LE = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) Q y K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s /\ &0 < Q /\
     (!u v. ~collinear {vec 0,u,v}
            ==> abs(lsectional (\z. Q %% rfs_pullback atlas e g z) y u v) <= K)
     ==> mfd_rm_norm atlas g (e y) <= Q * K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`] APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`N:real^3->bool`; `N':real^3->bool`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e`;
                 `h':real^3->real^3`] P2AP_DIFFEO_DERIV_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e)
                    (at y)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. ?z. (D:real^3->real^3) z = w` ASSUME_TAC THENL
   [MP_TAC(ISPEC `D:real^3->real^3` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:real^3` (SUBST_ALL_TAC o SYM) o SPEC `u':real^3`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v:real^3` (SUBST_ALL_TAC o SYM) o SPEC `v':real^3`) THEN
  SUBGOAL_THEN `~collinear {vec 0,u:real^3,v}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear {vec 0,(D:real^3->real^3) u,D v}` THEN
    REWRITE_TAC[CONTRAPOS_THM; COLLINEAR_LEMMA] THEN STRIP_TAC THEN
    ASM_MESON_TAC[LINEAR_0; LINEAR_CMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`; `u:real^3`; `v:real^3`]
                APX_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "lsectional")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `rfs_pullback atlas (e:real^3->A) g`; `Q:real`; `y:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < Q ==> abs Q = Q`; REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

(* C^2 closeness to a field with sectional curvatures bounded by K0 keeps  *)
(* them bounded by K0 + 1, with a closeness threshold depending only on K0. *)

let P3N_BASE_CURV = prove
 (`!K0. &0 <= K0
        ==> ?eta. &0 < eta /\
            !U (G0:real^3->real^3^3) H y.
              metric_field U G0 /\ metric_field U H /\ y IN U /\
              (!u v. ~collinear {vec 0,u,v} ==> abs(lsectional G0 y u v) <= K0) /\
              lck_dist2 2 G0 H y < eta pow 2
              ==> !u v. ~collinear {vec 0,u,v} ==> abs(lsectional H y u v) <= K0 + &1`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (ISPECL [`sqrt(C0 * K0 pow 2)`; `&1`] LCK_CURVATURE_STABILITY)) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `G0:real^3->real^3^3`; `H:real^3->real^3^3`;
                       `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "st" (MP_TAC o SPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
                                 `H:real^3->real^3^3`; `y:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= C0 * K0 pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `G0:real^3->real^3^3`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Curvature control on a window after a base time (P3N_WINDOW_CURV): from   *)
(* abs Rm <= K1 Q on an open set W at t0, Lemma 11.2 on W (P3N_L112_WINDOW,  *)
(* R <= 6 abs Rm) bounds R on a window of normalized length depending only   *)
(* on C and K1, as long as W persists; the Hamilton-Ivey pinching then       *)
(* bounds abs Rm (P3N_PINCH_RM).  The canonical neighbourhood assumption is  *)
(* used only before a cutoff time tc with s < tc (the form of Prop 16.5 with *)
(* a cutoff time).                                                           *)
(* ========================================================================= *)

let P3N_WINDOW_CURV = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !(hs:(A)rfs_history) C eps r K1 W t0 Q s tc.
           rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ rfs_pinched (rfs_view hs) /\
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < r /\ s < tc /\
           (!x t. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                  inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
           &1 <= Q /\ inv(r pow 2) <= Q /\ &0 <= K1 /\ &0 <= t0 /\
           open_in (rfs_vtop (rfs_view hs) t0) W /\
           (!y. y IN W ==> p3_vrm (rfs_view hs) t0 y <= K1 * Q) /\
           t0 <= s /\ s <= t0 + inv(&16 * max C (&2) * (&6 * K1 + &1)) / Q /\
           rfs_persists (rfs_view hs) W t0 s
           ==> !y. y IN W
                   ==> p3_vrm (rfs_view hs) s y <= (&24 * K1 + &16 + &2 * exp(&4)) * Q`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_L112_WINDOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LW"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r:real`; `K1:real`;
                       `W:A->bool`; `t0:real`; `Q:real`; `s:real`; `tc:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Q /\ &0 < inv(r pow 2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[REAL_POW_LT]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K1 * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t0 <= t /\ t <= s
                    ==> (y:A) IN topspace (rfs_vtop (rfs_view hs) t) /\
                        smooth_manifold_atlas (rfs_vtop (rfs_view hs) t) (rfs_vatlas (rfs_view hs) t) /\
                        riemannian_metric (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t)`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace (rfs_vtop (rfs_view (hs:(A)rfs_history)) t)` ASSUME_TAC THENL
     [ASM_CASES_TAC `t:real = t0` THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
        UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W t0 s` THEN
        REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `y:A`] P2C_REGULAR_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y <= &2 * (&6 * K1 * Q + inv(r pow 2))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real = t0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "sl" (MP_TAC o SPEC `t0:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) t0`;
                     `rfs_vatlas (rfs_view (hs:(A)rfs_history)) t0`;
                     `rfs_vmetric (rfs_view (hs:(A)rfs_history)) t0`; `y:A`] P3N_SCALAR_LE_RM) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm")) (concl th))) THEN
      ASM_REWRITE_TAC[p3_vrm] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "LW" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r:real`;
                                   `W:A->bool`; `t0:real`; `s:real`; `&6 * K1 * Q`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`x:A`; `t:real`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:A` THEN DISCH_TAC THEN
        USE_THEN "sl" (MP_TAC o SPEC `t0:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(z:A) IN topspace (rfs_vtop (rfs_view (hs:(A)rfs_history)) t0)` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
        MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) t0`;
                       `rfs_vatlas (rfs_view (hs:(A)rfs_history)) t0`;
                       `rfs_vmetric (rfs_view (hs:(A)rfs_history)) t0`; `z:A`] P3N_SCALAR_LE_RM) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm")) (concl th))) THEN
        ASM_REWRITE_TAC[p3_vrm] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `inv(&16 * max C (&2) * (&6 * K1 + &1)) / Q` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SUBGOAL_THEN `&0 < max C (&2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `&0 <= K1 * Q` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_pinched_at (rfs_vatlas (rfs_view (hs:(A)rfs_history)) s)
                               (rfs_vmetric (rfs_view hs) s) s y` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
    UNDISCH_TAC `(y:A) IN topspace (rfs_vtop (rfs_view (hs:(A)rfs_history)) s)` THEN
    REWRITE_TAC[rfs_view; rfs_pinched; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) s`;
                 `rfs_vatlas (rfs_view (hs:(A)rfs_history)) s`;
                 `rfs_vmetric (rfs_view (hs:(A)rfs_history)) s`; `s:real`; `y:A`] P3N_PINCH_RM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_pinched_at (rfs_vatlas (rfs_view (hs:(A)rfs_history)) s)
                              (rfs_vmetric (rfs_view hs) s) s y` THEN
  REWRITE_TAC[rfs_pinched_at] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `--(&6) <= --(&6) / (&4 * s + &1)` MP_TAC THENL
   [SUBGOAL_THEN `&1 <= &4 * s + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_LE_NEG2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_vscalar (rfs_view (hs:(A)rfs_history)) s y <= &2 * (&6 * K1 * Q + inv(r pow 2))` THEN
  REWRITE_TAC[P2C_VIEW_EXPAND; p3_vrm] THEN
  SUBGOAL_THEN `&0 <= K1 * Q /\ exp(&4) <= exp(&4) * Q` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Claim 16.10 with the closeness threshold dd0 depending only               *)
(* on eps (P3N_SLICE_DISC2, P3N_DISC2): the proofs of P3N_SLICE_DISC and     *)
(* P3N_DISC (unit pc_p3_s16disc) with the curvature bound K quantified after *)
(* dd0 (dd0 is the inner-neck threshold of P3N_INNER_NECK).  Needed because  *)
(* the core radius of Lemma 16.8 must be fixed before the curvature bound   *)
(* of the limit flow is known.                                               *)
(* ========================================================================= *)

let P3N_SLICE_DISC2 = prove
 (`?epsd. &0 < epsd /\
   !eps. &0 < eps /\ eps <= epsd
     ==> ?dd0. &0 < dd0 /\
         !K L. &0 <= K /\ &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !g0 A0 top atlas (g:A->real^3^3) Phi m0 m h G0 s d0 dd dl xc ec.
           p3_std_initial g0 A0 /\ hausdorff_space top /\
           smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
           mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\
           &0 < h /\ metric_field (:real^3) G0 /\
           &0 <= s /\ s < &1 /\ inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\
           &0 < dd /\ dd <= dd0 /\
           (!y. p3_std_dist g0 y < m0
                ==> lck_dist2 (rfs_kreg eps) G0
                      (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
           (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                ==> lck_dist2 (rfs_kreg eps)
                      (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
           (!y. p3_std_dist g0 y < m
                ==> mfd_scalar atlas g (Phi y) * h pow 2 <= K /\ norm y <= L /\
                    !w. w dot (rfs_pullback atlas Phi g y ** w) <= (h pow 2 * L) * (w dot w)) /\
           &0 < dl /\ dl <= dl1 /\ rfs_neck (top,atlas) g dl xc (ec:real^3->A)
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                        (IMAGE ec (sphere(vec 0,&1)))`,
  X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0") APX_CYL0_RM_BOUND THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIST"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CURV"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_SECTION_UNCOND) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1s:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEC"))) THEN
  EXISTS_TAC `min (&1 / &40) (min eps1d (min eps1c eps1s))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &40 /\ eps <= eps1d /\ eps <= eps1c /\ eps <= eps1s`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `eps:real` P3N_INNER_NECK) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ddI:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INNER"))) THEN
  EXISTS_TAC `ddI:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `L:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = &4 + &576 * (&1 + abs K0)` THEN
  ABBREV_TAC `Q = sqrt(&2 * (K + &1))` THEN
  ABBREV_TAC `ell = sqrt(&2 * L) * (&2 * L)` THEN
  SUBGOAL_THEN `&4 <= c0 /\ &0 < Q /\ Q pow 2 = &2 * (K + &1) /\ &0 <= ell`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "c0" THEN REAL_ARITH_TAC;
      EXPAND_TAC "Q" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Q" THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ell" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * Q * ell + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `min eps (inv(&2 * Q * ell + &1)) / c0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `dl:real`;
    `xc:A`; `ec:real^3->A`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `z:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `u0:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 * dl <= eps /\ c0 * dl <= inv(&2 * Q * ell + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c0 * dl <= min eps (inv(&2 * Q * ell + &1))` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * Q * ell + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * dl * (&2 * Q * ell + &1) <= &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c0 * dl`; `inv(&2 * Q * ell + &1)`; `&2 * Q * ell + &1`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl <= c0 * dl` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c0 * dl /\ dl <= &1 / &2 /\ c0 * dl <= &1 / &2 /\ dl <= eps /\
                dl <= eps1c /\ c0 * dl <= eps1d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d0 /\ &0 < m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < inv eps` THEN UNDISCH_TAC `m0 <= m:real` THEN
    UNDISCH_TAC `inv eps < d0` THEN UNDISCH_TAC `d0 + inv eps < m0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 m` THEN
  ABBREV_TAC `rho0 = p3s_rad_rinv g0 d0` THEN
  SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < m} = ball(vec 0,R) /\
                {x:real^3 | p3_std_dist g0 x = d0} = sphere(vec 0,rho0) /\
                &0 < rho0 /\ rho0 < R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN EXPAND_TAC "rho0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_STD_BALL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_STD_SPHERE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d0:real`] P3S_RINV_FACTS) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P3N_STD_RINV_LT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,R)) (Phi:real^3->A) /\
                (w0:real^3) IN ball(vec 0,R) /\
                (!y:real^3. y IN ball(vec 0,R) ==> p3_std_dist g0 y < m)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top atlas {x:real^3 | p3_std_dist g0 x < m} (Phi:real^3->A)` THEN
    UNDISCH_TAC `(w0:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,R)) G0` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= rfs_kreg eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN ball(vec 0,R)
      ==> mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) y) * h pow 2 <= K + &1 /\
          (!v. v dot (rfs_pullback atlas Phi g y ** v) <= (&2 * h pow 2 * L) * (v dot v))`
  (LABEL_TAC "BND") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3_std_dist g0 (y:real^3) < m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `mfd_scalar:((A->bool)#(A->real^3)->bool)->(A->real^3^3)->A->real`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) y) * h pow 2 <= K` THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `v:real^3` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(h pow 2 * L) * ((v:real^3) dot v)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= &2 * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w1 w2. w1 IN ball(vec 0:real^3,R) /\ w2 IN ball(vec 0,R)
      ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                  gamma (&0) = (Phi:real^3->A) w1 /\ gamma (&1) = Phi w2 /\
                  (!t. &0 <= t /\ t <= &1 ==> gamma t IN IMAGE Phi (ball(vec 0,R))) /\
                  mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) <= h * ell`
  (LABEL_TAC "CURVES") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Phi:real^3->A`; `R:real`; `&2 * h pow 2 * L`; `w1:real^3`; `w2:real^3`]
                  P3N_PARAM_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REPEAT STRIP_TAC THEN USE_THEN "BND" (MP_TAC o SPEC `y:real^3`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&2 * h pow 2 * L) * dist(w1:real^3,w2)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&2 * h pow 2 * L) = h * sqrt(&2 * L)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&2 * h pow 2 * L = h pow 2 * (&2 * L)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &2 * L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXPAND_TAC "ell" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(w1:real^3) <= L /\ norm(w2:real^3) <= L` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(w1:real^3) <= L /\ norm(w2:real^3) <= L
                              ==> dist(w1,w2) <= &2 * L`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) xc /\
                mfd_param top atlas (rfs_neck_dom dl) (ec:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl xc (ec:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(u0:real^3) = &1 /\ u0 IN rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u0:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ec:real^3->A) u0 = (Phi:real^3->A) w0` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) = (Phi:real^3->A) w0` THEN
    UNDISCH_TAC `(z:A) = (ec:real^3->A) u0` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) xc * h pow 2 <= Q pow 2` ASSUME_TAC THENL
   [USE_THEN "CURV" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`]
      APX_NECK_SCALAR_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "BND" (MP_TAC o SPEC `w0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `(mfd_scalar atlas (g:A->real^3^3) xc / &2) * h pow 2 <=
                  mfd_scalar atlas g ((Phi:real^3->A) w0) * h pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) w0) * h pow 2 <= K + &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,R)) SUBSET IMAGE ec (rfs_neck_dom dl)`
  (LABEL_TAC "INA") THENL
   [MATCH_MP_TAC P3N_SET_IN_NECK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `xc:A`; `u0:real^3`; `h:real`; `ell:real`; `Q:real`; `c0:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "CURVES" (MP_TAC o SPECL [`w0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas {x:real^3 | p3_std_dist g0 x < m0} (Phi:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,R)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < m0` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < inv eps` THEN UNDISCH_TAC `inv eps < d0` THEN
      UNDISCH_TAC `d0 + inv eps < m0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m0}` MP_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3N_STD_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  USE_THEN "INNER" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m0:real`;
    `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xS:A` (X_CHOOSE_THEN `eS:real^3->A` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `w1 = rho0 % (basis 1:real^3)` THEN
  SUBGOAL_THEN `(w1:real^3) IN ball(vec 0,R) /\ w1 IN sphere(vec 0,rho0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN
    SIMP_TAC[IN_BALL_0; IN_SPHERE_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->A) w1 IN IMAGE (eS:real^3->A) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "CURVES" (MP_TAC o SPECL [`w0:real^3`; `w1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`; `gamma1:real->A`; `&1`]
    APX_NECK_LIFT_SVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "INA" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(apx_sval v) <= &3 / (&4 * dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_SVAL_ARITH THEN
    MAP_EVERY EXISTS_TAC [`mfd_scalar atlas (g:A->real^3^3) xc`; `h:real`; `Q:real`; `ell:real`;
                          `c0:real`] THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) gamma1 (&0) (&1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `K0:real` APX_NECK_RECENTRE_GEN) THEN
  ANTS_TAC THENL [USE_THEN "K0" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `v:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `e2 = (ec:real^3->A) o (\w. norm(v:real^3) % w)` THEN
  ABBREV_TAC `u2 = inv(norm(v:real^3)) % v` THEN
  SUBGOAL_THEN `norm(u2:real^3) = &1 /\ (e2:real^3->A) u2 = (ec:real^3->A) v` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_NECK_DOM_NONZERO) THEN
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "e2" THEN EXPAND_TAC "u2" THEN
    ASM_SIMP_TAC[o_THM; NORM_MUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
                 REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((ec:real^3->A) v) * h pow 2 <= Q pow 2`
  ASSUME_TAC THENL
   [USE_THEN "BND" (MP_TAC o SPEC `w1:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,R)) SUBSET IMAGE e2 (rfs_neck_dom (c0 * dl))`
  (LABEL_TAC "INB") THENL
   [MATCH_MP_TAC P3N_SET_IN_NECK THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `(ec:real^3->A) v`; `u2:real^3`; `h:real`; `ell:real`; `Q:real`;
        `&1`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "CURVES" (MP_TAC o SPECL [`w1:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (eS:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e2 (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SPHERE_NEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `c0 * dl`; `xS:A`; `(ec:real^3->A) v`; `u2:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "DIST" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`; `z':real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 + &1 / &2 = &3 / &2`] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "DIST" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `c0 * dl`; `(ec:real^3->A) v`; `e2:real^3->A`; `y:real^3`;
        `z':real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - &1 / &2 = &1 / &2`] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "CURV" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`]
        APX_NECK_SCALAR_COMPARE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (Phi:real^3->A) (ball(vec 0,R))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_section (e2:real^3->A) (exp(--(inv(sqrt(&2) * (c0 * dl)))))
                  (exp(inv(sqrt(&2) * (c0 * dl)))) (IMAGE (eS:real^3->A) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(&2) * eps) <= inv(sqrt(&2) * (c0 * dl))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LE_LMUL_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC APX_SECTION_MONO THEN
    MAP_EVERY EXISTS_TAC [`exp(--(inv(sqrt(&2) * eps)))`; `exp(inv(sqrt(&2) * eps))`] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SEC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `(ec:real^3->A) v`; `xS:A`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `c0 * dl` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Phi:real^3->A`;
                 `rho0:real`; `R:real`] P3N_BALL_CORE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_SECTION_NOT_BOUNDING) THEN
  REWRITE_TAC[APX_SECTION_NOT_BOUNDING_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `e2:real^3->A`; `exp(--(inv(sqrt(&2) * (c0 * dl))))`; `exp(inv(sqrt(&2) * (c0 * dl)))`;
     `IMAGE (eS:real^3->A) (sphere(vec 0,&1))`;
     `top closure_of (IMAGE (Phi:real^3->A) (ball(vec 0,rho0)))`]) THEN
  SUBGOAL_THEN `annulus (exp(--(inv(sqrt(&2) * (c0 * dl))))) (exp(inv(sqrt(&2) * (c0 * dl)))) =
                rfs_neck_dom (c0 * dl) :real^3->bool` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (c0 * dl) ((ec:real^3->A) v) e2` THEN
      SIMP_TAC[rfs_neck];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (Phi:real^3->A) (ball(vec 0,R))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,rho0)) SUBSET {}` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM_REWRITE_TAC[SUBSET_EMPTY]]);;

let P3N_DISC2 = prove
 (`?epsd. &0 < epsd /\
   !eps. &0 < eps /\ eps <= epsd
     ==> ?dd0. &0 < dd0 /\
         !K L. &0 <= K /\ &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !(hs:(A)rfs_history) C eps' dl hh k g0 A0 Phi m0 m h d1 Gf sf d0 dd.
           rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
           rfs_surgery_ok hs C eps' dl hh k /\
           &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= dl1 /\
           p3_std_initial g0 A0 /\
           mfd_param (hs_top hs (k - 1)) (hs_atlas hs (k - 1))
                     {x | p3_std_dist g0 x < m} Phi /\
           &0 < h /\ &0 < d1 /\ inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\
           &0 < dd /\ dd <= dd0 /\
           (!s. hs_time hs k - d1 < s /\ s < hs_time hs k
                ==> metric_field (:real^3) (Gf s) /\ &0 <= sf s /\ sf s < &1 /\
                    (!y. p3_std_dist g0 y < m0
                         ==> lck_dist2 (rfs_kreg eps) (Gf s)
                               (\z. inv(h pow 2) %%
                                    rfs_pullback (hs_atlas hs (k - 1)) Phi
                                                 (hs_metric hs (k - 1) s) z) y
                             < dd pow 2) /\
                    (!x. d0 - inv eps < p3_std_dist g0 x /\
                         p3_std_dist g0 x < d0 + inv eps
                         ==> lck_dist2 (rfs_kreg eps)
                               (mpullback (p3_std_nc g0 A0) (cylinder_flow (sf s)))
                               (Gf s) x < dd pow 2) /\
                    (!y. p3_std_dist g0 y < m
                         ==> mfd_scalar (hs_atlas hs (k - 1)) (hs_metric hs (k - 1) s) (Phi y) *
                             h pow 2 <= K /\ norm y <= L /\
                             !w. w dot (rfs_pullback (hs_atlas hs (k - 1)) Phi
                                                     (hs_metric hs (k - 1) s) y ** w)
                                 <= (h pow 2 * L) * (w dot w)))
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                        (mfd_cut_spheres (ev_index(hs_event hs k)) (ev_neck(hs_event hs k))) /\
               (IMAGE Phi {x | p3_std_dist g0 x < m} SUBSET topspace(hs_top hs k) \/
                DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m}) (topspace(hs_top hs k)))`,
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD")) P3N_SLICE_DISC2 THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_STRONG_NECK_EARLIER) THEN
  REWRITE_TAC[APX_STRONG_NECK_EARLIER_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `kK:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N8"))) THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "SD" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD0"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "SD0" (MP_TAC o SPECL [`K:real`; `L:real`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1s:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD1"))) THEN
  EXISTS_TAC `min (dl1s / kK) (inv(&2 * kK))` THEN
  SUBGOAL_THEN `&0 < kK` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `k:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `d1:real`; `Gf:real->real^3->real^3^3`; `sf:real->real`; `d0:real`;
    `dd:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < kK * dl(hs_time (hs:(A)rfs_history) k) /\
                kK * dl(hs_time hs k) <= &1 / &2 /\ kK * dl(hs_time hs k) <= dl1s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dl(hs_time (hs:(A)rfs_history) k) <= min (dl1s / kK) (inv(&2 * kK))` THEN
    UNDISCH_TAC `&0 < dl(hs_time (hs:(A)rfs_history) k)` THEN
    SPEC_TAC(`(dl:real->real)(hs_time (hs:(A)rfs_history) k)`,`dk:real`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `inv(&2 * kK) = (&1 / &2) / kK` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < kK` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `dk <= min (dl1s / kK) (inv(&2 * kK))` THEN
    ASM_REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (hs_top (hs:(A)rfs_history) (k - 1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "hausdorff_space"))
          (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ev_index(hs_event (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_metric (hs:(A)rfs_history) (k - 1)) (hs_time hs k)
                   (hs_top hs k,hs_atlas hs k) (hs_metric hs k) (hs_event hs k)` THEN
    REWRITE_TAC[rfs_event_ok; mfd_cut_cap] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_surgery_ok (hs:(A)rfs_history) C eps' dl hh k` THEN
  REWRITE_TAC[rfs_surgery_ok] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:num->A` (LABEL_TAC "yy")) THEN
  MP_TAC(ISPECL
   [`ev_index(hs_event (hs:(A)rfs_history) k)`;
    `\i d. !s. hs_time (hs:(A)rfs_history) k - d < s /\ s < hs_time hs k
               ==> rfs_neck (hs_top hs (k - 1),hs_atlas hs (k - 1))
                            (hs_metric hs (k - 1) s) (kK * dl(hs_time hs k))
                            ((yy:num->A) i) (ev_neck(hs_event hs k) i)`]
   APX_FINITE_DELTA) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC APX_SLICE_NECKS THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "yy" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd"))) THEN
  ABBREV_TAC `t' = (max (hs_time (hs:(A)rfs_history) (k - 1))
                        (max (hs_time hs k - d) (hs_time hs k - d1)) + hs_time hs k) / &2` THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < t' /\ hs_time hs k - d < t' /\
                hs_time hs k - d1 < t' /\ t' < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k` THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < d1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas (hs:(A)rfs_history) (k - 1))
                                  (hs_metric hs (k - 1) t')` ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_time hs (k - 1)) (hs_time hs k) (hs_metric (hs:(A)rfs_history) (k - 1))` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < m})
             (mfd_cut_spheres (ev_index(hs_event hs k)) (ev_neck(hs_event hs k)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_cut_spheres;
                SET_RULE `DISJOINT (s:A->bool) (UNIONS f) <=> !t. t IN f ==> DISJOINT s t`;
                FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nd" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(MP_TAC o SPEC `t':real`)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t':real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sf:real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "SD1" (MP_TAC o SPECL
     [`g0:real^3->real^3^3`; `A0:real`; `hs_top (hs:(A)rfs_history) (k - 1)`;
      `hs_atlas (hs:(A)rfs_history) (k - 1)`; `hs_metric (hs:(A)rfs_history) (k - 1) t'`;
      `Phi:real^3->A`; `m0:real`; `m:real`; `h:real`; `(Gf:real->real^3->real^3^3) t'`;
      `(sf:real->real) t'`; `d0:real`; `dd:real`; `kK * dl(hs_time (hs:(A)rfs_history) k)`;
      `(yy:num->A) i`; `ev_neck(hs_event (hs:(A)rfs_history) k) i`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_EVENT_DICHOTOMY THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`;
    `hs_atlas (hs:(A)rfs_history) (k - 1)`;
    `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
    `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k`;
    `hs_event (hs:(A)rfs_history) k`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `{x:real^3 | p3_std_dist g0 x < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A)rfs_history) (k - 1)`;
                        `{x:real^3 | p3_std_dist g0 x < m}`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `inv eps < d0` THEN UNDISCH_TAC `d0 + inv eps < m0` THEN
    UNDISCH_TAC `m0 <= m:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3N_STD_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONNECTED_BALL]);;

(* ========================================================================= *)
(* Curvature of the slice from C^2 closeness of its rescaled                 *)
(* pullback to a field with bounded sectional curvature (P3N_BASE_RM).      *)
(* ========================================================================= *)

let P3N_BASE_RM = prove
 (`!K0. &0 <= K0
        ==> ?eta. &0 < eta /\
            !(hs:(A)rfs_history) Phi ts Q s U (M:real^3->real^3^3) y.
              smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s / Q))
                                    (rfs_vatlas (rfs_view hs) (ts + s / Q)) /\
              riemannian_metric (rfs_vatlas (rfs_view hs) (ts + s / Q))
                                (rfs_vmetric (rfs_view hs) (ts + s / Q)) /\
              mfd_param (rfs_vtop (rfs_view hs) (ts + s / Q))
                        (rfs_vatlas (rfs_view hs) (ts + s / Q)) U Phi /\
              &0 < Q /\ y IN U /\ metric_field U M /\
              (!u v. ~collinear {vec 0,u,v} ==> abs(lsectional M y u v) <= K0) /\
              lck_dist2 2 M (p3n_cfl hs Phi ts Q s) y < eta pow 2
              ==> p3_vrm (rfs_view hs) (ts + s / Q) (Phi y) <= (K0 + &1) * Q`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_BASE_CURV) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (p3n_cfl (hs:(A)rfs_history) Phi ts Q s)` ASSUME_TAC THENL
   [REWRITE_TAC[p3n_cfl] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p3_vrm] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC P3N_PULLBACK_RM_LE THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                        `U:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "bc" (MP_TAC o SPECL [`U:real^3->bool`; `M:real^3->real^3^3`;
                                 `p3n_cfl (hs:(A)rfs_history) Phi ts Q s`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p3n_cfl]);;

(* ========================================================================= *)
(* The contradiction sequence of Prop 16.5 (p3n_seq) and its basic           *)
(* properties: the scales Q n = h n^-2 tend to infinity (P3N_SEQ_Q_LARGE)    *)
(* and the rescaled caps are close to g0 at time 0 in every order on every   *)
(* ball (P3N_SEQ_CAP).  With a cutoff time tc n <= rfs_horizon (hs n) after  *)
(* ts n; the canonical neighbourhood assumption holds only before tc n.      *)
(* ========================================================================= *)

let p3n_seq = new_definition
 `p3n_seq (C,eps,hf,md,g0,A0,r) (rp:num->real->real) dl (hs:num->(A)rfs_history) k i Phi xi
          ts Q (tc:num->real) <=>
    !n. p3_struct (C,eps,hf,md,g0,A0) (rp n,dl n) (hs n) /\ tc n <= rfs_horizon (hs n) /\
        (!t x. &0 <= t /\ t < tc n /\ x IN topspace(rfs_top_at (hs n) t) /\
               inv(r pow 2) <= rfs_vscalar (rfs_view (hs n)) t x
               ==> p3_canon_at (rfs_view (hs n)) C eps x t) /\
        1 <= k n /\ k n <= hs_count (hs n) /\ i n IN ev_index(hs_event (hs n) (k n)) /\
        hs_time (hs n) (k n) = ts n /\ ts n < tc n /\
        p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n)) (hs n) (k n) (i n)
                     (Phi n) (xi n) /\
        dl n (ts n) <= inv(&n + &1) /\ rp n (ts n) <= eps /\
        inv(p3_hscale hf (rp n) (dl n) (ts n) pow 2) = Q n`;;

let P3N_SEQ_BASIC = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc n.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps
     ==> rfs_history_ok (hs n) /\ rfs_pinched (rfs_view (hs n)) /\ &0 <= ts n /\
         &0 < dl n (ts n) /\ &0 < rp n (ts n) /\
         &0 < p3_hscale hf (rp n) (dl n) (ts n) /\
         p3_hscale hf (rp n) (dl n) (ts n) <= dl n (ts n) pow 2 * eps /\
         &0 < Q n /\
         rfs_vtop (rfs_view (hs n)) (ts n) = hs_top (hs n) (k n) /\
         rfs_vatlas (rfs_view (hs n)) (ts n) = hs_atlas (hs n) (k n) /\
         rfs_vmetric (rfs_view (hs n)) (ts n) = hs_metric (hs n) (k n) (ts n) /\
         smooth_manifold_atlas (hs_top (hs n) (k n)) (hs_atlas (hs n) (k n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_seq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`) STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok ((hs:num->(A)rfs_history) n) /\ rfs_pinched (rfs_view (hs n)) /\
                (!t. &0 <= t ==> &0 < rp n t /\ &0 < dl n t)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp n,dl n) ((hs:num->(A)rfs_history) n)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (ts:num->real) n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_comb(rhs(concl th)) && rator(rhs(concl th)) = `ts:num->real`)) THEN
    MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `0`; `(k:num->num) n`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_history_ok ((hs:num->(A)rfs_history) n)` THEN
    SIMP_TAC[rfs_history_ok];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(ts:num->real) n` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `rp:num->real->real`)) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_struct")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3_hscale hf ((rp:num->real->real) n) (dl n) ((ts:num->real) n) /\
                p3_hscale hf (rp n) (dl n) (ts n) <= dl n (ts n) pow 2 * eps`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_hfun C (hf:real->real->real)` THEN REWRITE_TAC[p3_hfun; p3_hscale] THEN
    DISCH_THEN(MP_TAC o SPECL [`dl n ((ts:num->real) n) * (rp:num->real->real) n (ts n)`;
                               `(dl:num->real->real) n ((ts:num->real) n)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(dl n ((ts:num->real) n) * (rp:num->real->real) n (ts n)) * dl n (ts n)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(dl n ((ts:num->real) n) * (rp:num->real->real) n (ts n)) * dl n (ts n) =
                  dl n (ts n) pow 2 * rp n (ts n)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_comb(rhs(concl th)) && rator(rhs(concl th)) = `Q:num->real`)) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P3N_SEQ_Q_LARGE = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps
     ==> !B. ?N. !n. N <= n ==> B <= Q n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `B:real` THEN
  MP_TAC(SPEC `abs B * eps pow 2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`;
                 `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  ABBREV_TAC `h = p3_hscale hf ((rp:num->real->real) n) (dl n) ((ts:num->real) n)` THEN
  SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h <= eps * inv(&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(dl:num->real->real) n ((ts:num->real) n) pow 2 * eps` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(dl:num->real->real) n ((ts:num->real) n)` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&n + &1) / eps pow 2 <= Q (n:num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_comb(rhs(concl th)) && rator(rhs(concl th)) = `Q:num->real`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&n + &1) / eps pow 2 = inv((eps * inv(&n + &1)) pow 2) * inv(&n + &1)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &n + &1` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((eps * inv(&n + &1)) pow 2)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&n + &1) / eps pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&N <= &n` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `B * eps pow 2 <= abs B * eps pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3N_SEQ_CAP = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_modulus md /\ p3_std_initial g0 A0
     ==> !dd. &0 < dd
              ==> ?N. !n y. N <= n /\ p3_std_dist g0 y < inv dd
                            ==> lck_dist2 (rfs_kreg dd) g0
                                  (p3n_cfl (hs n) (Phi n) (ts n) (Q n) (&0)) y < dd pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `dd:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < min dd (md dd)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_modulus; REAL_LT_MIN]; ALL_TAC] THEN
  MP_TAC(SPEC `min dd (md dd)` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`;
                 `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(dl:num->real->real) n ((ts:num->real) n) <= min dd (md dd)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(N = 0)` THEN UNDISCH_TAC `N:num <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n))
                 ((hs:num->(A)rfs_history) n) (k n) (i n) (Phi n) (xi n)` THEN
  REWRITE_TAC[p3_cap_param] THEN DISCH_THEN(MP_TAC o SPEC `dd:real` o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real^3`))) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv dd <= inv((dl:num->real->real) n ((ts:num->real) n))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `d < e /\ x = y ==> y <= d ==> x < e`) THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3n_cfl; FUN_EQ_THM; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Continuity in time of the slices of a smooth family in the                *)
(* C-infinity sense (P3N_TIME_NEAR: along any sequence of times tending to  *)
(* b the slices are p2ci_near the slice at b), and the lck form for Ricci  *)
(* flows on R^3 from 0 (P3N_TIME_LCK).                                       *)
(* ========================================================================= *)

let P3N_SLICE_JET_BOUND = prove
 (`!W (Fm:real^(1,N)finite_sum->real^P) KC m.
     open W /\ smooth_map_on W Fm /\ compact KC /\ KC SUBSET W
     ==> ?B. !t y. pastecart (lift t) y IN KC /\
                   (?r. &0 < r /\ !z. z IN ball(y,r) ==> pastecart (lift t) z IN W)
                   ==> pde_jetn m (\z. Fm(pastecart (lift t) z)) y <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!l k. ?Blk. !w. w IN KC
                    ==> abs(rfa_jet l (\t z. drop(lift((Fm:real^(1,N)finite_sum->real^P)
                                              (pastecart (lift t) z)$k)))
                                    (drop(fstcart w)) (sndcart w)) <= Blk`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `k:num`] THEN
    MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\t z. drop(lift((Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t) z)$k))`;
                   `l:num list`] RFA_JET_JOINT_SMOOTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\w. lift(rfa_jet l (\t z. drop(lift((Fm:real^(1,N)finite_sum->real^P)
                                              (pastecart (lift t) z)$k)))
                                    (drop(fstcart w)) (sndcart w))`;
                   `KC:real^(1,N)finite_sum->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `Bf:(num)list->num->real`) THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                  (\l. sum(1..dimindex(:P)) (\k. abs((Bf:(num)list->num->real) l k)))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_map_on (ball(y:real^N,r))
                  (\z. (Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_W_SLICE_SMOOTH THEN EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:P))
                (\k. abs((iterated_partial l
                           (\z. (Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t) z)) y)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Bf:(num)list->num->real) l k` THEN CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `k:num`; `pastecart (lift t) (y:real^N)`]) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> abs a <= c ==> abs b <= c`) THEN
  REWRITE_TAC[rfa_jet; LIFT_DROP] THEN
  MP_TAC(ISPECL [`l:num list`; `ball(y:real^N,r)`;
                 `\z. (Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t) z)`; `k:num`;
                 `y:real^N`] RFA_ITERATED_PARTIAL_LIFT_COMPONENT) THEN
  ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; LIFT_DROP]);;

let P3N_PASTE_DIST = prove
 (`!t b (y:real^N) z0.
     dist(pastecart (lift t) y,pastecart (lift b) z0) <= abs(t - b) + dist(y,z0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist; PASTECART_SUB; GSYM LIFT_SUB] THEN
  MP_TAC(ISPECL [`lift(t - b)`; `y - z0:real^N`] NORM_PASTECART_LE) THEN
  REWRITE_TAC[NORM_LIFT]);;

let P3N_TIME_NEAR = prove
 (`!W (Fm:real^(1,N)finite_sum->real^P) b (z0:real^N) (s:num->real).
     open W /\ smooth_map_on W Fm /\ pastecart (lift b) z0 IN W /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - b) < e)
     ==> p2ci_near z0 (\n y. Fm(pastecart (lift(s n)) y)) (\y. Fm(pastecart (lift b) y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))) THEN
  MP_TAC(ISPEC `W:real^(1,N)finite_sum->bool` OPEN_CONTAINS_CBALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (z0:real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = d / &3` THEN
  SUBGOAL_THEN `&0 < r /\ &3 * r = d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t (y:real^N). abs(t - b) < r /\ dist(z0,y) < &2 * r
                   ==> pastecart (lift t) y IN (W:real^(1,N)finite_sum->bool)`
  (LABEL_TAC "geo") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `cball(pastecart (lift b) (z0:real^N),d) SUBSET W` THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    MP_TAC(SPECL [`t:real`; `b:real`; `y:real^N`; `z0:real^N`] P3N_PASTE_DIST) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `KC = cball(pastecart (lift b) (z0:real^N),&2 * r)` THEN
  SUBGOAL_THEN `compact (KC:real^(1,N)finite_sum->bool) /\ KC SUBSET W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "KC" THEN REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(pastecart (lift b) (z0:real^N),d)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t (y:real^N). abs(t - b) < r /\ dist(z0,y) < r
                   ==> pastecart (lift t) y IN (KC:real^(1,N)finite_sum->bool)`
  (LABEL_TAC "kc") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "KC" THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    MP_TAC(SPECL [`t:real`; `b:real`; `y:real^N`; `z0:real^N`] P3N_PASTE_DIST) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0")) THEN
  REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_W_SLICE_SMOOTH THEN EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "geo" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "N0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC RFA_W_SLICE_SMOOTH THEN EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "geo" MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`; `Fm:real^(1,N)finite_sum->real^P`;
                   `KC:real^(1,N)finite_sum->bool`; `m:num`] P3N_SLICE_JET_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `N0:num`] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs((s:num->real) n - b) < r` ASSUME_TAC THENL
     [USE_THEN "N0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[IN_BALL] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN USE_THEN "geo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`z0:real^N`; `y:real^N`; `z:real^N`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Fm:real^(1,N)finite_sum->real^P`; `KC:real^(1,N)finite_sum->bool`]
                  COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "conv" (MP_TAC o SPEC `min r de`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
    EXISTS_TAC `N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN
    REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
      USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`(s:num->real) n`; `b:real`; `y:real^N`; `y:real^N`] P3N_PASTE_DIST) THEN
      REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Tools for the extension step.  The chart representative                   *)
(* of a Ricci flow from 0 on R^N (P3N_RF_REP), its slices along converging *)
(* times converge with all derivatives (P3N_RF_MNEAR), uniform continuity  *)
(* and boundedness of its entries on compact time-space sets (P3N_RF_UC),  *)
(* entrywise closeness from order-0 lck closeness (P3N_LCK_ENTRY) and an   *)
(* increasing majorant of a sequence of indices (P3N_DIAG_INC).            *)
(* ========================================================================= *)

let P3N_RF_REP = prove
 (`!T0 (G:real->real^N->real^N^N).
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G
     ==> ?e Fm. &0 < e /\
                smooth_map_on (interval(lift(--e),lift T0) PCROSS (:real^N)) Fm /\
                !t y. &0 <= t /\ t < T0
                      ==> Fm(pastecart (lift t) y) =
                          (vectorize:real^N^N->real^(N,N)finite_prod) (G t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `((:real^N),(\x:real^N. x))` o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID; P2C_OPEN_SET_METRIC_LOCAL_UNIV;
              REAL_SUB_LZERO; IN_UNIV] THEN
  MESON_TAC[]);;

let P3N_RF_FIELD = prove
 (`!T0 (G:real->real^N->real^N^N) t.
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G /\ &0 <= t /\ t < T0
     ==> metric_field (:real^N) (G t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_OSA_RIEM THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`; `&0`; `T0:real`;
                 `G:real->real^N->real^N^N`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
  ASM_SIMP_TAC[]);;

let P3N_RF_MNEAR = prove
 (`!T0 (G:real->real^N->real^N^N) b (s:num->real) (z0:real^N).
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G /\
     &0 <= b /\ b < T0 /\ (!n. &0 <= s n /\ s n < T0) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - b) < e)
     ==> p2cm_mnear z0 (\n. G (s n)) (G b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) o
    MATCH_MP P3N_RF_REP) THEN
  REWRITE_TAC[p2cm_mnear] THEN BETA_TAC THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN REWRITE_TAC[REAL_LT_01] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[OPEN_BALL; SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN
      EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[OPEN_BALL; SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN
      EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(--e),lift T0) PCROSS (:real^N)`;
                 `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `b:real`; `z0:real^N`; `s:num->real`] P3N_TIME_NEAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV;
                 IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_RF_UC = prove
 (`!T0 (G:real->real^N->real^N^N) a b K.
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G /\
     &0 <= a /\ b < T0 /\ compact K
     ==> (?B. !t y p q. a <= t /\ t <= b /\ y IN K /\
                        1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> abs(G t y$p$q) <= B) /\
         (!e. &0 < e
              ==> ?mu. &0 < mu /\
                       !t t' y p q. a <= t /\ t <= b /\ a <= t' /\ t' <= b /\
                                    abs(t - t') < mu /\ y IN K /\
                                    1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                                    ==> abs(G t y$p$q - G t' y$p$q) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN
    `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) o
    MATCH_MP P3N_RF_REP) THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t <= b /\ (y:real^N) IN K
          ==> pastecart (lift t) y IN interval[lift a,lift b] PCROSS K /\
              Fm(pastecart (lift t) y) =
              (vectorize:real^N^N->real^(N,N)finite_prod) ((G:real->real^N->real^N^N) t y)`
  (LABEL_TAC "pt") THENL
   [REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (interval[lift a,lift b] PCROSS (K:real^N->bool)) /\
    (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod) continuous_on
    (interval[lift a,lift b] PCROSS K)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(--e0),lift T0) PCROSS (:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_UNIV] THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`Fm:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `interval[lift a,lift b] PCROSS (K:real^N->bool)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     ((G:real->real^N->real^N^N) t y))` THEN
    ASM_SIMP_TAC[P2CE_ENTRY_LE_VECTORIZE] THEN
    USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Fm:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `interval[lift a,lift b] PCROSS (K:real^N->bool)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                   ((G:real->real^N->real^N^N) t y - G t' y))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(G:real->real^N->real^N^N) t y - G t' y`; `p:num`; `q:num`]
                  P2CE_ENTRY_LE_VECTORIZE) THEN
    ASM_REWRITE_TAC[MATRIX_SUB_COMPONENT];
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`t':real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[VECTORIZE_SUB; GSYM dist] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`t:real`; `t':real`; `y:real^N`; `y:real^N`] P3N_PASTE_DIST) THEN
  REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC);;

let P3N_PRODUCT_12 = prove
 (`!f:num->real. product(1..2) f = f 1 * f 2`,
  GEN_TAC THEN
  MP_TAC(CONJUNCT2(ISPEC `f:num->real` (GEN `f:num->real` PRODUCT_CLAUSES_NUMSEG))) THEN
  DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
  REWRITE_TAC[ARITH; PRODUCT_SING_NUMSEG]);;

let P3N_MF_DIAG_POS = prove
 (`!U (G:real^N->real^N^N) y p.
     metric_field U G /\ y IN U /\ 1 <= p /\ p <= dimindex(:N) ==> &0 < G y$p$p`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `basis p:real^N` o CONJUNCT2) THEN
  ASM_SIMP_TAC[BASIS_NONZERO; RFB_BASIS_DOT_MATRIX]);;

let P3N_LCK_ENTRY = prove
 (`!V (G0:real^N->real^N^N) H y p q k.
     metric_field V G0 /\ metric_field V H /\ y IN V /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> (H y$p$q - G0 y$p$q) pow 2 <= lck_dist2 k G0 H y * (G0 y$p$p * G0 y$q$q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G0:real^N->real^N^N`; `H:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (H:real^N->real^N^N) z u - lmetric2 G0 z u`; `y:real^N`;
                 `\r. basis(if r = 1 then p else if r = 2 then q else 0):real^N`]
         LRG_LTNORM2_BOUND) THEN
  ASM_REWRITE_TAC[P3N_PRODUCT_12] THEN BETA_TAC THEN
  ASM_SIMP_TAC[P3S_LMETRIC2_BASIS; ARITH_RULE `~(2 = 1)`; RFB_BASIS_DOT_MATRIX] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `0`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                   `H:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; lnabla_iter];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC P3N_MF_DIAG_POS THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P3N_DIAG_INC = prove
 (`!N:num->num. ?J. (!m n. m < n ==> J m < J n) /\ !i. N i <= J i`,
  GEN_TAC THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(J:num->num) 0 = N 0 /\ !i. J(SUC i) = MAX (N(SUC i)) (J i + 1)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num->num` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let P3N_C0_ARITH = prove
 (`!x a b B ee lck ep.
     x pow 2 <= lck * (a * b) /\ &0 <= lck /\ lck <= ee /\ &0 < a /\ a <= B /\
     &0 < b /\ b <= B /\ ee * (B pow 2 + &1) < ep pow 2 /\ &0 < ep
     ==> abs x < ep`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a * b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a * b <= B pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lck * (a * b) <= ee * (B pow 2 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 < ep pow 2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

let P3N_DIAG_SEQ = prove
 (`!P:num->num->bool.
     (!i. ?N. !j. N <= j ==> P i j)
     ==> ?J. (!m n. m < n ==> J m < J n) /\ !i. P i (J i)`,
  GEN_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num->num`) THEN
  MP_TAC(SPEC `N:num->num` P3N_DIAG_INC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num->num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

let P3N_EVENT_FIN = prove
 (`!R:num->num->bool.
     (!m. ?N. !j. N <= j ==> R m j)
     ==> !i. ?N. !j. N <= j ==> !m. m <= i ==> R m j`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num->num` o REWRITE_RULE[SKOLEM_THM]) THEN
  X_GEN_TAC `i:num` THEN
  EXISTS_TAC `nsum(0..i) (N:num->num)` THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum(0..i) (N:num->num)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`N:num->num`; `nsum(0..i) (N:num->num)`; `0..i`] NSUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG; LE_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The first failure of persistence of an open set before a                  *)
(* given time is an event j at which the set is not kept whole and         *)
(* disjoint from the cut spheres (P3N_FIRST_FAILURE2, from                 *)
(* P3N_FIRST_FAILURE and the supremum of the persistence times).           *)
(* ========================================================================= *)

let P3N_PERSIST_STAGE = prove
 (`!(hs:(A)rfs_history) k W t.
     rfs_history_ok hs /\ k <= hs_count hs /\ open_in (hs_top hs k) W /\
     t < hs_time hs (k + 1)
     ==> rfs_persists (rfs_view hs) W (hs_time hs k) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

let P3N_FIRST_FAILURE2 = prove
 (`!(hs:(A)rfs_history) k W t1.
     rfs_history_ok hs /\ k <= hs_count hs /\ open_in (hs_top hs k) W /\
     hs_time hs k < t1 /\ t1 < rfs_horizon hs /\
     ~rfs_persists (rfs_view hs) W (hs_time hs k) t1
     ==> ?j. k < j /\ j <= hs_count hs /\ hs_time hs j <= t1 /\
             (!t. hs_time hs k < t /\ t < hs_time hs j
                  ==> rfs_persists (rfs_view hs) W (hs_time hs k) t) /\
             (!t. hs_time hs k <= t /\ t <= t1 /\
                  rfs_persists (rfs_view hs) W (hs_time hs k) t
                  ==> t <= hs_time hs j) /\
             open_in (hs_top hs (j - 1)) W /\
             ~(W SUBSET topspace (hs_top hs j) /\
               DISJOINT W (mfd_cut_spheres (ev_index (hs_event hs j))
                                           (ev_neck (hs_event hs j))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {t | hs_time (hs:(A)rfs_history) k <= t /\ t <= t1 /\
                       rfs_persists (rfs_view hs) W (hs_time hs k) t}` THEN
  SUBGOAL_THEN `!t. t IN S <=> hs_time (hs:(A)rfs_history) k <= t /\ t <= t1 /\
                               rfs_persists (rfs_view hs) W (hs_time hs k) t`
  (LABEL_TAC "S") THENL [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `?b:real. !x. x IN S ==> x <= b` (LABEL_TAC "bd") THENL
   [EXISTS_TAC `t1:real` THEN USE_THEN "S" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ta = min ((hs_time (hs:(A)rfs_history) k + hs_time hs (k + 1)) / &2) t1` THEN
  SUBGOAL_THEN `(ta:real) IN S /\ hs_time (hs:(A)rfs_history) k < ta` STRIP_ASSUME_TAC THENL
   [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < ta /\ ta <= t1 /\ ta < hs_time hs (k + 1)`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "ta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC P3N_PERSIST_STAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `tt = sup (S:real->bool)` THEN
  SUBGOAL_THEN `ta <= tt /\ tt <= t1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "tt" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "bd" ACCEPT_TAC;
      EXPAND_TAC "tt" THEN MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "S" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. hs_time (hs:(A)rfs_history) k < t /\ t < tt
                    ==> rfs_persists (rfs_view hs) W (hs_time hs k) t`
  (LABEL_TAC "below") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `t:real`] SUP_APPROACH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) k`; `x:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `W:A->bool`; `tt:real`] P3N_FIRST_FAILURE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "below" ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `tt + d <= t1` THENL
       [SUBGOAL_THEN `tt + d <= tt` MP_TAC THENL
         [EXPAND_TAC "tt" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
          CONJ_TAC THENL [USE_THEN "bd" ACCEPT_TAC; ALL_TAC] THEN
          USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `~rfs_persists (rfs_view (hs:(A)rfs_history)) W (hs_time hs k) t1` THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
        MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) k`; `tt + d`] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t <= sup(S:real->bool)` MP_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [USE_THEN "bd" ACCEPT_TAC; USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]]);;

let P3N_PERSIST_HORIZON = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_persists (rfs_view hs) W a b /\ ~(W = {}) /\ a < b ==> b < rfs_horizon hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[rfs_top_at; rfs_horizon] THEN COND_CASES_TAC THENL
   [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) b` THEN REWRITE_TAC[rfs_live] THEN
    SIMP_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[]]);;

let P3N_DISC_AT_FAIL = prove
 (`?epsd. &0 < epsd /\
   !eps. &0 < eps /\ eps <= epsd
     ==> ?dd0. &0 < dd0 /\
         !K L. &0 <= K /\ &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !(hs:(A)rfs_history) C eps' dl hh j g0 A0 Phi m0 m h d0 dd Gf sf ta.
           rfs_history_ok hs /\ 1 <= j /\ j <= hs_count hs /\
           rfs_surgery_ok hs C eps' dl hh j /\
           &0 < dl(hs_time hs j) /\ dl(hs_time hs j) <= dl1 /\
           p3_std_initial g0 A0 /\
           mfd_param (hs_top hs (j - 1)) (hs_atlas hs (j - 1))
                     {x | p3_std_dist g0 x < m} Phi /\
           &0 < h /\ inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\
           &0 < dd /\ dd <= dd0 /\ ta < hs_time hs j /\
           (!s. ta < s /\ s < hs_time hs j
                ==> metric_field (:real^3) (Gf s) /\ &0 <= sf s /\ sf s < &1 /\
                    (!y. p3_std_dist g0 y < m0
                         ==> lck_dist2 (rfs_kreg eps) (Gf s)
                               (\z. inv(h pow 2) %%
                                    rfs_pullback (rfs_vatlas (rfs_view hs) s) Phi
                                                 (rfs_vmetric (rfs_view hs) s) z) y
                             < dd pow 2) /\
                    (!x. d0 - inv eps < p3_std_dist g0 x /\
                         p3_std_dist g0 x < d0 + inv eps
                         ==> lck_dist2 (rfs_kreg eps)
                               (mpullback (p3_std_nc g0 A0) (cylinder_flow (sf s)))
                               (Gf s) x < dd pow 2) /\
                    (!y. p3_std_dist g0 y < m
                         ==> mfd_scalar (rfs_vatlas (rfs_view hs) s)
                                        (rfs_vmetric (rfs_view hs) s) (Phi y) *
                             h pow 2 <= K /\ norm y <= L /\
                             !w. w dot (rfs_pullback (rfs_vatlas (rfs_view hs) s) Phi
                                                     (rfs_vmetric (rfs_view hs) s) y ** w)
                                 <= (h pow 2 * L) * (w dot w)))
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                        (mfd_cut_spheres (ev_index(hs_event hs j)) (ev_neck(hs_event hs j))) /\
               (IMAGE Phi {x | p3_std_dist g0 x < m} SUBSET topspace(hs_top hs j) \/
                DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m}) (topspace(hs_top hs j)))`,
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2")) P3N_DISC2 THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "D2" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D3"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "D3" (MP_TAC o SPECL [`K:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D4"))) THEN
  EXISTS_TAC `dl1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `j:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `d0:real`; `dd:real`; `Gf:real->real^3->real^3^3`; `sf:real->real`;
    `ta:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "sc" (last (CONJUNCTS th))) THEN
  USE_THEN "D4" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `eps':real`; `dl:real->real`; `hh:real->real`; `A0:real`;
    `m0:real`; `h:real`; `hs_time (hs:(A)rfs_history) j - max ta (hs_time hs (j - 1))`;
    `Gf:real->real^3->real^3^3`; `sf:real->real`; `d0:real`; `dd:real`] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (j - 1) < hs_time hs j` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - 1`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  REMOVE_THEN "sc" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]);;

let P3N_QH_ARITH = prove
 (`!Q h a b L. Q * h pow 2 = &1 /\ &0 < h /\ Q * a <= L * b ==> a <= (h pow 2 * L) * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a = h pow 2 * (Q * a)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `h2 * (Q * a) = (Q * h2) * a`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]);;

let P3N_QH_ARITH2 = prove
 (`!Q h x K. Q * h pow 2 = &1 /\ &0 < h /\ x <= K * Q ==> x * h pow 2 <= K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(K * Q) * h pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RID; REAL_LE_REFL]]);;

let P3N_FAIL_DISCARD = prove
 (`?epsd. &0 < epsd /\
   !eps. &0 < eps /\ eps <= epsd
     ==> ?dd0. &0 < dd0 /\
         !K L. &0 <= K /\ &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !(hs:(A)rfs_history) C eps' dl hh k j g0 A0 Phi ts Q h m0 m d0 dd
          (Gf:real->real^3->real^3^3) sf sa.
           rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k = ts /\
           p2c_regular_view (rfs_view hs) /\ &0 < h /\ inv(h pow 2) = Q /\
           k < j /\ j <= hs_count hs /\ rfs_surgery_ok hs C eps' dl hh j /\
           &0 < dl(hs_time hs j) /\ dl(hs_time hs j) <= dl1 /\
           p3_std_initial g0 A0 /\
           inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\ &0 < dd /\ dd <= dd0 /\
           mfd_param (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts)
                     {x | p3_std_dist g0 x < m} Phi /\
           &0 <= sa /\ ts + sa / Q < hs_time hs j /\
           (!t. ts < t /\ t < hs_time hs j
                ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m}) ts t) /\
           ~(IMAGE Phi {x | p3_std_dist g0 x < m} SUBSET topspace (hs_top hs j) /\
             DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                      (mfd_cut_spheres (ev_index (hs_event hs j)) (ev_neck (hs_event hs j)))) /\
           (!s. sa < s /\ ts + s / Q < hs_time hs j /\
                rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + s / Q)
                ==> metric_field (:real^3) (Gf s) /\ &0 <= sf s /\ sf s < &1 /\
                    (!y. p3_std_dist g0 y < m0
                         ==> lck_dist2 (rfs_kreg eps) (Gf s) (p3n_cfl hs Phi ts Q s) y
                             < dd pow 2) /\
                    (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                         ==> lck_dist2 (rfs_kreg eps)
                               (mpullback (p3_std_nc g0 A0) (cylinder_flow (sf s)))
                               (Gf s) x < dd pow 2) /\
                    (!y. p3_std_dist g0 y < m
                         ==> mfd_scalar (rfs_vatlas (rfs_view hs) (ts + s / Q))
                                        (rfs_vmetric (rfs_view hs) (ts + s / Q)) (Phi y)
                             <= K * Q /\ norm y <= L /\
                             !w. w dot (p3n_cfl hs Phi ts Q s y ** w) <= L * (w dot w)))
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m}) (topspace (hs_top hs j))`,
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF")) P3N_DISC_AT_FAIL THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "DF" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "DF2" (MP_TAC o SPECL [`K:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF3"))) THEN
  EXISTS_TAC `dl1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `k:num`; `j:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`;
    `ts:real`; `Q:real`; `h:real`; `m0:real`; `m:real`; `d0:real`; `dd:real`;
    `Gf:real->real^3->real^3^3`; `sf:real->real`; `sa:real`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in let n = length cs in
    MAP_EVERY ASSUME_TAC (fst(chop_list (n - 3) cs)) THEN
    LABEL_TAC "below" (el (n - 3) cs) THEN LABEL_TAC "notkept" (el (n - 2) cs) THEN
    LABEL_TAC "sc" (el (n - 1) cs)) THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `Q:real`)) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q * h pow 2 = &1` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `Q:real`)) THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1) /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vtop (rfs_view (hs:(A)rfs_history)) ts = hs_top hs k /\
                rfs_vatlas (rfs_view hs) ts = hs_atlas hs k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `{x:real^3 | p3_std_dist g0 x < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_param (rfs_vtop (rfs_view (hs:(A)rfs_history)) ts)
                   (rfs_vatlas (rfs_view hs) ts) {x | p3_std_dist g0 x < m} Phi` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= sa / Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (j - 1) < hs_time hs j /\ ts <= hs_time hs (j - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `hs_time (hs:(A)rfs_history) k = ts`)) THEN
      MATCH_MP_TAC APX_HS_TIME_LE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `tq = (max (ts + sa / Q) (hs_time (hs:(A)rfs_history) (j - 1)) + hs_time hs j) / &2` THEN
  SUBGOAL_THEN `ts < tq /\ ts + sa / Q < tq /\ hs_time (hs:(A)rfs_history) (j - 1) <= tq /\
                tq < hs_time hs j` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) (j - 1)) (hs_atlas hs (j - 1))
                  {x | p3_std_dist g0 x < m} Phi` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `{x:real^3 | p3_std_dist g0 x < m}`;
                   `Phi:real^3->A`; `ts:real`; `tq:real`] P3N_PARAM_LATER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - 1`; `tq:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  USE_THEN "DF3" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `j:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `d0:real`; `dd:real`;
    `\t. (Gf:real->real^3->real^3^3) (Q * (t - ts))`; `\t. (sf:real->real) (Q * (t - ts))`;
    `ts + sa / Q`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ts + (Q * (t - ts)) / Q = t` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `sa < Q * (t - ts)` ASSUME_TAC THENL
     [SUBGOAL_THEN `sa / Q < t - ts` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "sc" (MP_TAC o SPEC `Q * (t - ts)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p3n_cfl] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th))) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_QH_ARITH2 THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN MATCH_MP_TAC P3N_QH_ARITH THEN EXISTS_TAC `Q:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let P3N_BIG_PERSIST = prove
 (`?epsd. &0 < epsd /\
   !eps. &0 < eps /\ eps <= epsd
     ==> ?dd0. &0 < dd0 /\
         !K L. &0 <= K /\ &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !(hs:(A)rfs_history) C eps' dl hh k g0 A0 Phi ts Q h m0 m mstar d0 dd
          (Gf:real->real^3->real^3^3) sf sa sp se.
           rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k = ts /\
           p2c_regular_view (rfs_view hs) /\ &0 < h /\ inv(h pow 2) = Q /\
           (!j. k < j /\ j <= hs_count hs
                ==> rfs_surgery_ok hs C eps' dl hh j /\
                    &0 < dl(hs_time hs j) /\ dl(hs_time hs j) <= dl1) /\
           p3_std_initial g0 A0 /\
           inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\ &0 < mstar /\ mstar <= m /\
           &0 < dd /\ dd <= dd0 /\
           mfd_param (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts)
                     {x | p3_std_dist g0 x < m} Phi /\
           &0 <= sa /\ sa <= sp /\ (sa < sp \/ sa = &0) /\
           rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + sp / Q) /\
           (!s. &0 <= s /\ s < se
                ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < mstar})
                                 ts (ts + s / Q)) /\
           (!s. sa < s /\ s < se /\
                rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + s / Q)
                ==> metric_field (:real^3) (Gf s) /\ &0 <= sf s /\ sf s < &1 /\
                    (!y. p3_std_dist g0 y < m0
                         ==> lck_dist2 (rfs_kreg eps) (Gf s) (p3n_cfl hs Phi ts Q s) y
                             < dd pow 2) /\
                    (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                         ==> lck_dist2 (rfs_kreg eps)
                               (mpullback (p3_std_nc g0 A0) (cylinder_flow (sf s)))
                               (Gf s) x < dd pow 2) /\
                    (!y. p3_std_dist g0 y < m
                         ==> mfd_scalar (rfs_vatlas (rfs_view hs) (ts + s / Q))
                                        (rfs_vmetric (rfs_view hs) (ts + s / Q)) (Phi y)
                             <= K * Q /\ norm y <= L /\
                             !w. w dot (p3n_cfl hs Phi ts Q s y ** w) <= L * (w dot w)))
           ==> !s. &0 <= s /\ s < se
                   ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m})
                                    ts (ts + s / Q)`,
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF")) P3N_DISC_AT_FAIL THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "DF" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "DF2" (MP_TAC o SPECL [`K:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DF3"))) THEN
  EXISTS_TAC `dl1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `k:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `ts:real`;
    `Q:real`; `h:real`; `m0:real`; `m:real`; `mstar:real`; `d0:real`; `dd:real`;
    `Gf:real->real^3->real^3^3`; `sf:real->real`; `sa:real`; `sp:real`; `se:real`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
    LABEL_TAC "sc" (last (CONJUNCTS th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "mstar" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `mstar:real`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "surg" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `dl1:real`)) (concl th))) THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `Q:real`)) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q * h pow 2 = &1` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `Q:real`)) THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1) /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vtop (rfs_view (hs:(A)rfs_history)) ts = hs_top hs k /\
                rfs_vatlas (rfs_view hs) ts = hs_atlas hs k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `{x:real^3 | p3_std_dist g0 x < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_param (rfs_vtop (rfs_view (hs:(A)rfs_history)) ts)
                   (rfs_vatlas (rfs_view hs) ts) {x | p3_std_dist g0 x < m} Phi` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->A) (vec 0) IN IMAGE Phi {x | p3_std_dist g0 x < mstar} /\
                IMAGE Phi {x | p3_std_dist g0 x < mstar} SUBSET
                IMAGE Phi {x | p3_std_dist g0 x < m}` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s1:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `sp < s1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(s1 <= sp) ==> sp < s1`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~rfs_persists (rfs_view (hs:(A)rfs_history))
                   (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + s1 / Q)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`ts:real`; `ts + sp / Q`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_LADD; REAL_LE_DIV2_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `s2 = (s1 + se) / &2` THEN
  SUBGOAL_THEN `s1 < s2 /\ s2 < se /\ &0 < s1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ts < ts + s1 / Q /\ ts + s1 / Q < ts + s2 / Q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; REAL_LT_LADD; REAL_LT_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history))
                  (IMAGE Phi {x | p3_std_dist g0 x < mstar}) ts (ts + s2 / Q)`
  ASSUME_TAC THENL
   [USE_THEN "mstar" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ts + s1 / Q < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `ts + s2 / Q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3N_PERSIST_HORIZON THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < mstar}`; `ts:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(Phi:real^3->A) (vec 0)` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < m}`;
                 `ts + s1 / Q`] P3N_FIRST_FAILURE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(LABEL_TAC "sup" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `ts + s1 / Q`)) (concl th) &&
    can (find_term ((=) `hs_time (hs:(A)rfs_history) j`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "below" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `hs_time (hs:(A)rfs_history) j`)) (concl th) &&
    not (can (find_term ((=) `ts + s1 / Q`)) (concl th)))) THEN
  FIRST_X_ASSUM(LABEL_TAC "notkept" o check (fun th -> is_neg(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_cut_spheres")) (concl th))) THEN
  SUBGOAL_THEN `ts < hs_time (hs:(A)rfs_history) j` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `hs_time (hs:(A)rfs_history) k = ts`)) THEN
    MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sa / Q /\ sa / Q <= sp / Q /\ sp / Q < s1 / Q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ts + sp / Q <= hs_time (hs:(A)rfs_history) j` ASSUME_TAC THENL
   [USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ts + sa / Q < hs_time (hs:(A)rfs_history) j` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [SUBGOAL_THEN `sa / Q < sp / Q` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (j - 1) < hs_time hs j /\ ts <= hs_time hs (j - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(k:num) < j`; `j <= hs_count (hs:(A)rfs_history)`] THEN ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `hs_time (hs:(A)rfs_history) k = ts`)) THEN
      MATCH_MP_TAC APX_HS_TIME_LE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(k:num) < j`; `j <= hs_count (hs:(A)rfs_history)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `tq = (max (ts + sa / Q) (hs_time (hs:(A)rfs_history) (j - 1)) + hs_time hs j) / &2` THEN
  SUBGOAL_THEN `ts < tq /\ ts + sa / Q < tq /\ hs_time (hs:(A)rfs_history) (j - 1) <= tq /\
                tq < hs_time hs j` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) (j - 1)) (hs_atlas hs (j - 1))
                  {x | p3_std_dist g0 x < m} Phi` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `{x:real^3 | p3_std_dist g0 x < m}`;
                   `Phi:real^3->A`; `ts:real`; `tq:real`] P3N_PARAM_LATER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - 1`; `tq:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL
       [UNDISCH_TAC `(k:num) < j` THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `j <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_surgery_ok (hs:(A)rfs_history) C eps' dl hh j /\ &0 < dl(hs_time hs j) /\
                dl(hs_time hs j) <= dl1` STRIP_ASSUME_TAC THENL
   [USE_THEN "surg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "DF3" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `j:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `d0:real`; `dd:real`;
    `\t. (Gf:real->real^3->real^3^3) (Q * (t - ts))`; `\t. (sf:real->real) (Q * (t - ts))`;
    `ts + sa / Q`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [UNDISCH_TAC `(k:num) < j` THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ts + (Q * (t - ts)) / Q = t` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `sa < Q * (t - ts) /\ Q * (t - ts) < se` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `sa / Q < t - ts /\ t - ts < s1 / Q` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "sc" (MP_TAC o SPEC `Q * (t - ts)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p3n_cfl] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th))) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_QH_ARITH2 THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN MATCH_MP_TAC P3N_QH_ARITH THEN EXISTS_TAC `Q:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL [REMOVE_THEN "notkept" MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `j:num`] P3N_VIEW_AT_EVENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(k:num) < j` THEN ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history))
                 (IMAGE Phi {x | p3_std_dist g0 x < mstar}) ts (ts + s2 / Q)` THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  DISCH_THEN(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) j`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(Phi:real^3->A) (vec 0)`; `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < mstar}`;
                 `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < m}`;
                 `topspace(hs_top (hs:(A)rfs_history) j)`]
    (SET_RULE `!a:A s t u. a IN s /\ s SUBSET t /\ DISJOINT t u ==> ~(s SUBSET u)`)) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Shi's estimates for the rescaled flows of a p2cv_hyp                      *)
(* sequence on windows [0,e n) whose end varies with n (e n <= 1), in the   *)
(* style of P2CQ_SEQ_FACTS / P2CQ_SHI of pc_p2c_flseq (which treat a fixed  *)
(* interval): P3N_SEQ_FACTS_VAR (uniform ball radius and curvature bound)  *)
(* and P3N_SHI_VAR (uniform bounds on all derivatives of Rm, from time 0). *)
(* ========================================================================= *)

let P3N_SEQ_FACTS_VAR = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m (e:num->real) CM N.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!n. e n <= &1) /\ &0 <= CM /\ m + 2 <= N /\
     (!n s. N <= n /\ &0 <= s /\ s < e n
            ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + &0 / Q n) (t n + s / Q n) /\
                (!z. z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u)))
     ==> ?r Kc. &0 < r /\ &0 < Kc /\
                !n s. N <= n /\ &0 <= s /\ s < e n
                      ==> riemannian_metric (restrict_atlas atlas (W (m + 2)))
                            (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas phi n s)) /\
                          (!xM. xM IN W m
                                ==> mfd_ball (subtopology top (W (m + 2)),
                                              restrict_atlas atlas (W (m + 2)))
                                      (restrict_metric atlas (W (m + 2))
                                         (p2cv_P V t Q atlas phi n s)) xM r
                                    SUBSET W (m + 1) /\
                                    compact_in (subtopology top (W (m + 2)))
                                      (subtopology top (W (m + 2)) closure_of
                                       mfd_ball (subtopology top (W (m + 2)),
                                                 restrict_atlas atlas (W (m + 2)))
                                         (restrict_metric atlas (W (m + 2))
                                            (p2cv_P V t Q atlas phi n s)) xM r)) /\
                          (!y. y IN W (m + 2)
                               ==> mfd_rm_norm (restrict_atlas atlas (W (m + 2)))
                                     (restrict_metric atlas (W (m + 2))
                                        (p2cv_P V t Q atlas phi n s)) y <= Kc)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "qf0")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `&0 < exp(&8 * CM)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `W:num->B->bool`; `m:num`; `sqrt(&2 * exp(&8 * CM))`] P2CQ_BALLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls"))) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv")) P2CQ_PB_CURV THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `sqrt C0 * CM + &1`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `b' = (s + (e:num->real) n) / &2` THEN
  SUBGOAL_THEN `s < b' /\ b' < (e:num->real) n /\ &0 < b' /\ b' <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b'" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1`)) (concl th) &&
      not (can (find_term (fun t -> t = `CM:real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) (m + 2)))
      (t n + &0 / Q n) (t n + b' / Q n) /\
    (!s' z. &0 <= s' /\ s' <= b' /\ z IN IMAGE (phi n) (W (m + 2))
            ==> p3_vrm (V n) (t n + s' / Q n) z <= CM * Q n)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "per" (MP_TAC o SPECL [`n:num`; `b':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      USE_THEN "per" (MP_TAC o SPECL [`n:num`; `s':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) (m + 2))
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                                      ((W:num->B->bool) (m + 2)))
      (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas (phi:num->B->A) n s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `xM:B` THEN DISCH_TAC THEN USE_THEN "balls" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:B`; `v:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN (W:num->B->bool) (m + 2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(W:num->B->bool) (m + 1) SUBSET W (m + 2)` MP_TAC THENL
       [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) (m + 2)`; `g0:B->real^3^3`;
                   `p2cv_P V t Q atlas (phi:num->B->A) n s`;
                   `sqrt(&2 * exp(&8 * CM)) pow 2`; `z:B`] P2CQ_RESTRICT_QF) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:real^3` THEN
    SUBGOAL_THEN `sqrt(&2 * exp(&8 * CM)) pow 2 = &2 * exp(&8 * CM)` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                   `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m + 2`;
                   `&0`; `b':real`; `CM:real`; `n:num`; `s:real`; `z:B`; `u:real^3`]
                  P2CQ_QF_MANIFOLD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "qf0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&0 <= u dot ((g0:B->real^3^3) z ** u)` ASSUME_TAC THENL
     [USE_THEN "qf0" (MP_TAC o SPECL [`n:num`; `z:B`; `u:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(&8 * CM * b') <= exp(&8 * CM)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `CM * b' <= CM * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `pp = u dot (p2cv_P V t Q atlas (phi:num->B->A) n s z ** u)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &2 * exp(&8 * CM * b')` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pp` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&2 * exp(&8 * CM * b')) * &0 <= (&2 * exp(&8 * CM * b')) * pp` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * exp(&8 * CM * b')) * pp` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt C0 * CM` THEN REWRITE_TAC[REAL_ARITH `a <= a + &1`] THEN
  REWRITE_TAC[P2CV_P_PB] THEN USE_THEN "curv" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `b':real`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "per" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[]]);;

let P3N_SHI_VAR = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m (e:num->real) CM N c K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!n. e n <= &1) /\ &0 <= CM /\ m + 2 <= N /\
     (!n s. N <= n /\ &0 <= s /\ s < e n
            ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + &0 / Q n) (t n + s / Q n) /\
                (!z. z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c INTER W m)
     ==> !j. ?C. !n s y. N <= n /\ &0 <= s /\ s < e n /\ y IN K
                         ==> lrm_deriv_norm2 j
                               (metric_local atlas c (p2cv_P V t Q atlas phi n s)) y <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "qf0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `e:num->real`; `CM:real`; `N:num`] P3N_SEQ_FACTS_VAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `Kc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "facts"))))) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `j:num`; `N:num`] P2CQ_INIT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "init")) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + 1) /\ W (m + 1) SUBSET W (m + 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (subtopology top ((W:num->B->bool) (m + 2)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace (subtopology top ((W:num->B->bool) (m + 2))) = W (m + 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(W:num->B->bool) (m + 2) SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Cl. !n s xM. N <= n /\ &0 <= s /\ s < (e:num->real) n /\ xM IN (W:num->B->bool) m
                  ==> rfa_rmd2 j (restrict_atlas atlas (W (m + 2)))
                        (restrict_metric atlas (W (m + 2))
                           (p2cv_P V t Q atlas (phi:num->B->A) n s)) xM <= Cl`
  (X_CHOOSE_THEN `Cl1:real` (LABEL_TAC "Cl1")) THENL
   [MP_TAC(ISPEC `(:B)` RFA_P2_THM_3_29) THEN REWRITE_TAC[P2_THM_3_29_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `Kc + abs K0`; `r:real`; `&1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "Cl")) THEN EXISTS_TAC `Cl:real` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `xM:B`] THEN STRIP_TAC THEN
    ABBREV_TAC `b' = (s + (e:num->real) n) / &2` THEN
    SUBGOAL_THEN `s < b' /\ b' < (e:num->real) n /\ &0 < b' /\ b' <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "b'" THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&1`)) (concl th) &&
        not (can (find_term (fun t -> t = `CM:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_persists ((V:num->p2cvv3) n)
                    (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) (m + 2)))
                    (t n + &0 / Q n) (t n + b' / Q n)` ASSUME_TAC THENL
     [USE_THEN "per" (MP_TAC o SPECL [`n:num`; `b':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (MP_TAC o C MP (ASSUME `(xM:B) IN (W:num->B->bool) m`) o SPEC `xM:B`) ASSUME_TAC)) THEN
    STRIP_TAC THEN
    USE_THEN "Cl" (MP_TAC o SPECL
     [`subtopology top ((W:num->B->bool) (m + 2))`;
      `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
      `&0`; `b':real`;
      `\r. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
             (p2cv_P V t Q atlas (phi:num->B->A) n r)`; `xM:B`]) THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_LE_REFL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_FROM THEN
        EXISTS_TAC `b':real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        MATCH_MP_TAC P2CV_HYP_ONE THEN
        MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`tt:real`; `yy:B`] THEN STRIP_TAC THEN
        USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `tt:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
        DISCH_THEN(MP_TAC o SPEC `yy:B`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`i:num`; `yy:B`] THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM rfa_rmd2] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN
        CONJ_TAC THENL
         [USE_THEN "init" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(MP_TAC o SPECL [`j:num`; `s:real`; `xM:B`]) THEN REWRITE_TAC[rfa_rmd2] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
      MP_TAC(ISPECL [`subtopology top ((W:num->B->bool) (m + 2))`;
                     `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
                     `restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
                        (p2cv_P V t Q atlas (phi:num->B->A) n (&0))`; `xM:B`; `r / &2`]
                    MFD_CENTRE_IN_BALL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s y. N <= n /\ &0 <= s /\ s < (e:num->real) n /\ y IN K
            ==> chart_inv (c:(B->bool)#(B->real^3)) y IN (W:num->B->bool) m /\
                lrm_deriv_norm2 j (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s)) y =
                rfa_rmd2 j (restrict_atlas atlas (W (m + 2)))
                  (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas phi n s))
                  (chart_inv c y)`
  (LABEL_TAC "tr") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) y IN FST c /\
                  chart_inv c y IN (W:num->B->bool) m /\ SND c (chart_inv c y) = y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(K:real^3->bool) SUBSET IMAGE (SND(c:(B->bool)#(B->real^3)))
                                              (FST c INTER (W:num->B->bool) m)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `xx:B` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) (m + 2)`; `p2cv_P V t Q atlas (phi:num->B->A) n s`;
                   `c:(B->bool)#(B->real^3)`; `chart_inv (c:(B->bool)#(B->real^3)) y`;
                   `j:num`] P2CQ_REGION_RMD2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_SIMP_TAC[];
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  EXISTS_TAC `Cl1:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "tr" (MP_TAC o SPECL [`n:num`; `s:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  USE_THEN "Cl1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_QF_BOUNDS_VAR = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m (e:num->real) CM N c K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!n. e n <= &1) /\ &0 <= CM /\ m <= N /\
     (!n s. N <= n /\ &0 <= s /\ s < e n
            ==> rfs_persists (V n) (IMAGE (phi n) (W m)) (t n + &0 / Q n) (t n + s / Q n) /\
                (!z. z IN IMAGE (phi n) (W m) ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W m
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c INTER W m)
     ==> ?Lm. &0 <= Lm /\
              !n s y v. N <= n /\ &0 <= s /\ s < e n /\ y IN K
                        ==> norm v pow 2 <=
                            Lm * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v)) /\
                            v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v) <=
                            Lm * norm v pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "qf0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                 `K:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0b"))))) THEN
  ABBREV_TAC `E = exp(&8 * CM)` THEN
  SUBGOAL_THEN `&1 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC P2CV_EXP_GE1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv c0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  EXISTS_TAC `&2 * E * (inv c0 + C0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m)
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b' = (s + (e:num->real) n) / &2` THEN
  SUBGOAL_THEN `s < b' /\ b' < (e:num->real) n /\ &0 < b' /\ b' <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b'" THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1`)) (concl th) &&
      not (can (find_term (fun t -> t = `CM:real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))
      (t n + &0 / Q n) (t n + b' / Q n) /\
    (!s' z. &0 <= s' /\ s' <= b' /\ z IN IMAGE (phi n) (W m)
            ==> p3_vrm (V n) (t n + s' / Q n) z <= CM * Q n)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "per" (MP_TAC o SPECL [`n:num`; `b':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      USE_THEN "per" (MP_TAC o SPECL [`n:num`; `s':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v) <=
    exp(&8 * CM * (b' - &0)) *
    (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v)) /\
    v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v) <=
    exp(&8 * CM * (b' - &0)) *
    (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[P2CV_P_PB] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2CV_QF_ALL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `(W:num->B->bool) m`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v) /\
    &0 <= v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CV_MF_QF_NONNEG THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&8 * CM * (b' - &0)) <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_MONO_LE; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `CM * b' <= CM * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v) <=
    E * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v)) /\
    v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v) <=
    E * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n s) y ** v))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `exp(&8 * CM * (b' - &0)) *
                  (v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n (&0)) y ** v))`;
      EXISTS_TAC `exp(&8 * CM * (b' - &0)) *
                  (v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s) y ** v))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) y IN (W:num->B->bool) m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                    (FST c INTER (W:num->B->bool) m)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n (&0)) y ** v) <=
    &3 / &2 * (v dot (metric_local atlas c (g0:B->real^3^3) y ** v)) /\
    v dot (metric_local atlas c g0 y ** v) <=
    &2 * (v dot (metric_local atlas c (p2cv_P V t Q atlas phi n (&0)) y ** v))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CV_ML_QF_MONO THEN X_GEN_TAC `u:real^3` THEN
    USE_THEN "qf0" (MP_TAC o SPECL [`n:num`; `chart_inv (c:(B->bool)#(B->real^3)) y`;
                                    `u:real^3`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);
    ALL_TAC] THEN
  USE_THEN "g0b" (STRIP_ASSUME_TAC o C MP (ASSUME `(y:real^3) IN K`) o
                  SPECL [`y:real^3`; `v:real^3`]) THEN
  SUBGOAL_THEN `&0 <= C0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2CV_QF_ARITH THEN
  EXISTS_TAC `v dot (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n (&0)) y ** v)` THEN
  EXISTS_TAC `v dot (metric_local atlas c (g0:B->real^3^3) y ** v)` THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2]);;

(* ========================================================================= *)
(* Links between the rescaled coordinate flows p3n_cfl and                   *)
(* the single-flow families p2cv_pb of pc_p2c_flloc on the base manifold    *)
(* (euclidean,open_set_atlas UNIV) with the identity chart, and the         *)
(* persistence of open subregions (P3N_PERSIST_SUB).                         *)
(* ========================================================================= *)

let P3N_PULLBACK_OSA = prove
 (`!atlas (e:real^N->A) (g:A->real^N^N) y.
     mfd_pullback_metric (open_set_atlas (:real^N)) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;

let P3N_CFL_PB = prove
 (`!(hs:(A)rfs_history) Phi ts Q s.
     p3n_cfl hs Phi ts Q s = p2cv_pb (rfs_view hs) ts Q (open_set_atlas (:real^3)) Phi s`,
  REWRITE_TAC[p3n_cfl; p2cv_pb; P3N_PULLBACK_OSA]);;

let P3N_CFL_LOCAL = prove
 (`!(hs:(A)rfs_history) Phi ts Q s.
     metric_local (open_set_atlas (:real^3)) ((:real^3),(\x:real^3. x))
       (p2cv_pb (rfs_view hs) ts Q (open_set_atlas (:real^3)) Phi s) =
     p3n_cfl hs Phi ts Q s`,
  REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; P3N_CFL_PB]);;

let P3N_OSA_CHART_IMAGE = prove
 (`!U:real^N->bool. IMAGE (SND((:real^N),(\x:real^N. x))) (FST((:real^N),(\x:real^N. x)) INTER U) = U`,
  REWRITE_TAC[FST; SND; INTER_UNIV; IMAGE_ID]);;

let P3N_OSA_IN = prove
 (`((:real^N),(\x:real^N. x)) IN open_set_atlas (:real^N)`,
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES]);;

let P3N_REGULAR_FROM_SMOOTH = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2c_regular_view V ==> p2cz_from_smooth V`,
  REWRITE_TAC[p2c_regular_view; p2cz_from_smooth] THEN SIMP_TAC[]);;

let P3N_MPULLBACK_ID = prove
 (`!(G:real^N->real^N^N) z. mpullback (\x. x) G z = G z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^N. x) (at z) = (\x. x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P3N_PULLBACK_OSA_ID = prove
 (`!(g:real^N->real^N^N) z.
     rfs_pullback (open_set_atlas (:real^N)) (\x. x) g z = g z`,
  REWRITE_TAC[rfs_pullback; GEOL_EUCLID_FACTS; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  REWRITE_TAC[o_DEF; ETA_AX; P3N_MPULLBACK_ID]);;

let P3N_OSA_PARAM_ID = prove
 (`mfd_param euclidean (open_set_atlas (:real^N)) (:real^N) (\x:real^N. x)`,
  REWRITE_TAC[mfd_param; IMAGE_ID] THEN EXISTS_TAC `\x:real^N. x` THEN
  MATCH_MP_TAC MFD_DIFFEO_ID THEN
  REWRITE_TAC[GEOL_EUCLID_FACTS; OPEN_IN_EUCLIDEAN; OPEN_UNIV] THEN
  REWRITE_TAC[GSYM OPEN_IN; TOPSPACE_EUCLIDEAN; OPEN_IN_TOPSPACE]);;

let P3N_STD_SEC = prove
 (`!g0 (G:real->real^3->real^3^3) t1.
     p3_std_flow g0 (&1) G /\ t1 < &1
     ==> ?K. &0 <= K /\
             !t y u v. &0 <= t /\ t <= t1 /\ ~collinear {vec 0,u,v}
                       ==> abs(lsectional (G t) y u v) <= K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_std_flow; p3_partial_std] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t1:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  EXISTS_TAC `abs K` THEN REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) t`; `(:real^3)`; `\x:real^3. x`; `&1`;
                 `y:real^3`; `u:real^3`; `v:real^3`] P3N_PULLBACK_SEC_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; P3N_OSA_PARAM_ID; IN_UNIV; REAL_LT_01] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `&1`;
                   `G:real->real^3->real^3^3`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P3N_PULLBACK_OSA_ID; MATRIX_CMUL_LID; ETA_AX; REAL_DIV_1] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= abs k ==> a <= b ==> a <= abs k`) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= k ==> b <= abs k`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The window lemma (P3N_WINDOW).  For a p2cv_hyp sequence                   *)
(* whose regions W (m + 2) persist with abs Rm <= CM Q on windows [0,e n),   *)
(* e n <= 1, C^0 convergence of the chart representatives at moving bases  *)
(* b n to a fixed metric field M near K' gives C^kk closeness to M on K for  *)
(* s in [b n,b n + lam), eventually.  By contradiction: along a bad         *)
(* sequence the representatives at the bad times have uniformly bounded    *)
(* jets (P3N_SHI_VAR, P3N_QF_BOUNDS_VAR, P2CQ_JETS0, P3N_HAM_VAR), move    *)
(* little in C^0 from the bases (P3N_LIP_ENTRY), hence converge to M in    *)
(* every C^k (P3N_SEQ_LCK).                                                  *)
(* ========================================================================= *)

let P3N_PERSIST_SUB = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q b W1.
     p2cv_one V (top,atlas) Wb f t0 q /\ &0 <= b /\
     rfs_persists V (IMAGE f Wb) (t0 + &0 / q) (t0 + b / q) /\
     open_in top W1 /\ W1 SUBSET Wb
     ==> rfs_persists V (IMAGE f W1) (t0 + &0 / q) (t0 + b / q)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:p2cvv3) u) (rfs_vatlas V u) /\
                open_in (rfs_vtop V u) (IMAGE (f:B->A) Wb)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_AT THEN
    MAP_EVERY EXISTS_TAC [`t0 + &0 / q`; `t0 + b / q`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t0 + (q * (u - t0)) / q = u` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `&0`; `b:real`;
                 `q * (u - t0)`] P2CV_PHI_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `&0 < u - t0 /\ u - t0 <= b / q` MP_TAC THENL
     [UNDISCH_TAC `t0 + &0 / q < u` THEN UNDISCH_TAC `u <= t0 + b / q` THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < q * (u - t0) /\ q * (u - t0) <= b` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `u - t0 <= b / q` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:A->B` MP_TAC) THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `IMAGE (f:B->A) Wb` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAPS_MAP] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphic_maps")) (concl th))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:B->A`; `subtopology (top:B topology) Wb`;
                 `subtopology (rfs_vtop (V:p2cvv3) u) (IMAGE (f:B->A) Wb)`;
                 `W1:B->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(W1:B->bool) SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `W1:B->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P3N_LFROM_BILIN_CONT = prove
 (`!U a b (G:real->real^N->real^N^N) y t u v.
     rfa_lfrom U a b G /\ y IN U /\ t < b
     ==> (\s. u dot (G s y ** v)) real_continuous_on real_interval[a,t]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`\(G0:real^N->real^N^N) y. u dot (G0 y ** v)`; `U:real^N->bool`;
                 `a:real`; `b:real`; `G:real->real^N->real^N^N`; `y:real^N`; `t:real`]
         RFA_LFROM_SLICE_CONT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
    SUBGOAL_THEN
     `(\z. lift(u dot ((G':real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** v))) =
      (\m:real^(N,N)finite_prod. lift(u dot ((matrify m:real^N^N) ** v))) o
      (\z. vectorize(G' (drop(fstcart z)) (sndcart z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT];
    SIMP_TAC[]]);;

let P3N_LIP_ENTRY0 = prove
 (`!U b (G:real->real^N->real^N^N) y t2 D Lm p q.
     rfa_lfrom U (&0) b G /\ y IN U /\ &0 < t2 /\ t2 < b /\ &0 <= D /\ &0 <= Lm /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
     (!t v. &0 < t /\ t <= t2
            ==> lrm_deriv_norm2 0 (G t) y <= D /\ v dot (G t y ** v) <= Lm * (v dot v))
     ==> abs(G t2 y$p$q - G (&0) y$p$q) <= (&8 * &(dimindex(:N)) * sqrt D * Lm) * t2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = &8 * &(dimindex(:N)) * sqrt D * Lm` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lricci_flow U (&0) b (G:real->real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfa_lfrom]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. abs((G:real->real^N->real^N^N) t2 y$p$q - G s y$p$q)`; `t2:real`;
                 `C * t2`] P2CV_RCONT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ABS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `&0`; `b:real`; `G:real->real^N->real^N^N`; `y:real^N`;
                   `t2:real`; `basis p:real^N`; `basis q:real^N`] P3N_LFROM_BILIN_CONT) THEN
    ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o BETA_RULE) THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (t2 - tau)` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC P3N_LIP_ENTRY THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `&0`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `v:real^N`]) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let P3N_WINDOW = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m (b:num->real) (e:num->real)
    CM N c K K' (M:real^3->real^3^3).
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!n. &0 <= b n /\ e n <= &1) /\ &0 <= CM /\ m + 2 <= N /\
     (!n s. N <= n /\ &0 <= s /\ s < e n
            ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + &0 / Q n) (t n + s / Q n) /\
                (!z. z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas /\ compact K /\ compact K' /\ K SUBSET K' /\
     K' SUBSET IMAGE (SND c) (FST c INTER W m) /\
     (!z. z IN K ==> ?r. &0 < r /\ ball(z,r) SUBSET K') /\
     metric_field (IMAGE (SND c) (FST c INTER W m)) M /\
     (!ep. &0 < ep
           ==> ?N'. !n y p q. N' <= n /\ y IN K' /\ 1 <= p /\ p <= 3 /\ 1 <= q /\ q <= 3
                    ==> abs(metric_local atlas c (p2cv_P V t Q atlas phi n (b n)) y$p$q - M y$p$q)
                        < ep)
     ==> !kk dd. &0 < dd
                 ==> ?lam N'. &0 < lam /\
                       !n s y. N' <= n /\ b n <= s /\ s < e n /\ s < b n + lam /\ y IN K
                               ==> lck_dist2 kk M (metric_local atlas c (p2cv_P V t Q atlas phi n s)) y
                                   < dd`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "hyp" (el 0 cs) THEN LABEL_TAC "be" (el 1 cs) THEN
    ASSUME_TAC (el 2 cs) THEN ASSUME_TAC (el 3 cs) THEN
    LABEL_TAC "per" (el 4 cs) THEN LABEL_TAC "qf0" (el 5 cs) THEN
    ASSUME_TAC (el 6 cs) THEN ASSUME_TAC (el 7 cs) THEN ASSUME_TAC (el 8 cs) THEN
    ASSUME_TAC (el 9 cs) THEN ASSUME_TAC (el 10 cs) THEN LABEL_TAC "ball" (el 11 cs) THEN
    ASSUME_TAC (el 12 cs) THEN LABEL_TAC "c0" (el 13 cs)) THEN
  USE_THEN "hyp" (STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m))`
  ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + 2) /\ open_in top (W m)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kk:num`; `dd:real`] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!i:num. ?n s y. N + i <= n /\ (b:num->real) n <= s /\ s < (e:num->real) n /\
                    s < b n + inv(&i + &1) /\ (y:real^3) IN K /\
                    dd <= lck_dist2 kk (M:real^3->real^3^3)
                            (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s)) y`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN USE_THEN "neg" (MP_TAC o SPECL [`inv(&i + &1)`; `N + i:num`]) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &i + &1`; NOT_FORALL_THM; NOT_IMP;
                REAL_NOT_LT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` (X_CHOOSE_THEN `ss:num->real`
    (X_CHOOSE_THEN `yy:num->real^3` (LABEL_TAC "bad")))) THEN
  SUBGOAL_THEN
   `!i. N <= (nn:num->num) i /\ i <= nn i /\ (b:num->real) (nn i) <= (ss:num->real) i /\
        ss i < (e:num->real) (nn i) /\ ss i < b(nn i) + inv(&i + &1) /\
        (yy:num->real^3) i IN K /\ &0 <= b (nn i) /\ e (nn i) <= &1 /\
        dd <= lck_dist2 kk (M:real^3->real^3^3) (metric_local atlas c
                (p2cv_P V t Q atlas (phi:num->B->A) (nn i) (ss i))) (yy i)`
  (LABEL_TAC "bd") THENL
   [GEN_TAC THEN USE_THEN "bad" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    USE_THEN "be" (STRIP_ASSUME_TAC o SPEC `(nn:num->num) i`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `en = \i:num. ((ss:num->real) i + (e:num->real) ((nn:num->num) i)) / &2` THEN
  SUBGOAL_THEN `!i. (ss:num->real) i < (en:num->real) i /\ en i < (e:num->real) ((nn:num->num) i) /\
                    &0 < en i /\ en i <= &1 /\ &0 <= ss i`
  (LABEL_TAC "en") THENL
   [GEN_TAC THEN EXPAND_TAC "en" THEN USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. N <= n /\ &0 <= s /\ s < (e:num->real) n
          ==> p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m) ((phi:num->B->A) n)
                       (t n) (Q n) /\
              p2cv_one (V n) (top,atlas) (W (m + 2)) (phi n) (t n) (Q n) /\
              rfs_persists (V n) (IMAGE (phi n) (W m)) (t n + &0 / Q n) (t n + s / Q n) /\
              (!z. z IN IMAGE (phi n) (W m) ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)`
  (LABEL_TAC "perm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m)
                           ((phi:num->B->A) n) (t n) (Q n) /\
                  p2cv_one (V n) (top,atlas) (W (m + 2)) (phi n) (t n) (Q n)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "per" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3N_PERSIST_SUB THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `(W:num->B->bool) (m + 2)`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `e:num->real`; `CM:real`; `N:num`; `c:(B->bool)#(B->real^3)`;
                 `K':real^3->bool`] P3N_QF_BOUNDS_VAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "perm" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);
      REPEAT STRIP_TAC THEN USE_THEN "qf0" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `Lm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qfb")))] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `e:num->real`; `CM:real`; `N:num`; `c:(B->bool)#(B->real^3)`;
                 `K':real^3->bool`] P3N_SHI_VAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "be" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(LABEL_TAC "shi")] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `c:(B->bool)#(B->real^3)`; `K':real^3->bool`; `N:num`] P2CQ_JETS0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(LABEL_TAC "jet0")] THEN
  SUBGOAL_THEN
   `!i. rfs_persists ((V:num->p2cvv3) ((nn:num->num) i))
          (IMAGE ((phi:num->B->A) (nn i)) ((W:num->B->bool) m))
          (t (nn i) + &0 / Q (nn i)) (t (nn i) + (en:num->real) i / Q (nn i)) /\
        p2cv_one (V (nn i)) (top,atlas) (W m) (phi (nn i)) (t (nn i)) (Q (nn i))`
  (LABEL_TAC "pi") THENL
   [GEN_TAC THEN USE_THEN "perm" (MP_TAC o SPECL [`(nn:num->num) i`; `(en:num->real) i`]) THEN
    ANTS_TAC THENL
     [USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                 `K':real^3->bool`;
                 `\i:num s:real. metric_local atlas (c:(B->bool)#(B->real^3))
                                   (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) s)`;
                 `en:num->real`; `&1`; `Lm:real`] P3N_HAM_VAR) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_LFLOW THEN
      EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `(en:num->real) i`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      MP_TAC(ISPECL [`(V:num->p2cvv3) ((nn:num->num) i)`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) m`;
                     `(phi:num->B->A) ((nn:num->num) i)`; `(t:num->real) ((nn:num->num) i)`;
                     `(Q:num->real) ((nn:num->num) i)`; `&0`; `(en:num->real) i`; `&0`;
                     `(en:num->real) i`; `c:(B->bool)#(B->real^3)`] P2CV_EXT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `ee:real` (X_CHOOSE_THEN
        `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`ee:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval(lift(&0 - ee),lift((en:num->real) i + ee)) PCROSS
                    IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`i:num`; `s:real`; `y:real^3`; `p:num`; `q:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2CV_ENTRY_BOUNDS THEN
      EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
        REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `(en:num->real) i`] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `v:real^3` THEN USE_THEN "qfb" (MP_TAC o SPECL
        [`(nn:num->num) i`; `s:real`; `y:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN
        USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:num`; `s:real`; `y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      USE_THEN "qfb" (MP_TAC o SPECL [`(nn:num->num) i`; `s:real`; `y:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN
        USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      X_GEN_TAC `j:num` THEN USE_THEN "shi" (X_CHOOSE_TAC `C:real` o SPEC `j:num`) THEN
      EXISTS_TAC `C:real` THEN MAP_EVERY X_GEN_TAC [`i:num`; `s:real`; `y:real^3`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN
      SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`k:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
      USE_THEN "jet0" (MP_TAC o SPECL [`k:num`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_3]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(nn:num->num) i - N`; `l:num list`; `y:real^3`]) THEN
      SUBGOAL_THEN `N + (nn:num->num) i - N = nn i` SUBST1_TAC THENL
       [USE_THEN "bd" (MP_TAC o SPEC `i:num`) THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "jets")] THEN
  USE_THEN "shi" (X_CHOOSE_TAC `D0:real` o SPEC `0`) THEN
  ABBREV_TAC `Lip = &8 * &(dimindex(:3)) * sqrt(abs D0) * Lm` THEN
  SUBGOAL_THEN `&0 <= Lip` ASSUME_TAC THENL
   [EXPAND_TAC "Lip" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y p q. y IN K' /\ 1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
      ==> abs(metric_local atlas c
                (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) ((ss:num->real) i)) y$p$q -
              metric_local atlas c (p2cv_P V t Q atlas phi (nn i) ((b:num->real) (nn i))) y$p$q)
          <= Lip * inv(&i + &1)`
  (LABEL_TAC "lip") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "bd" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    USE_THEN "en" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s v. &0 <= s /\ s <= (ss:num->real) i
            ==> lrm_deriv_norm2 0 (metric_local atlas c
                  (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) s)) y <= abs D0 /\
                v dot (metric_local atlas c (p2cv_P V t Q atlas phi (nn i) s) y ** v) <= Lm * (v dot v)`
    (LABEL_TAC "bds") THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= d ==> x <= abs d`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM NORM_POW_2] THEN
        USE_THEN "qfb" (MP_TAC o SPECL [`(nn:num->num) i`; `s:real`; `y:real^3`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lip * ((ss:num->real) i - (b:num->real) ((nn:num->num) i))` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `&0 < (b:num->real) ((nn:num->num) i)` THENL
     [EXPAND_TAC "Lip" THEN REWRITE_TAC[DIMINDEX_3] THEN
      MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                     `&0`; `(en:num->real) i`;
                     `\s. metric_local atlas (c:(B->bool)#(B->real^3))
                            (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) s)`;
                     `y:real^3`; `(b:num->real) ((nn:num->num) i)`; `(ss:num->real) i`;
                     `abs D0`; `Lm:real`; `p:num`; `q:num`] P3N_LIP_ENTRY) THEN
      REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_LFLOW THEN
        EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[DIMINDEX_3];
        ASM_MESON_TAC[DIMINDEX_3];
        REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "bds" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:num->real) ((nn:num->num) i) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    ASM_CASES_TAC `(ss:num->real) i = &0` THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
    EXPAND_TAC "Lip" THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                   `(en:num->real) i`;
                   `\s. metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) s)`;
                   `y:real^3`; `(ss:num->real) i`;
                   `abs D0`; `Lm:real`; `p:num`; `q:num`] P3N_LIP_ENTRY0) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_LFROM THEN
      EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "bds" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ep. &0 < ep
         ==> ?N1. !i y p q. N1 <= i /\ y IN K' /\ 1 <= p /\ p <= dimindex(:3) /\
                            1 <= q /\ q <= dimindex(:3)
                            ==> abs(metric_local atlas c
                                  (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i)
                                     ((ss:num->real) i)) y$p$q - (M:real^3->real^3^3) y$p$q) < ep`
  (LABEL_TAC "c0i") THENL
   [X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
    USE_THEN "c0" (MP_TAC o SPEC `ep / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    MP_TAC(SPEC `ep / &2 / (Lip + &1)` REAL_ARCH_INV) THEN
    SUBGOAL_THEN `&0 < ep / &2 / (Lip + &1)` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N3:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N2 + N3:num` THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `y:real^3`; `p:num`; `q:num`] THEN STRIP_TAC THEN
    USE_THEN "bd" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    USE_THEN "lip" (MP_TAC o SPECL [`i:num`; `y:real^3`; `p:num`; `q:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(nn:num->num) i`; `y:real^3`; `p:num`; `q:num`] o
      check (fun th -> can (find_term ((=) `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM DIMINDEX_3] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&i + &1) < ep / &2 / (Lip + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N3)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Lip * inv(&i + &1) < ep / &2` MP_TAC THENL
     [SUBGOAL_THEN `&0 < Lip + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(Lip + &1) * inv(&i + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `(Lip + &1) * (ep / &2 / (Lip + &1))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `(Lip + &1) * (ep / &2 / (Lip + &1)) = ep / &2` SUBST1_TAC THENL
           [UNDISCH_TAC `&0 < Lip + &1` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                 `K:real^3->bool`; `K':real^3->bool`; `M:real^3->real^3^3`;
                 `\i. metric_local atlas (c:(B->bool)#(B->real^3))
                        (p2cv_P V t Q atlas (phi:num->B->A) ((nn:num->num) i) ((ss:num->real) i))`]
                P3N_SEQ_LCK) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `i:num` THEN
      USE_THEN "bd" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      USE_THEN "en" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      USE_THEN "pi" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `(en:num->real) i`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`k:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
      USE_THEN "jets" (MP_TAC o SPECL [`k:num`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `B:real`)] THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `0`] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "en" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`kk:num`; `dd:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  USE_THEN "bd" (STRIP_ASSUME_TAC o SPEC `N4:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N4:num`; `(yy:num->real^3) N4`] o
    check (fun th -> can (find_term ((=) `N4:num`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The contradiction sequence as a p2cv_hyp sequence of                      *)
(* pc_p2c_flloc with J = {0}: the curvature of the slices at the event      *)
(* times is O(Q) on every fixed ball (P3N_CAP_CURV0, from the cap closeness  *)
(* and P3N_BASE_RM), and every subsequence satisfies p2cv_hyp              *)
(* (P3N_SEQ_HYP, from P3N_SLICE0).                                           *)
(* ========================================================================= *)

let P3N_CFL_FIELD = prove
 (`!(hs:(A)rfs_history) Phi ts Q s U.
     smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s / Q))
                           (rfs_vatlas (rfs_view hs) (ts + s / Q)) /\
     riemannian_metric (rfs_vatlas (rfs_view hs) (ts + s / Q))
                       (rfs_vmetric (rfs_view hs) (ts + s / Q)) /\
     mfd_param (rfs_vtop (rfs_view hs) (ts + s / Q)) (rfs_vatlas (rfs_view hs) (ts + s / Q))
               U Phi /\ &0 < Q
     ==> metric_field U (p3n_cfl hs Phi ts Q s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3n_cfl] THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
  EXISTS_TAC `rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)` THEN ASM_REWRITE_TAC[]);;

let P3N_G0_SEC_BOUND = prove
 (`!g0 A0 K. p3_std_initial g0 A0 /\ compact K
             ==> ?K0. &0 <= K0 /\
                      !y u v. y IN K /\ ~collinear {vec 0,u,v}
                              ==> abs(lsectional g0 y u v) <= K0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (:real^3) g0` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_OSA_RIEM THEN ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`open_set_atlas (:real^3)`; `g0:real^3->real^3^3`; `(:real^3)`;
                 `\x:real^3. x`; `K:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P3N_OSA_IN; IMAGE_ID; SUBSET_UNIV] THEN ASM_MESON_TAC[p3_std_initial];
    ALL_TAC] THEN
  REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`{&0}`; `(:real^3)`; `K:real^3->bool`; `\t:real. (g0:real^3->real^3^3)`;
                 `inv c0`; `0`] P2CJ_RMD2_FROM_JB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; IN_SING] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `norm(v:real^3) pow 2 = inv c0 * (c0 * norm v pow 2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < c0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_JB_FIXED THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
      MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN EXISTS_TAC `sqrt(abs C)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lrm_deriv_norm2 0 (g0:real^3->real^3^3) y)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[IN_UNIV];
    MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let P3N_CAP_CURV0 = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_modulus md /\ p3_std_initial g0 A0
     ==> !R. ?CM N. !n y. N <= n /\ p3_std_dist g0 y < R
                          ==> Phi n y IN topspace(rfs_vtop (rfs_view (hs n)) (ts n)) /\
                              p3_vrm (rfs_view (hs n)) (ts n) (Phi n y) <= CM * Q n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `R:real` THEN
  ABBREV_TAC `R1 = max R (&1)` THEN
  SUBGOAL_THEN `&0 < R1 /\ R <= R1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R1:real`] P3N_STD_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                 `cball(vec 0:real^3,p3s_rad_rinv g0 R1)`] P3N_G0_SEC_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  MP_TAC(SPEC `K0:real` P3N_BASE_RM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "brm"))) THEN
  ABBREV_TAC `dd = min (min eta (&1 / &2)) (inv(R1 + &1))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= eta /\ dd <= &1 / &2 /\ R1 < inv dd` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(R1 + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dd /\ dd <= eta /\ dd <= &1 / &2 /\ dd <= inv(R1 + &1)`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `R1 + &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`]
                P3N_SEQ_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "cap")) THEN
  MP_TAC(SPEC `R1:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MAP_EVERY EXISTS_TAC [`K0 + &1`; `N1 + N2:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`;
                 `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `U = {x:real^3 | --(inv((dl:num->real->real) n (ts n))) <
                               A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `mfd_param (hs_top ((hs:num->(A)rfs_history) n) (k n)) (hs_atlas (hs n) (k n))
                  U ((Phi:num->real^3->A) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n))
                   ((hs:num->(A)rfs_history) n) (k n) (i n) (Phi n) (xi n)` THEN
    REWRITE_TAC[p3_cap_param] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top ((hs:num->(A)rfs_history) n) (k n)`; `hs_atlas ((hs:num->(A)rfs_history) n) (k n)`;
                 `U:real^3->bool`; `(Phi:num->real^3->A) n`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `R1 <= inv((dl:num->real->real) n ((ts:num->real) n))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n + &1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP P3S_A0_POS (ASSUME `p3_std_initial g0 A0`)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (g0:real^3->real^3^3) /\
                metric_field U (p3n_cfl ((hs:num->(A)rfs_history) n) ((Phi:num->real^3->A) n)
                                        ((ts:num->real) n) ((Q:num->real) n) (&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_OSA_RIEM THEN
      ASM_MESON_TAC[p3_std_initial];
      MATCH_MP_TAC P3N_CFL_FIELD THEN ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "brm" (MP_TAC o SPECL [`(hs:num->(A)rfs_history) n`; `(Phi:num->real^3->A) n`;
    `(ts:num->real) n`; `(Q:num->real) n`; `&0`; `U:real^3->bool`; `g0:real^3->real^3^3`;
    `y:real^3`]) THEN
  REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN {x | p3_std_dist g0 x < R1}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dd) g0
                (p3n_cfl ((hs:num->(A)rfs_history) n) ((Phi:num->real^3->A) n)
                         ((ts:num->real) n) ((Q:num->real) n) (&0)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_KREG_TWO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dd pow 2` THEN CONJ_TAC THENL
     [USE_THEN "cap" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

let P3N_SEQ_HYP = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (sg:num->num).
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
           p3_modulus md /\ p3_std_initial g0 A0 /\ (!m n. m < n ==> sg m < sg n)
           ==> p2cv_hyp (\n. rfs_view (hs (sg n))) (\n. Phi (sg n) (vec 0)) (\n. ts (sg n))
                        (\n. Q (sg n)) {&0} (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
                        (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (sg n))`,
  GEN_TAC THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= (sg:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. rfs_history_ok ((hs:num->(A)rfs_history) n) /\ &0 < (Q:num->real) n /\
        hs_time (hs n) (k n) = (ts:num->real) n /\
        inv(p3_hscale hf ((rp:num->real->real) n) ((dl:num->real->real) n) (ts n) pow 2) = Q n /\
        &0 < p3_hscale hf (rp n) (dl n) (ts n) /\ &0 < dl n (ts n) /\
        dl n (ts n) <= inv(&n + &1) /\ 1 <= (k:num->num) n /\ k n <= hs_count (hs n) /\
        p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n)) (hs n) (k n)
                     ((i:num->num) n) ((Phi:num->real^3->A) n) ((xi:num->real^3->real^3) n)`
  (LABEL_TAC "sq") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`;
                   `n:num`] P3N_SEQ_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
    REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
                 `\n. (hs:num->(A)rfs_history) ((sg:num->num) n)`;
                 `\n. (k:num->num) ((sg:num->num) n)`;
                 `\n. (i:num->num) ((sg:num->num) n)`;
                 `\n. (dl:num->real->real) ((sg:num->num) n)`;
                 `\n. p3_hscale hf ((rp:num->real->real) ((sg:num->num) n))
                                   ((dl:num->real->real) ((sg:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((sg:num->num) n)`;
                 `\n. (xi:num->real^3->real^3) ((sg:num->num) n)`] P3N_SLICE0) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "sq" (STRIP_ASSUME_TAC o SPEC `(sg:num->num) n`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&((sg:num->num) n) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sg:num->num`)) (concl th) &&
      not (can (find_term (fun t -> t = `m:num`)) (concl th)))) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\n. hs_time ((hs:num->(A)rfs_history) ((sg:num->num) n)) ((k:num->num) (sg n))) =
    (\n. (ts:num->real) (sg n)) /\
    (\n. inv(p3_hscale hf ((rp:num->real->real) (sg n)) ((dl:num->real->real) (sg n))
               (hs_time (hs (sg n)) (k (sg n))) pow 2)) = (\n. (Q:num->real) (sg n))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN GEN_TAC THEN
    USE_THEN "sq" (STRIP_ASSUME_TAC o SPEC `(sg:num->num) n`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[p2cv_hyp] THEN ASM_REWRITE_TAC[IS_REALINTERVAL_SING; IN_SING] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "sq" (STRIP_ASSUME_TAC o SPEC `(sg:num->num) n`) THEN
    SUBGOAL_THEN `p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n)))`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P3N_REGULAR_FROM_SMOOTH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`]
                P3N_CAP_CURV0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&m + &1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "cc0"))) THEN
  MAP_EVERY EXISTS_TAC [`CM:real`; `N1:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= (sg:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sg:num->num`)) (concl th) &&
      not (can (find_term (fun t -> t = `m:num`)) (concl th)))) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a <= b` THENL
   [ALL_TAC;
    USE_THEN "sq" (STRIP_ASSUME_TAC o SPEC `(sg:num->num) n`) THEN
    SUBGOAL_THEN `b / (Q:num->real) ((sg:num->num) n) < a / Q (sg n)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2C_VIEW_EXPAND] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `a = &0 /\ b = &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET {&0}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "cc0" (MP_TAC o SPECL [`(sg:num->num) n`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[P2C_VIEW_EXPAND] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN
    UNDISCH_TAC `(z:A) IN IMAGE ((Phi:num->real^3->A) ((sg:num->num) n))
                                {x | p3_std_dist g0 x < &m + &1}` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cc0" (MP_TAC o SPECL [`(sg:num->num) n`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* From coordinate closeness of the rescaled flows to a                      *)
(* standard flow G, and persistence of a parametrised region, to the view   *)
(* closeness p3_view_close of P3_PROP_16_5_STATEMENT (P3N_VIEW_CLOSE_INTRO). *)
(* ========================================================================= *)

let P3N_VIEW_CLOSE_INTRO = prove
 (`!(hs:(A)rfs_history) Phi ts Q (G:real->real^3->real^3^3) g0 A0 A Sj dcl U.
     p3_std_initial g0 A0 /\ &0 < A /\ &0 < Q /\ &0 < dcl /\
     (!s. s IN Sj ==> &0 <= s /\ s < &1) /\
     open U /\ {x | p3_std_dist g0 x < A} SUBSET U /\
     (!s. s IN Sj
          ==> smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s / Q))
                                    (rfs_vatlas (rfs_view hs) (ts + s / Q)) /\
              mfd_param (rfs_vtop (rfs_view hs) (ts + s / Q))
                        (rfs_vatlas (rfs_view hs) (ts + s / Q)) U Phi) /\
     (!s x. s IN Sj /\ p3_std_dist g0 x < A
            ==> lck_dist2 (rfs_kreg dcl) (G s) (p3n_cfl hs Phi ts Q s) x < dcl pow 2 / &2)
     ==> p3_view_close
           (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
           (&0) (&1) {x | p3_std_dist g0 x < A} (rfs_view hs) ts Q Phi Sj dcl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p3_view_close; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s /\ s < &1` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; REAL_DIV_1; REAL_ADD_LID;
              IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < A}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A:real`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_param (rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q))
                   (rfs_vatlas (rfs_view hs) (ts + s / Q)) U Phi` THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
    EXISTS_TAC `e':A->real^3` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    EXISTS_TAC `U:real^3->bool` THEN EXISTS_TAC `IMAGE (Phi:real^3->A) U` THEN
    ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN ASM_SIMP_TAC[GSYM OPEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose; GEOL_EUCLID_FACTS; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  EXISTS_TAC `(dcl:real) pow 2 / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX; P3N_PULLBACK_OSA] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `x:real^3`]) THEN ASM_REWRITE_TAC[p3n_cfl]);;

let P3N_PTIME_FACTS = prove
 (`!g0 (hs:(A)rfs_history) Phi ts Q m th.
     &0 <= th /\ &0 < Q
     ==> &0 <= p3n_ptime g0 hs Phi ts Q m th /\ p3n_ptime g0 hs Phi ts Q m th <= th /\
         (!s. &0 <= s /\ s < p3n_ptime g0 hs Phi ts Q m th
              ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m})
                               ts (ts + s / Q)) /\
         (!s. &0 <= s /\ s <= th /\
              rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + s / Q)
              ==> s <= p3n_ptime g0 hs Phi ts Q m th)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3n_ptime] THEN
  ABBREV_TAC `S = {&0} UNION
                  {s | &0 <= s /\ s <= th /\
                       rfs_persists (rfs_view (hs:(A)rfs_history))
                         (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + s / Q)}` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (&0) IN S /\ (!x. x IN S ==> x <= th) /\
                (!x. x IN S ==> x = &0 \/
                     (&0 <= x /\ x <= th /\
                      rfs_persists (rfs_view (hs:(A)rfs_history))
                        (IMAGE Phi {x | p3_std_dist g0 x < m}) ts (ts + x / Q))) /\
                (!s. &0 <= s /\ s <= th /\
                     rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < m})
                       ts (ts + s / Q) ==> s IN S)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_UNION; IN_SING; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[IN_UNION; IN_SING];
      GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b. !x. x IN S ==> x <= b` ASSUME_TAC THENL
   [EXISTS_TAC `th:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `s:real`] SUP_APPROACH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      can (find_term (fun t -> t = `\/`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `s < x` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`ts:real`; `ts + x / Q`] THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_LADD; REAL_LE_DIV2_EQ; REAL_LT_IMP_LE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]]);;

let P3N_IO_SUBSEQ = prove
 (`!P:num->num->bool.
     (!i N. ?j. N <= j /\ P i j)
     ==> ?J:num->num. (!m n. m < n ==> J m < J n) /\ !i. P i (J i)`,
  GEN_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->num->num`) THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(J:num->num) 0 = f 0 0 /\ !i. J(SUC i) = f (SUC i) (J i + 1)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num->num` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC i`; `(J:num->num) i + 1`]) THEN ARITH_TAC;
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let P3N_STD_SUBLEVEL = prove
 (`!g0 A0 c. p3_std_initial g0 A0 /\ &0 <= c
             ==> {x:real^3 | p3_std_dist g0 x <= c} = cball(vec 0,p3s_rad_rinv g0 c) /\
                 {x:real^3 | p3_std_dist g0 x < c} = ball(vec 0,p3s_rad_rinv g0 c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL_0; IN_BALL_0] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`;
                `p3s_rad_rinv g0 c`] P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN SIMP_TAC[]);;

