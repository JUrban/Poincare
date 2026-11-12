(* ========================================================================= *)
(* Unit pc_rf_unique_ncint: integration tools on possibly noncompact         *)
(* manifolds for integrands supported in a compact set.  Finite chart        *)
(* partitions of compact sets (RFU_COMPACT_IN_PARTITION), the time           *)
(* derivative of integrals over a compact set along a Ricci flow             *)
(* (RFU_INTEGRAL_RF_DERIV_ON, the analogue of MFD_INTEGRAL_RF_DERIV of       *)
(* pc_grg_rfint), partitions of unity on compact sets and the divergence     *)
(* theorem for compactly supported fields (RFU_DIVERGENCE_ON).               *)
(* ========================================================================= *)

needs "src/pc_grg_divthm.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Finite chart partitions of a compact measurable set, each piece inside a  *)
(* closed box contained in its chart (adapted from GRGT_COMPACT_PARTITION of *)
(* pc_grg_rfint for compact manifolds).                                      *)
(* ========================================================================= *)

let RFU_COMPACT_IN_PARTITION = prove
 (`!top atlas (S:A->bool).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top S /\ mfd_lebesgue_measurable (top,atlas) S
        ==> ?k c E p q.
              mfd_chart_partition atlas S c E /\
              (!n. ~(n IN 1..k) ==> E n = {}) /\
              (!n. n IN 1..k
                   ==> c n IN atlas /\
                       interval[p n,q n] SUBSET IMAGE (SND(c n)) (FST(c n)) /\
                       IMAGE (SND(c n)) (E n) SUBSET interval[p n,q n])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{z:A | z IN FST c /\ SND c z IN interval(a,b)} |
     c IN (atlas:((A->bool)#(A->real^N))->bool) /\
     interval[a:real^N,b] SUBSET IMAGE (SND c) (FST c)}` o
   CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `interval(a:real^N,b)`] GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_INTERVAL];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `x:A`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` THEN
      REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^N)) x`) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`c:(A->bool)#(A->real^N)`; `a:real^N`; `b:real^N`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `k = CARD(V:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> ?c p q. c IN atlas /\
                    interval[p:real^N,q] SUBSET IMAGE (SND c) (FST c) /\
                    (w:num->A->bool) i =
                    {z | z IN FST(c:(A->bool)#(A->real^N)) /\ SND c z IN interval(p,q)}`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A->bool) i IN V` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `(V:(A->bool)->bool) SUBSET
      {{z:A | z IN FST c /\ SND c z IN interval(a,b)} |
       c IN (atlas:((A->bool)#(A->real^N))->bool) /\
       interval[a:real^N,b] SUBSET IMAGE (SND c) (FST c)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `p:num->real^N` (X_CHOOSE_THEN `q:num->real^N`
     (LABEL_TAC "W")))) THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> (c:num->(A->bool)#(A->real^N)) i IN atlas /\
            open_in top ((w:num->A->bool) i) /\ w i SUBSET FST(c i) /\
            IMAGE (SND(c i)) (w i) SUBSET interval((p:num->real^N) i,q i) /\
            interval[p i,q i] SUBSET IMAGE (SND(c i)) (FST(c i))`
  (LABEL_TAC "WF") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `i IN 1..k`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((c:num->(A->bool)#(A->real^N)) i)`;
                     `SND((c:num->(A->bool)#(A->real^N)) i)`;
                     `interval((p:num->real^N) i,q i)`] GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_INTERVAL];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> !x y. x IN FST((c:num->(A->bool)#(A->real^N)) i) /\ y IN FST(c i) /\
                  SND(c i) x = SND(c i) y ==> x = y`
  (LABEL_TAC "INJ") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c:num->(A->bool)#(A->real^N)) i`] MFDM_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `E = \n. if n IN 1..k
            then {z:A | z IN (w:num->A->bool) n /\ z IN S /\
                        !j. j IN 1..k /\ j < n ==> ~(z IN w j)}
            else {}` THEN
  SUBGOAL_THEN
   `!n z. z IN (E:num->A->bool) n <=>
          n IN 1..k /\ z IN (w:num->A->bool) n /\ z IN S /\
          !j. j IN 1..k /\ j < n ==> ~(z IN w j)`
  (LABEL_TAC "EIN") THENL
   [EXPAND_TAC "E" THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (E:num->A->bool) n SUBSET (w:num->A->bool) n`
  (LABEL_TAC "ESUB") THENL
   [ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(n IN 1..k) ==> (E:num->A->bool) n = {}` (LABEL_TAC "E0") THENL
   [ASM_REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`;
    `p:num->real^N`; `q:num->real^N`] THEN
  USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "WF" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "ESUB" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(p:num->real^N) n`; `(q:num->real^N) n`]
                  INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[]] THEN
  REWRITE_TAC[mfd_chart_partition] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n IN 1..k` THENL
     [ALL_TAC;
      USE_THEN "E0" (MP_TAC o C MATCH_MP (ASSUME `~(n IN 1..k)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY; EMPTY_SUBSET]] THEN
    USE_THEN "WF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "ESUB" (ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC
     `U = UNIONS {(w:num->A->bool) j | j IN 1..k /\ j < n}` THEN
    SUBGOAL_THEN `(E:num->A->bool) n = ((w:num->A->bool) n DIFF U) INTER S` SUBST1_TAC THENL
     [EXPAND_TAC "U" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) (((w:num->A->bool) n DIFF U) INTER S) =
      IMAGE (SND(c n)) (w n DIFF U) INTER IMAGE (SND(c n)) (FST(c n) INTER S)`
    SUBST1_TAC THENL
     [USE_THEN "INJ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
      UNDISCH_TAC `(w:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S` THEN
      REWRITE_TAC[mfd_lebesgue_measurable] THEN
      DISCH_THEN(MP_TAC o SPEC `(c:num->(A->bool)#(A->real^N)) n` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      USE_THEN "WF" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((w:num->A->bool) n DIFF U) =
      IMAGE (SND(c n)) (w n) DIFF IMAGE (SND(c n)) (FST(c n) INTER U)`
    SUBST1_TAC THENL
     [USE_THEN "INJ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
      UNDISCH_TAC `(w:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c:num->(A->bool)#(A->real^N)) n`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN CONJ_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
      (ARITH_RULE `~(m:num = n) ==> m < n \/ n < m`)) THEN
    POP_ASSUM MP_TAC THEN MESON_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `n IN 1..k /\ (x:A) IN (w:num->A->bool) n` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN (E:num->A->bool) n` THEN
        USE_THEN "EIN" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(x:A) IN (E:num->A->bool) n` THEN
      USE_THEN "EIN" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `?i. i IN 1..k /\ (x:A) IN (w:num->A->bool) i` MP_TAC THENL
       [UNDISCH_TAC `(S:A->bool) SUBSET UNIONS (V:(A->bool)->bool)` THEN
        ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num`
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "MIN"))) THEN
      EXISTS_TAC `(E:num->A->bool) i` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "EIN" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "MIN" MP_TAC THEN MESON_TAC[]]]);;


(* ========================================================================= *)
(* The time derivative of the integral over a compact set of a function      *)
(* smooth up to t = a along a Ricci flow, with the evolution of the volume   *)
(* form (adapted from MFD_INTEGRAL_RF_DERIV of pc_grg_rfint for compact      *)
(* manifolds), with the integrability statements.                            *)
(* ========================================================================= *)

let RFU_INTEGRAL_RF_DERIV_ON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g:real->A->real^N^N) (e:real->A->real) e' (S:A->bool).
        compact_in top S /\ mfd_lebesgue_measurable (top,atlas) S /\
        ricci_flow_from (top,atlas) a b g /\
        pde_sfun_from atlas a b e /\ pde_sfun_from atlas a b e' /\
        (!s x. a < s /\ s < b /\ x IN topspace top
               ==> ((\r. e r x) has_real_derivative e' s x) (atreal s))
        ==> (!s. a <= s /\ s < b ==> mfd_integrable_on (top,atlas) (g s) (e s) S) /\
            (!t. a < t /\ t < b
                 ==> mfd_integrable_on (top,atlas) (g t)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x) S) /\
            (\s. mfd_integral (top,atlas) (g s) S (e s))
              real_continuous_on {s | a <= s /\ s < b} /\
            !t. a < t /\ t < b
                ==> ((\s. mfd_integral (top,atlas) (g s) S (e s))
                     has_real_derivative
                     mfd_integral (top,atlas) (g t) S
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x)) (atreal t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DE")))))) THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `S:A->bool`]
                RFU_COMPACT_IN_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
    (X_CHOOSE_THEN `q:num->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "PART")
      (CONJUNCTS_THEN2 (LABEL_TAC "E0") (LABEL_TAC "PQ")))))))) THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> lebesgue_measurable (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                       ((E:num->A->bool) n))`
  (LABEL_TAC "MEAS") THENL
   [USE_THEN "PART" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> (!s. a <= s /\ s < b
                 ==> mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                       ((e:real->A->real) s) ((c:num->(A->bool)#(A->real^N)) n)
                     absolutely_integrable_on IMAGE (SND(c n)) ((E:num->A->bool) n)) /\
            (\s. drop(integral (IMAGE (SND(c n)) (E n))
                        (mfd_chart_integrand atlas (g s) (e s) (c n))))
              real_continuous_on {s | a <= s /\ s < b} /\
            (!t. a < t /\ t < b
                 ==> mfd_chart_integrand atlas (g t)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n)
                       absolutely_integrable_on IMAGE (SND(c n)) (E n) /\
                     ((\s. drop(integral (IMAGE (SND(c n)) (E n))
                                  (mfd_chart_integrand atlas (g s) (e s) (c n))))
                      has_real_derivative
                      drop(integral (IMAGE (SND(c n)) (E n))
                             (mfd_chart_integrand atlas (g t)
                               (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n))))
                     (atreal t))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGT_PIECE_INTEGRAL THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `(p:num->real^N) n`; `(q:num->real^N) n`] THEN
    USE_THEN "PQ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "MEAS" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `J = \s. sum(1..k)
              (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                        ((E:num->A->bool) n))
                     (mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                                         ((e:real->A->real) s) (c n))))` THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> mfd_integral (top,atlas) ((g:real->A->real^N^N) s) S
                         ((e:real->A->real) s) = J s`
  (LABEL_TAC "IJ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) s`; `(e:real->A->real) s`;
                   `S:A->bool`; `(J:real->real) s`]
                  MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_integrable_on] THEN
    EXISTS_TAC `(J:real->real) s` THEN EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_integrable_on] THEN
    EXISTS_TAC
     `sum(1..k)
        (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                  ((E:num->A->bool) n))
               (mfd_chart_integrand atlas ((g:real->A->real^N^N) t)
                 (\x. (e':real->A->real) t x -
                      mfd_scalar atlas (g t) x * (e:real->A->real) t x)
                 (c n))))` THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN EXISTS_TAC `J:real->real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "IJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "J" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `J:real->real` THEN EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "IJ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((g:real->A->real^N^N) t) S
      (\x. e' t x - mfd_scalar atlas (g t) x * (e:real->A->real) t x) =
    sum(1..k)
      (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                ((E:num->A->bool) n))
             (mfd_chart_integrand atlas (g t)
               (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `\x. (e':real->A->real) t x -
                        mfd_scalar atlas ((g:real->A->real^N^N) t) x *
                        (e:real->A->real) t x`;
                   `S:A->bool`;
                   `sum(1..k)
                      (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                ((E:num->A->bool) n))
                             (mfd_chart_integrand atlas ((g:real->A->real^N^N) t)
                               (\x. (e':real->A->real) t x -
                                    mfd_scalar atlas (g t) x * (e:real->A->real) t x)
                               (c n))))`]
                  MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "J" THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Partitions of unity on a compact set (chart bumps b_j                     *)
(* combined as rho_j = (1 - b_1) ... (1 - b_(j-1)) b_j, so that the sum     *)
(* telescopes to 1 - prod (1 - b_j), which is 1 on the compact set).        *)
(* ========================================================================= *)

let RFU_TELESCOPE = prove
 (`!(b:num->real) k.
        sum(1..k) (\j. product(1..j-1) (\i. &1 - b i) * b j) =
        &1 - product(1..k) (\i. &1 - b i)`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[SUC_SUB1] THEN REAL_ARITH_TAC);;

let RFU_PARTITION_OF_UNITY_ON = prove
 (`!top atlas (K:A->bool).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top K
        ==> ?k (U:num->A->bool) (phi:num->A->real^N) (y0:num->real^N) (r:num->real)
              (rho:num->A->real).
              (!j. j IN 1..k
                   ==> (U j,phi j) IN atlas /\ &0 < r j /\
                       cball(y0 j,&2 * r j) SUBSET IMAGE (phi j) (U j) /\
                       mfd_smooth atlas (\x. lift(rho j x)) /\
                       (!x. ~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j))
                            ==> rho j x = &0)) /\
              (!x. x IN K ==> sum(1..k) (\j. rho j x) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{p:A | p IN U /\ phi p IN ball(y,r)} |
     (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
     cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` o
   CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `topspace top:A->bool`; `x:A`] MFDC_LOCAL_BALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
        (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `{p:A | p IN V /\ (psi:A->real^N) p IN ball(psi x,s)}` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC
         [`V:A->bool`; `psi:A->real^N`; `(psi:A->real^N) x`; `s:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `k = CARD(F0:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?U phi y r. (U,phi) IN atlas /\ &0 < r /\
                        cball(y:real^N,&2 * r) SUBSET IMAGE (phi:A->real^N) U /\
                        (w:num->A->bool) j = {p | p IN U /\ phi p IN ball(y,r)}`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A->bool) j IN F0` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `(F0:(A->bool)->bool) SUBSET
      {{p:A | p IN U /\ phi p IN ball(y,r)} |
       (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
       cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:num->A->bool` (X_CHOOSE_THEN `phi:num->A->real^N`
   (X_CHOOSE_THEN `y0:num->real^N` (X_CHOOSE_THEN `r:num->real`
     (LABEL_TAC "W"))))) THEN
  ABBREV_TAC
   `b = \j (x:A). if x IN U j
                  then smooth_bump ((r:num->real) j) (&2 * r j)
                                   ((phi:num->A->real^N) j x - y0 j)
                  else &0` THEN
  SUBGOAL_THEN
   `!j (x:A). j IN 1..k
              ==> &0 <= (b:num->A->real) j x /\ b j x <= &1 /\
                  (x IN (U:num->A->bool) j /\ (phi:num->A->real^N) j x IN ball(y0 j,r j)
                   ==> b j x = &1) /\
                  (~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j)) ==> b j x = &0)`
  (LABEL_TAC "BV") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(U:num->A->bool) j`; `(phi:num->A->real^N) j`;
                   `(y0:num->real^N) j`; `(r:num->real) j`; `x:A`]
                  MFDC_BUMP_VALUES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                       (\x. lift((b:num->A->real) j x))`
  (LABEL_TAC "BS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC MFDC_BUMP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `U:num->A->bool`; `phi:num->A->real^N`; `y0:num->real^N`;
    `r:num->real`;
    `\j (x:A). product(1..j-1) (\i. &1 - (b:num->A->real) i x) * b j x`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_smooth; o_DEF] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
       [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. i IN 1..k
            ==> smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((b:num->A->real) i (chart_inv c y)))`
      ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "BS" (MP_TAC o C MATCH_MP (ASSUME `i IN 1..k`)) THEN
        REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\y. lift(product(1..j-1)
                   (\i. &1 - (b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y)))`;
        `\y. lift((b:num->A->real) j (chart_inv (c:(A->bool)#(A->real^N)) y))`]
       SMOOTH_MAP_ON_LIFT_MUL) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ALL_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\i y. lift(&1 - (b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y))`;
        `1..j-1`] SMOOTH_MAP_ON_LIFT_PRODUCT) THEN
      REWRITE_TAC[LIFT_DROP; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\y:real^N. lift(&1)`;
        `\y. lift((b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y))`]
       SMOOTH_MAP_ON_LIFT_SUB) THEN
      REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `j IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o
                     SPECL [`j:num`; `x:A`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. (b:num->A->real) i x`; `k:num`] RFU_TELESCOPE) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `p = &0 ==> &1 - p = &1`) THEN
  SIMP_TAC[PRODUCT_EQ_0_NUMSEG] THEN
  SUBGOAL_THEN `?j. j IN 1..k /\ (x:A) IN (w:num->A->bool) j` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (F0:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `j:num` THEN
  SUBGOAL_THEN `1 <= j /\ j <= k` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
  USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPECL [`j:num`; `x:A`]) THEN
  USE_THEN "W" (MP_TAC o last o CONJUNCTS o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `(x:A) IN (w:num->A->bool) j` THEN
                       REWRITE_TAC[th; IN_ELIM_THM]) THEN
  SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The divergence theorem for compactly supported fields: the integral over  *)
(* a compact measurable set S of div Z vanishes when Z is smooth and         *)
(* vanishes outside a compact subset of S (RFU_DIVERGENCE_ON).  First for    *)
(* fields supported in one chart (adapted from GRGT_DIV_SUPPORTED_ZERO of    *)
(* pc_grg_divthm), then with the partition of unity above.                   *)
(* ========================================================================= *)

let RFU_DIV_SUPPORTED_ZERO_ON = prove
 (`!top atlas (g:A->real^N^N) (Z:A->real^N) (U:A->bool) (phi:A->real^N) K L S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c)) /\
        (U,phi) IN atlas /\
        compact_in top S /\ mfd_lebesgue_measurable (top,atlas) S /\
        compact_in top L /\ L SUBSET S /\
        (!x. x IN topspace top /\ ~(x IN L) ==> Z x = vec 0) /\
        compact K /\ K SUBSET IMAGE phi U /\
        (!x. x IN topspace top /\ ~(x IN U /\ phi x IN K) ==> Z x = vec 0)
        ==> mfd_has_integral (top,atlas) g (mfd_div atlas g Z) S (&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "VS") STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(LABEL_TAC "ZK") THEN
  FIRST_X_ASSUM(LABEL_TAC "ZL" o check (fun th -> is_forall(concl th) &&
                                           free_in `L:A->bool` (concl th))) THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `Kt = {x:A | x IN U /\ (phi:A->real^N) x IN K}` THEN
  SUBGOAL_THEN `compact_in top (Kt:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kt" THEN MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (Kt:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Kt:A->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "Kt" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top DIFF Kt
        ==> mfd_div atlas (g:A->real^N^N) (Z:A->real^N) x = &0`
  (LABEL_TAC "DZ") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGT_MFD_DIV_ZERO_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `topspace top DIFF (Kt:A->bool)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "ZK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((z:A) IN Kt)` THEN EXPAND_TAC "Kt" THEN
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  (* the chart integrand: integrable with integral 0 on the chart image *)
  SUBGOAL_THEN
   `mfd_chart_integrand atlas (g:A->real^N^N) (mfd_div atlas g (Z:A->real^N)) (U,phi)
      absolutely_integrable_on IMAGE (phi:A->real^N) U /\
    integral (IMAGE (phi:A->real^N) U)
      (mfd_chart_integrand atlas g (mfd_div atlas g Z) (U,phi)) = vec 0`
  (LABEL_TAC "CH") THENL
   [SUBGOAL_THEN
     `metric_field (IMAGE (phi:A->real^N) U)
                   (metric_local atlas (U,phi) (g:A->real^N^N))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (IMAGE (phi:A->real^N) U)
                    (mfd_vrep atlas (Z:A->real^N) (U,phi))`
    ASSUME_TAC THENL
     [USE_THEN "VS" (MP_TAC o C MATCH_MP
        (ASSUME `(U:A->bool,phi:A->real^N) IN atlas`)) THEN
      REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN IMAGE (phi:A->real^N) U
          ==> mfd_chart_integrand atlas (g:A->real^N^N)
                (mfd_div atlas g (Z:A->real^N)) (U,phi) y =
              lift(trace(matrix(frechet_derivative
                (\z. sqrt(det(metric_local atlas (U,phi) g z)) %
                     mfd_vrep atlas Z (U,phi) z) (at y))))`
    (LABEL_TAC "CI") THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[mfd_chart_integrand; mfd_density] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
       `chart_inv (U,phi) y IN (U:A->bool) /\
        (phi:A->real^N)(chart_inv (U,phi) y) = y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `Z:A->real^N`; `U:A->bool`; `phi:A->real^N`;
                     `chart_inv (U:A->bool,phi:A->real^N) y`] GRGT_MFD_DIV_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGT_LDIV_DENSITY THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (IMAGE (phi:A->real^N) U)
        (\z. sqrt(det(metric_local atlas (U,phi) (g:A->real^N^N) z)) %
             mfd_vrep atlas (Z:A->real^N) (U,phi) z)`
    ASSUME_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
       [`IMAGE (phi:A->real^N) U`;
        `\z. lift(sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                        (g:A->real^N^N) z)))`;
        `mfd_vrep atlas (Z:A->real^N) (U:A->bool,phi:A->real^N)`]
       SMOOTH_MAP_ON_MUL_DROP_OPEN)) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGT_SQRT_DET_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (phi:A->real^N) U`;
      `\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N) z)) %
           mfd_vrep atlas (Z:A->real^N) (U,phi) z`;
      `K:real^N->bool`] GRGT_INTEGRAL_DIVERGENCE_ZERO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `mfd_vrep atlas (Z:A->real^N) (U:A->bool,phi:A->real^N) y = vec 0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      MATCH_MP_TAC GRGT_VREP_ZERO THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[FST; SND] THEN
      SUBGOAL_THEN
       `chart_inv (U,phi) y IN (U:A->bool) /\
        (phi:A->real^N)(chart_inv (U,phi) y) = y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "ZK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
      EXISTS_TAC
       `\y. lift(trace(matrix(frechet_derivative
              (\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                         (g:A->real^N^N) z)) %
                   mfd_vrep atlas (Z:A->real^N) (U,phi) z) (at y))))` THEN
      ASM_SIMP_TAC[];
      TRANS_TAC EQ_TRANS
       `integral (IMAGE (phi:A->real^N) U)
          (\y. lift(trace(matrix(frechet_derivative
              (\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                         (g:A->real^N^N) z)) %
                   mfd_vrep atlas (Z:A->real^N) (U,phi) z) (at y)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) = (S INTER U) UNION (S DIFF U)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ALL_TAC;
    SET_TAC[]] THENL
   [(* the part in the chart *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_div atlas (g:A->real^N^N) (Z:A->real^N)`;
                   `(U:A->bool,phi:A->real^N)`; `(S:A->bool) INTER U`; `&0`]
                  MFD_HAS_INTEGRAL_CHART) THEN
    ASM_REWRITE_TAC[FST; SND; INTER_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `lebesgue_measurable (IMAGE (phi:A->real^N) ((S:A->bool) INTER U))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S` THEN
      REWRITE_TAC[mfd_lebesgue_measurable] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[FST; SND] THEN REWRITE_TAC[INTER_COMM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[DROP_VEC] `x = vec 0 ==> drop x = &0`) THEN
    USE_THEN "CH" (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT2 th)]) THEN
    ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
    ASM_CASES_TAC `(y:real^N) IN IMAGE (phi:A->real^N) ((S:A->bool) INTER U)` THENL
     [SUBGOAL_THEN `(y:real^N) IN IMAGE (phi:A->real^N) U` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:real^N) IN IMAGE (phi:A->real^N) ((S:A->bool) INTER U)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[mfd_chart_integrand; GSYM LIFT_NUM; LIFT_EQ] THEN
    MATCH_MP_TAC(REAL_RING `x = &0 ==> &0 = x * d`) THEN
    SUBGOAL_THEN
     `chart_inv (U,phi) y IN (U:A->bool) /\
      (phi:A->real^N)(chart_inv (U,phi) y) = y`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(chart_inv (U:A->bool,phi:A->real^N) y IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^N) IN IMAGE (phi:A->real^N) ((S:A->bool) INTER U))` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^N) y` THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC GRGT_MFD_DIV_ZERO_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `topspace top DIFF (L:A->bool)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM SET_TAC[]];
        ASM SET_TAC[]];
      X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "ZL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* the part outside the chart *)
    SUBGOAL_THEN `compact_in top ((S:A->bool) DIFF U)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(S:A->bool) DIFF U = S INTER (topspace top DIFF U)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(S:A->bool) DIFF U`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(S:A->bool) DIFF U`; `v:real`; `&0`]
                  MFD_HAS_INTEGRAL_CONST) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "DZ" MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let RFU_DIVERGENCE_ON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Z:A->real^N)
    L S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        compact_in top S /\ mfd_lebesgue_measurable (top,atlas) S /\
        compact_in top L /\ L SUBSET S /\
        (!x. x IN topspace top /\ ~(x IN L) ==> Z x = vec 0) /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c))
        ==> mfd_has_integral (top,atlas) g (mfd_div atlas g Z) S (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "VS") THEN
  FIRST_X_ASSUM(LABEL_TAC "ZL" o check (fun th -> is_forall(concl th) &&
                                           free_in `L:A->bool` (concl th))) THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `L:A->bool`]
                RFU_PARTITION_OF_UNITY_ON) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `U:num->A->bool`
   (X_CHOOSE_THEN `phi:num->A->real^N` (X_CHOOSE_THEN `y0:num->real^N`
    (X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `rho:num->A->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "PU") (LABEL_TAC "SUM1")))))))) THEN
  SUBGOAL_THEN
   `!j c. j IN 1..k /\ c IN atlas
          ==> smooth_map_on (IMAGE (SND c) (FST c))
                (mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c)`
  (LABEL_TAC "WS") THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC
     `\y. drop(((\x. lift((rho:num->A->real) j x)) o
                chart_inv (c:(A->bool)#(A->real^N))) y) %
          mfd_vrep atlas (Z:A->real^N) c y` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM; LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Z:A->real^N`; `(rho:num->A->real) j`;
                     `(\i x. vec 0):num->A->real^N`; `0`;
                     `c:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
      USE_THEN "PU" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
      REWRITE_TAC[mfd_smooth] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> mfd_has_integral (top,atlas) (g:A->real^N^N)
              (mfd_div atlas g (\x. (rho:num->A->real) j x % (Z:A->real^N) x))
              S (&0)`
  (LABEL_TAC "IJ") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "PU" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC RFU_DIV_SUPPORTED_ZERO_ON THEN
    MAP_EVERY EXISTS_TAC
     [`(U:num->A->bool) j`; `(phi:num->A->real^N) j`;
      `cball((y0:num->real^N) j,&2 * (r:num->real) j)`; `L:A->bool`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      USE_THEN "WS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      USE_THEN "ZL" (MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[VECTOR_MUL_RZERO]];
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(rho:num->A->real) j x = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w. mfd_has_volume (top,atlas) (g:A->real^N^N) S w`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_COMPACT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\j. mfd_div atlas (g:A->real^N^N)
                 (\x. (rho:num->A->real) j x % (Z:A->real^N) x)`;
    `S:A->bool`; `k:num`] GRGT_HAS_INTEGRAL_SUM_ZERO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "IJ" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_div] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0))
                 (metric_local atlas c0 (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c0:(A->bool)#(A->real^N)) x IN IMAGE (SND c0) (FST c0)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `ldiv (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N))
         (\z. vsum(1..k)
                (\j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c0 z))
         (SND c0 x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LDIV_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c0 y =
          rho j (chart_inv (c0:(A->bool)#(A->real^N)) y) % mfd_vrep atlas Z c0 y`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Z:A->real^N`; `(rho:num->A->real) j`;
                     `(\i x. vec 0):num->A->real^N`; `0`;
                     `c0:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VSUM_RMUL] THEN
    SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
     [SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) y IN FST c0` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `FST(c0:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
       [ASM_SIMP_TAC[OPEN_IN_SUBSET]; SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `chart_inv (c0:(A->bool)#(A->real^N)) y IN (L:A->bool)` THENL
     [SUBGOAL_THEN
       `sum(1..k) (\j. (rho:num->A->real) j (chart_inv (c0:(A->bool)#(A->real^N)) y)) =
        &1`
      (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      USE_THEN "SUM1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `mfd_vrep atlas (Z:A->real^N) (c0:(A->bool)#(A->real^N)) y = vec 0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      MATCH_MP_TAC GRGT_VREP_ZERO THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ZL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)`;
    `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
    `\j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x)
                  (c0:(A->bool)#(A->real^N))`;
    `k:num`; `SND(c0:(A->bool)#(A->real^N)) x`] GRGT_LDIV_VSUM)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "WS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The product rule div(f Z) = f div Z + df(Z), in coordinates               *)
(* (RFU_LDIV_MUL) and on the manifold in the preferred chart                 *)
(* (RFU_MFD_DIV_MUL).                                                        *)
(* ========================================================================= *)

let RFU_LDIV_MUL = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) (V:real^N->real^N) y.
        metric_field U G /\ y IN U /\
        (\z. lift(f z)) differentiable at y /\ V differentiable at y
        ==> ldiv G (\z. f z % V z) y =
            f y * ldiv G V y + drop(frechet_derivative (\z. lift(f z)) (at y) (V y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (f:real^N->real) z % (V:real^N->real^N) z) (at y) =
    (\h. f y % frechet_derivative V (at y) h +
         drop(frechet_derivative (\z. lift(f z)) (at y) h) % V y)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`f:real^N->real`;
                   `\h. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) h)`;
                   `V:real^N->real^N`; `frechet_derivative (V:real^N->real^N) (at y)`;
                   `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) (basis i)) *
           ((V:real^N->real^N) y)$i) =
    drop(frechet_derivative (\z. lift(f z)) (at y) (V y))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE o
      check (fun th -> can (find_term ((=) `f:real^N->real`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`(V:real^N->real^N) y`; `1`] o
               MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ldiv; GRGT_TRACE_MATRIX; BILINEAR_RMUL] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; SUM_ADD_NUMSEG; SUM_LMUL] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFU_MFD_DIV_MUL = prove
 (`!top atlas (g:A->real^N^N) (psi:A->real) (Z:A->real^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ mfd_smooth atlas (\x. lift(psi x)) /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c))
        ==> mfd_div atlas g (\y. psi y % Z y) x =
            psi x * mfd_div atlas g Z x +
            drop(frechet_derivative
                   (\y. lift(psi(chart_inv (chart_at atlas x) y)))
                   (at (SND(chart_at atlas x) x))
                   (mfd_vrep atlas Z (chart_at atlas x) (SND(chart_at atlas x) x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((psi:A->real)(chart_inv c y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((psi:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_div] THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `ldiv (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
         (\y. (psi:A->real)(chart_inv c y) % mfd_vrep atlas (Z:A->real^N) c y)
         (SND c x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LDIV_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Z:A->real^N`; `psi:A->real`;
                   `(\i x. vec 0):num->A->real^N`; `0`;
                   `c:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `\y. (psi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `mfd_vrep atlas (Z:A->real^N) (c:(A->bool)#(A->real^N))`;
                 `SND(c:(A->bool)#(A->real^N)) x`] RFU_LDIV_MUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

