(* ========================================================================= *)
(* pc_moi_s30_comp: the compression step of Moise 30.4 and 30.6 (GTM 47,     *)
(* printed p.216).  Main theorems                                            *)
(*   SPLIT_ESSENTIAL |- MOI_S30_SPLIT_ESSENTIAL                              *)
(*   COMPRESS        |- MOI_S30_COMPRESS                                     *)
(* SPLIT_ESSENTIAL: the clopen pieces of the split surface each contain a    *)
(* capping disk (the original surface is connected), so it is connected or   *)
(* has two connected pieces; a spherical piece would make the essential      *)
(* curve null-homotopic (the capping disk on the end of the annulus is       *)
(* contractible and the annulus deforms into either end).  MOISE_273 is not  *)
(* used.  COMPRESS: split along the 26.4 disk (MOI_FND_SPLIT_DISK_R3); the   *)
(* separation passes through the bounding 3-manifold of BOUNDS and the       *)
(* x-clause; with two non-spherical pieces 30.2 gives a separating piece,    *)
(* whose Euler characteristic exceeds chi(m) by additivity and chi <= 1.     *)
(* ========================================================================= *)

needs "src/pc_moi_s30_cut_b.ml";;   (* model annulus lemmas *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* An annulus deforms into either end.  In the model annulus                *)
(* 1 <= n(y) <= 2 (n the max norm of real^2) the radial homotopy            *)
(* ((1 - t) + t c / n(y)) y, c = 1 or 2, stays in the model and ends on     *)
(* the square n = c; through the chart (f,g) of pl_annulus_with_ends the     *)
(* inclusion of any subset of the annulus is homotopic inside the annulus  *)
(* to a map into either end.                                                 *)
(* ========================================================================= *)

let MOI_S3CP_RF_SQUARE2 = prove
 (`!c. &0 < c
       ==> relative_frontier (interval[--vector[c;c]:real^2,vector[c;c]]) =
           {y:real^2 | max (abs(y$1)) (abs(y$2)) = c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior (interval[--vector[c;c]:real^2,vector[c;c]]) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2;
                FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_2;
              FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `m = c <=> m <= c /\ ~(m < c)`; REAL_MAX_LE;
              REAL_MAX_LT] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CP_N2_CMUL = prove
 (`!c y:real^2. &0 <= c
       ==> max (abs((c % y)$1)) (abs((c % y)$2)) =
           c * max (abs(y$1)) (abs(y$2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
  ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MAX_ACI]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_max] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_S3CP_N2_CONT = prove
 (`!s. (lift o (\y:real^2. max (abs(y$1)) (abs(y$2)))) continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[SUBSET_UNIV; o_DEF] THEN
  MP_TAC(SPEC `&0` MOI_S3CB_N2_PL) THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_ACCEPT_TAC PL_MAP_ON_IMP_CONTINUOUS_ON);;

let MOI_S3CP_RADIAL_CONT = prove
 (`!c s. (!y:real^2. y IN s ==> &1 <= max (abs(y$1)) (abs(y$2)))
         ==> (\z:real^(1,2)finite_sum.
                ((&1 - drop(fstcart z)) + drop(fstcart z) * c /
                   max (abs((sndcart z)$1)) (abs((sndcart z)$2))) % sndcart z)
             continuous_on (interval[vec 0,vec 1] PCROSS s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]] THEN
  ABBREV_TAC `ns = \w:real^(1,2)finite_sum.
                     max (abs((sndcart w)$1)) (abs((sndcart w)$2))` THEN
  SUBGOAL_THEN
   `lift o (\z:real^(1,2)finite_sum.
              (&1 - drop(fstcart z)) + drop(fstcart z) * c /
                max (abs((sndcart z)$1)) (abs((sndcart z)$2))) =
    (\z. (vec 1 - fstcart z) + drop(fstcart z) % (c % (lift o inv o ns) z))`
  SUBST1_TAC THENL
   [EXPAND_TAC "ns" THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; LIFT_ADD; LIFT_SUB; LIFT_CMUL;
                LIFT_NUM; LIFT_DROP] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `lift o (ns:real^(1,2)finite_sum->real) =
      (lift o (\y:real^2. max (abs(y$1)) (abs(y$2)))) o sndcart`
    SUBST1_TAC THENL
     [EXPAND_TAC "ns" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; MOI_S3CP_N2_CONT];
    EXPAND_TAC "ns" THEN REWRITE_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN s`)) THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3CP_RADIAL_END = prove
 (`!(a:real^3->bool) f g c s.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     s SUBSET a /\ &1 <= c /\ c <= &2
     ==> ?r. r continuous_on s /\
             IMAGE r s SUBSET IMAGE f {y:real^2 | max (abs(y$1)) (abs(y$2)) = c} /\
             homotopic_with (\h. T) (subtopology euclidean s,subtopology euclidean a)
               (\x. x) r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3CB_ANN_MODEL] THEN
  ABBREV_TAC `aa = {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
                               max (abs(y$1)) (abs(y$2)) <= &2}` THEN
  SUBGOAL_THEN `!y:real^2. y IN aa <=> &1 <= max (abs(y$1)) (abs(y$2)) /\
                                      max (abs(y$1)) (abs(y$2)) <= &2`
  (LABEL_TAC "aadef") THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC
   `ff = \z:real^(1,2)finite_sum.
           ((&1 - drop(fstcart z)) + drop(fstcart z) * c /
              max (abs((sndcart z)$1)) (abs((sndcart z)$2))) % sndcart z` THEN
  ABBREV_TAC `gg = \z:real^(1,3)finite_sum.
                     pastecart (fstcart z) ((g:real^3->real^2) (sndcart z))` THEN
  SUBGOAL_THEN
   `!t y. t IN interval[vec 0,vec 1] /\ y IN aa
          ==> (ff:real^(1,2)finite_sum->real^2) (pastecart t y) IN aa`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN USE_THEN "aadef" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "ff" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                DROP_VEC] THEN
    STRIP_TAC THEN
    ABBREV_TAC `n = max (abs((y:real^2)$1)) (abs(y$2))` THEN
    SUBGOAL_THEN `&0 <= (&1 - drop t) + drop t * c / n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S3CP_N2_CMUL] THEN
    SUBGOAL_THEN `((&1 - drop t) + drop t * c / n) * n = (&1 - drop t) * n + drop t * c`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&1 <= n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - drop t) * (n - &1) /\ &0 <= drop t * (c - &1) /\
                  &0 <= (&1 - drop t) * (&2 - n) /\ &0 <= drop t * (&2 - c)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
                    (pastecart (vec 1) ((g:real^3->real^2) x)))` THEN
  SUBGOAL_THEN
   `(\z. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
           (pastecart (fstcart z) ((g:real^3->real^2) (sndcart z)))))
    continuous_on (interval[vec 0,vec 1] PCROSS s) /\
    IMAGE (\z. f (ff (pastecart (fstcart z) (g (sndcart z)))))
          (interval[vec 0,vec 1] PCROSS s) SUBSET a`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (gg:real^(1,3)finite_sum->real^(1,2)finite_sum)
            (interval[vec 0,vec 1] PCROSS s) SUBSET interval[vec 0,vec 1] PCROSS aa`
    ASSUME_TAC THENL
     [EXPAND_TAC "gg" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      REPEAT STRIP_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^2) a = aa` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (ff:real^(1,2)finite_sum->real^2) (interval[vec 0,vec 1] PCROSS aa)
        SUBSET aa`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\z. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
               (pastecart (fstcart z) ((g:real^3->real^2) (sndcart z))))) =
        f o ff o gg`
      SUBST1_TAC THENL
       [EXPAND_TAC "gg" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [EXPAND_TAC "gg" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
          SUBGOAL_THEN `(\z:real^(1,3)finite_sum. (g:real^3->real^2) (sndcart z)) =
                        g o sndcart` SUBST1_TAC THENL
           [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
          ASM_REWRITE_TAC[IMAGE_SNDCART_PCROSS] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (aa:real^2->bool)` THEN
          ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN
          MATCH_MP_TAC MOI_S3CP_RADIAL_CONT THEN
          USE_THEN "aadef" (fun th -> SIMP_TAC[th])];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `aa:real^2->bool` THEN
        ASM_REWRITE_TAC[IMAGE_o] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (ff:real^(1,2)finite_sum->real^2)
                      (interval[vec 0:real^1,vec 1] PCROSS aa)` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET]];
      SUBGOAL_THEN
       `(\z. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
               (pastecart (fstcart z) ((g:real^3->real^2) (sndcart z))))) =
        f o ff o gg`
      SUBST1_TAC THENL
       [EXPAND_TAC "gg" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^2->real^3) aa` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (ff:real^(1,2)finite_sum->real^2)
                      (interval[vec 0:real^1,vec 1] PCROSS aa)` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET];
        ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(\z. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
                  (pastecart (fstcart z) ((g:real^3->real^2) (sndcart z))))) o
                (\x:real^3. pastecart (vec 1:real^1) x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (s:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      SIMP_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXPAND_TAC "ff" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ADD_LID; REAL_MUL_LID] THEN
    SUBGOAL_THEN `(g:real^3->real^2) x IN aa` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^2) a = aa` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "aadef" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= c / max (abs((g:real^3->real^2) x$1)) (abs(g x$2))`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S3CP_N2_CMUL] THEN
    UNDISCH_TAC `&1 <= max (abs((g:real^3->real^2) x$1)) (abs(g x$2))` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\x. (f:real^2->real^3) ((g:real^3->real^2) x)`;
      `\x. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
             (pastecart (vec 1) ((g:real^3->real^2) x)))`] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN
      EXISTS_TAC `\z. (f:real^2->real^3) ((ff:real^(1,2)finite_sum->real^2)
                    (pastecart (fstcart z) ((g:real^3->real^2) (sndcart z))))` THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      X_GEN_TAC `x:real^3` THEN
      EXPAND_TAC "ff" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
      REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; VECTOR_MUL_LID];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(x:real^3) IN s` THEN
      SET_TAC[]]]);;

let MOI_S3CP_ANNULUS_DEFORM = prove
 (`!(a:real^3->bool) j1 j2 s.
     pl_annulus_with_ends a j1 j2 /\ s SUBSET a
     ==> (?r. r continuous_on s /\ IMAGE r s SUBSET j1 /\
              homotopic_with (\h. T)
                (subtopology euclidean s,subtopology euclidean a) (\x. x) r) /\
         (?r. r continuous_on s /\ IMAGE r s SUBSET j2 /\
              homotopic_with (\h. T)
                (subtopology euclidean s,subtopology euclidean a) (\x. x) r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^2->real^3`
    (X_CHOOSE_THEN `g:real^3->real^2` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  ASM_SIMP_TAC[MOI_S3CP_RF_SQUARE2; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S3CP_RADIAL_END THEN
  EXISTS_TAC `g:real^3->real^2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The pieces of the split surface.  A set clopen in                         *)
(* x = (mm DIFF a) UNION dd and missing dd is clopen in the connected mm    *)
(* and misses a, so it is empty; hence x is connected or the union of two   *)
(* disjoint closed connected pieces, one through each capping disk.  The     *)
(* simplices of a complex inside one closed piece form a combinatorial     *)
(* 2-manifold with that polyhedron (vertex links unchanged).                *)
(* ========================================================================= *)

let MOI_S3CP_CLOPEN_MEETS = prove
 (`!mm a dd x q:real^3->bool.
     connected mm /\ closed a /\ a SUBSET mm /\ ~(a = {}) /\
     x = (mm DIFF a) UNION dd /\ closed q /\ closed (x DIFF q) /\ q SUBSET x /\
     DISJOINT q dd
     ==> q = {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3->bool) SUBSET mm DIFF a` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (q:real^3->bool) dd` THEN
    UNDISCH_TAC `(q:real^3->bool) SUBSET x` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (mm:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `q:real^3->bool`) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(q:real^3->bool) SUBSET mm DIFF a` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(mm:real^3->bool) DIFF q = mm INTER ((x DIFF q) UNION a)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(q:real^3->bool) SUBSET mm DIFF a` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[CLOSED_UNION]];
      SUBGOAL_THEN `(q:real^3->bool) = mm INTER q` SUBST1_TAC THENL
       [UNDISCH_TAC `(q:real^3->bool) SUBSET mm DIFF a` THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]]];
    STRIP_TAC THEN UNDISCH_TAC `(q:real^3->bool) SUBSET mm DIFF a` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(a:real^3->bool) SUBSET mm` THEN
    UNDISCH_TAC `~((a:real^3->bool) = {})` THEN SET_TAC[]]);;

let MOI_S3CP_CONNECTED_IN_CLOSED_SPLIT = prove
 (`!s e1 e2:real^3->bool.
     connected s /\ closed e1 /\ closed e2 /\ s SUBSET e1 UNION e2 /\
     e1 INTER e2 = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN ASM SET_TAC[]);;

let MOI_S3CP_PIECE_CONNECTED = prove
 (`!x e e' d d':real^3->bool.
     closed e /\ closed e' /\ e UNION e' = x /\ e INTER e' = {} /\
     (!q. closed q /\ closed (x DIFF q) /\ q SUBSET x /\ DISJOINT q (d UNION d')
          ==> q = {}) /\
     d SUBSET e /\ d' SUBSET e' /\ connected d /\ ~(d = {})
     ==> connected e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CONNECTED_CLOSED_SET] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f1:real^3->bool`; `f2:real^3->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f:real^3->bool. closed f /\ closed (x DIFF f) /\ f SUBSET x /\
                               ~(f = {}) /\ f SUBSET e ==> ~(f INTER d = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:real^3->bool) INTER d = {}` THEN
    UNDISCH_TAC `(f:real^3->bool) SUBSET e` THEN
    UNDISCH_TAC `(e:real^3->bool) INTER e' = {}` THEN
    UNDISCH_TAC `(d':real^3->bool) SUBSET e'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f1:real^3->bool) INTER d = {}) /\ ~((f2:real^3->bool) INTER d = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THENL
     [SUBGOAL_THEN `(x:real^3->bool) DIFF f1 = f2 UNION e'` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[CLOSED_UNION]];
      SUBGOAL_THEN `(x:real^3->bool) DIFF f2 = f1 UNION e'` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[CLOSED_UNION]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `f1:real^3->bool`; `f2:real^3->bool`]
    MOI_S3CP_CONNECTED_IN_CLOSED_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((f1:real^3->bool) INTER d = {})` THEN
  UNDISCH_TAC `~((f2:real^3->bool) INTER d = {})` THEN
  UNDISCH_TAC `(f1:real^3->bool) INTER f2 = {}` THEN
  UNDISCH_TAC `(f1:real^3->bool) UNION f2 = e` THEN
  UNDISCH_TAC `(d:real^3->bool) SUBSET e` THEN SET_TAC[]);;

let MOI_S3CP_PIECES_FINISH = prove
 (`!x e1 e2 d1 d2:real^3->bool.
     closed e1 /\ closed e2 /\ e1 UNION e2 = x /\ e1 INTER e2 = {} /\
     (!q. closed q /\ closed (x DIFF q) /\ q SUBSET x /\ DISJOINT q (d1 UNION d2)
          ==> q = {}) /\
     d1 SUBSET e1 /\ d2 SUBSET e2 /\ connected d1 /\ connected d2 /\
     ~(d1 = {}) /\ ~(d2 = {})
     ==> connected e1 /\ connected e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_S3CP_PIECE_CONNECTED THENL
   [MAP_EVERY EXISTS_TAC [`x:real^3->bool`; `e2:real^3->bool`;
                          `d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`x:real^3->bool`; `e1:real^3->bool`;
                          `d2:real^3->bool`; `d1:real^3->bool`] THEN
    ONCE_REWRITE_TAC[UNION_COMM; INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CP_PIECES = prove
 (`!mm a d1 d2 x:real^3->bool.
     connected mm /\ closed a /\ closed d1 /\ closed d2 /\
     connected d1 /\ connected d2 /\ ~(d1 = {}) /\ ~(d2 = {}) /\
     a SUBSET mm /\ ~(a = {}) /\ x = (mm DIFF a) UNION d1 UNION d2 /\ closed x
     ==> connected x \/
         ?p q. closed p /\ closed q /\ p UNION q = x /\ p INTER q = {} /\
               connected p /\ connected q /\ d1 SUBSET p /\ d2 SUBSET q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET x /\ d2 SUBSET x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x:real^3->bool = (mm DIFF a) UNION d1 UNION d2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. closed q /\ closed (x DIFF q) /\ q SUBSET x /\
        DISJOINT q ((d1:real^3->bool) UNION d2) ==> q = {}`
  (LABEL_TAC "meets") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CP_CLOPEN_MEETS THEN
    MAP_EVERY EXISTS_TAC [`mm:real^3->bool`; `a:real^3->bool`;
                          `(d1:real^3->bool) UNION d2`; `x:real^3->bool`] THEN
    ASM_REWRITE_TAC[UNION_ASSOC];
    ALL_TAC] THEN
  UNDISCH_TAC `x:real^3->bool = (mm DIFF a) UNION d1 UNION d2` THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `connected (x:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~connected (x:real^3->bool)` THEN
  REWRITE_TAC[MATCH_MP CONNECTED_CLOSED_SET (ASSUME `closed (x:real^3->bool)`)] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3->bool) DIFF e1 = e2 /\ x DIFF e2 = e1 /\
                e1 SUBSET x /\ e2 SUBSET x /\ d1 SUBSET e1 UNION e2 /\
                d2 SUBSET e1 UNION e2 /\ d1 SUBSET x /\ d2 SUBSET x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e1:real^3->bool) UNION e2 = x` THEN
    UNDISCH_TAC `(e1:real^3->bool) INTER e2 = {}` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e1:real^3->bool) INTER (d1 UNION d2) = {}) /\
                ~((e2:real^3->bool) INTER (d1 UNION d2) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "meets" (MP_TAC o SPEC `e1:real^3->bool`);
      USE_THEN "meets" (MP_TAC o SPEC `e2:real^3->bool`)] THEN
    REWRITE_TAC[DISJOINT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((d1:real^3->bool) SUBSET e1 \/ d1 SUBSET e2) /\
                ((d2:real^3->bool) SUBSET e1 \/ d2 SUBSET e2)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3CP_CONNECTED_IN_CLOSED_SPLIT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~((e2:real^3->bool) INTER (d1 UNION d2) = {})` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET e1` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET e1` THEN
    UNDISCH_TAC `(e1:real^3->bool) INTER e2 = {}` THEN SET_TAC[];
    MAP_EVERY EXISTS_TAC [`e1:real^3->bool`; `e2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CP_PIECES_FINISH THEN
    MAP_EVERY EXISTS_TAC [`x:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`e2:real^3->bool`; `e1:real^3->bool`] THEN
    SUBGOAL_THEN `(e2:real^3->bool) UNION e1 = x /\ e2 INTER e1 = {}`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(e1:real^3->bool) UNION e2 = x` THEN
      UNDISCH_TAC `(e1:real^3->bool) INTER e2 = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CP_PIECES_FINISH THEN
    MAP_EVERY EXISTS_TAC [`x:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~((e1:real^3->bool) INTER (d1 UNION d2) = {})` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET e2` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET e2` THEN
    UNDISCH_TAC `(e1:real^3->bool) INTER e2 = {}` THEN SET_TAC[]]);;

let MOI_S3CP_SUBCOMPLEX = prove
 (`!(c:(real^3->bool)->bool) p q.
     FINITE c /\ combinatorial_manifold 2 c /\ closed p /\ closed q /\
     p UNION q = UNIONS c /\ p INTER q = {}
     ==> FINITE {s | s IN c /\ s SUBSET p} /\
         combinatorial_manifold 2 {s | s IN c /\ s SUBSET p} /\
         UNIONS {s | s IN c /\ s SUBSET p} = p /\
         (!s. s IN c ==> s SUBSET p \/ s SUBSET q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [combinatorial_manifold]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN c ==> s SUBSET p \/ s SUBSET q`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S3CP_CONNECTED_IN_CLOSED_SPLIT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `(p:real^3->bool) UNION q = UNIONS c` THEN
      UNDISCH_TAC `(s:real^3->bool) IN c` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE {s:real^3->bool | s IN c /\ s SUBSET p}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[SUBSET];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS c` MP_TAC THENL
       [UNDISCH_TAC `(p:real^3->bool) UNION q = UNIONS c` THEN
        UNDISCH_TAC `(x:real^3) IN p` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(s:real^3->bool) IN c`)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:real^3->bool) INTER q = {}` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET q` THEN
      UNDISCH_TAC `(x:real^3) IN s` THEN UNDISCH_TAC `(x:real^3) IN p` THEN
      SET_TAC[]]] THEN
  REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s:real^3->bool | s IN c /\ s SUBSET p}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `simplicial_link {s:real^3->bool | s IN c /\ s SUBSET p} v =
                  simplicial_link c v` SUBST1_TAC THENL
     [REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:real^3->bool) SUBSET p` ASSUME_TAC THENL
         [FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(t:real^3->bool) IN c`)) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(p:real^3->bool) INTER q = {}` THEN
          UNDISCH_TAC `(t:real^3->bool) SUBSET q` THEN
          UNDISCH_TAC `(v:real^3) IN t` THEN
          UNDISCH_TAC `{v:real^3} SUBSET p` THEN SET_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
          EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* SPLIT_ESSENTIAL.  Facts on cells, annuli and complexes; a curve in an     *)
(* annulus whose end bounds a disk in X is null-homotopic in X; the theorem: *)
(* the pieces of the split surface are sub-complexes, and a spherical piece  *)
(* P would give the disk (P DIFF d1) UNION j1 (by SCH3_DISK_COMPLEMENT) on   *)
(* the end j1 inside the original surface.                                   *)
(* ========================================================================= *)

let MOI_S3CP_CELL_FACTS = prove
 (`!(s:real^3->bool) b.
     pl_cell_with_boundary 2 s b
     ==> compact s /\ closed s /\ connected s /\ b SUBSET s /\ ~(s = {}) /\
         contractible s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    DISCH_TAC THEN UNDISCH_TAC `&2 simplex (k:real^3->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`k:real^3->bool`; `s:real^3->bool`] HOMEOMORPHIC_CONTRACTIBLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]]);;

let MOI_S3CP_ANNULUS_FACTS = prove
 (`!(a:real^3->bool) j1 j2.
     pl_annulus_with_ends a j1 j2
     ==> compact a /\ closed a /\ ~(a = {}) /\ j1 SUBSET a /\ j2 SUBSET a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[MOI_S3CB_ANN_MODEL] THEN
  SUBGOAL_THEN
   `compact {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
                        max (abs(y$1)) (abs(y$2)) <= &2}`
  ASSUME_TAC THENL [REWRITE_TAC[MOI_S3CB_N2_CLOSED_BAND]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S3CB_ANN_MODEL]) THEN
  SUBGOAL_THEN `compact (a:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^3)
                   {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
                               max (abs(y$1)) (abs(y$2)) <= &2} = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_SIMP_TAC[MOI_S3CP_RF_SQUARE2; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3)
                 {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
                             max (abs(y$1)) (abs(y$2)) <= &2} = a` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `vector[&1; &0]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

let MOI_S3CP_COMPLEX_COMPACT = prove
 (`!n (c:(real^3->bool)->bool).
     FINITE c /\ combinatorial_manifold n c ==> compact (UNIONS c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_S3CP_NULL_VIA_END = prove
 (`!(a:real^3->bool) j1 j2 j e b xx.
     pl_annulus_with_ends a j1 j2 /\ j SUBSET a /\ a SUBSET xx /\
     pl_cell_with_boundary 2 e b /\ e SUBSET xx /\ (b = j1 \/ b = j2)
     ==> ?z. homotopic_with (\f. T)
               (subtopology euclidean j,subtopology euclidean xx) (\x. x) (\x. z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3CP_CELL_FACTS) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `j:real^3->bool`] MOI_S3CP_ANNULUS_DEFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r1:real^3->real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `r2:real^3->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?r:real^3->real^3. r continuous_on j /\ IMAGE r j SUBSET e /\
                       homotopic_with (\h. T)
                         (subtopology euclidean j,subtopology euclidean a) (\x. x) r`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [EXISTS_TAC `r1:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `j1:real^3->bool` THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `r2:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `j2:real^3->bool` THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^3->real^3`; `j:real^3->bool`; `e:real^3->bool`]
    NULLHOMOTOPIC_INTO_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
  EXISTS_TAC `z:real^3` THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `r:real^3->real^3` THEN CONJ_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THENL
   [EXISTS_TAC `a:real^3->bool`; EXISTS_TAC `e:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3CP_NOT_SPHERE = prove
 (`!(m:(real^3->bool)->bool) a j j1 j2 dd jj p.
     (!s d j:real^3->bool.
        pl_sphere 2 s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
        ==> pl_cell_with_boundary 2 ((s DIFF d) UNION j) j) /\
     pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m /\ j SUBSET a /\
     pl_cell_with_boundary 2 dd jj /\ (jj = j1 \/ jj = j2) /\ dd SUBSET p /\
     p DIFF dd SUBSET UNIONS m /\
     ~(?z. homotopic_with (\f. T)
             (subtopology euclidean j,subtopology euclidean (UNIONS m))
             (\x. x) (\x. z))
     ==> ~pl_sphere 2 p`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN DISCH_TAC THEN
  UNDISCH_TAC `~(?z. homotopic_with (\f. T)
                  (subtopology euclidean j,subtopology euclidean (UNIONS m))
                  (\x:real^3. x) (\x. z))` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CP_NULL_VIA_END THEN
  MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                        `(p DIFF dd) UNION jj:real^3->bool`; `jj:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
      MOI_S3CP_ANNULUS_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(jj:real^3->bool) = j1 \/ jj = j2` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET a` THEN
    UNDISCH_TAC `(j2:real^3->bool) SUBSET a` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS m` THEN
    UNDISCH_TAC `(p:real^3->bool) DIFF dd SUBSET UNIONS m` THEN
    SPEC_TAC(`UNIONS (m:(real^3->bool)->bool)`,`mm:real^3->bool`) THEN
    SET_TAC[]]);;

let SPLIT_ESSENTIAL = prove
 (MOI_S30_SPLIT_ESSENTIAL,
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "dc")) THEN
  MAP_EVERY X_GEN_TAC [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                       `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`;
                       `d2:real^3->bool`; `m':(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET a` ASSUME_TAC THENL
   [UNDISCH_TAC `(j:real^3->bool) SUBSET a DIFF (j1 UNION j2)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S3CP_ANNULUS_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `j2:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS (m':(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (m:(real^3->bool)->bool)`; `a:real^3->bool`;
                 `d1:real^3->bool`; `d2:real^3->bool`;
                 `UNIONS (m':(real^3->bool)->bool)`] MOI_S3CP_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `p:real^3->bool`; `q:real^3->bool`]
    MOI_S3CP_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `q:real^3->bool`; `p:real^3->bool`]
    MOI_S3CP_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MESON[UNION_COMM; INTER_COMM]
      `(q:real^3->bool) UNION p = p UNION q /\ q INTER p = p INTER q`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{s | s IN m' /\ s SUBSET (p:real^3->bool)}`;
                        `{s | s IN m' /\ s SUBSET (q:real^3->bool)}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[DISJOINT] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(d1:real^3->bool) SUBSET p` THEN
    UNDISCH_TAC `~((d1:real^3->bool) = {})` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S3CP_NOT_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                          `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`;
                          `j1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:real^3->bool) UNION q = (UNIONS m DIFF a) UNION d1 UNION d2` THEN
    UNDISCH_TAC `(p:real^3->bool) INTER q = {}` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET q` THEN
    SPEC_TAC(`UNIONS (m:(real^3->bool)->bool)`,`mm:real^3->bool`) THEN SET_TAC[];
    UNDISCH_TAC `(d2:real^3->bool) SUBSET q` THEN
    UNDISCH_TAC `~((d2:real^3->bool) = {})` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S3CP_NOT_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                          `j1:real^3->bool`; `j2:real^3->bool`; `d2:real^3->bool`;
                          `j2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:real^3->bool) UNION q = (UNIONS m DIFF a) UNION d1 UNION d2` THEN
    UNDISCH_TAC `(p:real^3->bool) INTER q = {}` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET p` THEN
    SPEC_TAC(`UNIONS (m:(real^3->bool)->bool)`,`mm:real^3->bool`) THEN SET_TAC[]]);;

(* ========================================================================= *)
(* COMPRESS.  Separation helpers (swap; separates_in in UNIV; the two sides  *)
(* of a surface given by 26.6; the transfer of a separation through the      *)
(* bounding 3-manifold and the x-clause of the splitting), Euler additivity  *)
(* for complexes with disjoint polyhedra and the bound chi <= 1 for          *)
(* non-spherical closed surfaces, the components of two disjoint closed      *)
(* connected sets, and the theorem.                                          *)
(* ========================================================================= *)

let MOI_S3CP_SEP_SWAP = prove
 (`!b s t:real^N->bool. euclidean_separates b s t ==> euclidean_separates b t s`,
  REWRITE_TAC[euclidean_separates] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^N->bool` (X_CHOOSE_THEN `vv:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`vv:real^N->bool`; `uu:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`DISJOINT (uu:real^N->bool) vv`;
                         `(uu:real^N->bool) UNION vv = (:real^N) DIFF b`] THEN
  SET_TAC[]);;

let MOI_S3CP_SEP_UNIV = prove
 (`!c s t:real^3->bool.
     separates_in (:real^3) c s t <=> euclidean_separates c s t`,
  REWRITE_TAC[separates_in; euclidean_separates; SUBTOPOLOGY_UNIV; GSYM OPEN_IN]);;

(* A connected set missing a surface lies inside or outside it; with the    *)
(* two components of 26.6 the inside is connected, so a separated pair has  *)
(* one set inside and the other outside.                                     *)

let MOI_S3CP_SIDES = prove
 (`!(mm:real^3->bool) b hs ks.
     closed mm /\ components ((:real^3) DIFF mm) = {b, outside mm} /\
     euclidean_separates mm hs ks /\ connected hs /\ connected ks /\
     ~(hs = {}) /\ ~(ks = {})
     ==> (hs SUBSET inside mm /\ ks SUBSET outside mm) \/
         (ks SUBSET inside mm /\ hs SUBSET outside mm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (outside mm:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `(:real^3) DIFF mm` THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (inside mm:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inside mm = (b:real^3->bool) DIFF outside mm` SUBST1_TAC THENL
     [REWRITE_TAC[INSIDE_OUTSIDE] THEN
      MP_TAC(ISPEC `(:real^3) DIFF mm` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `b:real^3->bool = outside mm` THENL
     [ASM_REWRITE_TAC[DIFF_EQ_EMPTY; CONNECTED_EMPTY];
      MP_TAC(ISPECL [`(:real^3) DIFF mm`; `b:real^3->bool`; `outside mm:real^3->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(b:real^3->bool) DIFF outside mm = b` SUBST1_TAC THENL
       [UNDISCH_TAC `(b:real^3->bool) INTER outside mm = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `(:real^3) DIFF mm` THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  UNDISCH_TAC `euclidean_separates (mm:real^3->bool) hs ks` THEN
  REWRITE_TAC[euclidean_separates] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^3->bool` (X_CHOOSE_THEN `vv:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(hs:real^3->bool) SUBSET (:real^3) DIFF mm /\ ks SUBSET (:real^3) DIFF mm /\
    inside mm SUBSET (:real^3) DIFF mm /\ outside mm SUBSET (:real^3) DIFF mm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `mm:real^3->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `mm:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
    MAP_EVERY UNDISCH_TAC
     [`(uu:real^3->bool) UNION vv = (:real^3) DIFF mm`; `(hs:real^3->bool) SUBSET uu`;
      `(ks:real^3->bool) SUBSET vv`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:real^3->bool. connected c /\ c SUBSET (:real^3) DIFF mm
                     ==> c SUBSET inside mm \/ c SUBSET outside mm`
  (LABEL_TAC "io") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CB_CONNECTED_OPEN_SPLIT THEN
    ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE; INSIDE_UNION_OUTSIDE] THEN
    REWRITE_TAC[DISJOINT; INSIDE_INTER_OUTSIDE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3->bool. connected w /\ w SUBSET (:real^3) DIFF mm
                     ==> ~(hs SUBSET w /\ ks SUBSET w)`
  (LABEL_TAC "nb") THENL
   [X_GEN_TAC `w:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:real^3->bool`; `uu:real^3->bool`; `vv:real^3->bool`]
      MOI_S3CB_CONNECTED_OPEN_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (uu:real^3->bool) vv`; `(hs:real^3->bool) SUBSET uu`;
      `(ks:real^3->bool) SUBSET vv`; `~((hs:real^3->bool) = {})`;
      `~((ks:real^3->bool) = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "io" (MP_TAC o SPEC `hs:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "io" (MP_TAC o SPEC `ks:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "nb" (MP_TAC o SPEC `inside mm:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "nb" (MP_TAC o SPEC `outside mm:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MESON_TAC[]);;

(* The separation of the split surface: hs inside the original surface lies *)
(* in the bounding 3-manifold and off the change set, hence in the interior *)
(* of the new 3-manifold; ks outside lies off both.                          *)

let MOI_S3CP_SEP_TRANSFER = prove
 (`!(mm:real^3->bool) mm' hs ks u xx'.
     hs SUBSET inside mm /\ ks SUBSET outside mm /\
     DISJOINT u hs /\ DISJOINT u ks /\ mm' SUBSET u /\
     compact xx' /\ frontier xx' = mm' /\
     ((mm UNION inside mm) DIFF xx') UNION (xx' DIFF (mm UNION inside mm)) SUBSET u
     ==> euclidean_separates mm' hs ks`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[euclidean_separates] THEN
  MAP_EVERY EXISTS_TAC [`interior xx':real^3->bool`; `(:real^3) DIFF xx'`] THEN
  SUBGOAL_THEN `closed (xx':real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  SUBGOAL_THEN `mm' = (xx':real^3->bool) DIFF interior xx'` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (xx':real^3->bool) = mm'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[frontier; CLOSURE_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPEC `xx':real^3->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `mm:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `mm:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  MAP_EVERY UNDISCH_TAC
   [`(hs:real^3->bool) SUBSET inside mm`; `(ks:real^3->bool) SUBSET outside mm`;
    `DISJOINT (u:real^3->bool) hs`; `DISJOINT (u:real^3->bool) ks`;
    `(mm':real^3->bool) SUBSET u`;
    `((mm UNION inside mm) DIFF xx') UNION (xx' DIFF (mm UNION inside mm))
     SUBSET (u:real^3->bool)`;
    `mm' = (xx':real^3->bool) DIFF interior xx'`] THEN
  UNDISCH_TAC `frontier (xx':real^3->bool) = mm'` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`interior xx':real^3->bool`,`iix:real^3->bool`) THEN
  SPEC_TAC(`inside mm:real^3->bool`,`ins:real^3->bool`) THEN
  SPEC_TAC(`outside mm:real^3->bool`,`ous:real^3->bool`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* Euler characteristics. *)

let MOI_S3CP_EULER_DISJOINT = prove
 (`!c d:(real^3->bool)->bool.
     FINITE c /\ FINITE d /\ DISJOINT (UNIONS c) (UNIONS d)
     ==> complex_euler (c UNION d) = complex_euler c + complex_euler d`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_EULER_UNION] THEN
  SUBGOAL_THEN `complex_euler ((c:(real^3->bool)->bool) INTER d) = &0`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM_ALT; FINITE_INTER] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `s:real^3->bool` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s:real^3->bool = {}` (fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY UNDISCH_TAC
   [`DISJOINT (UNIONS (c:(real^3->bool)->bool)) (UNIONS d)`;
    `(s:real^3->bool) IN c`; `(s:real^3->bool) IN d`] THEN
  SET_TAC[]);;

let MOI_S3CP_EULER_LE1 = prove
 (mk_imp(moi_n3 MOI_FND_SURFACE_SPHERE,
  `!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\ ~pl_sphere 2 (UNIONS c)
     ==> complex_euler c <= &1`),
  DISCH_TAC THEN X_GEN_TAC `c:(real^3->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^3->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`complex_euler (c:(real^3->bool)->bool)`; `&2`] REAL_LT_INTEGERS) THEN
  REWRITE_TAC[MOI_STD_EULER_INTEGER; INTEGER_CLOSED] THEN
  MAP_EVERY UNDISCH_TAC
   [`complex_euler (c:(real^3->bool)->bool) <= &2`;
    `~(complex_euler (c:(real^3->bool)->bool) = &2)`] THEN
  REAL_ARITH_TAC);;

let MOI_S3CP_COMPONENTS_2 = prove
 (`!p q:real^3->bool.
     closed p /\ closed q /\ connected p /\ connected q /\ ~(p = {}) /\ ~(q = {}) /\
     DISJOINT p q
     ==> components (p UNION q) = {p, q}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_UNIQUE_2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `q:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`DISJOINT (p:real^3->bool) q`; `~((p:real^3->bool) = {})`;
    `~((q:real^3->bool) = {})`] THEN
  SET_TAC[]);;

(* The theorem COMPRESS. *)

let COMPRESS = prove
 (MOI_S30_COMPRESS,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "split") (CONJUNCTS_THEN2 (LABEL_TAC "302")
    (CONJUNCTS_THEN2 (LABEL_TAC "266") (CONJUNCTS_THEN2 (LABEL_TAC "sph")
    (CONJUNCTS_THEN2 (LABEL_TAC "bounds") (LABEL_TAC "ess")))))) THEN
  MAP_EVERY X_GEN_TAC [`m:(real^3->bool)->bool`; `hs:real^3->bool`; `ks:real^3->bool`;
                       `u:real^3->bool`; `s:real^3->bool`; `d:real^3->bool`;
                       `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  (* the disk and its boundary curve *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (d:real^3->bool)
      (IMAGE (f:real^3->real^3) (relative_frontier s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (f:real^3->real^3) (relative_frontier s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      MP_TAC(ISPECL [`s:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* split along the disk *)
  USE_THEN "split" (MP_TAC o SPECL
    [`m:(real^3->bool)->bool`; `d:real^3->bool`;
     `IMAGE (f:real^3->real^3) (relative_frontier s)`; `u:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `j2:real^3->bool` (X_CHOOSE_THEN `d1:real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `m':(real^3->bool)->bool`
    (MAP_EVERY (fun th ->
       if is_forall (concl th) then LABEL_TAC "xcl" th
       else if is_eq (concl th) &&
               lhs (concl th) = `UNIONS (m':(real^3->bool)->bool)`
       then ASSUME_TAC (SYM th) else ASSUME_TAC th) o CONJUNCTS))))))) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `j2:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(a:real^3->bool) SUBSET UNIONS m /\ UNIONS (m':(real^3->bool)->bool) SUBSET u /\
    ~(UNIONS m' = {}) /\ DISJOINT u (hs:real^3->bool) /\ DISJOINT u (ks:real^3->bool) /\
    DISJOINT (UNIONS m') hs /\ DISJOINT (UNIONS m') ks`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(UNIONS m DIFF a) UNION d1 UNION d2 =
                 UNIONS (m':(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC
     [`(a:real^3->bool) SUBSET UNIONS m INTER u`; `UNIONS (m:(real^3->bool)->bool) SUBSET u`;
      `(d1:real^3->bool) SUBSET u`; `(d2:real^3->bool) SUBSET u`;
      `~((d1:real^3->bool) = {})`; `DISJOINT (u:real^3->bool) (hs UNION ks)`] THEN
    SPEC_TAC(`UNIONS (m:(real^3->bool)->bool)`,`mm:real^3->bool`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (hs:real^3->bool) ks` ASSUME_TAC THENL
   [UNDISCH_TAC `euclidean_separates (UNIONS (m:(real^3->bool)->bool)) hs ks` THEN
    REWRITE_TAC[euclidean_separates] THEN
    DISCH_THEN(X_CHOOSE_THEN `uu:real^3->bool` (X_CHOOSE_THEN `vv:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (uu:real^3->bool) vv`; `(hs:real^3->bool) SUBSET uu`;
      `(ks:real^3->bool) SUBSET vv`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the bounding 3-manifold and its modification *)
  USE_THEN "bounds" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "xcl" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
       (ASSUME_TAC o REWRITE_RULE[ASSUME
         `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)`])
       (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `compact (UNIONS (x':(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the two sides (26.6) and the separation of the split surface *)
  USE_THEN "266" (MP_TAC o SPEC `m:(real^3->bool)->bool` o
                  REWRITE_RULE[MOISE_266_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closed (UNIONS (m:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `euclidean_separates (UNIONS (m':(real^3->bool)->bool)) hs ks`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (m:(real^3->bool)->bool)`; `b:real^3->bool`;
                   `hs:real^3->bool`; `ks:real^3->bool`] MOI_S3CP_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [MATCH_MP_TAC MOI_S3CP_SEP_TRANSFER;
      MATCH_MP_TAC MOI_S3CP_SEP_SWAP THEN MATCH_MP_TAC MOI_S3CP_SEP_TRANSFER] THEN
    MAP_EVERY EXISTS_TAC [`UNIONS (m:(real^3->bool)->bool)`; `u:real^3->bool`;
                          `UNIONS (x':(real^3->bool)->bool)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* 30.4 cases *)
  USE_THEN "ess" (MP_TAC o SPECL
    [`m:(real^3->bool)->bool`; `a:real^3->bool`;
     `IMAGE (f:real^3->real^3) (relative_frontier s)`; `j1:real^3->bool`;
     `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
     `m':(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m1:(real^3->bool)->bool` (X_CHOOSE_THEN `m2:(real^3->bool)->bool`
      STRIP_ASSUME_TAC))) THENL
   [EXISTS_TAC `m':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* two non-spherical pieces: chi of each exceeds chi(m), 30.2 picks one *)
  SUBGOAL_THEN `UNIONS m1 UNION UNIONS m2 = UNIONS (m':(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `m':(real^3->bool)->bool = m1 UNION m2` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[UNIONS_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_euler (m:(real^3->bool)->bool) + &2 =
    complex_euler (m1:(real^3->bool)->bool) + complex_euler (m2:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `complex_euler (m':(real^3->bool)->bool) =
                 complex_euler (m:(real^3->bool)->bool) + &2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `m':(real^3->bool)->bool = m1 UNION m2` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S3CP_EULER_DISJOINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `m':(real^3->bool)->bool = m1 UNION m2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   `complex_euler (m1:(real^3->bool)->bool) <= &1 /\
    complex_euler (m2:(real^3->bool)->bool) <= &1`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "sph" (fun th -> CONJ_TAC THEN
      MATCH_MP_TAC (MATCH_MP MOI_S3CP_EULER_LE1 th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_euler (m:(real^3->bool)->bool) < complex_euler (m1:(real^3->bool)->bool) /\
    complex_euler (m:(real^3->bool)->bool) < complex_euler (m2:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`complex_euler (m:(real^3->bool)->bool) + &2 =
       complex_euler (m1:(real^3->bool)->bool) + complex_euler (m2:(real^3->bool)->bool)`;
      `complex_euler (m1:(real^3->bool)->bool) <= &1`;
      `complex_euler (m2:(real^3->bool)->bool) <= &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (m1:(real^3->bool)->bool) SUBSET u /\ UNIONS (m2:(real^3->bool)->bool) SUBSET u`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`UNIONS m1 UNION UNIONS m2 = UNIONS (m':(real^3->bool)->bool)`;
      `UNIONS (m':(real^3->bool)->bool) SUBSET u`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (UNIONS (m1:(real^3->bool)->bool)) /\ closed (UNIONS (m2:(real^3->bool)->bool)) /\
    closed (UNIONS (m':(real^3->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components (UNIONS (m':(real^3->bool)->bool)) = {UNIONS m1, UNIONS m2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS m1 UNION UNIONS m2 = UNIONS (m':(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S3CP_COMPONENTS_2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "302" (MP_TAC o SPECL [`(:real^3)`; `UNIONS (m':(real^3->bool)->bool)`;
                                  `hs:real^3->bool`; `ks:real^3->bool`] o
                  REWRITE_RULE[MOISE_302_STATEMENT]) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; separates_in; GSYM OPEN_IN;
              GSYM euclidean_separates] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_UNIV; CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV;
                 FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dd = UNIONS (m1:(real^3->bool)->bool) \/ dd = UNIONS m2` MP_TAC THENL
   [UNDISCH_TAC `(dd:real^3->bool) IN components (UNIONS (m':(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `m1:(real^3->bool)->bool`; EXISTS_TAC `m2:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

