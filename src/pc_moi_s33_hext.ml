(* ========================================================================= *)
(* pc_moi_s33_hext: Moise GTM 47 p.237 (Fig. 33.2): PL holed disks have PL  *)
(* homeomorphisms realizing any matching of the boundary circles and any    *)
(* PL homeomorphism on one circle (either orientation).                      *)
(* Main theorem HOLED_EXT : |- MOI_S33_HOLED_EXT (pc_moi_s33_stmt.ml).      *)
(* Route:                                                                   *)
(*   A1 the labelled circles are the model circles (connectedness);         *)
(*   A2 ambient exchange of two families of disks (two MOI_FSB_MDE0 steps); *)
(*   A3 a model self-map taking any boundary circle to the outer one        *)
(*      (annulus end swap, then A2);                                        *)
(*   A4 the model lemma: extend over the outer square (cone extension) and  *)
(*      move the holes back (A2);  B: conjugation with f, f'.               *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1 (A1): labelled circles.  A connected set inside the union of      *)
(* two disjoint closed sets lies in one of them; two finite families of     *)
(* pairwise disjoint nonempty closed connected sets with the same union    *)
(* are the same family up to relabelling.                                   *)
(* ========================================================================= *)

let MOI_S3HX_CONNECTED_IN_ONE = prove
 (`!(s:real^N->bool) t u.
     connected s /\ closed t /\ closed u /\ s SUBSET t UNION u /\ DISJOINT t u /\
     ~(s INTER t = {})
     ==> s SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOSED] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^N->bool`; `u:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((s:real^N->bool) INTER t = {})` THEN
  UNDISCH_TAC `DISJOINT (t:real^N->bool) u` THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET t UNION u` THEN SET_TAC[]);;

let MOI_S3HX_CLOSED_UNIONS_OTHER = prove
 (`!k (C:num->real^N->bool) j.
     (!i. i <= k ==> closed (C i))
     ==> closed (UNIONS {C i | i <= k /\ ~(i = j)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i:num | i <= k}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3HX_CIRCLE_ID = prove
 (`!k (C:num->real^N->bool) (J:num->real^N->bool).
     (!i. i <= k ==> closed (C i) /\ connected (C i) /\ ~(C i = {}) /\
                     closed (J i) /\ connected (J i) /\ ~(J i = {})) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i')
             ==> DISJOINT (C i) (C i') /\ DISJOINT (J i) (J i')) /\
     UNIONS {C i | i <= k} = UNIONS {J i | i <= k}
     ==> (!i. i <= k ==> ?j. j <= k /\ J i = C j) /\
         (!j. j <= k ==> ?i. i <= k /\ J i = C j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f") (CONJUNCTS_THEN2 (LABEL_TAC "d") (LABEL_TAC "u"))) THEN
  SUBGOAL_THEN `!i. i <= k ==> ?j. j <= k /\ (J:num->real^N->bool) i = C j` (LABEL_TAC "one") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "f" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `?j x:real^N. j <= k /\ x IN (C:num->real^N->bool) j /\ x IN (J:num->real^N->bool) i` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((J:num->real^N->bool) i = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS {(C:num->real^N->bool) i | i <= k}` MP_TAC THENL
       [USE_THEN "u" SUBST1_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `(J:num->real^N->bool) i` THEN ASM_MESON_TAC[];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "f" (MP_TAC o C MP (ASSUME `j:num <= k`) o SPEC `j:num`) THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3HX_CONNECTED_IN_ONE THEN
      EXISTS_TAC `UNIONS {(C:num->real^N->bool) i' | i' <= k /\ ~(i' = j)}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3HX_CLOSED_UNIONS_OTHER THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS {(J:num->real^N->bool) i | i <= k}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
          USE_THEN "u" (SUBST1_TAC o SYM) THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]];
        REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `i':num` THEN STRIP_TAC THEN
        USE_THEN "d" (MP_TAC o SPECL [`j:num`; `i':num`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[DISJOINT]];
        UNDISCH_TAC `(x:real^N) IN C (j:num)` THEN
        UNDISCH_TAC `(x:real^N) IN (J:num->real^N->bool) i` THEN SET_TAC[]];
      MATCH_MP_TAC MOI_S3HX_CONNECTED_IN_ONE THEN
      EXISTS_TAC `UNIONS {(J:num->real^N->bool) i' | i' <= k /\ ~(i' = i)}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3HX_CLOSED_UNIONS_OTHER THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS {(C:num->real^N->bool) i | i <= k}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
          USE_THEN "u" SUBST1_TAC THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]];
        REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `i':num` THEN STRIP_TAC THEN
        USE_THEN "d" (MP_TAC o SPECL [`i:num`; `i':num`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[DISJOINT]];
        UNDISCH_TAC `(x:real^N) IN C (j:num)` THEN
        UNDISCH_TAC `(x:real^N) IN (J:num->real^N->bool) i` THEN SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "f" (MP_TAC o C MP (ASSUME `j:num <= k`) o SPEC `j:num`) THEN STRIP_TAC THEN
  UNDISCH_TAC `~((C:num->real^N->bool) j = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS {(J:num->real^N->bool) i | i <= k}` MP_TAC THENL
   [USE_THEN "u" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(C:num->real^N->bool) j` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "one" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `j':num = j` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "d" (MP_TAC o SPECL [`j:num`; `j':num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN s` THEN UNDISCH_TAC `(y:real^N) IN C (j:num)` THEN
  UNDISCH_TAC `s = (J:num->real^N->bool) i` THEN
  UNDISCH_TAC `(J:num->real^N->bool) i = C (j':num)` THEN SET_TAC[]);;

(* ========================================================================= *)
(* Part 2 (A2): ambient exchange of two families of k disjoint PL disks      *)
(* in an open connected W of the plane, by a PLH of the plane fixing the    *)
(* complement of W.  W is open and nonempty in real^2, hence not compact,   *)
(* so it has a point z off the finitely many compact disks; k small         *)
(* disjoint squares near z serve as an intermediate family, and           *)
(* MOI_FSB_MDE0 moves X onto them and them onto Y.                          *)
(* ========================================================================= *)

let MOI_S3HX_FREE_POINT = prove
 (`!W (D:real^2->bool). open W /\ ~(W = {}) /\ compact D /\ D SUBSET W
     ==> ?z. z IN W /\ ~(z IN D)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!W D:real^2->bool. ~(W SUBSET D) ==> ?z. z IN W /\ ~(z IN D)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `W:real^2->bool = D` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `D:real^2->bool` CLOPEN) THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

let MOI_S3HX_SQUARES = prove
 (`!(z:real^2) d k.
     &0 < d
     ==> (!i. i < k ==> dist(z,z + (&3 * &i * d) % basis 1) + d < (&3 * &k + &3) * d) /\
         (!i j. i < k /\ j < k /\ ~(i = j)
                ==> DISJOINT (moi_fsb_sq (z + (&3 * &i * d) % basis 1) d)
                             (moi_fsb_sq (z + (&3 * &j * d) % basis 1) d))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH `z - (z + x):real^2 = --x`; NORM_NEG; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
    SUBGOAL_THEN `abs(&3 * &i * d) = (&3 * &i) * d` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&3 * &i) * d + d = (&3 * &i + &1) * d`] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i:num < k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= abs(&i - &j:real)` ASSUME_TAC THENL
     [ASM_CASES_TAC `i:num < j` THENL
       [SUBGOAL_THEN `&i + &1 <= &j:real` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
        SUBGOAL_THEN `&j + &1 <= &i:real` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 * d <= abs(&3 * &i * d - &3 * &j * d)` ASSUME_TAC THENL
     [SUBGOAL_THEN `abs(&3 * &i * d - &3 * &j * d) = (&3 * d) * abs(&i - &j)`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&3 * &i * d - &3 * &j * d = (&3 * d) * (&i - &j)`] THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`&3 * d`; `&1`; `abs(&i - &j:real)`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_FSB_IN_SQ] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    X_GEN_TAC `y:real^2` THEN
    UNDISCH_TAC `&3 * d <= abs(&3 * &i * d - &3 * &j * d)` THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC]);;

let MOI_S3HX_EXCHANGE = prove
 (`!k W (X:num->real^2->bool) (Y:num->real^2->bool).
     open W /\ connected W /\
     (!i. i < k ==> pl_sphere 1 (X i) /\ X i UNION inside (X i) SUBSET W /\
                    pl_sphere 1 (Y i) /\ Y i UNION inside (Y i) SUBSET W) /\
     (!i j. i < k /\ j < k /\ ~(i = j)
            ==> DISJOINT (X i UNION inside (X i)) (X j UNION inside (X j)) /\
                DISJOINT (Y i UNION inside (Y i)) (Y j UNION inside (Y j)))
     ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
               (!x. ~(x IN W) ==> h x = x) /\
               (!i. i < k ==> IMAGE h (X i UNION inside (X i)) = Y i UNION inside (Y i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "xy") (LABEL_TAC "dis")))) THEN
  ASM_CASES_TAC `k = 0` THENL
   [MATCH_MP_TAC MOI_FSB_MDE0 THEN ASM_REWRITE_TAC[LT]; ALL_TAC] THEN
  (* the compact union of all the disks, and a free point *)
  ABBREV_TAC `D = UNIONS {(X:num->real^2->bool) i UNION inside (X i) | i < k} UNION
                  UNIONS {(Y:num->real^2->bool) i UNION inside (Y i) | i < k}` THEN
  SUBGOAL_THEN
   `!i. i < k ==> (X:num->real^2->bool) i UNION inside (X i) SUBSET D /\
                  (Y:num->real^2->bool) i UNION inside (Y i) SUBSET D`
  (LABEL_TAC "inD") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    UNDISCH_TAC `i:num < k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (D:real^2->bool) /\ D SUBSET W /\ ~(W:real^2->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "xy" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      MESON_TAC[MOI_S5C_SPHERE1_COMPACT];
      EXPAND_TAC "D" THEN
      MATCH_MP_TAC(SET_RULE `!a b w:real^2->bool. a SUBSET w /\ b SUBSET w ==> a UNION b SUBSET w`) THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      USE_THEN "xy" (fun th -> MESON_TAC[th]);
      SUBGOAL_THEN `0 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "xy" (STRIP_ASSUME_TAC o C MP (ASSUME `0 < k`) o SPEC `0`) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON o check (fun th ->
        concl th = `pl_sphere 1 ((X:num->real^2->bool) 0)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `polygonal_path (pp:(real^2)list)` PATH_IMAGE_NONEMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:num->real^2->bool) 0 UNION inside (X 0) SUBSET W` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `D:real^2->bool`] MOI_S3HX_FREE_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W DIFF D:real^2->bool`; `z:real^2`] MOI_FSB_SQ_IN_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = r / (&3 * &k + &3)` THEN
  SUBGOAL_THEN `&0 < d /\ (&3 * &k + &3) * d = r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_LMUL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^2`; `d:real`; `k:num`] MOI_S3HX_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sqn") (LABEL_TAC "sqd")) THEN
  SUBGOAL_THEN
   `!i. i < k ==> moi_fsb_sq (z + (&3 * &i * d) % basis 1) d SUBSET W DIFF (D:real^2->bool)`
  (LABEL_TAC "sq") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_sq z r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (moi_fsb_sq z r)` THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC MOI_FSB_SQ_NEST THEN
    USE_THEN "sqn" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z = \i. relative_frontier
                        (moi_fsb_sq (z + (&3 * &i * d) % basis 1) d:real^2->bool)` THEN
  SUBGOAL_THEN
   `!i. i < k ==> pl_sphere 1 ((Z:num->real^2->bool) i) /\
                  Z i UNION inside (Z i) = moi_fsb_sq (z + (&3 * &i * d) % basis 1) d`
  (LABEL_TAC "zs") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "Z" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_fsb_sq (z + (&3 * &i * d) % basis 1) d:real^2->bool` MOI_FSB_POLY2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FSB_SQ]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* first exchange: X onto Z *)
  MP_TAC(ISPECL [`k:num`; `W:real^2->bool`; `X:num->real^2->bool`; `Z:num->real^2->bool`]
                MOI_FSB_MDE0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "xy" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "sq" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      SET_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "dis" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (CONJ (ASSUME `j:num < k`)
        (ASSUME `~(i:num = j)`))) o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      USE_THEN "sqd" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (CONJ (ASSUME `j:num < k`)
        (ASSUME `~(i:num = j)`))) o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "sq" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      USE_THEN "inD" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `g1:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "im1"))))) THEN
  (* second exchange: Z onto Y *)
  MP_TAC(ISPECL [`k:num`; `W:real^2->bool`; `Z:num->real^2->bool`; `Y:num->real^2->bool`]
                MOI_FSB_MDE0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "xy" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "sq" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      SET_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "dis" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (CONJ (ASSUME `j:num < k`)
        (ASSUME `~(i:num = j)`))) o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "zs" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      USE_THEN "sqd" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (CONJ (ASSUME `j:num < k`)
        (ASSUME `~(i:num = j)`))) o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "sq" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "inD" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "im2"))))) THEN
  MAP_EVERY EXISTS_TAC [`(h2:real^2->real^2) o (h1:real^2->real^2)`;
                        `(g1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[o_THM];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
    USE_THEN "im1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < k`)]) THEN
    USE_THEN "im2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < k`)])]);;

(* ========================================================================= *)
(* Part 3 (A3): any hole circle of the model can be made the outer          *)
(* circle by a PL self-homeomorphism of the model preserving its frontier.  *)
(* The annulus A = R DIFF interior Q_m (MOI_FSB_POLY_ANN) has a PLH S        *)
(* exchanging its ends (two parametrizations, MOI_S5C_ANN_SWAP); S carries  *)
(* the model onto R minus the open disks Q_m, S(Q_i) (i <> m), which A2     *)
(* moves back onto the Q_i fixing the outer circle.                          *)
(* ========================================================================= *)

let MOI_S3HX_SQ_ENDS = prove
 (`relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1]) /\
   relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1])`,
  SUBGOAL_THEN
   `!r. &0 < r
        ==> relative_frontier (interval[--vector[r;r]:real^2,vector[r;r]]) =
            interval[--vector[r;r],vector[r;r]] DIFF interval(--vector[r;r],vector[r;r])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `interval[--vector[r;r]:real^2,vector[r;r]]` MOI_FSB_POLY2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; VECTOR_2; DIMINDEX_2; FORALL_2] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[el 4 (CONJUNCTS th); INTERIOR_CLOSED_INTERVAL])];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_NEG_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S3HX_ANN_SELF_SWAP = prove
 (`!(a:real^2->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?S S'. pl_homeomorphism (a,a) (S,S') /\ IMAGE S j0 = j1 /\ IMAGE S j1 = j0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5C_ANN_SWAP) THEN
  UNDISCH_TAC `pl_annulus_with_ends (a:real^2->bool) j0 j1` THEN
  REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2` (X_CHOOSE_THEN `g1:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`(f2:real^2->real^2) o (g1:real^2->real^2)`;
                        `(f1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
             interval(--vector[&1;&1]:real^2,vector[&1;&1])
        ==> (g1:real^2->real^2) (f1 x) = x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f1:real^2->real^2,g1)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  SUBGOAL_THEN
   `IMAGE (g1:real^2->real^2)
      (IMAGE f1 (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) =
    relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
    IMAGE g1
      (IMAGE f1 (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) =
    relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC MOI_S3HX_SQ_ENDS THEN
    UNDISCH_TAC
     `!x. x IN interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
               interval(--vector[&1;&1]:real^2,vector[&1;&1])
          ==> (g1:real^2->real^2) (f1 x) = x` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* A self-homeomorphism of a closed set of real^N maps its frontier onto     *)
(* itself (invariance of domain on the interior).                            *)

let MOI_S3HX_HOMEO_FRONTIER = prove
 (`!(f:real^N->real^N) g s.
     homeomorphism (s,s) (f,g) /\ closed s ==> IMAGE f (frontier s) = frontier s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!(u:real^N->real^N) v. u continuous_on s /\ IMAGE u s = s /\
                  (!x. x IN s ==> v(u x) = x)
                  ==> IMAGE u (interior s) SUBSET interior s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
        MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (interior s) = interior s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g:real^N->real^N` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `IMAGE (g:real^N->real^N) (interior s) SUBSET interior s` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `f:real^N->real^N` THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

(* An ambient homeomorphism fixing the complement of interior R maps R and   *)
(* interior R onto themselves, and so does its inverse.                      *)

let MOI_S3HX_AMB_FIX = prove
 (`!(h:real^N->real^N) h' R.
     homeomorphism ((:real^N),(:real^N)) (h,h') /\ (!x. ~(x IN interior R) ==> h x = x)
     ==> IMAGE h (interior R) = interior R /\ IMAGE h R = R /\
         (!x. ~(x IN interior R) ==> h' x = x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~((x:real^N) IN interior R) ==> h' x = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `R:real^N->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `!x. ~((x:real^N) IN interior R) ==> h' x = x` THEN
  UNDISCH_TAC `!x. ~((x:real^N) IN interior R) ==> h x = x` THEN
  UNDISCH_TAC `!x:real^N. (h':real^N->real^N) ((h:real^N->real^N) x) = x` THEN
  UNDISCH_TAC `!y:real^N. (h:real^N->real^N) ((h':real^N->real^N) y) = y` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]);;

(* Images of differences of indexed unions under maps injective on T.        *)

let MOI_S3HX_IMAGE_DIFF_UNIONS = prove
 (`!(h:real^N->real^N) tt R R' (X:num->real^N->bool) Y k.
     (!x y. x IN tt /\ y IN tt /\ h x = h y ==> x = y) /\ R SUBSET tt /\
     (!i. i < k ==> X i SUBSET tt /\ IMAGE h (X i) = Y i) /\ IMAGE h R = R'
     ==> IMAGE h (R DIFF UNIONS {X i | i < k}) = R' DIFF UNIONS {Y i | i < k}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "xy") ASSUME_TAC))) THEN
  EXPAND_TAC "R'" THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "xy" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE (h:real^N->real^N) ((X:num->real^N->bool) i)` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^N = x'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "xy" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `~(?i. i < k /\ (y:real^N) IN (Y:num->real^N->bool) i)` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_S3HX_IMAGE_DIFF_UNIONS_P = prove
 (`!(h:real^N->real^N) tt R R' (X:num->real^N->bool) Y P.
     (!x y. x IN tt /\ y IN tt /\ h x = h y ==> x = y) /\ R SUBSET tt /\
     (!i. P i ==> X i SUBSET tt /\ IMAGE h (X i) = Y i) /\ IMAGE h R = R'
     ==> IMAGE h (R DIFF UNIONS {X i | P i}) = R' DIFF UNIONS {Y i | P i}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "xy") ASSUME_TAC))) THEN
  EXPAND_TAC "R'" THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "xy" (MP_TAC o C MP (ASSUME `(P:num->bool) i`) o SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE (h:real^N->real^N) ((X:num->real^N->bool) i)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^N = x'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_MESON_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "xy" (MP_TAC o C MP (ASSUME `(P:num->bool) i`) o SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `~(?i. P i /\ (y:real^N) IN (Y:num->real^N->bool) i)` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Part 4 (A3): any hole circle of the model is carried onto the outer      *)
(* circle by a PL self-homeomorphism of the model.  S swaps the ends of the *)
(* annulus A = R DIFF interior Q_m; the disks X_m = Q_m and X_i = S(Q_i)    *)
(* (i <> m) lie in interior R and are moved back onto the Q_i by A2.        *)
(* ========================================================================= *)

let MOI_S3HX_HOLE_FACTS = prove
 (`!k i. i < k
         ==> polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
             moi_fsb_hc i SUBSET interior (moi_fsb_hq k) /\
             pl_sphere 1 (relative_frontier (moi_fsb_hc i)) /\
             relative_frontier (moi_fsb_hc i) UNION inside (relative_frontier (moi_fsb_hc i)) =
             moi_fsb_hc i /\
             inside (relative_frontier (moi_fsb_hc i)) = interior (moi_fsb_hc i) /\
             relative_frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
             interior (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
             frontier (moi_fsb_hc i) = relative_frontier (moi_fsb_hc i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
                moi_fsb_hc i SUBSET interior (moi_fsb_hr k)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
  MP_TAC(ISPEC `moi_fsb_hc i` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 1 (CONJUNCTS th)); GSYM(el 2 (CONJUNCTS th));
                                   el 3 (CONJUNCTS th); el 7 (CONJUNCTS th)]) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
  MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `moi_fsb_hr k SUBSET interior (moi_fsb_hq k)` THEN
  UNDISCH_TAC `moi_fsb_hc i SUBSET interior (moi_fsb_hr k)` THEN SET_TAC[]);;

let MOI_S3HX_OUTER_FACTS = prove
 (`!k. polytope (moi_fsb_hq k) /\ ~(interior (moi_fsb_hq k) = {}) /\
       pl_cell_with_boundary 2 (moi_fsb_hq k) (relative_frontier (moi_fsb_hq k)) /\
       relative_frontier (moi_fsb_hq k) SUBSET moi_fsb_hq k /\
       DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k)) /\
       moi_fsb_hq k SUBSET relative_frontier (moi_fsb_hq k) UNION interior (moi_fsb_hq k) /\
       interior (moi_fsb_hq k) SUBSET moi_fsb_hq k /\
       open (interior (moi_fsb_hq k)) /\ connected (interior (moi_fsb_hq k))`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_fsb_hr k SUBSET interior (moi_fsb_hq k)` THEN
    UNDISCH_TAC `~(interior (moi_fsb_hr k) = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_fsb_hq k` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 0 (CONJUNCTS th)) THEN ASSUME_TAC(el 4 (CONJUNCTS th))) THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET; OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[]; SET_TAC[]; SET_TAC[];
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTERIOR THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX]]);;

let MOI_S3HX_AMB_FRONTIER = prove
 (`!(h:real^N->real^N) h' s.
     homeomorphism ((:real^N),(:real^N)) (h,h')
     ==> IMAGE h (frontier s) = frontier (IMAGE h s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `h':real^N->real^N`; `(:real^N)`; `(:real^N)`;
                 `s:real^N->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_FRONTIER_OF]);;

let MOI_S3HX_NORMAL = prove
 (`!k m. m < k
     ==> ?p q. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (p,q) /\
               IMAGE p (relative_frontier (moi_fsb_hc m)) = relative_frontier (moi_fsb_hq k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "hcd")))))) THEN
  MP_TAC(SPEC `k:num` MOI_S3HX_OUTER_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
            moi_fsb_hc i SUBSET interior (moi_fsb_hq k) /\
            pl_sphere 1 (relative_frontier (moi_fsb_hc i)) /\
            relative_frontier (moi_fsb_hc i) UNION inside (relative_frontier (moi_fsb_hc i)) =
            moi_fsb_hc i /\
            inside (relative_frontier (moi_fsb_hc i)) = interior (moi_fsb_hc i) /\
            relative_frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
            interior (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
            frontier (moi_fsb_hc i) = relative_frontier (moi_fsb_hc i)`
  (LABEL_TAC "hc") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3HX_HOLE_FACTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `m:num < k`) o SPEC `m:num`) THEN
  ABBREV_TAC `R = moi_fsb_hq k` THEN
  (* the end swap of the annulus R DIFF interior Q_m *)
  MP_TAC(ISPECL [`R:real^2->bool`; `moi_fsb_hc m`] MOI_FSB_POLY_ANN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3HX_ANN_SELF_SWAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->real^2` (X_CHOOSE_THEN `S':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "SA") (CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "S2"))))) THEN
  USE_THEN "SA" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  SUBGOAL_THEN `relative_frontier (R:real^2->bool) SUBSET (R DIFF interior (moi_fsb_hc m)) /\
                relative_frontier (moi_fsb_hc m) SUBSET (R DIFF interior (moi_fsb_hc m)) /\
                DISJOINT (relative_frontier R) (relative_frontier (moi_fsb_hc m)) /\
                DISJOINT (relative_frontier R) (moi_fsb_hc m)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `relative_frontier R SUBSET (R:real^2->bool)` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier R) (interior (R:real^2->bool))` THEN
    UNDISCH_TAC `moi_fsb_hc m SUBSET interior (R:real^2->bool)` THEN
    UNDISCH_TAC `relative_frontier (moi_fsb_hc m) SUBSET moi_fsb_hc m` THEN
    UNDISCH_TAC `interior (moi_fsb_hc m) SUBSET moi_fsb_hc m` THEN
    UNDISCH_TAC `interior (R:real^2->bool) SUBSET R` THEN
    MP_TAC(ISPEC `relative_frontier (moi_fsb_hc m)` INSIDE_NO_OVERLAP) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* S on the other holes *)
  SUBGOAL_THEN
   `!i. i < k /\ ~(i = m)
        ==> moi_fsb_hc i SUBSET R DIFF interior (moi_fsb_hc m) /\
            IMAGE (S:real^2->real^2) (moi_fsb_hc i) SUBSET interior R DIFF moi_fsb_hc m`
  (LABEL_TAC "Shc") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    SUBGOAL_THEN `DISJOINT (moi_fsb_hc i) (moi_fsb_hc m)` ASSUME_TAC THENL
     [USE_THEN "hcd" (ACCEPT_TAC o C MP (ASSUME `~(i:num = m)`) o SPECL [`i:num`; `m:num`]);
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_fsb_hc i SUBSET R DIFF interior (moi_fsb_hc m)` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (moi_fsb_hc i) (moi_fsb_hc m)` THEN
      UNDISCH_TAC `moi_fsb_hc i SUBSET interior (R:real^2->bool)` THEN
      UNDISCH_TAC `interior (R:real^2->bool) SUBSET R` THEN
      UNDISCH_TAC `interior (moi_fsb_hc m) SUBSET moi_fsb_hc m` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN R DIFF interior (moi_fsb_hc m) /\
                  ~(x IN relative_frontier (moi_fsb_hc m)) /\ ~(x IN relative_frontier R)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN moi_fsb_hc i` THEN
      UNDISCH_TAC `moi_fsb_hc i SUBSET R DIFF interior (moi_fsb_hc m)` THEN
      UNDISCH_TAC `DISJOINT (moi_fsb_hc i) (moi_fsb_hc m)` THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc m) SUBSET moi_fsb_hc m` THEN
      UNDISCH_TAC `moi_fsb_hc i SUBSET interior (R:real^2->bool)` THEN
      UNDISCH_TAC `DISJOINT (relative_frontier R) (interior (R:real^2->bool))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((S:real^2->real^2) x IN relative_frontier R) /\
                  ~(S x IN relative_frontier (moi_fsb_hc m)) /\
                  S x IN R DIFF interior (moi_fsb_hc m)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "S1" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `x:real^2 = y` SUBST_ALL_TAC THENL
         [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
        USE_THEN "S2" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `x:real^2 = y` SUBST_ALL_TAC THENL
         [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
        UNDISCH_TAC `IMAGE (S:real^2->real^2) (R DIFF interior (moi_fsb_hc m)) =
                     R DIFF interior (moi_fsb_hc m)` THEN
        UNDISCH_TAC `(x:real^2) IN R DIFF interior (moi_fsb_hc m)` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(S:real^2->real^2) x IN R DIFF interior (moi_fsb_hc m)` THEN
    UNDISCH_TAC `~((S:real^2->real^2) x IN relative_frontier R)` THEN
    UNDISCH_TAC `~((S:real^2->real^2) x IN relative_frontier (moi_fsb_hc m))` THEN
    UNDISCH_TAC `(R:real^2->bool) SUBSET relative_frontier R UNION interior R` THEN
    UNDISCH_TAC `relative_frontier (moi_fsb_hc m) UNION
                 inside (relative_frontier (moi_fsb_hc m)) = moi_fsb_hc m` THEN
    UNDISCH_TAC `inside (relative_frontier (moi_fsb_hc m)) = interior (moi_fsb_hc m)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the images of the other holes under S *)
  SUBGOAL_THEN
   `!i. i < k /\ ~(i = m)
        ==> pl_sphere 1 (IMAGE (S:real^2->real^2) (relative_frontier (moi_fsb_hc i))) /\
            IMAGE S (moi_fsb_hc i) =
            IMAGE S (relative_frontier (moi_fsb_hc i)) UNION
            inside (IMAGE S (relative_frontier (moi_fsb_hc i))) /\
            frontier (IMAGE S (moi_fsb_hc i)) = IMAGE S (relative_frontier (moi_fsb_hc i)) /\
            inside (IMAGE S (relative_frontier (moi_fsb_hc i))) =
            IMAGE S (interior (moi_fsb_hc i))`
  (LABEL_TAC "Sim") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    USE_THEN "Shc" (STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `i:num < k`)
      (ASSUME `~(i:num = m)`)) o SPEC `i:num`) THEN
    MP_TAC(ISPECL [`R DIFF interior (moi_fsb_hc m)`; `R DIFF interior (moi_fsb_hc m)`;
                   `S:real^2->real^2`; `S':real^2->real^2`; `moi_fsb_hc i`]
                  MOI_FSB_IMG_CELL) THEN
    ANTS_TAC THENL [USE_THEN "SA" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `interior (moi_fsb_hc i) =
                  moi_fsb_hc i DIFF relative_frontier (moi_fsb_hc i)` SUBST1_TAC THENL
     [MP_TAC(ISPEC `relative_frontier (moi_fsb_hc i)` INSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc i) UNION
                   inside (relative_frontier (moi_fsb_hc i)) = moi_fsb_hc i` THEN
      UNDISCH_TAC `inside (relative_frontier (moi_fsb_hc i)) = interior (moi_fsb_hc i)` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (S:real^2->real^2) (moi_fsb_hc i DIFF relative_frontier (moi_fsb_hc i)) =
      IMAGE S (moi_fsb_hc i) DIFF IMAGE S (relative_frontier (moi_fsb_hc i))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsb_hc i SUBSET R DIFF interior (moi_fsb_hc m)` THEN
      UNDISCH_TAC `!x. x IN R DIFF interior (moi_fsb_hc m) ==> (S':real^2->real^2) (S x) = x` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (S:real^2->real^2) (moi_fsb_hc i) =
                 IMAGE S (relative_frontier (moi_fsb_hc i)) UNION
                 inside (IMAGE S (relative_frontier (moi_fsb_hc i)))` THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `IMAGE (S:real^2->real^2) (relative_frontier (moi_fsb_hc i))`
      INSIDE_NO_OVERLAP) THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the family X: Q_m and the images S(Q_i) *)
  ABBREV_TAC `X = \i. if i = m then relative_frontier (moi_fsb_hc m)
                      else IMAGE (S:real^2->real^2) (relative_frontier (moi_fsb_hc i))` THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> pl_sphere 1 ((X:num->real^2->bool) i) /\
            X i UNION inside (X i) SUBSET interior R /\
            frontier (X i UNION inside (X i)) = X i /\
            X i UNION inside (X i) =
              (if i = m then moi_fsb_hc m else IMAGE (S:real^2->real^2) (moi_fsb_hc i)) /\
            inside (X i) =
              (if i = m then interior (moi_fsb_hc m) else IMAGE S (interior (moi_fsb_hc i)))`
  (LABEL_TAC "xf") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `relative_frontier (moi_fsb_hc m) UNION interior (moi_fsb_hc m) =
                    moi_fsb_hc m` SUBST1_TAC THENL
       [UNDISCH_TAC `relative_frontier (moi_fsb_hc m) UNION
                     inside (relative_frontier (moi_fsb_hc m)) = moi_fsb_hc m` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      USE_THEN "Sim" (STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `i:num < k`)
        (ASSUME `~(i:num = m)`)) o SPEC `i:num`) THEN
      USE_THEN "Shc" (STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `i:num < k`)
        (ASSUME `~(i:num = m)`)) o SPEC `i:num`) THEN
      UNDISCH_TAC `IMAGE (S:real^2->real^2) (moi_fsb_hc i) =
                   IMAGE S (relative_frontier (moi_fsb_hc i)) UNION
                   inside (IMAGE S (relative_frontier (moi_fsb_hc i)))` THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (S:real^2->real^2) (moi_fsb_hc i) SUBSET
                   interior R DIFF moi_fsb_hc m` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < k /\ j < k /\ ~(i = j)
          ==> DISJOINT ((X:num->real^2->bool) i UNION inside (X i)) (X j UNION inside (X j))`
  (LABEL_TAC "xd") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "xf" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (MP (SPEC `i:num` th) (ASSUME `i:num < k`)))))]) THEN
    USE_THEN "xf" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (MP (SPEC `j:num` th) (ASSUME `j:num < k`)))))]) THEN
    SUBGOAL_THEN `DISJOINT (moi_fsb_hc i) (moi_fsb_hc j)` ASSUME_TAC THENL
     [USE_THEN "hcd" (ACCEPT_TAC o C MP (ASSUME `~(i:num = j)`) o SPECL [`i:num`; `j:num`]);
      ALL_TAC] THEN
    ASM_CASES_TAC `i:num = m` THEN ASM_CASES_TAC `j:num = m` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      USE_THEN "Shc" (MP_TAC o C MP (CONJ (ASSUME `j:num < k`) (ASSUME `~(j:num = m)`)) o
        SPEC `j:num`) THEN
      UNDISCH_TAC `i:num = m` THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
      USE_THEN "Shc" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (ASSUME `~(i:num = m)`)) o
        SPEC `i:num`) THEN
      UNDISCH_TAC `j:num = m` THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
      USE_THEN "Shc" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (ASSUME `~(i:num = m)`)) o
        SPEC `i:num`) THEN
      USE_THEN "Shc" (MP_TAC o C MP (CONJ (ASSUME `j:num < k`) (ASSUME `~(j:num = m)`)) o
        SPEC `j:num`) THEN
      UNDISCH_TAC `DISJOINT (moi_fsb_hc i) (moi_fsb_hc j)` THEN
      UNDISCH_TAC `!x. x IN R DIFF interior (moi_fsb_hc m) ==> (S':real^2->real^2) (S x) = x` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  (* A2 moves the X disks back onto the holes *)
  MP_TAC(ISPECL [`k:num`; `interior R:real^2->bool`; `X:num->real^2->bool`;
                 `\i. relative_frontier (moi_fsb_hc i)`] MOI_S3HX_EXCHANGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "xf" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "xd" (ACCEPT_TAC o C MP (CONJ (ASSUME `i:num < k`) (CONJ (ASSUME `j:num < k`)
          (ASSUME `~(i:num = j)`))) o SPECL [`i:num`; `j:num`]);
        USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
        USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "hcd" (ACCEPT_TAC o C MP (ASSUME `~(i:num = j)`) o SPECL [`i:num`; `j:num`])]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "hP") (CONJUNCTS_THEN2 (LABEL_TAC "hfix") (LABEL_TAC "him"))))) THEN
  SUBGOAL_THEN `homeomorphism ((:real^2),(:real^2)) (h:real^2->real^2,h')` (LABEL_TAC "hH") THENL
   [USE_THEN "hP" (fun th -> REWRITE_TAC[CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `R:real^2->bool`] MOI_S3HX_AMB_FIX) THEN
  ANTS_TAC THENL [USE_THEN "hH" (fun th -> USE_THEN "hfix" (fun th' -> REWRITE_TAC[th; th']));
                  ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h'fix"))) THEN
  (* circles and insides *)
  SUBGOAL_THEN
   `!i. i < k ==> IMAGE (h:real^2->real^2) (X i) = relative_frontier (moi_fsb_hc i) /\
                  IMAGE h (inside (X i)) = interior (moi_fsb_hc i)`
  (LABEL_TAC "hci") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "xf" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    USE_THEN "him" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `relative_frontier (moi_fsb_hc i) UNION
                        inside (relative_frontier (moi_fsb_hc i)) = moi_fsb_hc i`] THEN
    DISCH_THEN(LABEL_TAC "hXi") THEN
    SUBGOAL_THEN `IMAGE (h:real^2->real^2) (X(i:num)) = relative_frontier (moi_fsb_hc i)`
    (LABEL_TAC "hX") THENL
     [SUBGOAL_THEN `IMAGE (h:real^2->real^2) (X(i:num)) =
                    IMAGE h (frontier (X i UNION inside (X i)))` SUBST1_TAC THENL
       [REWRITE_TAC[ASSUME `frontier ((X:num->real^2->bool) i UNION inside (X i)) = X i`];
        ALL_TAC] THEN
      USE_THEN "hH" (fun th -> REWRITE_TAC[MATCH_MP MOI_S3HX_AMB_FRONTIER th]) THEN
      USE_THEN "hXi" SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "hX" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `inside ((X:num->real^2->bool) i) = (X i UNION inside (X i)) DIFF X i`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `(X:num->real^2->bool) i` INSIDE_NO_OVERLAP) THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (h:real^2->real^2) (((X:num->real^2->bool) i UNION inside (X i)) DIFF X i) =
      IMAGE h (X i UNION inside (X i)) DIFF IMAGE h (X i)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN CONJ_TAC THENL
       [USE_THEN "hH" (MP_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN MESON_TAC[];
        SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "hXi" SUBST1_TAC THEN USE_THEN "hX" SUBST1_TAC THEN
    MP_TAC(ISPEC `relative_frontier (moi_fsb_hc i)` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `relative_frontier (moi_fsb_hc i) UNION
                 inside (relative_frontier (moi_fsb_hc i)) = moi_fsb_hc i` THEN
    UNDISCH_TAC `inside (relative_frontier (moi_fsb_hc i)) = interior (moi_fsb_hc i)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the model under S and then under h *)
  SUBGOAL_THEN `holed_disk_model k = R DIFF UNIONS {interior (moi_fsb_hc i) | i < k}`
  (LABEL_TAC "Mdef") THENL
   [REWRITE_TAC[MOI_FSB_HD_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holed_disk_model k =
    (R DIFF interior (moi_fsb_hc m)) DIFF
    UNIONS {interior (moi_fsb_hc i) | i < k /\ ~(i = m)}`
  (LABEL_TAC "M2") THENL
   [USE_THEN "Mdef" SUBST1_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    UNDISCH_TAC `m:num < k` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (S:real^2->real^2) (holed_disk_model k) =
    R DIFF UNIONS {inside ((X:num->real^2->bool) i) | i < k}`
  (LABEL_TAC "SM") THENL
   [USE_THEN "M2" SUBST1_TAC THEN
    MP_TAC(ISPECL [`S:real^2->real^2`; `R DIFF interior (moi_fsb_hc m)`;
                   `R DIFF interior (moi_fsb_hc m)`; `R DIFF interior (moi_fsb_hc m)`;
                   `\i. interior (moi_fsb_hc i)`; `\i. inside ((X:num->real^2->bool) i)`;
                   `\i:num. i < k /\ ~(i = m)`] MOI_S3HX_IMAGE_DIFF_UNIONS_P) THEN
    REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `!x. x IN R DIFF interior (moi_fsb_hc m)
                         ==> (S':real^2->real^2) (S x) = x` THEN MESON_TAC[];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        USE_THEN "xf" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "hc" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
        USE_THEN "Shc" (MP_TAC o C MP (CONJ (ASSUME `i:num < k`) (ASSUME `~(i:num = m)`)) o
          SPEC `i:num`) THEN
        UNDISCH_TAC `interior (moi_fsb_hc i) SUBSET moi_fsb_hc i` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "xf" (MP_TAC o C MP (ASSUME `m:num < k`) o SPEC `m:num`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    UNDISCH_TAC `inside ((X:num->real^2->bool) m) = interior (moi_fsb_hc m)` THEN
    UNDISCH_TAC `m:num < k` THEN REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^2->real^2) (R DIFF UNIONS {inside ((X:num->real^2->bool) i) | i < k}) =
    holed_disk_model k`
  (LABEL_TAC "hM") THENL
   [USE_THEN "Mdef" SUBST1_TAC THEN
    MP_TAC(ISPECL [`h:real^2->real^2`; `(:real^2)`; `R:real^2->bool`; `R:real^2->bool`;
                   `\i. inside ((X:num->real^2->bool) i)`; `\i. interior (moi_fsb_hc i)`;
                   `\i:num. i < k`] MOI_S3HX_IMAGE_DIFF_UNIONS_P) THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "hH" (MP_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN MESON_TAC[];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "hci" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the PL homeomorphism h o S of the model *)
  SUBGOAL_THEN `holed_disk_model k SUBSET R DIFF interior (moi_fsb_hc m)` ASSUME_TAC THENL
   [USE_THEN "M2" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R DIFF interior (moi_fsb_hc m)`; `R DIFF interior (moi_fsb_hc m)`;
                 `S:real^2->real^2`; `S':real^2->real^2`; `holed_disk_model k`]
                MOI_CEL_PLH_RESTRICT) THEN
  ANTS_TAC THENL [USE_THEN "SA" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
  USE_THEN "SM" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `(:real^2)`; `h':real^2->real^2`; `h:real^2->real^2`;
                 `holed_disk_model k`] MOI_CEL_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    USE_THEN "hP" (fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM] th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h':real^2->real^2) (holed_disk_model k) =
                R DIFF UNIONS {inside ((X:num->real^2->bool) i) | i < k}` SUBST1_TAC THENL
   [USE_THEN "hM" (SUBST1_TAC o SYM) THEN
    USE_THEN "hH" (MP_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM]) THEN
  MAP_EVERY EXISTS_TAC [`(h:real^2->real^2) o (S:real^2->real^2)`;
                        `(S':real^2->real^2) o (h':real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `R DIFF UNIONS {inside ((X:num->real^2->bool) i) | i < k}` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN USE_THEN "S1" SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!f:real^2->real^2 s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN USE_THEN "hfix" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier R` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier R) (interior (R:real^2->bool))` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 5 (A4 part 1): the model circles moi_s3hx_circ k j (j = 0 the       *)
(* outer circle, j = i + 1 the circle of the hole Q_i); labelled families   *)
(* of circles of the model are relabellings of them (A1); each circle can   *)
(* be made the outer one (A3); PL self-homeomorphisms of the model carry    *)
(* labelled families to labelled families.                                  *)
(* ========================================================================= *)

let moi_s3hx_circ = new_definition
 `moi_s3hx_circ k (j:num) =
    if j = 0 then relative_frontier (moi_fsb_hq k)
    else relative_frontier (moi_fsb_hc (j - 1))`;;

let MOI_S3HX_SPHERE1_BASIC = prove
 (`!s:real^2->bool. pl_sphere 1 s ==> closed s /\ connected s /\ ~(s = {}) /\ compact s`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_SPHERE1_COMPACT) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC o
    MATCH_MP PL_SPHERE_1_POLYGON) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_comb(lhand(concl th)) &&
    fst(dest_const(rator(lhand(concl th)))) = "path_image")) THEN
  REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN MATCH_MP_TAC CONNECTED_PATH_IMAGE THEN
  ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]);;

let MOI_S3HX_CIRC_FACTS = prove
 (`!k. (!j. j <= k ==> pl_sphere 1 (moi_s3hx_circ k j) /\ closed (moi_s3hx_circ k j) /\
                       connected (moi_s3hx_circ k j) /\ ~(moi_s3hx_circ k j = {})) /\
       (!j j'. j <= k /\ j' <= k /\ ~(j = j')
               ==> DISJOINT (moi_s3hx_circ k j) (moi_s3hx_circ k j')) /\
       UNIONS {moi_s3hx_circ k j | j | j <= k} = frontier (holed_disk_model k)`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` MOI_S3HX_OUTER_FACTS) THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (relative_frontier (moi_fsb_hq k))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hq k` MOI_FSB_POLY2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o el 3 o CONJUNCTS)];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= k ==> pl_sphere 1 (moi_s3hx_circ k j)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[moi_s3hx_circ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3HX_HOLE_FACTS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `j:num <= k`) o SPEC `j:num`) THEN
    MESON_TAC[MOI_S3HX_SPHERE1_BASIC];
    MAP_EVERY X_GEN_TAC [`j:num`; `j':num`] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s3hx_circ] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_CASES_TAC `j' = 0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      MP_TAC(SPECL [`k:num`; `j' - 1`] MOI_S3HX_HOLE_FACTS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc (j' - 1)) SUBSET moi_fsb_hc (j' - 1)` THEN
      UNDISCH_TAC `moi_fsb_hc (j' - 1) SUBSET interior (moi_fsb_hq k)` THEN
      UNDISCH_TAC `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))` THEN
      SET_TAC[];
      MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3HX_HOLE_FACTS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc (j - 1)) SUBSET moi_fsb_hc (j - 1)` THEN
      UNDISCH_TAC `moi_fsb_hc (j - 1) SUBSET interior (moi_fsb_hq k)` THEN
      UNDISCH_TAC `DISJOINT (relative_frontier (moi_fsb_hq k)) (interior (moi_fsb_hq k))` THEN
      SET_TAC[];
      MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3HX_HOLE_FACTS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(SPECL [`k:num`; `j' - 1`] MOI_S3HX_HOLE_FACTS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `DISJOINT (moi_fsb_hc (j - 1)) (moi_fsb_hc (j' - 1))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th))) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc (j - 1)) SUBSET moi_fsb_hc (j - 1)` THEN
      UNDISCH_TAC `relative_frontier (moi_fsb_hc (j' - 1)) SUBSET moi_fsb_hc (j' - 1)` THEN
      SET_TAC[]];
    REWRITE_TAC[MOI_FSB_HD_FRONTIER; UNIONS_GSPEC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[moi_s3hx_circ] THEN COND_CASES_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
      DISJ2_TAC THEN EXISTS_TAC `j - 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      STRIP_TAC THENL
       [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LE_0; moi_s3hx_circ];
        EXISTS_TAC `i + 1` THEN ASM_REWRITE_TAC[moi_s3hx_circ; ADD_SUB; ADD_EQ_0; ARITH_EQ] THEN
        ASM_ARITH_TAC]]]);;

let MOI_S3HX_LABELS = prove
 (`!k (J:num->real^2->bool).
     (!i. i <= k ==> pl_sphere 1 (J i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J i) (J i')) /\
     UNIONS {J i | i <= k} = frontier (holed_disk_model k)
     ==> (!i. i <= k ==> ?j. j <= k /\ J i = moi_s3hx_circ k j) /\
         (!j. j <= k ==> ?i. i <= k /\ J i = moi_s3hx_circ k j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_S3HX_CIRC_FACTS) THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3HX_CIRCLE_ID THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `J:num->real^2->bool`)) (concl th) &&
      not(can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th)))) THEN
    MESON_TAC[MOI_S3HX_SPHERE1_BASIC];
    ASM_MESON_TAC[]]);;

let MOI_S3HX_NORMAL0 = prove
 (`!k j. j <= k
     ==> ?p q. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (p,q) /\
               IMAGE p (moi_s3hx_circ k j) = relative_frontier (moi_fsb_hq k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3hx_circ] THEN COND_CASES_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[IMAGE_ID] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    REWRITE_TAC[HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    SIMP_TAC[MOI_FSB_HD_POLY];
    MATCH_MP_TAC MOI_S3HX_NORMAL THEN ASM_ARITH_TAC]);;

let MOI_S3HX_TRANSPORT = prove
 (`!k (J:num->real^2->bool) p q.
     pl_homeomorphism (holed_disk_model k,holed_disk_model k) (p,q) /\
     (!i. i <= k ==> pl_sphere 1 (J i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J i) (J i')) /\
     UNIONS {J i | i <= k} = frontier (holed_disk_model k)
     ==> (!i. i <= k ==> pl_sphere 1 (IMAGE p (J i))) /\
         (!i i'. i <= k /\ i' <= k /\ ~(i = i')
                 ==> DISJOINT (IMAGE p (J i)) (IMAGE p (J i'))) /\
         UNIONS {IMAGE p (J i) | i <= k} = frontier (holed_disk_model k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P") (CONJUNCTS_THEN2 (LABEL_TAC "S")
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "U")))) THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (holed_disk_model k) SUBSET holed_disk_model k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= k ==> (J:num->real^2->bool) i SUBSET holed_disk_model k`
  (LABEL_TAC "sub") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier (holed_disk_model k)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "U" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "P" (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    REWRITE_RULE[pl_homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5C_SPHERE_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`holed_disk_model k`; `holed_disk_model k`; `q:real^2->real^2`] THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
    USE_THEN "D" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (CONJ (ASSUME `i':num <= k`)
      (ASSUME `~(i:num = i')`))) o SPECL [`i:num`; `i':num`]) THEN
    USE_THEN "sub" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    USE_THEN "sub" (MP_TAC o C MP (ASSUME `i':num <= k`) o SPEC `i':num`) THEN
    UNDISCH_TAC `!x. x IN holed_disk_model k ==> (q:real^2->real^2) (p x) = x` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    SUBGOAL_THEN `UNIONS {IMAGE (p:real^2->real^2) (J i) | i <= k} =
                  IMAGE p (UNIONS {(J:num->real^2->bool) i | i <= k})` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "U" SUBST1_TAC THEN MATCH_MP_TAC MOI_S3HX_HOMEO_FRONTIER THEN
    EXISTS_TAC `q:real^2->real^2` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    USE_THEN "P" (fun th -> REWRITE_TAC[CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)])]);;

(* ========================================================================= *)
(* Part 6 (A4 part 2): lemmas for the outer-normalized model lemma:         *)
(* the reindexing of {0..k} minus i0 by {0..k-1}; the hole circles of a     *)
(* labelled family whose i0-th circle is the outer one; the images of the   *)
(* hole disks under a PL self-homeomorphism of R fixing rf R setwise; the   *)
(* images of disks and their insides under ambient homeomorphisms.          *)
(* ========================================================================= *)

let moi_s3hx_rho = new_definition
 `moi_s3hx_rho (i0:num) (l:num) = if l < i0 then l else l + 1`;;

let MOI_S3HX_RHO = prove
 (`!i0 k. i0 <= k
     ==> (!l. l < k ==> moi_s3hx_rho i0 l <= k /\ ~(moi_s3hx_rho i0 l = i0)) /\
         (!i. i <= k /\ ~(i = i0) ==> ?l. l < k /\ moi_s3hx_rho i0 l = i) /\
         (!l l'. l < k /\ l' < k /\ moi_s3hx_rho i0 l = moi_s3hx_rho i0 l' ==> l = l')`,
  REWRITE_TAC[moi_s3hx_rho] THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN ASM_ARITH_TAC;
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i:num < i0` THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXISTS_TAC `i - 1` THEN
      SUBGOAL_THEN `~(i - 1 < (i0:num))` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC]];
    POP_ASSUM MP_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let MOI_S3HX_HOLE_ID = prove
 (`!k (J:num->real^2->bool) i0.
     (!i. i <= k ==> pl_sphere 1 (J i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J i) (J i')) /\
     UNIONS {J i | i <= k} = frontier (holed_disk_model k) /\
     i0 <= k /\ J i0 = relative_frontier (moi_fsb_hq k)
     ==> (!i. i <= k /\ ~(i = i0) ==> ?j. j < k /\ J i = relative_frontier (moi_fsb_hc j)) /\
         (!j. j < k ==> ?i. i <= k /\ ~(i = i0) /\ J i = relative_frontier (moi_fsb_hc j))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s") (CONJUNCTS_THEN2 (LABEL_TAC "d")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`k:num`; `J:num->real^2->bool`] MOI_S3HX_LABELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l2")) THEN
  SUBGOAL_THEN `!i. i <= k ==> ~((J:num->real^2->bool) i = {})` (LABEL_TAC "ne") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "s" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    MESON_TAC[MOI_S3HX_SPHERE1_BASIC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "l1" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `j = 0` THENL
     [UNDISCH_TAC `(J:num->real^2->bool) i = moi_s3hx_circ k j` THEN
      ASM_REWRITE_TAC[moi_s3hx_circ] THEN DISCH_TAC THEN
      USE_THEN "d" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (CONJ (ASSUME `i0:num <= k`)
        (ASSUME `~(i:num = i0)`))) o SPECL [`i:num`; `i0:num`]) THEN
      USE_THEN "ne" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXISTS_TAC `j - 1` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(J:num->real^2->bool) i = moi_s3hx_circ k j` THEN
      ASM_REWRITE_TAC[moi_s3hx_circ]];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "l2" (MP_TAC o C MP (MP (ARITH_RULE `j < k ==> j + 1 <= k`)
      (ASSUME `j:num < k`)) o SPEC `j + 1`) THEN
    REWRITE_TAC[moi_s3hx_circ; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(J:num->real^2->bool) i = relative_frontier (moi_fsb_hc j)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `k:num` MOI_S3HX_CIRC_FACTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`0`; `j + 1`] o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s3hx_circ; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    UNDISCH_TAC `relative_frontier (moi_fsb_hq k) = relative_frontier (moi_fsb_hc j)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MOI_S3HX_SPHERE1_BASIC; SET_RULE `!s:real^2->bool. DISJOINT s s <=> s = {}`]]);;

let MOI_S3HX_HOLES_UNION = prove
 (`!k (J:num->real^2->bool) i0.
     (!i. i <= k /\ ~(i = i0) ==> ?j. j < k /\ J i = relative_frontier (moi_fsb_hc j)) /\
     (!j. j < k ==> ?i. i <= k /\ ~(i = i0) /\ J i = relative_frontier (moi_fsb_hc j))
     ==> holed_disk_model k =
         moi_fsb_hq k DIFF UNIONS {inside (J i) | i <= k /\ ~(i = i0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_FSB_HD_EQ] THEN
  AP_TERM_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
      SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN inside ((J:num->real^2->bool) i)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN ASM_SIMP_TAC[]]);;

(* Images of a polytope disk under a PLH of R onto R keeping rf R.           *)

let MOI_S3HX_DISK_IMAGE = prove
 (`!(R:real^2->bool) E E' P.
     pl_homeomorphism (R,R) (E,E') /\ IMAGE E (relative_frontier R) = relative_frontier R /\
     relative_frontier R SUBSET R /\ R SUBSET relative_frontier R UNION interior R /\
     DISJOINT (relative_frontier R) (interior R) /\
     polytope P /\ ~(interior P = {}) /\ P SUBSET interior R
     ==> pl_sphere 1 (IMAGE E (relative_frontier P)) /\
         IMAGE E (relative_frontier P) UNION inside (IMAGE E (relative_frontier P)) =
         IMAGE E P /\
         IMAGE E P SUBSET interior R /\
         frontier (IMAGE E P) = IMAGE E (relative_frontier P) /\
         inside (IMAGE E (relative_frontier P)) = IMAGE E (interior P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:real^2->bool) SUBSET R` ASSUME_TAC THENL
   [MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^2->bool`; `R:real^2->bool`; `E:real^2->real^2`; `E':real^2->real^2`;
                 `P:real^2->bool`] MOI_FSB_IMG_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    REWRITE_RULE[pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (R:real^2->bool,R) (E:real^2->real^2,E')`)) THEN
  MP_TAC(ISPEC `P:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(el 2 (CONJUNCTS th)) THEN MP_TAC(el 4 (CONJUNCTS th))) THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN interior R` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((E:real^2->real^2) x IN relative_frontier R)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^2->real^2) (relative_frontier R) = relative_frontier R` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^2 = y` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]];
      UNDISCH_TAC `IMAGE (E:real^2->real^2) R = R` THEN
      UNDISCH_TAC `(R:real^2->bool) SUBSET relative_frontier R UNION interior R` THEN
      UNDISCH_TAC `(x:real^2) IN P` THEN UNDISCH_TAC `(P:real^2->bool) SUBSET R` THEN
      SET_TAC[]];
    SUBGOAL_THEN `interior P = (P:real^2->bool) DIFF relative_frontier P` SUBST1_TAC THENL
     [MP_TAC(ISPEC `P:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (E:real^2->real^2) (P DIFF relative_frontier P) =
                  IMAGE E P DIFF IMAGE E (relative_frontier P)` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `IMAGE (E:real^2->real^2) P`)) THEN
    MP_TAC(ISPEC `IMAGE (E:real^2->real^2) (relative_frontier P)` INSIDE_NO_OVERLAP) THEN
    SET_TAC[]]);;

(* Disks and their insides under an ambient homeomorphism.                   *)

let MOI_S3HX_AMB_DISK = prove
 (`!(h:real^2->real^2) h' (X:real^2->bool) Y.
     homeomorphism ((:real^2),(:real^2)) (h,h') /\
     IMAGE h (X UNION inside X) = Y UNION inside Y /\
     frontier (X UNION inside X) = X /\ frontier (Y UNION inside Y) = Y
     ==> IMAGE h X = Y /\ IMAGE h (inside X) = inside Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) X = Y` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (h:real^2->real^2) X = IMAGE h (frontier (X UNION inside X))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_S3HX_AMB_FRONTIER th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inside (X:real^2->bool) = (X UNION inside X) DIFF X` SUBST1_TAC THENL
   [MP_TAC(ISPEC `X:real^2->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) ((X UNION inside X) DIFF X) =
                IMAGE h (X UNION inside X) DIFF IMAGE h X` SUBST1_TAC THENL
   [MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN CONJ_TAC THENL
     [UNDISCH_TAC `homeomorphism ((:real^2),(:real^2)) (h:real^2->real^2,h')` THEN
      REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `Y:real^2->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[]);;

(* ========================================================================= *)
(* Part 7 (A4 part 3): the model lemma when the chosen circle is the        *)
(* outer circle rf R on both sides.  psi on rf R extends to a PLH E of R    *)
(* (MOI_CEL_CELL_EXTENSION); the hole disks E(J i) (i <> i0, reindexed by   *)
(* l < k) are moved onto the J' i by an ambient PLH h fixing rf R (A2);     *)
(* h o E restricts to the model.                                             *)
(* ========================================================================= *)

let MOI_S3HX_MODEL_OUT = prove
 (`!k (J:num->real^2->bool) J' i0 (psi:real^2->real^2) psi'.
     (!i. i <= k ==> pl_sphere 1 (J i) /\ pl_sphere 1 (J' i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i')
             ==> DISJOINT (J i) (J i') /\ DISJOINT (J' i) (J' i')) /\
     UNIONS {J i | i <= k} = frontier (holed_disk_model k) /\
     UNIONS {J' i | i <= k} = frontier (holed_disk_model k) /\
     i0 <= k /\ J i0 = relative_frontier (moi_fsb_hq k) /\
     J' i0 = relative_frontier (moi_fsb_hq k) /\
     pl_homeomorphism (relative_frontier (moi_fsb_hq k),relative_frontier (moi_fsb_hq k))
                      (psi,psi')
     ==> ?H H'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (H,H') /\
                (!y. y IN relative_frontier (moi_fsb_hq k) ==> H y = psi y) /\
                (!i. i <= k ==> IMAGE H (J i) = J' i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sp") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    (CONJUNCTS_THEN2 (LABEL_TAC "uJ") (CONJUNCTS_THEN2 (LABEL_TAC "uJ'")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "J0")
    (CONJUNCTS_THEN2 (LABEL_TAC "J'0") (LABEL_TAC "psi")))))))) THEN
  (* the holes of both families *)
  MP_TAC(SPECL [`k:num`; `J:num->real^2->bool`; `i0:num`] MOI_S3HX_HOLE_ID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th]);
      USE_THEN "uJ" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; USE_THEN "J0" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hJ") (LABEL_TAC "hJs"))] THEN
  MP_TAC(SPECL [`k:num`; `J':num->real^2->bool`; `i0:num`] MOI_S3HX_HOLE_ID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th]);
      USE_THEN "uJ'" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; USE_THEN "J'0" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hJ'") (LABEL_TAC "hJ's"))] THEN
  SUBGOAL_THEN
   `holed_disk_model k =
    moi_fsb_hq k DIFF UNIONS {inside ((J:num->real^2->bool) i) | i <= k /\ ~(i = i0)} /\
    holed_disk_model k =
    moi_fsb_hq k DIFF UNIONS {inside ((J':num->real^2->bool) i) | i <= k /\ ~(i = i0)}`
  (CONJUNCTS_THEN2 (LABEL_TAC "MJ") (LABEL_TAC "MJ'")) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3HX_HOLES_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `k:num` MOI_S3HX_OUTER_FACTS) THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN
  DISCH_THEN(LABEL_TAC "hcd" o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  ABBREV_TAC `R = moi_fsb_hq k` THEN
  (* the cone extension E of psi over R *)
  MP_TAC(ISPECL [`2`; `R:real^2->bool`; `relative_frontier R:real^2->bool`;
                 `R:real^2->bool`; `relative_frontier R:real^2->bool`;
                 `psi:real^2->real^2`; `psi':real^2->real^2`] MOI_CEL_CELL_EXTENSION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^2->real^2` (X_CHOOSE_THEN `E':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "EP") (LABEL_TAC "Epsi")))) THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^2) (relative_frontier R) = relative_frontier R`
  ASSUME_TAC THENL
   [USE_THEN "psi" (fun th -> MP_TAC(CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th))) THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^2->real^2) (relative_frontier R) = relative_frontier R`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (E:real^2->real^2) (relative_frontier R) =
                  IMAGE (psi:real^2->real^2) (relative_frontier R)` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN USE_THEN "Epsi" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "EP" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  (* the hole disks of J under E, and those of J' *)
  SUBGOAL_THEN
   `!i. i <= k /\ ~(i = i0)
        ==> pl_sphere 1 (IMAGE (E:real^2->real^2) ((J:num->real^2->bool) i)) /\
            IMAGE E (J i) UNION inside (IMAGE E (J i)) = IMAGE E (J i UNION inside (J i)) /\
            IMAGE E (J i) UNION inside (IMAGE E (J i)) SUBSET interior R /\
            frontier (IMAGE E (J i) UNION inside (IMAGE E (J i))) = IMAGE E (J i) /\
            inside (IMAGE E (J i)) = IMAGE E (inside (J i)) /\
            J i UNION inside (J i) SUBSET R /\ inside (J i) SUBSET R`
  (LABEL_TAC "Ji") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "hJ" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
      SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->real^2`; `E':real^2->real^2`;
                   `moi_fsb_hc j`] MOI_S3HX_DISK_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_fsb_hc j SUBSET interior (R:real^2->bool)` THEN
    UNDISCH_TAC `interior (moi_fsb_hc j) SUBSET moi_fsb_hc j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= k /\ ~(i = i0)
        ==> pl_sphere 1 ((J':num->real^2->bool) i) /\
            J' i UNION inside (J' i) SUBSET interior R /\
            frontier (J' i UNION inside (J' i)) = J' i /\ inside (J' i) SUBSET R`
  (LABEL_TAC "J'i") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "hJ'" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
      SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_fsb_hc j SUBSET interior (R:real^2->bool)` THEN
    UNDISCH_TAC `interior (moi_fsb_hc j) SUBSET moi_fsb_hc j` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the holes of distinct indices are disjoint *)
  SUBGOAL_THEN
   `!i i'. i <= k /\ i' <= k /\ ~(i = i0) /\ ~(i' = i0) /\ ~(i = i')
           ==> DISJOINT ((J:num->real^2->bool) i UNION inside (J i))
                        (J i' UNION inside (J i')) /\
               DISJOINT ((J':num->real^2->bool) i UNION inside (J' i))
                        (J' i' UNION inside (J' i'))`
  (LABEL_TAC "dJ") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!(K:num->real^2->bool).
        (!i. i <= k /\ ~(i = i0) ==> ?j. j < k /\ K i = relative_frontier (moi_fsb_hc j)) /\
        (!i. i <= k ==> pl_sphere 1 (K i)) /\
        (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (K i) (K i'))
        ==> DISJOINT (K i UNION inside (K i)) (K i' UNION inside (K i'))`
    (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THENL
      [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th])];
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th])]]) THEN
    X_GEN_TAC `K:num->real^2->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kh") (CONJUNCTS_THEN2 (LABEL_TAC "ks")
      (LABEL_TAC "kd"))) THEN
    USE_THEN "kh" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
      SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    USE_THEN "kh" (MP_TAC o C MP (CONJ (ASSUME `i':num <= k`) (ASSUME `~(i':num = i0)`)) o
      SPEC `i':num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j':num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(j:num = j')` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "kd" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (CONJ (ASSUME `i':num <= k`)
        (ASSUME `~(i:num = i')`))) o SPECL [`i:num`; `i':num`]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`k:num`; `j':num`] MOI_S3HX_HOLE_FACTS) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[MOI_S3HX_SPHERE1_BASIC; SET_RULE `!s:real^2->bool. DISJOINT s s <=> s = {}`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `j:num`] MOI_S3HX_HOLE_FACTS) THEN
    MP_TAC(SPECL [`k:num`; `j':num`] MOI_S3HX_HOLE_FACTS) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "hcd" (ACCEPT_TAC o C MP (ASSUME `~(j:num = j')`) o SPECL [`j:num`; `j':num`]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`i0:num`; `k:num`] MOI_S3HX_RHO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r1") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
    (LABEL_TAC "r3"))) THEN
  (* A2 on the reindexed holes *)
  MP_TAC(ISPECL [`k:num`; `interior R:real^2->bool`;
                 `\l. IMAGE (E:real^2->real^2) ((J:num->real^2->bool) (moi_s3hx_rho i0 l))`;
                 `\l. (J':num->real^2->bool) (moi_s3hx_rho i0 l)`] MOI_S3HX_EXCHANGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN
      USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
        (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
      USE_THEN "J'i" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
        (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`l:num`; `l':num`] THEN STRIP_TAC THEN
      USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN
      USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l':num < k`) o SPEC `l':num`) THEN
      SUBGOAL_THEN `~(moi_s3hx_rho i0 l = moi_s3hx_rho i0 l')` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(l:num = l')` THEN REWRITE_TAC[] THEN
        USE_THEN "r3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "dJ" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
        (CONJ (ASSUME `moi_s3hx_rho i0 l' <= k`) (CONJ (ASSUME `~(moi_s3hx_rho i0 l = i0)`)
        (CONJ (ASSUME `~(moi_s3hx_rho i0 l' = i0)`)
        (ASSUME `~(moi_s3hx_rho i0 l = moi_s3hx_rho i0 l')`))))) o
        SPECL [`moi_s3hx_rho i0 l`; `moi_s3hx_rho i0 l'`]) THEN
      USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
        (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
      USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l' <= k`)
        (ASSUME `~(moi_s3hx_rho i0 l' = i0)`)) o SPEC `moi_s3hx_rho i0 l'`) THEN
      UNDISCH_TAC `!x. x IN R ==> (E':real^2->real^2) (E x) = x` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "hP") (CONJUNCTS_THEN2 (LABEL_TAC "hfix") (LABEL_TAC "him"))))) THEN
  SUBGOAL_THEN `homeomorphism ((:real^2),(:real^2)) (h:real^2->real^2,h')` (LABEL_TAC "hH") THENL
   [USE_THEN "hP" (fun th -> REWRITE_TAC[CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `R:real^2->bool`] MOI_S3HX_AMB_FIX) THEN
  ANTS_TAC THENL [USE_THEN "hH" (fun th -> USE_THEN "hfix" (fun th' -> REWRITE_TAC[th; th']));
                  ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h'fix"))) THEN
  SUBGOAL_THEN
   `!l. l < k
        ==> IMAGE (h:real^2->real^2) (IMAGE (E:real^2->real^2)
              ((J:num->real^2->bool) (moi_s3hx_rho i0 l))) = J' (moi_s3hx_rho i0 l) /\
            IMAGE h (inside (IMAGE E (J (moi_s3hx_rho i0 l)))) =
            inside ((J':num->real^2->bool) (moi_s3hx_rho i0 l))`
  (LABEL_TAC "hd") THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN
    USE_THEN "Ji" (STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
      (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
    USE_THEN "J'i" (STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
      (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
    MATCH_MP_TAC MOI_S3HX_AMB_DISK THEN EXISTS_TAC `h':real^2->real^2` THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "hH" ACCEPT_TAC;
      USE_THEN "him" (MATCH_MP_TAC o REWRITE_RULE[]) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the model under E and under h *)
  SUBGOAL_THEN
   `IMAGE (E:real^2->real^2) (holed_disk_model k) =
    R DIFF UNIONS {inside (IMAGE E ((J:num->real^2->bool) (moi_s3hx_rho i0 l))) | l < k}`
  (LABEL_TAC "EM") THENL
   [USE_THEN "MJ" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    MP_TAC(ISPECL [`E:real^2->real^2`; `R:real^2->bool`; `R:real^2->bool`; `R:real^2->bool`;
                   `\i. inside ((J:num->real^2->bool) i)`;
                   `\i. IMAGE (E:real^2->real^2) (inside ((J:num->real^2->bool) i))`;
                   `\i:num. i <= k /\ ~(i = i0)`] MOI_S3HX_IMAGE_DIFF_UNIONS_P) THEN
    REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `!x. x IN R ==> (E':real^2->real^2) (E x) = x` THEN MESON_TAC[];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
          SPEC `i:num`) THEN SIMP_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "r2" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
        SPEC `i:num`) THEN
      DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
        SPEC `i:num`) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN
      EXISTS_TAC `moi_s3hx_rho i0 l` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Ji" (MP_TAC o C MP (CONJ (ASSUME `moi_s3hx_rho i0 l <= k`)
        (ASSUME `~(moi_s3hx_rho i0 l = i0)`)) o SPEC `moi_s3hx_rho i0 l`) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^2->real^2)
      (R DIFF UNIONS {inside (IMAGE (E:real^2->real^2) ((J:num->real^2->bool)
                                 (moi_s3hx_rho i0 l))) | l < k}) =
    holed_disk_model k`
  (LABEL_TAC "hM") THENL
   [MP_TAC(ISPECL [`h:real^2->real^2`; `(:real^2)`; `R:real^2->bool`; `R:real^2->bool`;
                   `\l. inside (IMAGE (E:real^2->real^2) ((J:num->real^2->bool)
                                   (moi_s3hx_rho i0 l)))`;
                   `\l. inside ((J':num->real^2->bool) (moi_s3hx_rho i0 l))`;
                   `\l:num. l < k`] MOI_S3HX_IMAGE_DIFF_UNIONS_P) THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "hH" (MP_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN MESON_TAC[];
        X_GEN_TAC `l:num` THEN DISCH_TAC THEN
        USE_THEN "hd" (MP_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN SIMP_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "MJ'" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "r1" (STRIP_ASSUME_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN
      EXISTS_TAC `moi_s3hx_rho i0 l` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "r2" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
        SPEC `i:num`) THEN
      DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the PL homeomorphism h o E of the model *)
  SUBGOAL_THEN `holed_disk_model k SUBSET (R:real^2->bool)` ASSUME_TAC THENL
   [USE_THEN "MJ" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^2->bool`; `R:real^2->bool`; `E:real^2->real^2`; `E':real^2->real^2`;
                 `holed_disk_model k`] MOI_CEL_PLH_RESTRICT) THEN
  ANTS_TAC THENL [USE_THEN "EP" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
  USE_THEN "EM" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `(:real^2)`; `h':real^2->real^2`; `h:real^2->real^2`;
                 `holed_disk_model k`] MOI_CEL_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    USE_THEN "hP" (fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM] th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h':real^2->real^2) (holed_disk_model k) =
    R DIFF UNIONS {inside (IMAGE (E:real^2->real^2) ((J:num->real^2->bool)
                             (moi_s3hx_rho i0 l))) | l < k}` SUBST1_TAC THENL
   [USE_THEN "hM" (SUBST1_TAC o SYM) THEN
    USE_THEN "hH" (MP_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM]) THEN
  MAP_EVERY EXISTS_TAC [`(h:real^2->real^2) o (E:real^2->real^2)`;
                        `(E':real^2->real^2) o (h':real^2->real^2)`] THEN
  SUBGOAL_THEN `!y. y IN relative_frontier R ==> (h:real^2->real^2) y = y` (LABEL_TAC "hrf") THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN USE_THEN "hfix" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^2) IN relative_frontier R` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier R) (interior (R:real^2->bool))` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `R DIFF UNIONS {inside (IMAGE (E:real^2->real^2) ((J:num->real^2->bool)
                                 (moi_s3hx_rho i0 l))) | l < k}` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "Epsi" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^2) IN relative_frontier R`)]) THEN
    USE_THEN "hrf" MATCH_MP_TAC THEN
    UNDISCH_TAC `IMAGE (psi:real^2->real^2) (relative_frontier R) = relative_frontier R` THEN
    UNDISCH_TAC `(y:real^2) IN relative_frontier R` THEN SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
    ASM_CASES_TAC `i:num = i0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "J0" SUBST1_TAC THEN USE_THEN "J'0" SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!f:real^2->real^2 s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      USE_THEN "hrf" ACCEPT_TAC;
      USE_THEN "r2" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (ASSUME `~(i:num = i0)`)) o
        SPEC `i:num`) THEN
      DISCH_THEN(X_CHOOSE_THEN `l:num` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
      USE_THEN "hd" (MP_TAC o C MP (ASSUME `l:num < k`) o SPEC `l:num`) THEN SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Part 8 (A4): the model lemma.  The i0-th circles of both families         *)
(* are model circles (A1); NORMAL0 carries them to the outer circle by PL   *)
(* self-homeomorphisms p, p' of the model; the transported families and     *)
(* psi0 = p' o psi o q satisfy MODEL_OUT; conjugating back gives H.         *)
(* ========================================================================= *)

let MOI_S3HX_FAMILY_SUBSET = prove
 (`!k (J:num->real^2->bool).
     UNIONS {J i | i <= k} = frontier (holed_disk_model k)
     ==> !i. i <= k ==> J i SUBSET holed_disk_model k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `frontier (holed_disk_model k)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN
    SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]]);;

let MOI_S3HX_MODEL = prove
 (`!k (J:num->real^2->bool) J' i0 (psi:real^2->real^2) psi'.
     (!i. i <= k ==> pl_sphere 1 (J i) /\ pl_sphere 1 (J' i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i')
             ==> DISJOINT (J i) (J i') /\ DISJOINT (J' i) (J' i')) /\
     UNIONS {J i | i <= k} = frontier (holed_disk_model k) /\
     UNIONS {J' i | i <= k} = frontier (holed_disk_model k) /\
     i0 <= k /\ pl_homeomorphism (J i0,J' i0) (psi,psi')
     ==> ?H H'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (H,H') /\
                (!y. y IN J i0 ==> H y = psi y) /\
                (!i. i <= k ==> IMAGE H (J i) = J' i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sp") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    (CONJUNCTS_THEN2 (LABEL_TAC "uJ") (CONJUNCTS_THEN2 (LABEL_TAC "uJ'")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "psi")))))) THEN
  SUBGOAL_THEN
   `(!i. i <= k ==> pl_sphere 1 ((J:num->real^2->bool) i)) /\
    (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J i) (J i')) /\
    (!i. i <= k ==> pl_sphere 1 ((J':num->real^2->bool) i)) /\
    (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J' i) (J' i'))`
  (CONJUNCTS_THEN2 (LABEL_TAC "sJ") (CONJUNCTS_THEN2 (LABEL_TAC "dJ")
    (CONJUNCTS_THEN2 (LABEL_TAC "sJ'") (LABEL_TAC "dJ'")))) THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th]);
      USE_THEN "sp" (fun th -> MESON_TAC[th]); USE_THEN "dj" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `J:num->real^2->bool`] MOI_S3HX_FAMILY_SUBSET) THEN
  ANTS_TAC THENL [USE_THEN "uJ" ACCEPT_TAC; DISCH_THEN(LABEL_TAC "Jsub")] THEN
  MP_TAC(SPECL [`k:num`; `J':num->real^2->bool`] MOI_S3HX_FAMILY_SUBSET) THEN
  ANTS_TAC THENL [USE_THEN "uJ'" ACCEPT_TAC; DISCH_THEN(LABEL_TAC "J'sub")] THEN
  (* the i0-th circles are model circles *)
  MP_TAC(SPECL [`k:num`; `J:num->real^2->bool`] MOI_S3HX_LABELS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sJ" ACCEPT_TAC; USE_THEN "dJ" ACCEPT_TAC; USE_THEN "uJ" ACCEPT_TAC];
    DISCH_THEN(MP_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num` o CONJUNCT1)] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Jc"))) THEN
  MP_TAC(SPECL [`k:num`; `J':num->real^2->bool`] MOI_S3HX_LABELS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sJ'" ACCEPT_TAC; USE_THEN "dJ'" ACCEPT_TAC; USE_THEN "uJ'" ACCEPT_TAC];
    DISCH_THEN(MP_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num` o CONJUNCT1)] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0':num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "J'c"))) THEN
  (* the normalizations p and p' *)
  MP_TAC(SPECL [`k:num`; `j0:num`] MOI_S3HX_NORMAL0) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "pP") (LABEL_TAC "pJ")))) THEN
  MP_TAC(SPECL [`k:num`; `j0':num`] MOI_S3HX_NORMAL0) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^2->real^2` (X_CHOOSE_THEN `q':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "p'P") (LABEL_TAC "p'J")))) THEN
  USE_THEN "pP" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  USE_THEN "p'P" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  (* the transported families *)
  MP_TAC(SPECL [`k:num`; `J:num->real^2->bool`; `p:real^2->real^2`; `q:real^2->real^2`]
                MOI_S3HX_TRANSPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "pP" ACCEPT_TAC; USE_THEN "sJ" ACCEPT_TAC; USE_THEN "dJ" ACCEPT_TAC;
      USE_THEN "uJ" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tS") (CONJUNCTS_THEN2 (LABEL_TAC "tD")
      (LABEL_TAC "tU")))] THEN
  MP_TAC(SPECL [`k:num`; `J':num->real^2->bool`; `p':real^2->real^2`; `q':real^2->real^2`]
                MOI_S3HX_TRANSPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "p'P" ACCEPT_TAC; USE_THEN "sJ'" ACCEPT_TAC; USE_THEN "dJ'" ACCEPT_TAC;
      USE_THEN "uJ'" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tS'") (CONJUNCTS_THEN2 (LABEL_TAC "tD'")
      (LABEL_TAC "tU'")))] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^2->real^2) ((J:num->real^2->bool) i0) = relative_frontier (moi_fsb_hq k)`
  ASSUME_TAC THENL
   [USE_THEN "Jc" SUBST1_TAC THEN USE_THEN "pJ" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p':real^2->real^2) ((J':num->real^2->bool) i0) = relative_frontier (moi_fsb_hq k)`
  ASSUME_TAC THENL
   [USE_THEN "J'c" SUBST1_TAC THEN USE_THEN "p'J" ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "Jc" (K ALL_TAC) THEN REMOVE_THEN "J'c" (K ALL_TAC) THEN
  (* psi0 on the outer circle *)
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier (moi_fsb_hq k),relative_frontier (moi_fsb_hq k))
      ((p':real^2->real^2) o (psi:real^2->real^2) o (q:real^2->real^2),
       ((p:real^2->real^2) o (psi':real^2->real^2)) o (q':real^2->real^2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `locally_polyhedral ((J:num->real^2->bool) i0) /\
                  locally_polyhedral ((J':num->real^2->bool) i0)` STRIP_ASSUME_TAC THENL
     [USE_THEN "psi" (fun th -> MP_TAC(REWRITE_RULE[pl_homeomorphism] th)) THEN
      MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`holed_disk_model k`; `holed_disk_model k`; `p:real^2->real^2`;
                   `q:real^2->real^2`; `(J:num->real^2->bool) i0`] MOI_CEL_PLH_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "Jsub" (ACCEPT_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM]) THEN
    MP_TAC(ISPECL [`holed_disk_model k`; `holed_disk_model k`; `p':real^2->real^2`;
                   `q':real^2->real^2`; `(J':num->real^2->bool) i0`] MOI_CEL_PLH_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "J'sub" (ACCEPT_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(J':num->real^2->bool) i0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(J:num->real^2->bool) i0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "psi" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the outer-normalized lemma *)
  MP_TAC(SPECL [`k:num`; `\i. IMAGE (p:real^2->real^2) ((J:num->real^2->bool) i)`;
                `\i. IMAGE (p':real^2->real^2) ((J':num->real^2->bool) i)`; `i0:num`;
                `(p':real^2->real^2) o (psi:real^2->real^2) o (q:real^2->real^2)`;
                `((p:real^2->real^2) o (psi':real^2->real^2)) o (q':real^2->real^2)`]
               MOI_S3HX_MODEL_OUT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "tS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num <= k`)]) THEN
      USE_THEN "tS'" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num <= k`)]);
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "tD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "tD'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "tU" ACCEPT_TAC; USE_THEN "tU'" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:real^2->real^2` (X_CHOOSE_THEN `H0':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "H0P") (CONJUNCTS_THEN2 (LABEL_TAC "H0psi")
    (LABEL_TAC "H0J"))))) THEN
  MAP_EVERY EXISTS_TAC [`(q':real^2->real^2) o (H0:real^2->real^2) o (p:real^2->real^2)`;
                        `((q:real^2->real^2) o (H0':real^2->real^2)) o (p':real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
      CONJ_TAC THENL [USE_THEN "pP" ACCEPT_TAC; USE_THEN "H0P" ACCEPT_TAC];
      USE_THEN "p'P" (fun th -> ACCEPT_TAC(ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM] th))];
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(y:real^2) IN holed_disk_model k /\ (p:real^2->real^2) y IN
                  relative_frontier (moi_fsb_hq k)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "Jsub" (MP_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`) THEN
        UNDISCH_TAC `(y:real^2) IN (J:num->real^2->bool) i0` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (p:real^2->real^2) ((J:num->real^2->bool) i0) =
                     relative_frontier (moi_fsb_hq k)` THEN
        UNDISCH_TAC `(y:real^2) IN (J:num->real^2->bool) i0` THEN SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "H0psi" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(p:real^2->real^2) y IN relative_frontier (moi_fsb_hq k)`)]) THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(q:real^2->real^2) (p y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `q:real^2->real^2`)) (concl th) &&
        can (find_term ((=) `p:real^2->real^2`)) (concl th) &&
        is_imp(snd(dest_forall(concl th))) &&
        lhs(snd(dest_imp(snd(dest_forall(concl th))))) =
          `(q:real^2->real^2) ((p:real^2->real^2) x)`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^2->real^2) y IN holed_disk_model k` ASSUME_TAC THENL
     [USE_THEN "J'sub" (MP_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`) THEN
      USE_THEN "psi" (MP_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
        REWRITE_RULE[pl_homeomorphism]) THEN
      UNDISCH_TAC `(y:real^2) IN (J:num->real^2->bool) i0` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_imp(snd(dest_forall(concl th))) &&
      lhs(snd(dest_imp(snd(dest_forall(concl th))))) =
        `(q':real^2->real^2) ((p':real^2->real^2) x)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
    USE_THEN "H0J" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num <= k`)]) THEN
    USE_THEN "J'sub" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    UNDISCH_TAC `!x. x IN holed_disk_model k ==> (q':real^2->real^2) (p' x) = x` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Part 9 (B): the theorem HOLED_EXT.  Pull the labelled circles of a and   *)
(* a' back to the model by g, g' (J i = g(jj i), J' i = g'(jj' i)),         *)
(* apply the model lemma to psi = g' o phi o f, and push the result         *)
(* forward: G = f' o H o g.                                                 *)
(* ========================================================================= *)

let MOI_S3HX_SPHERE_LP = prove
 (`!n (s:real^N->bool). pl_sphere n s ==> locally_polyhedral s`,
  REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]);;

let HOLED_EXT = prove
 (MOI_S33_HOLED_EXT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fP") (CONJUNCTS_THEN2 (LABEL_TAC "f'P")
    (CONJUNCTS_THEN2 (LABEL_TAC "fJ") (CONJUNCTS_THEN2 (LABEL_TAC "f'J")
    (CONJUNCTS_THEN2 (LABEL_TAC "sp") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "phi")))))))) THEN
  USE_THEN "fP" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  USE_THEN "f'P" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism]
    (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))) THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (holed_disk_model k) SUBSET holed_disk_model k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  (* the circles lie in a and a' *)
  SUBGOAL_THEN `!i. i <= k ==> (jj:num->real^N->bool) i SUBSET a /\
                               (jj':num->real^M->bool) i SUBSET a'`
  (LABEL_TAC "jsub") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS {(jj:num->real^N->bool) i | i <= k}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        USE_THEN "fJ" (SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) (holed_disk_model k) = a` THEN
        UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN SET_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {(jj':num->real^M->bool) i | i <= k}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        USE_THEN "f'J" (SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `IMAGE (f':real^2->real^M) (holed_disk_model k) = a'` THEN
        UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* the pulled back circles *)
  SUBGOAL_THEN
   `!i. i <= k ==> pl_homeomorphism ((jj:num->real^N->bool) i,IMAGE (g:real^N->real^2) (jj i))
                                    (g,f) /\
                   pl_homeomorphism ((jj':num->real^M->bool) i,
                                     IMAGE (g':real^M->real^2) (jj' i)) (g',f')`
  (LABEL_TAC "jP") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "sp" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    USE_THEN "jsub" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THENL
     [EXISTS_TAC `a:real^N->bool` THEN EXISTS_TAC `holed_disk_model k`;
      EXISTS_TAC `a':real^M->bool` THEN EXISTS_TAC `holed_disk_model k`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC MOI_S3HX_SPHERE_LP THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC) THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `\i. IMAGE (g:real^N->real^2) ((jj:num->real^N->bool) i)`;
                `\i. IMAGE (g':real^M->real^2) ((jj':num->real^M->bool) i)`; `i0:num`;
                `(g':real^M->real^2) o (phi:real^N->real^M) o (f:real^2->real^N)`;
                `((g:real^N->real^2) o (phi':real^M->real^N)) o (f':real^2->real^M)`]
               MOI_S3HX_MODEL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "sp" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
      USE_THEN "jP" (STRIP_ASSUME_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5C_SPHERE1_TO_PLANE THEN
        MAP_EVERY EXISTS_TAC [`(jj:num->real^N->bool) i`; `g:real^N->real^2`;
                              `f:real^2->real^N`] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC(INST_TYPE [`:M`,`:N`] MOI_S5C_SPHERE1_TO_PLANE) THEN
        MAP_EVERY EXISTS_TAC [`(jj':num->real^M->bool) i`; `g':real^M->real^2`;
                              `f':real^2->real^M`] THEN
        ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
      USE_THEN "dj" (MP_TAC o C MP (CONJ (ASSUME `i:num <= k`) (CONJ (ASSUME `i':num <= k`)
        (ASSUME `~(i:num = i')`))) o SPECL [`i:num`; `i':num`]) THEN
      USE_THEN "jsub" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
      USE_THEN "jsub" (MP_TAC o C MP (ASSUME `i':num <= k`) o SPEC `i':num`) THEN
      UNDISCH_TAC `!y. y IN a ==> (f:real^2->real^N) ((g:real^N->real^2) y) = y` THEN
      UNDISCH_TAC `!y. y IN a' ==> (f':real^2->real^M) ((g':real^M->real^2) y) = y` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      SUBGOAL_THEN `UNIONS {IMAGE (g:real^N->real^2) ((jj:num->real^N->bool) i) | i <= k} =
                    IMAGE g (UNIONS {jj i | i <= k})` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "fJ" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `!x. x IN holed_disk_model k ==> (g:real^N->real^2) ((f:real^2->real^N) x) = x` THEN
      UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      SUBGOAL_THEN `UNIONS {IMAGE (g':real^M->real^2) ((jj':num->real^M->bool) i) | i <= k} =
                    IMAGE g' (UNIONS {jj' i | i <= k})` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "f'J" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `!x. x IN holed_disk_model k ==>
                       (g':real^M->real^2) ((f':real^2->real^M) x) = x` THEN
      UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "jP" (STRIP_ASSUME_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`) THEN
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `(jj':num->real^M->bool) i0` THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
        EXISTS_TAC `(jj:num->real^N->bool) i0` THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
          USE_THEN "phi" ACCEPT_TAC];
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^2->real^2` (X_CHOOSE_THEN `H':real^2->real^2`
    (CONJUNCTS_THEN2 (LABEL_TAC "HP") (CONJUNCTS_THEN2 (LABEL_TAC "Hpsi")
    (LABEL_TAC "HJ"))))) THEN
  MAP_EVERY EXISTS_TAC [`(f':real^2->real^M) o (H:real^2->real^2) o (g:real^N->real^2)`;
                        `((f:real^2->real^N) o (H':real^2->real^2)) o (g':real^M->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
      CONJ_TAC THENL
       [USE_THEN "fP" (fun th -> ACCEPT_TAC(ONCE_REWRITE_RULE[PL_HOMEOMORPHISM_SYM] th));
        USE_THEN "HP" ACCEPT_TAC];
      USE_THEN "f'P" ACCEPT_TAC];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "jsub" (STRIP_ASSUME_TAC o C MP (ASSUME `i0:num <= k`) o SPEC `i0:num`) THEN
    SUBGOAL_THEN `(g:real^N->real^2) y IN IMAGE g ((jj:num->real^N->bool) i0)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "Hpsi" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(g:real^N->real^2) y IN IMAGE g ((jj:num->real^N->bool) i0)`)]) THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(f:real^2->real^N) ((g:real^N->real^2) y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(jj:num->real^N->bool) i0 SUBSET a` THEN
      UNDISCH_TAC `(y:real^N) IN (jj:num->real^N->bool) i0` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "phi" (MP_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      REWRITE_RULE[pl_homeomorphism]) THEN
    UNDISCH_TAC `(jj':num->real^M->bool) i0 SUBSET a'` THEN
    UNDISCH_TAC `(y:real^N) IN (jj:num->real^N->bool) i0` THEN SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
    USE_THEN "HJ" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num <= k`)]) THEN
    USE_THEN "jsub" (MP_TAC o C MP (ASSUME `i:num <= k`) o SPEC `i:num`) THEN
    UNDISCH_TAC `!y. y IN a' ==> (f':real^2->real^M) ((g':real^M->real^2) y) = y` THEN
    SET_TAC[]]);;

