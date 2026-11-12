(* ========================================================================= *)
(* pc_moi_s32_init: Moise Sec 32 Lemmas 1-3, p.225.  Main theorem INITIAL    *)
(* (the statement MOI_S32_INITIAL of pc_moi_s3032_stmt): the initial barrier *)
(* M_1 = K UNION L UNION {P'} with the components of L as the family of a    *)
(* state.  Route: M_1 is closed in M (Lemma 1, local finiteness) and         *)
(* separates g qlo from g qhi (Lemma 3, via the separating image of the      *)
(* disk); each level surface L_i is a combinatorial surface with boundary    *)
(* its trace on K (Lemma 2 at the crossings, SURFACE_TRIANG), and the        *)
(* components of the L_i form the family.                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_s32_iter.ml";;
needs "src/pc_moi_s28_cut.ml";;
needs "src/pc_moi_s28_torus.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: general separation facts.  A closed superset of a separating      *)
(* set separates; the frontier of a set containing a separating set          *)
(* separates the points off its closure.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_SEP_MONO = prove
 (`!(m:real^N->bool) c d s t.
     separates_in m c s t /\ c SUBSET d /\ closed_in (subtopology euclidean m) d /\
     DISJOINT d (s UNION t)
     ==> separates_in m d s t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `w:real^N->bool`
    STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u DIFF (d:real^N->bool)`; `w DIFF (d:real^N->bool)`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean m) ((m:real^N->bool) DIFF d)` ASSUME_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean m) (d:real^N->bool)` THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET m /\ (w:real^N->bool) SUBSET m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `u DIFF (d:real^N->bool) = u INTER (m DIFF d)` SUBST1_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `w DIFF (d:real^N->bool) = w INTER (m DIFF d)` SUBST1_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3I2_FRONTIER_SEP = prove
 (`!(m:real^N->bool) c v s t.
     open m /\ separates_in m c s t /\ c SUBSET v /\
     s SUBSET m DIFF closure v /\ t SUBSET m DIFF closure v
     ==> separates_in m (m INTER frontier v) s t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET m /\ (w:real^N->bool) SUBSET m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(u DIFF closure v) UNION ((m:real^N->bool) INTER interior v)`;
    `(w:real^N->bool) DIFF closure v`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean m) ((m:real^N->bool) DIFF closure v) /\
                open_in (subtopology euclidean m) ((m:real^N->bool) INTER interior v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CLOSURE; OPEN_INTER; OPEN_INTERIOR] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `v:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[frontier] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
     [SUBGOAL_THEN `u DIFF closure v = (u:real^N->bool) INTER (m DIFF closure v)`
      SUBST1_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `w DIFF closure v = (w:real^N->bool) INTER (m DIFF closure v)`
    SUBST1_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: the disk separates in the model and its image separates in       *)
(* M (Moise p.225: Int D separates v1 from v2, preserved by h); the radial   *)
(* intervals [r_i, r_(i+1)] cover (0,1).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_DISK_SEP_MODEL = prove
 (`separates_in (interior moi_s32_cyl) {x:real^3 | x IN interior moi_s32_cyl /\ x$2 = &0}
                {moi_s32_qlo} {moi_s32_qhi}`,
  REWRITE_TAC[separates_in] THEN
  MAP_EVERY EXISTS_TAC [`interior moi_s32_cyl INTER {x:real^3 | x$2 < &0}`;
                        `interior moi_s32_cyl INTER {x:real^3 | &0 < x$2}`] THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN interior moi_s32_cyl` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SING_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s32_qlo; VECTOR_3] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SING_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s32_qhi; VECTOR_3] THEN REAL_ARITH_TAC]);;

let MOI_S3I2_SEP_IMAGE = prove
 (`!(g:real^N->real^N) m c s t.
     open m /\ g continuous_on m /\ (!x y. x IN m /\ y IN m /\ g x = g y ==> x = y) /\
     c SUBSET m /\ separates_in m c s t
     ==> separates_in (IMAGE g m) (IMAGE g c) (IMAGE g s) (IMAGE g t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET m /\ (w:real^N->bool) SUBSET m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `open (u:real^N->bool) /\ open (w:real^N->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (g:real^N->real^N) u`; `IMAGE (g:real^N->real^N) w`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* Integer-indexed increasing sequences. *)

let MOI_S3I2_INT_MONO = prove
 (`!f:int->real. (!i. f i < f (i + &1)) ==> !i j. i < j ==> f i < f j`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n i. (f:int->real) i < f (i + &n + &1)` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[INT_ADD_LID];
      GEN_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `(f:int->real) (i + &n + &1)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i + &(SUC n) + &1 = (i + &n + &1) + &1:int` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. (j:int) - i - &1 = &k` (X_CHOOSE_TAC `k:num`) THENL
   [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(j:int) = i + &k + &1` SUBST1_TAC THENL
   [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let MOI_S3I2_RADIAL_INDEX = prove
 (`!(f:int->real) r.
     (!i. f i < f (i + &1)) /\ (!e. &0 < e ==> (?i. f i < e) /\ (?i. &1 - e < f i)) /\
     &0 < r /\ r < &1
     ==> ?i. f i <= r /\ r <= f (i + &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inc")
    (CONJUNCTS_THEN2 (LABEL_TAC "lim") STRIP_ASSUME_TAC)) THEN
  USE_THEN "inc" (LABEL_TAC "mono" o MATCH_MP MOI_S3I2_INT_MONO) THEN
  USE_THEN "lim" (MP_TAC o C MP (ASSUME `&0 < r`) o SPEC `r:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `i0:int` o CONJUNCT1) THEN
  USE_THEN "lim" (MP_TAC o SPEC `&1 - r`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:int` o CONJUNCT2) THEN
  SUBGOAL_THEN `r < (f:int->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i0 < j:int` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `i0:int = j` THENL
     [UNDISCH_TAC `(f:int->real) i0 < r` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:int->real) j < f i0` MP_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. (f:int->real) (j - &(SUC n)) <= r` num_WOP) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `?k. (j:int) - i0 - &1 = &k` (X_CHOOSE_TAC `k:num`) THENL
     [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `k:num` THEN
    SUBGOAL_THEN `j - &(SUC k) = i0:int` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_INT_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j - &(SUC n0):int` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n0 = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j - &(SUC 0) + &1 = j:int` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n0 - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j - &(SUC (n0 - 1)) = j - &(SUC n0) + &1:int` SUBST1_TAC THENL
   [SUBGOAL_THEN `SUC (n0 - 1) = n0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: the union V of the solid tori with the centre contains the        *)
(* image of the open disk (the revolved segments [p_i, p_(i+1)] lie in Int   *)
(* S''_i and cover the punctured disk), and locally finite unions of closed  *)
(* subsets of the tori, with the centre, are closed in M (Lemma 1).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_TOWER_SEG = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_tower g v pp dd s2
     ==> IMAGE g (revolution (segment[pp i,pp (i + &1)])) SUBSET interior (s2 i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cc") STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "cc" (MP_TAC o SPEC `i:int`) THEN
  REWRITE_TAC[canonical_configuration] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[ARITH; INT_ADD_RID] THEN SIMP_TAC[]);;

let MOI_S3I2_DISK_IN_V = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> IMAGE g {x:real^3 | x IN interior moi_s32_cyl /\ x$2 = &0} SUBSET
         UNIONS {s2 i | i IN (:int)} UNION {g (vec 0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION; IN_SING; IN_UNIONS] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^3) IN interior moi_s32_cyl` THEN
  REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `r = sqrt((x:real^3)$1 pow 2 + x$3 pow 2)` THEN
  SUBGOAL_THEN `&0 < (x:real^3)$1 pow 2 + x$3 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ ~(a + b = &0) ==> &0 < a + b`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(x:real^3)$3` REAL_LE_POW_2) THEN
    UNDISCH_TAC `(x:real^3)$1 pow 2 + x$3 pow 2 = &0` THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MESON_TAC[REAL_ENTIRE; REAL_ARITH `&0 <= a /\ &0 <= b /\ a + b = &0 ==> a = &0 /\ b = &0`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r < &1 /\ r pow 2 = (x:real^3)$1 pow 2 + x$3 pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s32_tower g v pp dd s2` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(GEN_REWRITE_RULE I [moi_s32_tower] th)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\i:int. ((pp:int->real^3) i)$1`; `r:real`] MOI_S3I2_RADIAL_INDEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
  DISJ1_TAC THEN EXISTS_TAC `(s2:int->real^3->bool) i` THEN
  CONJ_TAC THENL [EXISTS_TAC `i:int` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. ?a. (pp:int->real^3) k = a % basis 1` (LABEL_TAC "ppform") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ppform" (X_CHOOSE_TAC `a:real` o SPEC `i:int`) THEN
  USE_THEN "ppform" (X_CHOOSE_TAC `b:real` o SPEC `i + &1:int`) THEN
  SUBGOAL_THEN `!c. (c % basis 1:real^3)$1 = c /\ (c % basis 1:real^3)$2 = &0 /\
                    (c % basis 1:real^3)$3 = &0`
  (LABEL_TAC "comp") THENL
   [GEN_TAC THEN SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= r /\ r <= b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `((pp:int->real^3) i)$1 <= r` THEN
    UNDISCH_TAC `r <= ((pp:int->real^3) (i + &1))$1` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN revolution (segment[(pp:int->real^3) i,pp (i + &1)])`
  ASSUME_TAC THENL
   [REWRITE_TAC[revolution; IN_ELIM_THM] THEN EXISTS_TAC `r % basis 1:real^3` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    ASM_CASES_TAC `a:real = b` THENL
     [EXISTS_TAC `&0` THEN
      REWRITE_TAC[REAL_LE_REFL; REAL_POS; REAL_SUB_RZERO; VECTOR_MUL_LID;
                  VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      SUBGOAL_THEN `r = a:real` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `(r - a) / (b - a)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < b - a` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                    MOI_S3I2_TOWER_SEG)
            (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
  MP_TAC(ISPEC `(s2:int->real^3->bool) i` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(x:real^3) IN revolution (segment[(pp:int->real^3) i,pp (i + &1)])` THEN
  MATCH_ACCEPT_TAC(SET_RULE `!(x:real^3) a i s (g:real^3->real^3).
    x IN a ==> i SUBSET s ==> IMAGE g a SUBSET i ==> g x IN s`));;

(* ------------------------------------------------------------------------- *)
(* Part 4: Lemma 1 (local finiteness gives closedness in M) and the          *)
(* barrier set as the union of all the tori frontiers and the centre minus   *)
(* the even interiors.                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_LF_FAMILY = prove
 (`!(g:real^3->real^3) v pp dd s2 (h:int->int) (a:int->real^3->bool) x.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     (!i j. h i = h j ==> i = j) /\
     (!i. a i SUBSET IMAGE g (revolution (dd (h i)))) /\
     x IN moi_s32_open g /\ ~(x = g (vec 0))
     ==> ?u. open u /\ x IN u /\ FINITE {i | ~(a i INTER u = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
                MOI_S3IT_LOCAL_FINITE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i:int | (h:int->int) i IN
                {j | ~(IMAGE (g:real^3->real^3) (revolution (dd j)) INTER u = {})}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th ->
    is_forall(concl th) && is_comb(snd(dest_forall(concl th))) &&
    (try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) = "SUBSET"
     with Failure _ -> false))) THEN
  SET_TAC[]);;

let MOI_S3I2_LF_CLOSED_IN = prove
 (`!(m:real^3->bool) (a:int->real^3->bool) q.
     (!i. closed (a i)) /\ (!i. a i SUBSET m) /\ q IN m /\
     (!x. x IN m /\ ~(x = q) ==> ?u. open u /\ x IN u /\ FINITE {i | ~(a i INTER u = {})})
     ==> closed_in (subtopology euclidean m) (UNIONS {a i | i IN (:int)} UNION {q})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_LIMPT] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; SING_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = q` THENL [ASM_REWRITE_TAC[IN_UNION; IN_SING]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ff = {i:int | ~((a:int->real^3->bool) i INTER u = {})}` THEN
  SUBGOAL_THEN `closed (UNIONS (IMAGE (a:int->real^3->bool) ff))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) limit_point_of UNIONS (IMAGE (a:int->real^3->bool) ff)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIMPT_SUBSET THEN
    EXISTS_TAC `(UNIONS {(a:int->real^3->bool) i | i IN (:int)} UNION {q}) INTER
                (u DIFF {q})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3IT_LIMPT_INTER_OPEN THEN ASM_REWRITE_TAC[IN_DIFF; IN_SING] THEN
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_SING];
      EXPAND_TAC "ff" THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_UNIONS; IN_IMAGE; IN_ELIM_THM; IN_UNIV;
                  IN_DIFF; IN_SING] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      ASM_MESON_TAC[SET_RULE `!(y:real^3) s u. y IN s /\ y IN u ==> ~(s INTER u = {})`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS (IMAGE (a:int->real^3->bool) ff)` MP_TAC THENL
   [ASM_MESON_TAC[CLOSED_LIMPT]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: Lemma 3.  M_1 = K UNION L UNION {P'} is the union of all          *)
(* the tori frontiers and the centre minus the even interiors; it is closed *)
(* in M; it contains the part in M of the frontier of V = UNIONS S''_i      *)
(* UNION {P'}; V contains the image of the open disk, which separates; so   *)
(* M_1 separates g qlo from g qhi in M.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_TORI_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> (!k. compact (s2 k) /\ s2 k SUBSET moi_s32_open g /\
              frontier (s2 k) SUBSET s2 k /\ closed (frontier (s2 k)) /\
              ~(g (vec 0) IN s2 k) /\ ~(g moi_s32_qlo IN s2 k) /\ ~(g moi_s32_qhi IN s2 k)) /\
         g (vec 0) IN moi_s32_open g /\ g moi_s32_qlo IN moi_s32_open g /\
         g moi_s32_qhi IN moi_s32_open g /\
         ~(g moi_s32_qlo = g (vec 0)) /\ ~(g moi_s32_qhi = g (vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tt") THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(moi_s32_qlo IN v) /\ ~(moi_s32_qhi IN v) /\
                ~(moi_s32_qlo = vec 0) /\ ~(moi_s32_qhi = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      REWRITE_TAC[moi_s32_qlo; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[moi_s32_qhi; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN moi_s32_cyl /\ (g:real^3->real^3) z IN IMAGE g v ==> z IN v`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `z:real^3 = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:int` THEN USE_THEN "tt" (STRIP_ASSUME_TAC o SPEC `k:int`) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED; FRONTIER_CLOSED] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN IMAGE g v)` THEN
      ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(moi_s32_qlo IN v)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(moi_s32_qhi IN v)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(moi_s32_qlo = vec 0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(moi_s32_qhi = vec 0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* The even interiors miss the even frontiers and the centre. *)

let MOI_S3I2_EVEN_INTERIORS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> DISJOINT (moi_s32_evens s2) (UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) /\
         ~(g (vec 0) IN UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) /\
         open (UNIONS {interior (s2 (&2 * i)) | i IN (:int)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS)
            (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") STRIP_ASSUME_TAC) THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI)
            (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
  DISCH_THEN(LABEL_TAC "tt") THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s32_evens; SET_RULE `!a b:real^3->bool.
                  DISJOINT a b <=> !x. x IN a ==> ~(x IN b)`; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:int`)
      ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:int`)
      ASSUME_TAC)) THEN
    UNDISCH_TAC `(y:real^3) IN t` THEN UNDISCH_TAC `(y:real^3) IN t'` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `i:int = j` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * j))` THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i:int`; `&2 * j:int`]
                  MOI_S3IT_FAR_DISJOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "tt" (STRIP_ASSUME_TAC o SPEC `&2 * i:int`) THEN
    USE_THEN "tt" (STRIP_ASSUME_TAC o SPEC `&2 * j:int`) THEN
    MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * j)` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:int`)
      ASSUME_TAC)) THEN
    UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "tf" (MP_TAC o SPEC `&2 * i:int`) THEN
    MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * i)` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_INTERIOR]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: Lemma 3 continued.  M_1 is the union of all the tori             *)
(* frontiers and the centre minus the even interiors, hence closed in M;    *)
(* V = UNIONS S''_i UNION {P'} is closed in M; the part in M of the         *)
(* frontier of V lies in M_1; V contains the separating image of the disk;  *)
(* so M_1 separates g qlo from g qhi in M.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_INT_PARITY = prove
 (`!k:int. ?i. k = &2 * i \/ k = &2 * i + &1`,
  GEN_TAC THEN MP_TAC(SPECL [`k:int`; `&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_ARITH `~(&2:int = &0)`; INT_ABS_NUM] THEN STRIP_TAC THEN
  EXISTS_TAC `k div &2` THEN ASM_INT_ARITH_TAC);;

let MOI_S3I2_ALL_FRONTIERS = prove
 (`!s2:int->real^3->bool.
     moi_s32_evens s2 UNION UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} =
     UNIONS {frontier (s2 k) | k IN (:int)}`,
  GEN_TAC THEN REWRITE_TAC[moi_s32_evens; GSYM UNIONS_UNION] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `t:real^3->bool` THEN EQ_TAC THENL
   [MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:int` SUBST1_TAC) THEN
    MP_TAC(SPEC `k:int` MOI_S3I2_INT_PARITY) THEN MESON_TAC[]]);;

let MOI_S3I2_M1_EQ = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> moi_s32_evens s2 UNION
         (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
          UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)} =
         (UNIONS {frontier (s2 k) | k IN (:int)} UNION {g (vec 0)}) DIFF
         UNIONS {interior (s2 (&2 * i)) | i IN (:int)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3I2_EVEN_INTERIORS) THEN
  SUBST1_TAC(SYM(SPEC `s2:int->real^3->bool` MOI_S3I2_ALL_FRONTIERS)) THEN
  MATCH_ACCEPT_TAC(SET_RULE `!ev od e (q:real^3) p.
    DISJOINT ev e /\ ~(q IN e) /\ p
    ==> ev UNION (od DIFF e) UNION {q} = ((ev UNION od) UNION {q}) DIFF e`));;

(* Locally finite unions of closed subsets of the tori, with the centre,    *)
(* are closed in M.                                                          *)

let MOI_S3I2_LF_TOWER = prove
 (`!(g:real^3->real^3) v pp dd s2 (a:int->real^3->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     (!k. closed (a k)) /\ (!k. a k SUBSET s2 k)
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (UNIONS {a i | i IN (:int)} UNION {g (vec 0)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS)
            (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") STRIP_ASSUME_TAC) THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI)
            (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
  DISCH_THEN(LABEL_TAC "tt") THEN
  MATCH_MP_TAC MOI_S3I2_LF_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:int` THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(s2:int->real^3->bool) k` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `\k:int. k`;
                   `a:int->real^3->bool`; `x:real^3`] MOI_S3I2_LF_FAMILY) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:int` THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(s2:int->real^3->bool) k` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3I2_V_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (UNIONS {s2 i | i IN (:int)} UNION {g (vec 0)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `s2:int->real^3->bool`]
                MOI_S3I2_LF_TOWER) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI)
            (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
  MESON_TAC[COMPACT_IMP_CLOSED]);;

let MOI_S3I2_M1_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> closed_in (subtopology euclidean (moi_s32_open g))
           (moi_s32_evens s2 UNION
            (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
             UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3I2_M1_EQ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3I2_TORI_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3I2_EVEN_INTERIORS) THEN STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_DIFF THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                   `\k:int. frontier ((s2:int->real^3->bool) k)`] MOI_S3I2_LF_TOWER) THEN
    ASM_REWRITE_TAC[FRONTIER_CLOSED] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `k:int` THEN USE_THEN "tf" (MP_TAC o SPEC `k:int`) THEN SIMP_TAC[];
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `i:int` THEN USE_THEN "tf" (MP_TAC o SPEC `&2 * i:int`) THEN
    MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * i)` INTERIOR_SUBSET) THEN SET_TAC[]]);;

(* The part in M of the frontier of V lies in M_1. *)

let MOI_S3I2_FRONTIER_V = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> moi_s32_open g INTER frontier (UNIONS {s2 i | i IN (:int)} UNION {g (vec 0)})
         SUBSET
         moi_s32_evens s2 UNION
         (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
          UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_V_CLOSED)
            (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`))) THEN
  REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
  ABBREV_TAC `vv = UNIONS {(s2:int->real^3->bool) i | i IN (:int)} UNION
                   {(g:real^3->real^3) (vec 0)}` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `!k. interior ((s2:int->real^3->bool) k) SUBSET interior vv`
  (LABEL_TAC "isub") THENL
   [GEN_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN EXPAND_TAC "vv" THEN
    REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI)
            (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
  DISCH_THEN(LABEL_TAC "tt") THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (STRIP_ASSUME_TAC o REWRITE_RULE[frontier; IN_DIFF])) THEN
  SUBGOAL_THEN `(x:real^3) IN vv` ASSUME_TAC THENL
   [UNDISCH_TAC `vv = moi_s32_open g INTER closure vv` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s32_open g` THEN
    UNDISCH_TAC `(x:real^3) IN closure vv` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!c m v (x:real^3).
      x IN c ==> x IN m ==> v = m INTER c ==> x IN v`);
    ALL_TAC] THEN
  ASM_CASES_TAC `x = (g:real^3->real^3) (vec 0)` THENL
   [ASM_REWRITE_TAC[IN_UNION; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `?k:int. (x:real^3) IN (s2:int->real^3->bool) k` (X_CHOOSE_TAC `k:int`) THENL
   [UNDISCH_TAC `(x:real^3) IN vv` THEN
    UNDISCH_TAC `~(x = (g:real^3->real^3) (vec 0))` THEN EXPAND_TAC "vv" THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j:int. ~((x:real^3) IN interior ((s2:int->real^3->bool) j))` ASSUME_TAC THENL
   [X_GEN_TAC `j:int` THEN USE_THEN "isub" (MP_TAC o SPEC `j:int`) THEN
    UNDISCH_TAC `~((x:real^3) IN interior vv)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "tt" (STRIP_ASSUME_TAC o SPEC `k:int`) THEN
  SUBGOAL_THEN `(x:real^3) IN frontier (s2 (k:int))` MP_TAC THENL
   [REWRITE_TAC[frontier; IN_DIFF] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:int` MOI_S3I2_INT_PARITY) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (DISJ_CASES_THEN SUBST1_TAC)) THEN DISCH_TAC THENL
   [REWRITE_TAC[IN_UNION; moi_s32_evens] THEN DISJ1_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_UNION; IN_DIFF] THEN DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!j:int. ~((x:real^3) IN interior ((s2:int->real^3->bool) j))` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]]]);;

(* Lemma 3: M_1 separates g qlo from g qhi in M. *)

let MOI_S3I2_M1_SEP = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> separates_in (moi_s32_open g)
           (moi_s32_evens s2 UNION
            (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
             UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)})
           {g moi_s32_qlo} {g moi_s32_qhi}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS)
            (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k:int. ~((g:real^3->real^3) moi_s32_qlo IN (s2:int->real^3->bool) k) /\ ~(g moi_s32_qhi IN s2 k) /\
                    ~(g moi_s32_qlo IN frontier (s2 k)) /\ ~(g moi_s32_qhi IN frontier (s2 k))`
  (LABEL_TAC "qq") THENL
   [X_GEN_TAC `k:int` THEN USE_THEN "tf" (MP_TAC o SPEC `k:int`) THEN SET_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(CONJUNCT2(MATCH_MP MOI_S3GF_MODEL_OPEN (ASSUME `moi_s32_model g v`))) THEN
  SUBGOAL_THEN
   `~((g:real^3->real^3) moi_s32_qlo IN
      closure (UNIONS {(s2:int->real^3->bool) i | i IN (:int)} UNION {g (vec 0)})) /\
    ~(g moi_s32_qhi IN closure (UNIONS {s2 i | i IN (:int)} UNION {g (vec 0)}))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MP (ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_V_CLOSED)
              (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`))) THEN
    REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
    SUBGOAL_THEN `~((g:real^3->real^3) moi_s32_qlo IN
                    UNIONS {(s2:int->real^3->bool) i | i IN (:int)} UNION {g (vec 0)}) /\
                  ~(g moi_s32_qhi IN UNIONS {s2 i | i IN (:int)} UNION {g (vec 0)})`
    MP_TAC THENL
     [USE_THEN "qq" MP_TAC THEN
      MP_TAC(ASSUME `~((g:real^3->real^3) moi_s32_qlo = g (vec 0))`) THEN
      MP_TAC(ASSUME `~((g:real^3->real^3) moi_s32_qhi = g (vec 0))`) THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_SING] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN moi_s32_open g` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN moi_s32_open g` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!m vv (a:real^3) b.
      a IN m ==> b IN m ==> ~(a IN vv) /\ ~(b IN vv) ==> m INTER closure vv = vv
      ==> ~(a IN closure vv) /\ ~(b IN closure vv)`);
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3I2_SEP_MONO THEN
  EXISTS_TAC `moi_s32_open g INTER
              frontier (UNIONS {(s2:int->real^3->bool) i | i IN (:int)} UNION
                        {(g:real^3->real^3) (vec 0)})` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3I2_FRONTIER_SEP THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) {x:real^3 | x IN interior moi_s32_cyl /\ x$2 = &0}` THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_DIFF] THEN CONJ_TAC THENL
     [SUBST1_TAC(CONJUNCT1(MATCH_MP MOI_S3GF_MODEL_OPEN (ASSUME `moi_s32_model g v`))) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `interior moi_s32_cyl`;
                     `{x:real^3 | x IN interior moi_s32_cyl /\ x$2 = &0}`;
                     `{moi_s32_qlo}`; `{moi_s32_qhi}`] MOI_S3I2_SEP_IMAGE) THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[OPEN_INTERIOR; MOI_S3I2_DISK_SEP_MODEL] THEN
      UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\
                           (g:real^3->real^3) x = g y ==> x = y` THEN
        UNDISCH_TAC `interior moi_s32_cyl SUBSET moi_s32_cyl` THEN SET_TAC[];
        SET_TAC[]];
      MATCH_MP_TAC MOI_S3I2_DISK_IN_V THEN
      MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_S3I2_FRONTIER_V THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3I2_M1_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SET_RULE `!s (a:real^3) b. DISJOINT s ({a} UNION {b}) <=>
                                           ~(a IN s) /\ ~(b IN s)`] THEN
    USE_THEN "qq" MP_TAC THEN
    MP_TAC(ASSUME `~((g:real^3->real^3) moi_s32_qlo = g (vec 0))`) THEN
    MP_TAC(ASSUME `~((g:real^3->real^3) moi_s32_qhi = g (vec 0))`) THEN
    REWRITE_TAC[moi_s32_evens; IN_UNION; IN_DIFF; IN_SING; UNIONS_GSPEC; IN_ELIM_THM;
                IN_UNIV] THEN
    MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 7: Lemma 2, the local structure at a crossing (p.225).  A            *)
(* connected set missing the frontier of a closed set s lies in its interior *)
(* or misses it; a PL solid torus is the closure of its interior; a crossing *)
(* chart in either order; at a crossing point y of a surface t with the      *)
(* frontier of a regular closed s, exactly one of the two half balls of the *)
(* chart goes into the interior of s, so t minus the interior of s is a      *)
(* half plane near y.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_CONNECTED_SIDE = prove
 (`!(c:real^3->bool) s.
     connected c /\ closed s /\ c INTER frontier s = {}
     ==> c SUBSET interior s \/ c INTER s = {}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(c:real^3->bool) INTER s = {}` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real^3->bool) DIFF s = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `s:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` CLOSURE_CLOSED) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(c:real^3->bool) INTER frontier s = {}` THEN
  UNDISCH_TAC `(c:real^3->bool) DIFF s = {}` THEN
  REWRITE_TAC[frontier] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* A PL solid torus is compact and the closure of its interior (as in        *)
(* MOI_S8TO_SIDES of pc_moi_s28_torus, whose statement hides it).            *)

let MOI_S3I2_SOLID_TORUS_REGULAR = prove
 (`!s:real^3->bool. pl_solid_torus s ==> compact s /\ closure (interior s) = s`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact(s:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `s = IMAGE (f:real^(2,1)finite_sum->real^3) moi_fps_m` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_FPS_M_COMPACT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^(2,1)finite_sum->real^3) (interior moi_fps_m) SUBSET interior s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^(2,1)finite_sum->real^3`; `moi_fps_m`]
                  CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET closure(interior s)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^(2,1)finite_sum->real^3) (closure(interior moi_fps_m))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^(2,1)finite_sum->real^3) moi_fps_m = s` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[MOI_S8TO_M_CLOSURE];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_fps_m` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
        SIMP_TAC[INTERIOR_SUBSET; COMPACT_IMP_CLOSED; MOI_FPS_M_COMPACT];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior(s:real^3->bool)` THEN
        ASM_REWRITE_TAC[CLOSURE_SUBSET]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[INTERIOR_SUBSET; COMPACT_IMP_CLOSED]);;

(* A crossing in either order gives a chart with t on x1 = 0 and m on      *)
(* x2 = 0 (compose with the coordinate swap in the second case).            *)

let MOI_S3I2_SWAP_FACTS = prove
 (`!sw:real^3->real^3.
     sw = (\z. vector[z$2; z$1; z$3])
     ==> linear sw /\ (!z. sw (sw z) = z) /\ (!z. (sw z)$1 = z$2 /\ (sw z)$2 = z$1)`,
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT]);;

let MOI_S3I2_CROSS_CHART = prove
 (`!(t:real^3->bool) m y.
     pl_crossing_at t m y \/ pl_crossing_at m t y
     ==> ?u (f:real^3->real^3) g.
           open u /\ y IN u /\ homeomorphism (u,IMAGE f u) (f,g) /\
           open (IMAGE f u) /\ f y = vec 0 /\
           IMAGE f (t INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0} /\
           IMAGE f (m INTER u) = IMAGE f u INTER {z:real^3 | z$2 = &0}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN
    `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)))) THENL
   [MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sw = \z:real^3. vector[z$2; z$1; z$3]:real^3` THEN
  MP_TAC(SPEC `sw:real^3->real^3` MOI_S3I2_SWAP_FACTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o SYM); STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `(sw:real^3->real^3) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (sw:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  SUBGOAL_THEN `!a:real^3->bool. IMAGE (sw:real^3->real^3) (a INTER {z | z$1 = &0}) =
                                 IMAGE sw a INTER {z | z$2 = &0} /\
                                 IMAGE sw (a INTER {z | z$2 = &0}) =
                                 IMAGE sw a INTER {z | z$1 = &0}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    UNDISCH_TAC `!z:real^3. (sw:real^3->real^3) (sw z) = z` THEN SET_TAC[];
    MP_TAC(ISPECL [`sw:real^3->real^3`; `IMAGE (f:real^3->real^3) u`]
                  OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `sw:real^3->real^3` LINEAR_0) THEN ASM_REWRITE_TAC[]]);;

(* Norms on the chart planes, and homeomorphisms from continuous left       *)
(* inverses.                                                                 *)

let MOI_S3I2_PLANE_NORMS = prove
 (`!e. e * e = &1
       ==> (!z:real^3. z$1 = &0 ==> norm(vector[z$3; --e * z$2]:real^2) = norm z) /\
           (!w:real^2. norm(vector[&0; --e * w$2; w$1]:real^3) = norm w)`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[vector_norm; DOT_2; DOT_3; VECTOR_2; VECTOR_3] THEN
  TRY DISCH_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `e * e = &1` THEN CONV_TAC REAL_RING);;

let MOI_S3I2_HOMEO_LEFT_INV = prove
 (`!(p:real^M->real^N) q n.
     p continuous_on n /\ q continuous_on IMAGE p n /\ (!x. x IN n ==> q (p x) = x)
     ==> homeomorphism (n,IMAGE p n) (p,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[homeomorphism] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `!x:real^M. x IN n ==> (q:real^N->real^M) (p x) = x` THEN
  SET_TAC[]);;

(* The half plane chart, when the half ball of e * x2 > 0 goes into the     *)
(* interior of s and the other one misses s.                                 *)

let MOI_S3I2_HALF_CHART = prove
 (`!(s:real^3->bool) t y u (f:real^3->real^3) g r e.
     (e = &1 \/ e = -- &1) /\ &0 < r /\ ball(vec 0,r) SUBSET IMAGE f u /\
     homeomorphism (u,IMAGE f u) (f,g) /\ open u /\
     y IN u /\ f y = vec 0 /\ y IN t /\ y IN frontier s /\
     IMAGE f (t INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0} /\
     IMAGE f (frontier s INTER u) = IMAGE f u INTER {z:real^3 | z$2 = &0} /\
     IMAGE g (ball(vec 0,r) INTER {z:real^3 | &0 < e * z$2}) SUBSET interior s /\
     IMAGE g (ball(vec 0,r) INTER {z:real^3 | e * z$2 < &0}) INTER s = {}
     ==> moi_s28_locally_half (t DIFF interior s) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real) * e = &1` ASSUME_TAC THENL
   [USE_THEN "e" (DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `e:real` MOI_S3I2_PLANE_NORMS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n1") (LABEL_TAC "n2")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!z:real^3. z IN ball(vec 0,r) ==> (g:real^3->real^3) z IN u /\ f (g z) = z`
  (LABEL_TAC "inv") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u) = u` THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) =
                {x:real^3 | x IN u /\ (f:real^3->real^3) x IN ball(vec 0,r)}`
  (LABEL_TAC "gge") THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "inv" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(f:real^3->real^3) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) (ball(vec 0,r))) /\
                (y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r)) /\
                IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET u`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "gge" SUBST1_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN (t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))
       ==> x IN t /\ x IN u /\ ~(x IN interior s) /\
           (f:real^3->real^3) x IN ball(vec 0,r) /\ (f x)$1 = &0 /\ e * (f x)$2 <= &0`
  (LABEL_TAC "nf") THENL
   [X_GEN_TAC `x:real^3` THEN USE_THEN "gge" SUBST1_TAC THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE f (t INTER u)` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x:real^3) IN interior s)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `x = (g:real^3->real^3) ((f:real^3->real^3) x)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ASSUME `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | &0 < e * z$2})
                     SUBSET interior s`) THEN
      MATCH_MP_TAC(SET_RULE `!(g:real^3->real^3) a b z.
        z IN a ==> (IMAGE g a SUBSET b ==> g z IN b)`) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. vector[((f:real^3->real^3) x)$3; --e * (f x)$2]:real^2)
          ((t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))) =
    {w:real^2 | w IN ball(vec 0,r) /\ &0 <= w$2}`
  (LABEL_TAC "img") THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "nf" (MP_TAC o C MATCH_MP (ASSUME
      `(x:real^3) IN (t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))`)) THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_2; IN_BALL_0] THEN CONJ_TAC THENL
       [USE_THEN "n1" (fun th -> ASM_SIMP_TAC[th]) THEN
        UNDISCH_TAC `(f:real^3->real^3) x IN ball(vec 0,r)` THEN REWRITE_TAC[IN_BALL_0];
        ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN
      ABBREV_TAC `z = vector[&0; --e * (w:real^2)$2; w$1]:real^3` THEN
      SUBGOAL_THEN `(z:real^3)$1 = &0 /\ z$2 = --e * (w:real^2)$2 /\ z$3 = w$1`
      STRIP_ASSUME_TAC THENL [EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN ball(vec 0,r)` ASSUME_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[IN_BALL_0] THEN
        USE_THEN "n2" (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `(w:real^2) IN ball(vec 0,r)` THEN REWRITE_TAC[IN_BALL_0];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
        UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "inv" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) z IN t` ASSUME_TAC THENL
       [SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (t INTER u)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~((g:real^3->real^3) z IN interior s)` ASSUME_TAC THENL
       [ASM_CASES_TAC `(w:real^2)$2 = &0` THENL
         [SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (frontier s INTER u)`
          MP_TAC THENL
           [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; REAL_MUL_RZERO]; ALL_TAC] THEN
          REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
          DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
          ASM_SIMP_TAC[] THEN UNDISCH_TAC `(x':real^3) IN frontier s` THEN
          REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[];
          MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | e * z$2 < &0})
                       INTER s = {}` THEN
          SUBGOAL_THEN `(z:real^3) IN ball(vec 0,r) INTER {z:real^3 | e * z$2 < &0}` MP_TAC THENL
           [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
            SUBGOAL_THEN `e * --e * (w:real^2)$2 = --(w$2)` SUBST1_TAC THENL
             [UNDISCH_TAC `(e:real) * e = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_ACCEPT_TAC(SET_RULE `!(g:real^3->real^3) a s i z.
            z IN a ==> IMAGE g a INTER s = {} ==> i SUBSET s ==> ~(g z IN i)`)];
        ALL_TAC] THEN
      EXISTS_TAC `(g:real^3->real^3) z` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      UNDISCH_TAC `(e:real) * e = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN (t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))
       ==> (\w:real^2. g (vector[&0; --e * w$2; w$1]))
           ((\x:real^3. vector[((f:real^3->real^3) x)$3; --e * (f x)$2]:real^2) x) = x`
  (LABEL_TAC "linv") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "nf" (MP_TAC o C MATCH_MP (ASSUME
      `(x:real^3) IN (t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))`)) THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_2] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(g:real^3->real^3) ((f:real^3->real^3) x)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:real) * e = &1` THEN CONV_TAC REAL_RING;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_HALF_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC
   [`(t DIFF interior s) INTER IMAGE (g:real^3->real^3) (ball(vec 0,r))`;
    `\x:real^3. vector[((f:real^3->real^3) x)$3; --e * (f x)$2]:real^2`;
    `\w:real^2. (g:real^3->real^3) (vector[&0; --e * w$2; w$1])`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_ELIM_THM; CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(y:real^3) IN frontier s` THEN REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[];
    MATCH_MP_TAC MOI_S3I2_HOMEO_LEFT_INV THEN USE_THEN "linv" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^3. vector[((f:real^3->real^3) x)$3; --e * (f x)$2]:real^2) =
                    (\z:real^3. vector[z$3; --e * z$2]:real^2) o f` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET u` THEN SET_TAC[];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC];
      USE_THEN "img" SUBST1_TAC THEN
      SUBGOAL_THEN `(\w:real^2. (g:real^3->real^3) (vector[&0; --e * w$2; w$1])) =
                    g o (\w:real^2. vector[&0; --e * w$2; w$1]:real^3)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
        USE_THEN "n2" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]]];
    USE_THEN "img" SUBST1_TAC THEN
    SUBGOAL_THEN `{w:real^2 | w IN ball(vec 0,r) /\ &0 <= w$2} =
                  {z:real^2 | &0 <= z$2} INTER ball(vec 0,r)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* Lemma 2 at a crossing point: t minus the interior of s is a half plane. *)

let MOI_S3I2_CROSS_HALF = prove
 (`!(s:real^3->bool) t y u (f:real^3->real^3) g.
     closed s /\ s SUBSET closure (interior s) /\ y IN t /\ y IN frontier s /\
     open u /\ y IN u /\ homeomorphism (u,IMAGE f u) (f,g) /\
     open (IMAGE f u) /\ f y = vec 0 /\
     IMAGE f (t INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0} /\
     IMAGE f (frontier s INTER u) = IMAGE f u INTER {z:real^3 | z$2 = &0}
     ==> moi_s28_locally_half (t DIFF interior s) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:real^3->real^3) u` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBST1_TAC(SYM(ASSUME `(f:real^3->real^3) y = vec 0`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN ball(vec 0,r) ==> (g:real^3->real^3) z IN u /\ f (g z) = z`
  (LABEL_TAC "inv") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u) = u` THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | z$2 = &0})
                SUBSET frontier s`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (frontier s INTER u)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gp = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | &0 < z$2})` THEN
  ABBREV_TAC `gm = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | z$2 < &0})` THEN
  SUBGOAL_THEN `connected (gp:real^3->bool) /\ connected (gm:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["gp"; "gm"] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN
       ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
       MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
       REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_LT;
                   REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(gp:real^3->bool) INTER frontier s = {} /\
                (gm:real^3->bool) INTER frontier s = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["gp"; "gm"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "inv" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (frontier s INTER u)` MP_TAC THENL
      [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN
       UNDISCH_TAC `(x:real^3) IN frontier s` THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gp:real^3->bool`; `s:real^3->bool`] MOI_S3I2_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`gm:real^3->bool`; `s:real^3->bool`] MOI_S3I2_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET gp UNION gm UNION frontier s`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["gp"; "gm"] THEN REWRITE_TAC[IN_UNION] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (REAL_ARITH `&0 < (z:real^3)$2 \/ z$2 < &0 \/ z$2 = &0`) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
      DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
      DISJ2_TAC THEN DISJ2_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | z$2 = &0})
                   SUBSET frontier s` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) (ball(vec 0,r))) /\
                (y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) =
                  {x:real^3 | x IN u /\ (f:real^3->real^3) x IN ball(vec 0,r)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        USE_THEN "inv" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vec 0,r)`)) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN EXISTS_TAC `(f:real^3->real^3) x` THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 IN interior s) /\ (y:real^3) IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN frontier s` THEN REWRITE_TAC[frontier; IN_DIFF] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gp:real^3->bool) SUBSET interior s /\ (gm:real^3->bool) SUBSET interior s)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET interior s` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `s:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET gp UNION gm UNION frontier s` THEN
      UNDISCH_TAC `(gp:real^3->bool) SUBSET interior s` THEN
      UNDISCH_TAC `(gm:real^3->bool) SUBSET interior s` THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r))` THEN
      UNDISCH_TAC `~(y:real^3 IN interior s)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gp:real^3->bool) INTER s = {} /\ (gm:real^3->bool) INTER s = {})`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) INTER interior s = {}`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN
      SUBGOAL_THEN `frontier s INTER interior (s:real^3->bool) = {}` MP_TAC THENL
       [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET gp UNION gm UNION frontier s` THEN
      UNDISCH_TAC `(gp:real^3->bool) INTER s = {}` THEN
      UNDISCH_TAC `(gm:real^3->bool) INTER s = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (ball(vec 0,r))`; `interior s:real^3->bool`]
                  OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r))` THEN
    UNDISCH_TAC `(y:real^3) IN s` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET closure (interior s)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((gp:real^3->bool) SUBSET interior s /\ (gm:real^3->bool) INTER s = {}) \/
                (gm SUBSET interior s /\ gp INTER s = {})`
  MP_TAC THENL
   [UNDISCH_TAC `~((gp:real^3->bool) INTER s = {} /\ (gm:real^3->bool) INTER s = {})` THEN
    UNDISCH_TAC `~((gp:real^3->bool) SUBSET interior s /\ (gm:real^3->bool) SUBSET interior s)` THEN
    UNDISCH_TAC `(gm:real^3->bool) SUBSET interior s \/ gm INTER s = {}` THEN
    UNDISCH_TAC `(gp:real^3->bool) SUBSET interior s \/ gp INTER s = {}` THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S3I2_HALF_CHART THENL
   [MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                          `r:real`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID];
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                          `r:real`; `-- &1`] THEN
    ASM_REWRITE_TAC[REAL_ARITH `!x. &0 < -- &1 * x <=> x < &0`;
                    REAL_ARITH `!x. -- &1 * x < &0 <=> &0 < x`]]);;


(* ------------------------------------------------------------------------- *)
(* Part 8: the level surfaces L_i = T''_(2i+1) minus the interiors of       *)
(* S''_(2i) and S''_(2i+2) (p.225).  Far tori are disjoint; consecutive      *)
(* frontiers cross; L_i is locally a half plane at its points on the even    *)
(* tori and locally R^2 elsewhere; it is triangulated (T''_(2i+1) is a PL    *)
(* torus, the crossing curves are polyhedra, MOI_S8CU_REMOVE_OPEN), and by   *)
(* SURFACE_TRIANG a combinatorial surface with boundary its trace on K.     *)
(* ------------------------------------------------------------------------- *)

let moi_s3i2_lsurf = new_definition
 `moi_s3i2_lsurf (s2:int->real^3->bool) (i:int) =
    frontier (s2 (&2 * i + &1)) DIFF (interior (s2 (&2 * i)) UNION interior (s2 (&2 * i + &2)))`;;

let MOI_S3I2_FAR_TORI = prove
 (`!(g:real^3->real^3) v pp dd s2 a b.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ (a + &2 <= b \/ b + &2 <= a)
     ==> DISJOINT (s2 a) (s2 b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP MOI_S3IT_FAR_DISJOINT th) THEN
                       MP_TAC(MATCH_MP MOI_S3GF_TOWER_TORI (CONJUNCT1(CONJUNCT2 th)))) THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `a:int` th)))) THEN
                       MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `b:int` th))))) THEN
  SET_TAC[]);;

let MOI_S3I2_SOLID_TORUS_POLY = prove
 (`!s:real^3->bool. pl_solid_torus s ==> pl_polyhedron s`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [homeomorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_FPS_M_PL_POLYHEDRON]);;

(* Consecutive frontiers cross (the canonical configurations of the tower). *)

let MOI_S3I2_TOWER_CROSS = prove
 (`!(g:real^3->real^3) v pp dd s2 b y.
     moi_s32_tower g v pp dd s2 /\ y IN frontier (s2 b) INTER frontier (s2 (b + &1))
     ==> pl_crossing_at (frontier (s2 b)) (frontier (s2 (b + &1))) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower; canonical_configuration] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `b:int` o CONJUNCT1) ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`0`; `y:real^3`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[ARITH; INT_ADD_RID]);;

(* The tori facts at the three indices of a level. *)

let MOI_S3I2_LEVEL_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> (!k. k = &2 * i \/ k = &2 * i + &1 \/ k = &2 * i + &2
              ==> pl_solid_torus (s2 k) /\ compact (s2 k) /\ closed (s2 k) /\
                  s2 k SUBSET closure (interior (s2 k)) /\
                  frontier (s2 k) SUBSET s2 k /\ interior (s2 k) SUBSET s2 k /\
                  (!x. x IN s2 k ==> x IN interior (s2 k) \/ x IN frontier (s2 k)) /\
                  (!x. x IN frontier (s2 k) ==> ~(x IN interior (s2 k)))) /\
         DISJOINT (s2 (&2 * i)) (s2 (&2 * i + &2)) /\
         (!y. y IN frontier (s2 (&2 * i)) INTER frontier (s2 (&2 * i + &1))
              ==> pl_crossing_at (frontier (s2 (&2 * i))) (frontier (s2 (&2 * i + &1))) y) /\
         (!y. y IN frontier (s2 (&2 * i + &1)) INTER frontier (s2 (&2 * i + &2))
              ==> pl_crossing_at (frontier (s2 (&2 * i + &1)))
                                 (frontier (s2 (&2 * i + &2))) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP MOI_S3GF_TOWER_TORI (ASSUME `moi_s32_tower g v pp dd s2`)) THEN
    DISCH_THEN(MP_TAC o SPEC `k:int`) THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP MOI_S3I2_SOLID_TORUS_REGULAR
      (ASSUME `pl_solid_torus ((s2:int->real^3->bool) k)`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; INTERIOR_SUBSET; SUBSET_REFL] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S3I2_FAR_TORI THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3I2_TOWER_CROSS THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 * i + &2 = (&2 * i + &1) + &1:int` SUBST1_TAC THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3I2_TOWER_CROSS THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1)) INTER
                 frontier (s2 (&2 * i + &2))` THEN
    REWRITE_TAC[INT_ARITH `(&2 * i + &1) + &1 = &2 * i + &2:int`]]);;

(* The odd torus of a level meets no other even torus and no other odd one. *)

let MOI_S3I2_LEVEL_FAR = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> (!k. ~(k = i) /\ ~(k = i + &1) ==> DISJOINT (s2 (&2 * i + &1)) (s2 (&2 * k))) /\
         (!j. ~(j = i) ==> DISJOINT (s2 (&2 * i + &1)) (s2 (&2 * j + &1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S3I2_FAR_TORI THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                        `dd:int->real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Part 9: Lemma 2 for L_i.  At its points on T''_(2i) or T''_(2i+2)        *)
(* L_i is a half plane (crossing chart, CROSS_HALF, the other even solid     *)
(* torus kept away); elsewhere it is open in the PL torus T''_(2i+1), so     *)
(* locally R^2 (MOI_S8TO_PL_TORUS_R2).                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_L_LOCAL = prove
 (`!(g:real^3->real^3) v pp dd s2 i y.
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ y IN moi_s3i2_lsurf s2 i
     ==> (y IN frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))
          ==> moi_s28_locally_half (moi_s3i2_lsurf s2 i) y) /\
         (~(y IN frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)))
          ==> moi_s28_locally_r2 (moi_s3i2_lsurf s2 i) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tb") STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `i:int` (MATCH_MP MOI_S3I2_LEVEL_FACTS
    (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kf") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")))) THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &1:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &2:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN moi_s3i2_lsurf s2 i` THEN
  REWRITE_TAC[moi_s3i2_lsurf; IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i + &1))`;
                     `frontier ((s2:int->real^3->bool) (&2 * i))`; `y:real^3`]
                    MOI_S3I2_CROSS_CHART) THEN
      ANTS_TAC THENL
       [DISJ2_TAC THEN USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
        (X_CHOOSE_THEN `h:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`(s2:int->real^3->bool) (&2 * i)`;
                     `frontier ((s2:int->real^3->bool) (&2 * i + &1))`; `y:real^3`;
                     `u:real^3->bool`; `f:real^3->real^3`; `h:real^3->real^3`]
                    MOI_S3I2_CROSS_HALF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC
       [`frontier ((s2:int->real^3->bool) (&2 * i + &1)) DIFF interior (s2 (&2 * i))`;
        `(frontier ((s2:int->real^3->bool) (&2 * i + &1)) DIFF interior (s2 (&2 * i))) INTER
         ((:real^3) DIFF s2 (&2 * i + &2))`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `DISJOINT ((s2:int->real^3->bool) (&2 * i)) (s2 (&2 * i + &2))` THEN
        UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
        UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i))` THEN
        UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN
        UNDISCH_TAC `~((y:real^3) IN interior ((s2:int->real^3->bool) (&2 * i)))` THEN
        SET_TAC[];
        UNDISCH_TAC `interior ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
        SET_TAC[];
        SET_TAC[]];
      MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i + &1))`;
                     `frontier ((s2:int->real^3->bool) (&2 * i + &2))`; `y:real^3`]
                    MOI_S3I2_CROSS_CHART) THEN
      ANTS_TAC THENL
       [DISJ1_TAC THEN USE_THEN "c2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
        (X_CHOOSE_THEN `h:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`(s2:int->real^3->bool) (&2 * i + &2)`;
                     `frontier ((s2:int->real^3->bool) (&2 * i + &1))`; `y:real^3`;
                     `u:real^3->bool`; `f:real^3->real^3`; `h:real^3->real^3`]
                    MOI_S3I2_CROSS_HALF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC
       [`frontier ((s2:int->real^3->bool) (&2 * i + &1)) DIFF interior (s2 (&2 * i + &2))`;
        `(frontier ((s2:int->real^3->bool) (&2 * i + &1)) DIFF interior (s2 (&2 * i + &2))) INTER
         ((:real^3) DIFF s2 (&2 * i))`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `DISJOINT ((s2:int->real^3->bool) (&2 * i)) (s2 (&2 * i + &2))` THEN
        UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
        UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &2))` THEN
        UNDISCH_TAC `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN
        UNDISCH_TAC `~((y:real^3) IN interior ((s2:int->real^3->bool) (&2 * i + &2)))` THEN
        SET_TAC[];
        UNDISCH_TAC `interior ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
        SET_TAC[];
        SET_TAC[]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN (s2:int->real^3->bool) (&2 * i)) /\
                  ~((y:real^3) IN (s2:int->real^3->bool) (&2 * i + &2))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "tb" (MP_TAC o C MATCH_MP
      (ASSUME `pl_solid_torus ((s2:int->real^3->bool) (&2 * i + &1))`)) THEN
    REWRITE_TAC[pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3` (X_CHOOSE_THEN
      `h:real^3->real^(2,2)finite_sum` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S8TO_PL_TORUS_R2) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`frontier ((s2:int->real^3->bool) (&2 * i + &1))`;
      `frontier ((s2:int->real^3->bool) (&2 * i + &1)) INTER
       ((:real^3) DIFF (s2 (&2 * i) UNION s2 (&2 * i + &2)))`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
      MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNION; IN_UNIV];
      UNDISCH_TAC `interior ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
      UNDISCH_TAC `interior ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
      SET_TAC[];
      SET_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* Part 10: L_i is triangulated (T''_(2i+1) is a PL torus, the curves       *)
(* where it crosses T''_(2i) and T''_(2i+2) are polyhedra, and the open part *)
(* inside the even solid tori is removed, MOI_S8CU_REMOVE_OPEN); by          *)
(* SURFACE_TRIANG it is a combinatorial surface whose boundary is its trace *)
(* on K; the L_i make up L.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_L_TRIANG = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?e. simplicial_complex e /\ UNIONS e = moi_s3i2_lsurf s2 i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tb") STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `i:int` (MATCH_MP MOI_S3I2_LEVEL_FACTS
    (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kf") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")))) THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &1:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &2:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "tb" (MP_TAC o C MATCH_MP
      (ASSUME `pl_solid_torus ((s2:int->real^3->bool) (&2 * i + &1))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3` (X_CHOOSE_TAC
      `h:real^3->real^(2,2)finite_sum`)) THEN
  MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i + &1))`;
                 `f:real^(2,2)finite_sum->real^3`; `h:real^3->real^(2,2)finite_sum`]
                MOI_S8TO_TRIANG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_FRONTIER_EMPTY THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `pl_polyhedron (frontier ((s2:int->real^3->bool) (&2 * i + &1))) /\
    pl_polyhedron ((s2:int->real^3->bool) (&2 * i)) /\
    pl_polyhedron ((s2:int->real^3->bool) (&2 * i + &2)) /\
    pl_polyhedron (frontier ((s2:int->real^3->bool) (&2 * i)) INTER frontier (s2 (&2 * i + &1))) /\
    pl_polyhedron (frontier ((s2:int->real^3->bool) (&2 * i + &1)) INTER frontier (s2 (&2 * i + &2)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
      EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3I2_SOLID_TORUS_POLY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3I2_SOLID_TORUS_POLY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4L_CROSSING_POLYHEDRON THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_INTER THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_FRONTIER THEN
        ASM_REWRITE_TAC[];
        USE_THEN "c1" MATCH_ACCEPT_TAC];
      MATCH_MP_TAC MOI_S4L_CROSSING_POLYHEDRON THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_INTER THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_FRONTIER THEN
        ASM_REWRITE_TAC[];
        USE_THEN "c2" MATCH_ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(frontier ((s2:int->real^3->bool) (&2 * i + &1)) INTER (s2 (&2 * i) UNION s2 (&2 * i + &2)))
    DIFF ((frontier (s2 (&2 * i)) INTER frontier (s2 (&2 * i + &1))) UNION
          (frontier (s2 (&2 * i + &1)) INTER frontier (s2 (&2 * i + &2)))) =
    frontier (s2 (&2 * i + &1)) INTER (interior (s2 (&2 * i)) UNION interior (s2 (&2 * i + &2)))`
  (LABEL_TAC "sl") THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`!x. x IN (s2:int->real^3->bool) (&2 * i) ==> x IN interior (s2 (&2 * i)) \/
                                                    x IN frontier (s2 (&2 * i))`;
      `!x. x IN (s2:int->real^3->bool) (&2 * i + &2) ==> x IN interior (s2 (&2 * i + &2)) \/
                                                         x IN frontier (s2 (&2 * i + &2))`;
      `!x. x IN frontier ((s2:int->real^3->bool) (&2 * i)) ==> ~(x IN interior (s2 (&2 * i)))`;
      `!x. x IN frontier ((s2:int->real^3->bool) (&2 * i + &2))
           ==> ~(x IN interior (s2 (&2 * i + &2)))`;
      `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)`;
      `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)`;
      `interior ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)`;
      `interior ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)`;
      `DISJOINT ((s2:int->real^3->bool) (&2 * i)) (s2 (&2 * i + &2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`;
                 `frontier ((s2:int->real^3->bool) (&2 * i + &1)) INTER
                  (s2 (&2 * i) UNION s2 (&2 * i + &2))`;
                 `(frontier ((s2:int->real^3->bool) (&2 * i)) INTER frontier (s2 (&2 * i + &1))) UNION
                  (frontier (s2 (&2 * i + &1)) INTER frontier (s2 (&2 * i + &2)))`]
                MOI_S8CU_REMOVE_OPEN) THEN
  USE_THEN "sl" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_SIMP_TAC[PL_POLYHEDRON_UNION];
      MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[INTER_SUBSET];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      SIMP_TAC[OPEN_UNION; OPEN_INTERIOR]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[moi_s3i2_lsurf] THEN SET_TAC[]);;

(* On the odd torus of a level, K is the union of its two even tori. *)

let MOI_S3I2_ODD_EVENS = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> !x. x IN frontier (s2 (&2 * i + &1))
             ==> (x IN moi_s32_evens s2 <=>
                  x IN frontier (s2 (&2 * i)) \/ x IN frontier (s2 (&2 * i + &2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:int` o MATCH_MP MOI_S3I2_LEVEL_FAR) THEN
  DISCH_THEN(LABEL_TAC "far" o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3I2_TORI_FACTS) THEN
  DISCH_THEN(LABEL_TAC "tf") THEN
  REWRITE_TAC[moi_s32_evens; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `k:int`) THEN
    ASM_CASES_TAC `k:int = i` THENL
     [DISJ1_TAC THEN UNDISCH_TAC `(x:real^3) IN frontier ((s2:int->real^3->bool) (&2 * k))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `k:int = i + &1` THENL
     [DISJ2_TAC THEN UNDISCH_TAC `(x:real^3) IN frontier ((s2:int->real^3->bool) (&2 * k))` THEN
      ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1) = &2 * i + &2:int`];
      ALL_TAC] THEN
    USE_THEN "far" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(k:int = i)`) (ASSUME `~(k:int = i + &1)`))) THEN
    USE_THEN "tf" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `&2 * k:int`) THEN
    USE_THEN "tf" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `&2 * i + &1:int`) THEN
    UNDISCH_TAC `(x:real^3) IN frontier ((s2:int->real^3->bool) (&2 * k))` THEN
    UNDISCH_TAC `(x:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN
    SET_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `i + &1:int` THEN
      ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1) = &2 * i + &2:int`]]]);;

(* SURFACE_TRIANG on L_i. *)

let MOI_S3I2_L_SURFACE = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     (!c:(real^3->bool)->bool.
        lf_simplicial_complex c /\
        (!y. y IN UNIONS c
             ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
        ==> combinatorial_manifold_with_boundary 2 c /\
            surface_boundary c = {y | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y} /\
            (surface_boundary c = {} ==> combinatorial_manifold 2 c)) /\
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?e. simplicial_complex e /\ UNIONS e = moi_s3i2_lsurf s2 i /\
             combinatorial_manifold_with_boundary 2 e /\
             surface_boundary e = moi_s3i2_lsurf s2 i INTER moi_s32_evens s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 (LABEL_TAC "tb")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                MOI_S3I2_L_TRIANG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "st" (MP_TAC o SPEC `e:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (e:(real^3->bool)->bool)` THEN
      SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `y:real^3`]
                    MOI_S3I2_L_LOCAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
  ASM_CASES_TAC `(y:real^3) IN moi_s3i2_lsurf s2 i` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `y:real^3`]
                MOI_S3I2_L_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                MOI_S3I2_ODD_EVENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  SUBGOAL_THEN `(y:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s3i2_lsurf s2 i` THEN
    REWRITE_TAC[moi_s3i2_lsurf; IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN
  MESON_TAC[MOI_S8TA_HALF_NOT_R2]);;

(* The L_i make up L. *)

let MOI_S3I2_L_UNIONS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> UNIONS {moi_s3i2_lsurf s2 i | i IN (:int)} =
         UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
         UNIONS {interior (s2 (&2 * i)) | i IN (:int)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_DIFF; moi_s3i2_lsurf;
              IN_UNION; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `k:int` THEN
    ASM_CASES_TAC `k:int = i` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `k:int = i + &1` THENL
     [ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1) = &2 * i + &2:int`]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:int` o MATCH_MP MOI_S3I2_LEVEL_FAR) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (CONJ (ASSUME `~(k:int = i)`) (ASSUME `~(k:int = i + &1)`))
               o CONJUNCT1) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3I2_TORI_FACTS) THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `&2 * i + &1:int` th))))) THEN
    MP_TAC(ISPEC `(s2:int->real^3->bool) (&2 * k)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^3) IN frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN
    SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:int`) ASSUME_TAC) THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i + &1:int`) THEN
    REWRITE_TAC[INT_ARITH `&2 * (i + &1) = &2 * i + &2:int`]]);;


(* ------------------------------------------------------------------------- *)
(* Part 11: the family of the components of the L_i (p.225) and              *)
(* INITIAL.  Each component is a compact connected combinatorial surface in  *)
(* its level region with boundary its trace on K (COMPONENT_COMPLEX on the   *)
(* complex of L_i); components of different L_i are disjoint (far odd       *)
(* tori); a level region meets only the L_j with j = i - 1, i, i + 1; the    *)
(* union of the family is L; closedness and separation are Lemma 1 and 3.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3I2_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 i c.
     (!c:(real^3->bool)->bool.
        lf_simplicial_complex c /\
        (!y. y IN UNIONS c
             ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
        ==> combinatorial_manifold_with_boundary 2 c /\
            surface_boundary c = {y | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y} /\
            (surface_boundary c = {} ==> combinatorial_manifold 2 c)) /\
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     c IN components (moi_s3i2_lsurf s2 i)
     ==> ?cc. c SUBSET moi_s32_lvl g dd i /\
              FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
              UNIONS cc = c /\ connected c /\ ~(c = {}) /\
              surface_boundary cc = c INTER moi_s32_evens s2 /\
              c INTER moi_s32_evens s2 SUBSET
                frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 (LABEL_TAC "tb")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                MOI_S3I2_L_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_CONNECTED) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET moi_s32_lvl g dd i` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `&2 * i + &1:int`
      (MATCH_MP MOI_S3GF_TOWER_TORI (ASSUME `moi_s32_tower g v pp dd s2`))))))) THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s3i2_lsurf s2 i` THEN
    REWRITE_TAC[moi_s32_lvl; moi_s3i2_lsurf] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET
                frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                  MOI_S3I2_ODD_EVENS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s3i2_lsurf s2 i` THEN
    REWRITE_TAC[moi_s3i2_lsurf; SUBSET; IN_INTER; IN_UNION; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s3i2_lsurf s2 i INTER moi_s32_evens s2) INTER c =
                (c:real^3->bool) INTER moi_s32_evens s2` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s3i2_lsurf s2 i` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` COMPONENT_COMPLEX) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (e:(real^3->bool)->bool)` THEN
      SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{s | s IN e /\ s SUBSET (c:real^3->bool)}` THEN ASM_REWRITE_TAC[]);;

let MOI_S3I2_FAM_DISJOINT = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> pairwise DISJOINT {c | ?i. c IN components (moi_s3i2_lsurf s2 i)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^3->bool`; `c':real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:int`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:int`) ASSUME_TAC)) THEN
  ASM_CASES_TAC `j:int = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `moi_s3i2_lsurf s2 i` PAIRWISE_DISJOINT_COMPONENTS) THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:int` o MATCH_MP MOI_S3I2_LEVEL_FAR) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `~(j:int = i)`) o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3I2_TORI_FACTS) THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `&2 * i + &1:int` th)))) THEN
                       MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `&2 * j + &1:int` th))))) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 j`; `c':real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s3i2_lsurf] THEN SET_TAC[]);;

let MOI_S3I2_FAM_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> FINITE {c | (?j. c IN components (moi_s3i2_lsurf s2 j)) /\
                     c SUBSET moi_s32_lvl g dd i}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tb") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!j. FINITE (components (moi_s3i2_lsurf (s2:int->real^3->bool) j))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:int` THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `j:int`]
                  MOI_S3I2_L_TRIANG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S8CU_FINITE_COMPONENTS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `components (moi_s3i2_lsurf s2 (i - &1)) UNION
              components (moi_s3i2_lsurf s2 i) UNION
              components (moi_s3i2_lsurf (s2:int->real^3->bool) (i + &1))` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `c:real^3->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:int`) ASSUME_TAC) THEN
  ASM_CASES_TAC `j:int = i - &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j:int = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j:int = i + &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (moi_s32_lvl g dd i)
                         (IMAGE (g:real^3->real^3)
                                (revolution ((dd:int->real^3->bool) (&2 * j + &1))))`
  MP_TAC THENL
   [REWRITE_TAC[moi_s32_lvl; DISJOINT_UNION] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3IT_FAR_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `&2 * j + &1:int`
    (MATCH_MP MOI_S3GF_TOWER_TORI (ASSUME `moi_s32_tower g v pp dd s2`))))))) THEN
  SUBGOAL_THEN `moi_s3i2_lsurf s2 j SUBSET frontier ((s2:int->real^3->bool) (&2 * j + &1))`
  MP_TAC THENL [REWRITE_TAC[moi_s3i2_lsurf; SUBSET_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 j`; `c:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 j`; `c:real^3->bool`] IN_COMPONENTS_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd i` THEN SET_TAC[]);;

let MOI_S3I2_FAM_UNIONS = prove
 (`!s2:int->real^3->bool.
     UNIONS {c | ?i. c IN components (moi_s3i2_lsurf s2 i)} =
     UNIONS {moi_s3i2_lsurf s2 i | i IN (:int)}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:int`) ASSUME_TAC)) THEN
    EXISTS_TAC `i:int` THEN
    MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN c` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN
    MP_TAC(ISPEC `moi_s3i2_lsurf s2 i` UNIONS_COMPONENTS) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` (REWRITE_RULE[EXTENSION] th))) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]]);;

(* Moise p.225, Lemmas 1-3: the initial barrier and its family. *)

let INITIAL = prove
 (MOI_S32_INITIAL,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (LABEL_TAC "tb" o CONJUNCT2)) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `{c:real^3->bool | ?i. c IN components (moi_s3i2_lsurf s2 i)}` THEN
  SUBGOAL_THEN
   `moi_s32_set g s2 {c:real^3->bool | ?i. c IN components (moi_s3i2_lsurf s2 i)} =
    moi_s32_evens s2 UNION
    (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
     UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_set; MOI_S3I2_FAM_UNIONS] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_L_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s32_state; NOT_IN_EMPTY; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3I2_FAM_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:real^3->bool` THEN DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN
    EXISTS_TAC `i:int` THEN MATCH_MP_TAC MOI_S3I2_MEMBER THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:int` THEN MATCH_MP_TAC MOI_S3I2_FAM_FINITE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3I2_M1_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3I2_M1_SEP THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

