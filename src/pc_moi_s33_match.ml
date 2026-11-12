(* ========================================================================= *)
(* pc_moi_s33_match: Moise 33.1 Lemma 13 (GTM 47, pp.236-237, Figs          *)
(* 33.2-33.3).  Main theorem MATCH : |- MOI_S33_MATCH                       *)
(* (pc_moi_s33_stmt.ml): a PLH Bd N -> Bd X carrying every piece A_v onto   *)
(* A_v' and every rim onto its trace.  Route: the book's induction over a   *)
(* connected vertex order with HOLED_EXT, the Moebius-band step replaced by *)
(* side orientations of piece maps.  O1 circle orientation and O2 collar    *)
(* adjustment are in pc_moi_s33_circ; this file has O5 multi-circle         *)
(* extension and I induction; O3/O4 (side orientation, pc_moi_s33_sorient)  *)
(* enter as antecedents MOI_S3MT_SORIENT_..._TERM, and so do the surface    *)
(* data of Bd N and Bd X (pc_moi_s33_msides, terms MOI_S3MT_SIDES_TERM,     *)
(* VDATA_STMT, PCS_STMT): MOI_S3MT_MATCH_COND : |- those six terms ==>      *)
(* MOI_S33_MATCH, and MATCH discharges them by the theorems of the two      *)
(* files.                                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_s33_circ.ml";;
needs "src/pc_moi_s33_hext.ml";;
needs "src/pc_moi_s33_sorstmt.ml";;
needs "src/pc_moi_fnd_tubeh.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_s33_sorient.ml";;
needs "src/pc_moi_s33_msides.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Collars of the frontier circles of holed_disk_model k (circles           *)
(* moi_s3hx_circ k j of pc_moi_s33_hext: j = 0 the outer square, j >= 1 the *)
(* hole j - 1).  The outer collar is moi_fsb_hq k minus the interior of     *)
(* moi_fsb_hr k; the collar of hole i is the square moi_s3mt_hq2 i minus the *)
(* open hole.  They are PL annuli, pairwise disjoint, inside the model.     *)
(* ------------------------------------------------------------------------- *)

let moi_s3mt_hq2 = new_definition
 `moi_s3mt_hq2 i = interval[vector[&4 * &i + &7 / &4; &3 / &4]:real^2,
                            vector[&4 * &i + &17 / &4; &13 / &4]]`;;

let moi_s3mt_coll = new_definition
 `moi_s3mt_coll k j =
    if j = 0 then moi_fsb_hq k DIFF interior (moi_fsb_hr k)
    else moi_s3mt_hq2 (j - 1) DIFF interior (moi_fsb_hc (j - 1))`;;

let moi_s3mt_cend = new_definition
 `moi_s3mt_cend k j =
    if j = 0 then relative_frontier (moi_fsb_hr k)
    else relative_frontier (moi_s3mt_hq2 (j - 1))`;;

let MOI_S3MT_HQ2_FACTS = prove
 (`!k i. polytope (moi_s3mt_hq2 i) /\ ~(interior (moi_s3mt_hq2 i) = {}) /\
         moi_fsb_hc i SUBSET interior (moi_s3mt_hq2 i) /\
         (i < k ==> moi_s3mt_hq2 i SUBSET interior (moi_fsb_hr k)) /\
         (!j. ~(i = j) ==> DISJOINT (moi_s3mt_hq2 i) (moi_s3mt_hq2 j)) /\
         (!j. ~(i = j) ==> DISJOINT (moi_s3mt_hq2 i) (moi_fsb_hc j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s3mt_hq2; moi_fsb_hr; moi_fsb_hc; POLYTOPE_INTERVAL;
              INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; SUBSET_INTERVAL;
              DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  SUBGOAL_THEN `&0 <= &i` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST
   [ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `&i + &1 <= &k` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; DISJOINT_INTERVAL; DIMINDEX_2] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[VECTOR_2; ARITH] THEN
    SUBGOAL_THEN `(i:num) + 1 <= j \/ j + 1 <= i` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* Two nested rectangles bound a PL annulus. *)
let MOI_S3MT_RECT_ANN = prove
 (`!P Q:real^2->bool.
     polytope P /\ ~(interior P = {}) /\ polytope Q /\ ~(interior Q = {}) /\
     P SUBSET interior Q
     ==> pl_annulus_with_ends (Q DIFF interior P) (relative_frontier P)
                              (relative_frontier Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_sphere 1 (relative_frontier P:real^2->bool) /\
    pl_sphere 1 (relative_frontier Q:real^2->bool) /\
    inside(relative_frontier P) = interior P /\
    inside(relative_frontier Q) = interior Q /\
    relative_frontier Q UNION interior Q = Q /\ relative_frontier P SUBSET P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `P:real^2->bool` MOI_FSB_POLY2) THEN
    MP_TAC(ISPEC `Q:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier P:real^2->bool`; `relative_frontier Q:real^2->bool`]
    MOI_S5C_ANN2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[]);;

let MOI_S3MT_COLL_ANN = prove
 (`!k j. j <= k
         ==> pl_annulus_with_ends (moi_s3mt_coll k j) (moi_s3hx_circ k j) (moi_s3mt_cend k j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3mt_coll; moi_s3mt_cend; moi_s3hx_circ] THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MOI_S5C_ANN_SWAP THEN MATCH_MP_TAC MOI_S3MT_RECT_ANN THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `moi_fsb_hq k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3MT_HQ2_FACTS) THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3MT_RECT_ANN THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `moi_fsb_hc`)) (concl th) &&
      can (find_term ((=) `polytope:(real^2->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let MOI_S3MT_IN_MODEL = prove
 (`!k x:real^2. x IN holed_disk_model k <=>
                x IN moi_fsb_hq k /\ !i. i < k ==> ~(x IN interior (moi_fsb_hc i))`,
  REWRITE_TAC[MOI_FSB_HD_EQ; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3MT_COLL_FACTS = prove
 (`!k. (!j. j <= k ==> moi_s3mt_coll k j SUBSET holed_disk_model k /\
                       moi_s3hx_circ k j SUBSET moi_s3mt_coll k j /\
                       moi_s3mt_cend k j SUBSET moi_s3mt_coll k j /\
                       compact (moi_s3mt_coll k j)) /\
       (!j j'. j <= k /\ j' <= k /\ ~(j = j')
               ==> DISJOINT (moi_s3mt_coll k j) (moi_s3mt_coll k j')) /\
       vector[&3 / &2; &2] IN holed_disk_model k /\
       (!j. j <= k ==> ~(vector[&3 / &2; &2] IN moi_s3mt_coll k j))`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < k ==> moi_s3mt_hq2 i SUBSET interior (moi_fsb_hr k) /\
                  moi_fsb_hc i SUBSET interior (moi_s3mt_hq2 i) /\
                  polytope (moi_s3mt_hq2 i)`
  ASSUME_TAC THENL [MESON_TAC[MOI_S3MT_HQ2_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!P:real^2->bool. interior P SUBSET P` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P:real^2->bool. polytope P /\ ~(interior P = {})
                     ==> relative_frontier P = P DIFF interior P /\ compact P`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier] THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED];
      ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3mt_coll; moi_s3mt_cend; moi_s3hx_circ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `relative_frontier (moi_fsb_hq k) = moi_fsb_hq k DIFF interior (moi_fsb_hq k) /\
                    compact (moi_fsb_hq k) /\
                    relative_frontier (moi_fsb_hr k) = moi_fsb_hr k DIFF interior (moi_fsb_hr k)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; MOI_S3MT_IN_MODEL; IN_DIFF] THEN
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `moi_fsb_hr`)) (concl th) &&
          can (find_term ((=) `moi_fsb_hc`)) (concl th) &&
          not (can (find_term ((=) `moi_s3mt_hq2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `moi_fsb_hc i` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `moi_fsb_hq k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]];
      SUBGOAL_THEN `j - 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3MT_HQ2_FACTS) THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_fsb_hr`)) (concl th) &&
        can (find_term ((=) `moi_fsb_hc`)) (concl th) &&
        not (can (find_term ((=) `moi_s3mt_hq2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `relative_frontier (moi_fsb_hc (j - 1)) =
        moi_fsb_hc (j - 1) DIFF interior (moi_fsb_hc (j - 1)) /\
        relative_frontier (moi_s3mt_hq2 (j - 1)) =
        moi_s3mt_hq2 (j - 1) DIFF interior (moi_s3mt_hq2 (j - 1)) /\
        compact (moi_s3mt_hq2 (j - 1))`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; MOI_S3MT_IN_MODEL; IN_DIFF] THEN
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN
          MP_TAC(ISPEC `moi_fsb_hq k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN
          ASM_CASES_TAC `i = j - 1` THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th) &&
            can (find_term ((=) `moi_fsb_hc`)) (concl th) &&
            can (find_term ((=) `moi_s3mt_hq2`)) (concl th))) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
          MP_TAC(ISPEC `moi_fsb_hc i` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
        MP_TAC(ISPEC `moi_fsb_hc (j - 1)` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MP_TAC(ISPEC `moi_fsb_hc (j - 1)` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `moi_s3mt_hq2 (j - 1)` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]]];
    MAP_EVERY X_GEN_TAC [`j:num`; `j':num`] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s3mt_coll] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_CASES_TAC `j' = 0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `j' - 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j' - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_s3mt_hq2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
      SUBGOAL_THEN `j - 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_s3mt_hq2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
      MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3MT_HQ2_FACTS) THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j' - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th) &&
        not (can (find_term ((=) `moi_fsb_hc`)) (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN SET_TAC[]];
    REWRITE_TAC[MOI_S3MT_IN_MODEL; moi_fsb_hq; moi_fsb_hc; IN_INTERVAL;
                INTERIOR_CLOSED_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3mt_coll] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IN_DIFF; moi_fsb_hq; moi_fsb_hr; moi_s3mt_hq2; moi_fsb_hc; IN_INTERVAL;
                INTERIOR_CLOSED_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    MP_TAC(SPEC `k:num` REAL_POS) THEN MP_TAC(SPEC `j - 1` REAL_POS) THEN
    REAL_ARITH_TAC]);;

let MOI_S3MT_COLL_EXT = prove
 (`!k j (c:real^2->real^2) c'.
     j <= k /\ pl_homeomorphism (moi_s3mt_coll k j,moi_s3mt_coll k j) (c,c') /\
     (!x. x IN moi_s3mt_cend k j ==> c x = x)
     ==> ?C C'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (C,C') /\
                (!x. x IN moi_s3mt_coll k j ==> C x = c x) /\
                (!x. x IN holed_disk_model k /\ ~(x IN moi_s3mt_coll k j) ==> C x = x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_S3MT_COLL_FACTS) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  ABBREV_TAC `K = moi_s3mt_coll k j` THEN ABBREV_TAC `E = moi_s3mt_cend k j` THEN
  (* a closed set Y on which the map is the identity, with K UNION Y containing the model *)
  SUBGOAL_THEN
   `?Y:real^2->bool. closed Y /\ locally_polyhedral Y /\ K INTER Y SUBSET E /\
                     holed_disk_model k SUBSET K UNION Y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "E"] THEN REWRITE_TAC[moi_s3mt_coll; moi_s3mt_cend] THEN
    COND_CASES_TAC THENL
     [EXISTS_TAC `moi_fsb_hr k` THEN
      MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED; LOCALLY_POLYHEDRAL_POLYTOPE] THEN
      SUBGOAL_THEN `~(interior (moi_fsb_hr k) = {}) /\ polytope (moi_fsb_hr k)`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `relative_frontier (moi_fsb_hr k) =
                    moi_fsb_hr k DIFF interior (moi_fsb_hr k)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier; CLOSURE_CLOSED;
                     POLYTOPE_IMP_CLOSED];
        ALL_TAC] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `holed_disk_model k SUBSET moi_fsb_hq k` MP_TAC THENL
       [REWRITE_TAC[SUBSET; MOI_S3MT_IN_MODEL] THEN SIMP_TAC[];
        MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN SET_TAC[]];
      EXISTS_TAC `(:real^2) DIFF interior (moi_s3mt_hq2 (j - 1))` THEN
      MP_TAC(SPECL [`k:num`; `j - 1`] MOI_S3MT_HQ2_FACTS) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR; MOI_SA2_LP_COMPLEMENT_INTERIOR;
                   POLYTOPE_IMP_POLYHEDRON] THEN
      SUBGOAL_THEN `relative_frontier (moi_s3mt_hq2 (j - 1)) =
                    moi_s3mt_hq2 (j - 1) DIFF interior (moi_s3mt_hq2 (j - 1))` SUBST1_TAC THENL
       [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier; CLOSURE_CLOSED;
                     POLYTOPE_IMP_CLOSED];
        ALL_TAC] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_TAC THEN ASM_CASES_TAC `(x:real^2) IN interior (moi_s3mt_hq2 (j - 1))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^2) IN holed_disk_model k` THEN
      REWRITE_TAC[MOI_S3MT_IN_MODEL] THEN
      DISCH_THEN(MP_TAC o SPEC `j - 1` o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `moi_s3mt_hq2 (j - 1)` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^2) IN interior (moi_s3mt_hq2 (j - 1))` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `Y:real^2->bool`; `K:real^2->bool`; `Y:real^2->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `\x:real^2. x`; `\x:real^2. x`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
      ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID];
      ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!f s. (!x. x IN s ==> f x = x) ==> IMAGE f s = (s:real^2->bool)`) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_IDEMPOT] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (K,K) (c:real^2->real^2,c')`)) THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. if x IN K then (c:real^2->real^2) x else x)
          (holed_disk_model k) = holed_disk_model k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(y:real^2) IN K` THENL
       [EXISTS_TAC `(c':real^2->real^2) y` THEN
        SUBGOAL_THEN `(c':real^2->real^2) y IN K` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. if x IN K then (c:real^2->real^2) x else x`;
    `\x:real^2. if x IN K then (c':real^2->real^2) x else x`] THEN
  SIMP_TAC[] THEN
  MP_TAC(ISPECL [`(K:real^2->bool) UNION Y`; `(K:real^2->bool) UNION Y`;
                 `\x:real^2. if x IN K then (c:real^2->real^2) x else x`;
                 `\x:real^2. if x IN K then (c':real^2->real^2) x else x`;
                 `holed_disk_model k`] MOI_CEL_PLH_RESTRICT) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The model reflection (x,y) |-> (x, 4 - y) maps holed_disk_model k and     *)
(* each of its frontier circles onto itself; labels of the circles of a     *)
(* piece; the reflection transported to a piece.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_INVOL_IMAGE = prove
 (`!(r:real^2->real^2) s.
     (!x. r (r x) = x) /\ (!x. x IN s ==> r x IN s) ==> IMAGE r s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let MOI_S3MT_REFL_BOX = prove
 (`!a b c:real.
     IMAGE (\x:real^2. vector[x$1; &4 - x$2])
           (interval[vector[a; c]:real^2,vector[b; &4 - c]]) =
     interval[vector[a; c]:real^2,vector[b; &4 - c]] /\
     IMAGE (\x:real^2. vector[x$1; &4 - x$2])
           (interval(vector[a; c]:real^2,vector[b; &4 - c])) =
     interval(vector[a; c]:real^2,vector[b; &4 - c])`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S3MT_INVOL_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3MT_REFL_FACTS = prove
 (`!k. pl_homeomorphism (holed_disk_model k,holed_disk_model k)
         ((\x:real^2. vector[x$1; &4 - x$2]),(\x:real^2. vector[x$1; &4 - x$2])) /\
       (!j. j <= k ==> IMAGE (\x:real^2. vector[x$1; &4 - x$2]) (moi_s3hx_circ k j) =
                       moi_s3hx_circ k j)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!x:real^2. vector[(vector[x$1; &4 - x$2]:real^2)$1; &4 - (vector[x$1; &4 - x$2]:real^2)$2] = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!B:real^2->bool. (!x. x IN B ==> (vector[x$1; &4 - x$2]:real^2) IN B)
                     ==> IMAGE (\x:real^2. vector[x$1; &4 - x$2]) B = B`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3MT_INVOL_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^2. vector[x$1; &4 - x$2]) (holed_disk_model k) =
                holed_disk_model k` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[MOI_S3MT_IN_MODEL; moi_fsb_hq; moi_fsb_hc; IN_INTERVAL;
                INTERIOR_CLOSED_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pl_map_on (holed_disk_model k) (\x:real^2. vector[x$1; &4 - x$2]:real^2)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\x:real^2. vector[x$1; &4 - x$2]:real^2) =
                    (\x. (\x:real^2. vector[x$1; --(x$2)]:real^2) x + vector[&0; &4])`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                    VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[MOI_FSB_HD_POLY] THEN
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
     [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s3hx_circ] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier; CLOSURE_CLOSED;
                   POLYTOPE_IMP_CLOSED];
      SUBGOAL_THEN `j - 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_fsb_hr`)) (concl th) &&
        can (find_term ((=) `moi_fsb_hc`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier; CLOSURE_CLOSED;
                   POLYTOPE_IMP_CLOSED]] THEN
    REWRITE_TAC[moi_fsb_hq; moi_fsb_hc; IN_DIFF; IN_INTERVAL; INTERIOR_CLOSED_INTERVAL;
                DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3MT_IMAGE_UNIONS_FAM = prove
 (`!(f:real^3->real^2) (jj:num->real^3->bool) k.
     IMAGE f (UNIONS {jj i | i <= k}) = UNIONS {IMAGE f (jj i) | i <= k}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    EXISTS_TAC `IMAGE (f:real^3->real^2) (jj (i:num))` THEN
    CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(jj:num->real^3->bool) i` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

(* The labelled circles of a piece are the images of the model circles. *)
let MOI_S3MT_PIECE_LABELS = prove
 (`!k (G:real^2->real^3) G' (A:real^3->bool) (jj:num->real^3->bool).
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     IMAGE G (frontier (holed_disk_model k)) = UNIONS {jj i | i <= k} /\
     (!i. i <= k ==> pl_sphere 1 (jj i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (jj i) (jj i'))
     ==> ?sigma. (!i. i <= k ==> sigma i <= k /\
                                 jj i = IMAGE G (moi_s3hx_circ k (sigma i))) /\
                 (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> ~(sigma i = sigma i'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term (fun u -> is_const u &&
      fst(dest_const u) = "pl_homeomorphism")) (concl th))) THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (holed_disk_model k) SUBSET holed_disk_model k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= k ==> (jj:num->real^3->bool) i SUBSET A` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(jj:num->real^3->bool) i SUBSET UNIONS {jj i | i <= k}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
      can (find_term ((=) `frontier (holed_disk_model k)`)) (lhs(concl th))
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN
    UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = \i. IMAGE (G':real^3->real^2) ((jj:num->real^3->bool) i)` THEN
  SUBGOAL_THEN
   `(!i. i <= k ==> pl_sphere 1 ((J:num->real^2->bool) i)) /\
    (!i i'. i <= k /\ i' <= k /\ ~(i = i') ==> DISJOINT (J i) (J i')) /\
    UNIONS {J i | i <= k} = frontier (holed_disk_model k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `pl_homeomorphism ((jj:num->real^3->bool) i,
                                      IMAGE (G':real^3->real^2) (jj i)) (G',G)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
        MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `holed_disk_model k`] THEN
        ASM_SIMP_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM];
          MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
          MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `(jj:num->real^3->bool) i` MOI_S8PL_SPHERE1_STD) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^2->real^3` (X_CHOOSE_THEN `q':real^3->real^2`
        ASSUME_TAC)) THEN
      REWRITE_TAC[pl_sphere] THEN
      MAP_EVERY EXISTS_TAC [`std_triangle`; `(G':real^3->real^2) o (q:real^2->real^3)`;
                            `(q':real^3->real^2) o (G:real^2->real^3)`] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `(jj:num->real^3->bool) i` THEN REWRITE_TAC[std_triangle] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `i':num`] o check (fun th ->
        can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(jj:num->real^3->bool) i SUBSET A /\ jj i' SUBSET A` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `!y. y IN A ==> (G:real^2->real^3) ((G':real^3->real^2) y) = y` THEN
      SET_TAC[];
      SUBGOAL_THEN `frontier (holed_disk_model k) =
                    IMAGE (G':real^3->real^2) (IMAGE (G:real^2->real^3)
                      (frontier (holed_disk_model k)))` SUBST1_TAC THENL
       [UNDISCH_TAC `frontier (holed_disk_model k) SUBSET holed_disk_model k` THEN
        UNDISCH_TAC `!x. x IN holed_disk_model k ==> (G':real^3->real^2) (G x) = x` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[MOI_S3MT_IMAGE_UNIONS_FAM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `J:num->real^2->bool`] MOI_S3HX_LABELS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_TAC `sigma:num->num`) THEN EXISTS_TAC `sigma:num->num` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_comb(lhs(concl th)) && rator(lhs(concl th)) = `J:num->real^2->bool`)) THEN
    EXPAND_TAC "J" THEN
    SUBGOAL_THEN `(jj:num->real^3->bool) i SUBSET A` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!y. y IN A ==> (G:real^2->real^3) ((G':real^3->real^2) y) = y` THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `i':num` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `i':num`] o check (fun th ->
      can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[DISJOINT; INTER_IDEMPOT] THEN
    MP_TAC(SPEC `k:num` MOI_S3HX_CIRC_FACTS) THEN
    DISCH_THEN(MP_TAC o SPEC `(sigma:num->num) i'` o CONJUNCT1) THEN
    ASM_SIMP_TAC[]]);;

(* The model reflection transported to a piece: a PL self-homeomorphism    *)
(* fixing each image of a model circle setwise.                             *)
let MOI_S3MT_PIECE_REFL = prove
 (`!k (G:real^2->real^3) G' (A:real^3->bool).
     pl_homeomorphism (holed_disk_model k,A) (G,G')
     ==> pl_homeomorphism (A,A)
           ((\x. G (vector[(G' x)$1; &4 - (G' x)$2])),
            (\x. G (vector[(G' x)$1; &4 - (G' x)$2]))) /\
         (!j. j <= k
              ==> IMAGE (\x. G (vector[(G' x)$1; &4 - (G' x)$2]))
                        (IMAGE G (moi_s3hx_circ k j)) =
                  IMAGE G (moi_s3hx_circ k j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `k:num` MOI_S3MT_REFL_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (G:real^2->real^3) (vector[((G':real^3->real^2) x)$1; &4 - (G' x)$2])) =
    G o (\x:real^2. vector[x$1; &4 - x$2]:real^2) o G'`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `pl_homeomorphism (A,A)
        ((G:real^2->real^3) o (\x:real^2. vector[x$1; &4 - x$2]:real^2) o (G':real^3->real^2),
         (G o (\x:real^2. vector[x$1; &4 - x$2]:real^2)) o G')`
    MP_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[o_ASSOC]];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
      check (fun th -> concl th = `pl_homeomorphism (holed_disk_model k,A)
                                     (G:real^2->real^3,G')`)) THEN
    SUBGOAL_THEN `moi_s3hx_circ k j SUBSET holed_disk_model k` ASSUME_TAC THENL
     [MP_TAC(SPEC `k:num` MOI_S3HX_CIRC_FACTS) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      MP_TAC(SPEC `k:num` MOI_FSB_HD_POLY) THEN
      SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier (holed_disk_model k)` THEN
      ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (G':real^3->real^2) (IMAGE G (moi_s3hx_circ k j)) = moi_s3hx_circ k j`
    SUBST1_TAC THENL
     [UNDISCH_TAC `moi_s3hx_circ k j SUBSET holed_disk_model k` THEN
      UNDISCH_TAC `!x. x IN holed_disk_model k ==> (G':real^3->real^2) (G x) = x` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Composing collar adjustments of finitely many model circles (disjoint     *)
(* collars) into one PL self-homeomorphism of the model.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_ADJ_COMPOSE = prove
 (`!k (sigma:num->num) (phi:num->real^2->real^2) (W:num->bool).
     (!i. i IN W ==> sigma i <= k) /\
     (!i i'. i IN W /\ i' IN W /\ ~(i = i') ==> ~(sigma i = sigma i')) /\
     (!i x. i IN W /\ x IN moi_s3hx_circ k (sigma i)
            ==> phi i x IN moi_s3hx_circ k (sigma i)) /\
     (!i. i IN W
          ==> ?C C'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (C,C') /\
                     (!x. x IN moi_s3hx_circ k (sigma i) ==> C x = phi i x) /\
                     (!x. x IN holed_disk_model k /\ ~(x IN moi_s3mt_coll k (sigma i))
                          ==> C x = x))
     ==> !S. FINITE S /\ S SUBSET W
             ==> ?D D'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (D,D') /\
                        (!i x. i IN S /\ x IN moi_s3hx_circ k (sigma i) ==> D x = phi i x) /\
                        (!x. x IN holed_disk_model k /\
                             (!i. i IN S ==> ~(x IN moi_s3mt_coll k (sigma i)))
                             ==> D x = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[NOT_IN_EMPTY; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; MOI_FSB_HD_POLY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i0:num`; `S:num->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^2->real^2` (X_CHOOSE_THEN `D':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term is_exists) (concl th)
    then MP_TAC(MP (SPEC `i0:num` th) (ASSUME `(i0:num) IN W`)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^2->real^2` (X_CHOOSE_THEN `C':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(C:real^2->real^2) o (D:real^2->real^2)`;
                        `(D':real^2->real^2) o (C':real^2->real^2)`] THEN
  MP_TAC(SPEC `k:num` MOI_S3MT_COLL_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN S
        ==> DISJOINT (moi_s3mt_coll k (sigma i)) (moi_s3mt_coll k (sigma (i0:num)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT; o_THM] THEN MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN
    DISCH_THEN DISJ_CASES_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN moi_s3mt_coll k (sigma (i0:num)) /\ x IN holed_disk_model k`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(D:real^2->real^2) x = x` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `D:real^2->real^2`)) (concl th) &&
          not (can (find_term ((=) `phi:num->real^2->real^2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:real^2) IN moi_s3mt_coll k (sigma (i0:num))` THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `(i0:num)`)) (concl th) &&
          can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th))) THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[];
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(D:real^2->real^2) x = phi (i:num) x` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(phi:num->real^2->real^2) i x IN moi_s3hx_circ k (sigma (i:num))`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `phi:num->real^2->real^2`)) (concl th)))) THEN
      SUBGOAL_THEN `(sigma:num->num) i <= k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(i0:num)`)) (concl th) &&
        can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; DISJOINT; IN_INTER; NOT_IN_EMPTY]];
    REWRITE_TAC[IN_INSERT; o_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(D:real^2->real^2) x = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `phi:num->real^2->real^2`)) (concl th)))) THEN
      ASM_MESON_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `phi:num->real^2->real^2`)) (concl th)))) THEN
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* O5: multi-circle extension.  A predicate P on PL maps of a piece A onto   *)
(* A' with (P1) h or h o (transported reflection) satisfies P, (P2) P        *)
(* spreads from a nonempty open part, (P3) for a pre-mapped circle J_i with *)
(* map psi_i every P-map h with h J_i = J'_i has psi_i' o h orientation-    *)
(* preserving.  Then some PLH h of A onto A' has P h, maps every J_i onto  *)
(* J'_i and equals psi_i on the pre-mapped circles.  HOLED_EXT gives a map *)
(* matching the circles; P1 adjusts it; collar adjustments (s33_circ, in    *)
(* the model, disjoint collars) fix the pre-mapped circles; P2 keeps P.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_O5_BODY =
 `!k (G:real^2->real^3) G' (A:real^3->bool) (A':real^3->bool) (G2:real^2->real^3) G2'
   (jj:num->real^3->bool) (jj':num->real^3->bool) (S:num->bool)
   (psi:num->real^3->real^3) (psi':num->real^3->real^3) (P:(real^3->real^3)->bool).
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     pl_homeomorphism (holed_disk_model k,A') (G2,G2') /\
     IMAGE G (frontier (holed_disk_model k)) = UNIONS {jj i | i <= k} /\
     IMAGE G2 (frontier (holed_disk_model k)) = UNIONS {jj' i | i <= k} /\
     (!i. i <= k ==> pl_sphere 1 (jj i) /\ pl_sphere 1 (jj' i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i')
             ==> DISJOINT (jj i) (jj i') /\ DISJOINT (jj' i) (jj' i')) /\
     (!i. i IN S ==> i <= k /\ pl_homeomorphism (jj i,jj' i) (psi i,psi' i)) /\
     (!h h'. pl_homeomorphism (A,A') (h,h')
             ==> P h \/ P (\x. h (G (vector[(G' x)$1; &4 - (G' x)$2])))) /\
     (!f f' g g' U. pl_homeomorphism (A,A') (f,f') /\ pl_homeomorphism (A,A') (g,g') /\
                    P g /\ open U /\ ~(U INTER A = {}) /\
                    (!x. x IN U INTER A ==> f x = g x)
                    ==> P f) /\
     (!i h h'. i IN S /\ pl_homeomorphism (A,A') (h,h') /\ P h /\ IMAGE h (jj i) = jj' i
               ==> ?j j'. pl_homeomorphism (relative_frontier std_triangle,jj i) (j,j') /\
                          moi_s3ci_cycpres (j' o psi' i o h o j))
     ==> ?h h'. pl_homeomorphism (A,A') (h,h') /\ P h /\
                (!i. i <= k ==> IMAGE h (jj i) = jj' i) /\
                (!i x. i IN S /\ x IN jj i ==> h x = psi i x)`;;

(* A pre-mapped circle pulled back through the chart and the first map. *)
let MOI_S3MT_CIRC_PULL = prove
 (`!k j (G:real^2->real^3) G' (A:real^3->bool) A' (H1:real^3->real^3) H1'
    (J:real^3->bool) J' (p:real^3->real^3) p' x.
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     pl_homeomorphism (A,A') (H1,H1') /\
     pl_homeomorphism (J,J') (p,p') /\
     IMAGE H1 J = J' /\ j <= k /\ J = IMAGE G (moi_s3hx_circ k j) /\
     x IN moi_s3hx_circ k j
     ==> G' (H1' (p (G x))) IN moi_s3hx_circ k j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3hx_circ k j SUBSET holed_disk_model k` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` MOI_S3MT_COLL_FACTS) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `j:num <= k`) o CONJUNCT1) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^3) x IN J` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `J:real^3->bool`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->real^3) ((G:real^2->real^3) x) IN J'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^3->real^3) J = J'` THEN
    UNDISCH_TAC `(G:real^2->real^3) x IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z. z IN J /\ (p:real^3->real^3) ((G:real^2->real^3) x) = (H1:real^3->real^3) z`
  (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `IMAGE (H1:real^3->real^3) J = J'` THEN
    UNDISCH_TAC `(p:real^3->real^3) ((G:real^2->real^3) x) IN J'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN moi_s3hx_circ k j /\ (z:real^3) = (G:real^2->real^3) w`
  (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `J = IMAGE (G:real^2->real^3) (moi_s3hx_circ k j)` THEN
    UNDISCH_TAC `(z:real^3) IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) IN holed_disk_model k` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN moi_s3hx_circ k j` THEN
    UNDISCH_TAC `moi_s3hx_circ k j SUBSET holed_disk_model k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^3) w IN A` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN
    UNDISCH_TAC `(w:real^2) IN holed_disk_model k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G':real^3->real^2) ((H1':real^3->real^3) ((p:real^3->real^3)
                  ((G:real^2->real^3) x))) = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let MOI_S3MT_O5 = prove
 (mk_imp(inst [`:3`,`:N`; `:3`,`:M`] MOI_S33_HOLED_EXT, MOI_S3MT_O5_BODY),
  DISCH_THEN(LABEL_TAC "hext") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `G:real^2->real^3`; `G':real^3->real^2`; `A:real^3->bool`;
                 `jj:num->real^3->bool`] MOI_S3MT_PIECE_LABELS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `G:real^2->real^3`; `G':real^3->real^2`; `A:real^3->bool`]
    MOI_S3MT_PIECE_REFL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?H1 H1'. pl_homeomorphism (A,A') (H1,H1') /\ (P:(real^3->real^3)->bool) H1 /\
             (!i. i <= k ==> IMAGE H1 ((jj:num->real^3->bool) i) = jj' i)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(jj:num->real^3->bool) 0`; `(jj':num->real^3->bool) 0`]
      MOI_S8PL_SPHERE1_PLH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `phi0:real^3->real^3` (X_CHOOSE_TAC `phi0':real^3->real^3`)) THEN
    USE_THEN "hext" (MP_TAC o SPECL
     [`k:num`; `A:real^3->bool`; `A':real^3->bool`; `G:real^2->real^3`;
      `G':real^3->real^2`; `G2:real^2->real^3`; `G2':real^3->real^2`;
      `jj:num->real^3->bool`; `jj':num->real^3->bool`; `0`;
      `phi0:real^3->real^3`; `phi0':real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `H0:real^3->real^3` (X_CHOOSE_THEN `H0':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`H0:real^3->real^3`; `H0':real^3->real^3`] o
      check (fun th -> is_forall(concl th) && can (find_term is_disj) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. (H0:real^3->real^3) ((G:real^2->real^3)
              (vector[((G':real^3->real^2) x)$1; &4 - (G' x)$2]))) =
      H0 o (\x. G (vector[(G' x)$1; &4 - (G' x)$2]))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`H0:real^3->real^3`; `H0':real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC
       [`(H0:real^3->real^3) o (\x. (G:real^2->real^3)
           (vector[((G':real^3->real^2) x)$1; &4 - (G' x)$2]))`;
        `(\x. (G:real^2->real^3) (vector[((G':real^3->real^2) x)$1; &4 - (G' x)$2])) o
         (H0':real^3->real^3)`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_o] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sigma:num->num`)) (concl th) &&
          can (find_term ((=) `G:real^2->real^3`)) (concl th) &&
          not (can (find_term is_neg) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?jf jf'. !i. i IN S
                 ==> pl_homeomorphism (relative_frontier std_triangle,
                                       (jj:num->real^3->bool) i) (jf i,jf' i) /\
                     moi_s3ci_cycpres
                       ((jf':num->real^3->real^2) i o (psi':num->real^3->real^3) i o
                        (H1:real^3->real^3) o (jf:num->real^2->real^3) i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) IN S` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `moi_s3ci_cycpres`)) (concl th))) THEN
    EXISTS_TAC `H1':real^3->real^3` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN S
        ==> ?C C'. pl_homeomorphism (holed_disk_model k,holed_disk_model k) (C,C') /\
                   (!x. x IN moi_s3hx_circ k ((sigma:num->num) i)
                        ==> C x = (G':real^3->real^2) ((H1':real^3->real^3)
                                    ((psi:num->real^3->real^3) i ((G:real^2->real^3) x)))) /\
                   (!x. x IN holed_disk_model k /\ ~(x IN moi_s3mt_coll k (sigma i))
                        ==> C x = x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `psi':num->real^3->real^3`)) (concl th) &&
      not (can (find_term ((=) `moi_s3ci_cycpres`)) (concl th)) &&
      not (can (find_term ((=) `H1:real^3->real^3`)) (concl th)))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `moi_s3ci_cycpres`)) (concl th) &&
      can (find_term ((=) `jf:num->real^2->real^3`)) (concl th))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sigma:num->num`)) (concl th) &&
      can (find_term ((=) `G:real^2->real^3`)) (concl th) &&
      not (can (find_term is_neg) (concl th)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
    ABBREV_TAC `j = (sigma:num->num) i` THEN
    ABBREV_TAC `Ci = moi_s3hx_circ k j` THEN
    MP_TAC(SPEC `k:num` MOI_S3MT_COLL_FACTS) THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pl_sphere 1 (Ci:real^2->bool) /\ locally_polyhedral (Ci:real^2->bool) /\
                  Ci SUBSET holed_disk_model k`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `k:num` MOI_S3HX_CIRC_FACTS) THEN
      DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s3mt_coll k j` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_homeomorphism (Ci:real^2->bool,(jj:num->real^3->bool) i)
                    (G:real^2->real^3,G')` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (G:real^2->real^3) Ci = (jj:num->real^3->bool) i`
        then SUBST1_TAC(SYM th) THEN ASSUME_TAC th else NO_TAC) THEN
      MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`holed_disk_model k`; `A:real^3->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
      check (fun th -> concl th = `pl_homeomorphism (A:real^3->bool,A') (H1:real^3->real^3,H1')`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
      check (fun th -> concl th = `pl_homeomorphism (holed_disk_model k,A:real^3->bool)
                                     (G:real^2->real^3,G')`)) THEN
    SUBGOAL_THEN `(jj:num->real^3->bool) i SUBSET A /\ jj' i SUBSET A' /\
                  IMAGE (H1':real^3->real^3) (jj' i) = jj i /\ pl_sphere 1 (jj' i)`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `H1:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `jj':num->real^3->bool`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "pl_sphere")) (concl th) &&
        can (find_term ((=) `jj':num->real^3->bool`)) (concl th) &&
        not (can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th)))) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `IMAGE (G:real^2->real^3) Ci = (jj:num->real^3->bool) i` THEN
        UNDISCH_TAC `(Ci:real^2->bool) SUBSET holed_disk_model k` THEN
        UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `(jj':num->real^3->bool) i`)) THEN
        UNDISCH_TAC `IMAGE (G:real^2->real^3) Ci = (jj:num->real^3->bool) i` THEN
        UNDISCH_TAC `(Ci:real^2->bool) SUBSET holed_disk_model k` THEN
        UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN
        UNDISCH_TAC `IMAGE (H1:real^3->real^3) A = A'` THEN SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `(jj':num->real^3->bool) i`)) THEN
        UNDISCH_TAC `IMAGE (G:real^2->real^3) Ci = (jj:num->real^3->bool) i` THEN
        UNDISCH_TAC `(Ci:real^2->bool) SUBSET holed_disk_model k` THEN
        UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN
        UNDISCH_TAC `!x. x IN A ==> (H1':real^3->real^3) (H1 x) = x` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_homeomorphism ((jj':num->real^3->bool) i,(jj:num->real^3->bool) i)
                    (H1':real^3->real^3,H1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if concl th =
          `IMAGE (H1':real^3->real^3) ((jj':num->real^3->bool) i) = jj i`
        then SUBST1_TAC(SYM th) THEN ASSUME_TAC th else NO_TAC) THEN
      MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`A':real^3->bool`; `A:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pl_homeomorphism (Ci,Ci)
        ((G':real^3->real^2) o (H1':real^3->real^3) o (psi:num->real^3->real^3) i o
         (G:real^2->real^3),
         (((G' o (psi':num->real^3->real^3) i) o H1) o G))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(jj:num->real^3->bool) i` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(jj':num->real^3->bool) i` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(jj:num->real^3->bool) i` THEN
        ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pl_homeomorphism (relative_frontier std_triangle,Ci)
        ((G':real^3->real^2) o (jf:num->real^2->real^3) i,
         (jf':num->real^3->real^2) i o (G:real^2->real^3))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(jj:num->real^3->bool) i` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(fun th -> if concl th = t then
      STRIP_ASSUME_TAC(REWRITE_RULE[FORALL_AND_THM] (MATCH_MP MOI_S5W_HOMEO_PTS (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th))))
      else NO_TAC))
   [`pl_homeomorphism (relative_frontier std_triangle,(jj:num->real^3->bool) i)
       ((jf:num->real^2->real^3) i,(jf':num->real^3->real^2) i)`;
    `pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
       ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)`;
    `pl_homeomorphism ((jj':num->real^3->bool) i,(jj:num->real^3->bool) i)
       (H1':real^3->real^3,H1)`;
    `pl_homeomorphism (Ci:real^2->bool,(jj:num->real^3->bool) i) (G:real^2->real^3,G')`] THEN
    SUBGOAL_THEN
   `moi_s3ci_cycpres
      (((jf':num->real^3->real^2) i o (G:real^2->real^3)) o
       ((G':real^3->real^2) o (H1':real^3->real^3) o (psi:num->real^3->real^3) i o G) o
       (G' o (jf:num->real^2->real^3) i))`
  ASSUME_TAC THENL
     [MP_TAC(SPECL [`(jf':num->real^3->real^2) i o (psi':num->real^3->real^3) i o
                   (H1:real^3->real^3) o (jf:num->real^2->real^3) i`;
                  `(jf':num->real^3->real^2) i o (H1':real^3->real^3) o
                   (psi:num->real^3->real^3) i o (jf:num->real^2->real^3) i`]
      MOI_S3CI_INVERSE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(jf:num->real^2->real^3) i x IN (jj:num->real^3->bool) i` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:num->real^3->real^3) i ((jf:num->real^2->real^3) i x) IN
                (jj':num->real^3->bool) i /\
                (H1:real^3->real^3) ((jf:num->real^2->real^3) i x) IN jj' i`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(H1':real^3->real^3) ((psi:num->real^3->real^3) i ((jf:num->real^2->real^3) i x))
                IN (jj:num->real^3->bool) i /\
                (psi':num->real^3->real^3) i ((H1:real^3->real^3) (jf i x)) IN jj i`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
    MATCH_MP_TAC(MESON[MOI_S3CI_PTWISE]
     `!q1 q2:real^2->real^2.
        (!x. x IN relative_frontier std_triangle ==> q1 x = q2 x)
        ==> (moi_s3ci_cycpres q1 <=> moi_s3ci_cycpres q2)`) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(jf:num->real^2->real^3) i x IN (jj:num->real^3->bool) i` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:num->real^3->real^3) i ((jf:num->real^2->real^3) i x) IN
                  (jj':num->real^3->bool) i` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(H1':real^3->real^3) ((psi:num->real^3->real^3) i ((jf:num->real^2->real^3) i x))
                  IN (jj:num->real^3->bool) i` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s3mt_coll k j`; `Ci:real^2->bool`; `moi_s3mt_cend k j`;
                 `(G':real^3->real^2) o (jf:num->real^2->real^3) i`;
                 `(jf':num->real^3->real^2) i o (G:real^2->real^3)`;
                 `(G':real^3->real^2) o (H1':real^3->real^3) o (psi:num->real^3->real^3) i o
                  (G:real^2->real^3)`;
                 `(((G':real^3->real^2) o (psi':num->real^3->real^3) i) o (H1:real^3->real^3)) o
                  (G:real^2->real^3)`] MOI_S3CI_COLLAR_DEF) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `moi_s3hx_circ k j = (Ci:real^2->bool)`)) THEN
    MATCH_MP_TAC MOI_S3MT_COLL_ANN THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`k:num`; `j:num`; `c:real^2->real^2`; `c':real^2->real^2`]
    MOI_S3MT_COLL_EXT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^2->real^2` (X_CHOOSE_THEN `C':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`C:real^2->real^2`; `C':real^2->real^2`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN moi_s3mt_coll k j` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN Ci` THEN
      UNDISCH_TAC `(Ci:real^2->bool) SUBSET moi_s3mt_coll k j` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `C:real^2->real^2`)) (concl th) &&
        can (find_term ((=) `c:real^2->real^2`)) (concl th)
      then REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN moi_s3mt_coll k j`)] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `c:real^2->real^2`)) (concl th) &&
        can (find_term ((=) `Ci:real^2->bool`)) (concl th)
      then REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN Ci`)] else NO_TAC) THEN
    REWRITE_TAC[o_THM];
    FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* compose the collar adjustments over S *)
  MP_TAC(ISPECL [`k:num`; `sigma:num->num`;
                 `\i x. (G':real^3->real^2) ((H1':real^3->real^3)
                          ((psi:num->real^3->real^3) i ((G:real^2->real^3) x)))`;
                 `S:num->bool`] MOI_S3MT_ADJ_COMPOSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(i:num) <= k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term is_neg) (concl th) &&
        can (find_term ((=) `sigma:num->num`)) (concl th))) THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(i:num) <= k` ASSUME_TAC THENL
       [UNDISCH_TAC `(i:num) IN S` THEN
        UNDISCH_TAC `!i. i IN S ==> i <= k /\
          pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                           ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_S3MT_CIRC_PULL THEN
      MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `A':real^3->bool`; `H1:real^3->real^3`;
        `(jj:num->real^3->bool) i`; `(jj':num->real^3->bool) i`;
        `(psi':num->real^3->real^3) i`] THEN
      MP_TAC(MP (SPEC `i:num` (ASSUME `!i. i IN S ==> i <= k /\
          pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                           ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)`))
        (ASSUME `(i:num) IN S`)) THEN STRIP_TAC THEN
      MP_TAC(MP (SPEC `i:num` (ASSUME `!i. i <= k ==> (sigma:num->num) i <= k /\
          (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))`))
        (ASSUME `(i:num) <= k`)) THEN STRIP_TAC THEN
      MP_TAC(MP (SPEC `i:num` (ASSUME `!i. i <= k ==> IMAGE (H1:real^3->real^3)
          ((jj:num->real^3->bool) i) = jj' i`))
        (ASSUME `(i:num) <= k`)) THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `S:num->bool`) THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i:num | i <= k}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^2->real^2` (X_CHOOSE_THEN `D':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (holed_disk_model k,A:real^3->bool)
                                   (G:real^2->real^3,G')`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (A:real^3->bool,A') (H1:real^3->real^3,H1')`)) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (A,A')
      ((H1:real^3->real^3) o (G:real^2->real^3) o (D:real^2->real^2) o (G':real^3->real^2),
       (((G o (D':real^2->real^2)) o G') o (H1':real^3->real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model k` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` MOI_S3MT_COLL_FACTS) THEN STRIP_TAC THEN
  (* agreement with psi on the pre-mapped circles *)
  SUBGOAL_THEN
   `!i x. i IN S /\ x IN (jj:num->real^3->bool) i
          ==> ((H1:real^3->real^3) o (G:real^2->real^3) o (D:real^2->real^2) o
               (G':real^3->real^2)) x = (psi:num->real^3->real^3) i x`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `x:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `psi':num->real^3->real^3`)) (concl th) &&
      not (can (find_term ((=) `moi_s3ci_cycpres`)) (concl th)) &&
      not (can (find_term ((=) `H1:real^3->real^3`)) (concl th)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[FORALL_AND_THM]
      (MATCH_MP MOI_S5W_HOMEO_PTS (CONJUNCT1(REWRITE_RULE[pl_homeomorphism] th)))))) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sigma:num->num`)) (concl th) &&
      can (find_term ((=) `G:real^2->real^3`)) (concl th) &&
      not (can (find_term is_neg) (concl th)))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `(x:real^3) IN (jj:num->real^3->bool) i`)) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `(jj:num->real^3->bool) i`
      then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] else NO_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `moi_s3mt_cend`)) (concl th)
      then STRIP_ASSUME_TAC(MP (SPEC `(sigma:num->num) i` th)
             (ASSUME `(sigma:num->num) i <= k`))
      else NO_TAC) THEN
    SUBGOAL_THEN `(c:real^2) IN holed_disk_model k` ASSUME_TAC THENL
     [UNDISCH_TAC `(c:real^2) IN moi_s3hx_circ k ((sigma:num->num) i)` THEN
      UNDISCH_TAC `moi_s3hx_circ k ((sigma:num->num) i) SUBSET moi_s3mt_coll k (sigma i)` THEN
      UNDISCH_TAC `moi_s3mt_coll k ((sigma:num->num) i) SUBSET holed_disk_model k` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `x:real^3`)) THEN
    SUBGOAL_THEN `(psi:num->real^3->real^3) i ((G:real^2->real^3) c) IN (jj':num->real^3->bool) i`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(jj':num->real^3->bool) i SUBSET A'` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `H1:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `jj':num->real^3->bool`)) (concl th))) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))` THEN
      UNDISCH_TAC `moi_s3hx_circ k ((sigma:num->num) i) SUBSET moi_s3mt_coll k (sigma i)` THEN
      UNDISCH_TAC `moi_s3mt_coll k ((sigma:num->num) i) SUBSET holed_disk_model k` THEN
      UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN
      UNDISCH_TAC `IMAGE (H1:real^3->real^3) A = A'` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:num->real^3->real^3) i ((G:real^2->real^3) c) IN A'` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(jj':num->real^3->bool) i SUBSET A'`) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(H1':real^3->real^3) ((psi:num->real^3->real^3) i ((G:real^2->real^3) c)) IN A`
    ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (H1':real^3->real^3) A' = A` THEN
      UNDISCH_TAC `(psi:num->real^3->real^3) i ((G:real^2->real^3) c) IN A'` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(H1:real^3->real^3) o (G:real^2->real^3) o (D:real^2->real^2) o (G':real^3->real^2)`;
    `(((G:real^2->real^3) o (D':real^2->real^2)) o (G':real^3->real^2)) o (H1':real^3->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
  SUBGOAL_THEN `FINITE (S:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i <= k}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
    UNDISCH_TAC `!i. i IN S ==> i <= k /\
      pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                       ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN holed_disk_model k /\ y IN holed_disk_model k /\
                      (G:real^2->real^3) x = G y ==> x = y` (LABEL_TAC "INJ") THENL
   [UNDISCH_TAC `!x. x IN holed_disk_model k ==> (G':real^3->real^2) ((G:real^2->real^3) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN S ==> i <= k /\ (sigma:num->num) i <= k /\
                    moi_s3mt_coll k (sigma i) SUBSET holed_disk_model k /\
                    moi_s3hx_circ k (sigma i) SUBSET moi_s3mt_coll k (sigma i) /\
                    (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))`
  (LABEL_TAC "SF") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:num) <= k` ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) IN S` THEN
      UNDISCH_TAC `!i. i IN S ==> i <= k /\
        pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                         ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sigma:num->num) i <= k /\
                  (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) <= k` THEN
      UNDISCH_TAC `!i. i <= k ==> (sigma:num->num) i <= k /\
        (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(sigma:num->num) i <= k` THEN
    UNDISCH_TAC `!j. j <= k
          ==> moi_s3mt_coll k j SUBSET holed_disk_model k /\
              moi_s3hx_circ k j SUBSET moi_s3mt_coll k j /\
              moi_s3mt_cend k j SUBSET moi_s3mt_coll k j /\
              compact (moi_s3mt_coll k j)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN holed_disk_model k
        ==> ((G:real^2->real^3) x IN
             UNIONS {IMAGE G (moi_s3mt_coll k ((sigma:num->num) i)) | i IN S} <=>
             ?i. i IN S /\ x IN moi_s3mt_coll k (sigma i))`
  (LABEL_TAC "UN") THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `t:real^3->bool`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SF" (MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`)) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN holed_disk_model k` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^2) IN moi_s3mt_coll k ((sigma:num->num) i)` THEN
        UNDISCH_TAC `moi_s3mt_coll k ((sigma:num->num) i) SUBSET holed_disk_model k` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^2) = z` (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (G:real^2->real^3) (moi_s3mt_coll k ((sigma:num->num) i))` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term (fun u -> is_const u && fst(dest_const u) = "open")) (concl th)
   then MATCH_MP_TAC(SPECL
     [`(H1:real^3->real^3) o (G:real^2->real^3) o (D:real^2->real^2) o (G':real^3->real^2)`;
      `(((G:real^2->real^3) o (D':real^2->real^2)) o (G':real^3->real^2)) o (H1':real^3->real^3)`;
      `H1:real^3->real^3`; `H1':real^3->real^3`;
      `(:real^3) DIFF UNIONS {IMAGE (G:real^2->real^3) (moi_s3mt_coll k ((sigma:num->num) i)) | i IN S}`] th)
   else NO_TAC) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "SF" (MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`)) THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `holed_disk_model k` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(sigma:num->num) i <= k`) o check (fun th ->
          is_forall(concl th) && can (find_term (fun u -> is_const u &&
            fst(dest_const u) = "compact")) (concl th))) THEN
        SIMP_TAC[]]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(G:real^2->real^3) (vector[&3 / &2; &2])` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN
    CONJ_TAC THENL
     [USE_THEN "UN" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(vector[&3 / &2; &2]:real^2) IN holed_disk_model k`)]) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "SF" (MP_TAC o C MATCH_MP (ASSUME `(i:num) IN S`)) THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(sigma:num->num) i <= k`) o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `(vector[&3 / &2; &2]:real^2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (G:real^2->real^3) (holed_disk_model k) = A` THEN
      UNDISCH_TAC `(vector[&3 / &2; &2]:real^2) IN holed_disk_model k` THEN SET_TAC[]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G':real^3->real^2) x IN holed_disk_model k` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (G':real^3->real^2) A = holed_disk_model k` THEN
      UNDISCH_TAC `(x:real^3) IN A` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real^2->real^3) ((G':real^3->real^2) x) = x` ASSUME_TAC THENL
     [MP_TAC(MP (SPEC `x:real^3` (ASSUME
        `!y. y IN A ==> (G:real^2->real^3) ((G':real^3->real^2) y) = y`))
        (ASSUME `(x:real^3) IN A`)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(D:real^2->real^2) ((G':real^3->real^2) x) = G' x` SUBST1_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:real^2->real^2`)) (concl th) &&
        not (can (find_term ((=) `psi:num->real^3->real^3`)) (concl th)))) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "UN" (MP_TAC o C MATCH_MP
        (ASSUME `(G':real^3->real^2) x IN holed_disk_model k`)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM_REWRITE_TAC[]]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `(i:num) IN S` THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:num->real^3->real^3) i) ((jj:num->real^3->bool) i)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `D:real^2->real^2`)) (concl th) &&
          can (find_term ((=) `psi:num->real^3->real^3`)) (concl th) &&
          can (find_term ((=) `H1:real^3->real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(MP (SPEC `i:num` (ASSUME `!i. i IN S ==> i <= k /\
          pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                           ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)`))
          (ASSUME `(i:num) IN S`)) THEN
        SIMP_TAC[pl_homeomorphism; homeomorphism]];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (H1:real^3->real^3) ((jj:num->real^3->bool) i)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN
        SUBGOAL_THEN `(sigma:num->num) i <= k /\
                      (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THENL
         [UNDISCH_TAC `(i:num) <= k` THEN
          UNDISCH_TAC `!i. i <= k ==> (sigma:num->num) i <= k /\
            (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))` THEN
          MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(sigma:num->num) i <= k`) o check (fun th ->
          is_forall(concl th) && can (find_term (fun u -> is_const u &&
            fst(dest_const u) = "compact")) (concl th))) THEN STRIP_TAC THEN
        SUBGOAL_THEN `(c:real^2) IN holed_disk_model k` ASSUME_TAC THENL
         [UNDISCH_TAC `(c:real^2) IN moi_s3hx_circ k ((sigma:num->num) i)` THEN
          UNDISCH_TAC `moi_s3hx_circ k ((sigma:num->num) i) SUBSET moi_s3mt_coll k (sigma i)` THEN
          UNDISCH_TAC `moi_s3mt_coll k ((sigma:num->num) i) SUBSET holed_disk_model k` THEN
          SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(G':real^3->real^2) ((G:real^2->real^3) c) = c` SUBST1_TAC THENL
         [MP_TAC(MP (SPEC `c:real^2` (ASSUME
            `!x. x IN holed_disk_model k ==> (G':real^3->real^2) ((G:real^2->real^3) x) = x`))
            (ASSUME `(c:real^2) IN holed_disk_model k`)) THEN SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(D:real^2->real^2) c = c` (fun th -> REWRITE_TAC[th]) THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `D:real^2->real^2`)) (concl th) &&
            not (can (find_term ((=) `psi:num->real^3->real^3`)) (concl th)))) THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        X_GEN_TAC `i':num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(i':num) <= k` ASSUME_TAC THENL
         [UNDISCH_TAC `(i':num) IN S` THEN
          UNDISCH_TAC `!i. i IN S ==> i <= k /\
            pl_homeomorphism ((jj:num->real^3->bool) i,(jj':num->real^3->bool) i)
                             ((psi:num->real^3->real^3) i,(psi':num->real^3->real^3) i)` THEN
          MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(sigma:num->num) i' <= k` ASSUME_TAC THENL
         [UNDISCH_TAC `(i':num) <= k` THEN
          UNDISCH_TAC `!i. i <= k ==> (sigma:num->num) i <= k /\
            (jj:num->real^3->bool) i = IMAGE (G:real^2->real^3) (moi_s3hx_circ k (sigma i))` THEN
          MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `~((sigma:num->num) i = sigma i')` ASSUME_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `sigma:num->num`)) (concl th) &&
            (let b = snd(strip_forall(concl th)) in is_imp b && is_neg(rand b)))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((i:num) IN S)` THEN UNDISCH_TAC `(i':num) IN S` THEN MESON_TAC[];
          ALL_TAC] THEN
        MP_TAC(SPECL [`(sigma:num->num) i`; `(sigma:num->num) i'`] (ASSUME
          `!j j'. j <= k /\ j' <= k /\ ~(j = j')
                  ==> DISJOINT (moi_s3mt_coll k j) (moi_s3mt_coll k j')`)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(c:real^2) IN moi_s3hx_circ k ((sigma:num->num) i)` THEN
        UNDISCH_TAC `moi_s3hx_circ k ((sigma:num->num) i) SUBSET moi_s3mt_coll k (sigma i)` THEN
        SET_TAC[];
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:num) <= k`) o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `H1:real^3->real^3`)) (concl th) &&
          can (find_term ((=) `jj':num->real^3->bool`)) (concl th) &&
          not (can (find_term ((=) `D:real^2->real^2`)) (concl th)))) THEN
        SIMP_TAC[]]];
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* I: induction over finite sets of vertices.  Source pieces a v and target *)
(* pieces a' v (closed), rims r u v and r' u v of adjacent u, v (the pieces *)
(* of distinct vertices meet exactly in the rim, or not at all), a          *)
(* predicate SP v on maps of a v that depends only on the values on a v.    *)
(* A step oracle extends a map g of the pieces of S to a map h of a new     *)
(* piece w with SP, matching rims, equal to g on the rims shared with S;    *)
(* pasting (MOI_PL2_PL_HOMEOMORPHISM_UNION) then gives a PL homeomorphism   *)
(* of the union of all pieces onto the union of their targets.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_PASTE_BODY =
 `!(V:A->bool) (a:A->real^3->bool) (a':A->real^3->bool) (adj:A->A->bool)
   (r:A->A->real^3->bool) (r':A->A->real^3->bool) (SP:A->(real^3->real^3)->bool).
     FINITE V /\
     (!v. v IN V ==> closed (a v) /\ closed (a' v)) /\
     (!u v. adj u v ==> u IN V /\ v IN V /\ ~(u = v) /\ adj v u /\
                        r u v = r v u /\ r' u v = r' v u) /\
     (!u v. u IN V /\ v IN V /\ ~(u = v)
            ==> a u INTER a v = (if adj u v then r u v else {}) /\
                a' u INTER a' v = (if adj u v then r' u v else {})) /\
     (!v f g. (!x. x IN a v ==> f x = g x) ==> (SP v f <=> SP v g)) /\
     (!S w (g:real^3->real^3) g'.
        S SUBSET V /\ w IN V /\ ~(w IN S) /\
        pl_homeomorphism (UNIONS (IMAGE a S),UNIONS (IMAGE a' S)) (g,g') /\
        (!v. v IN S ==> IMAGE g (a v) = a' v /\ SP v g /\
                        (!u. adj v u ==> IMAGE g (r v u) = r' v u))
        ==> ?h h'. pl_homeomorphism (a w,a' w) (h,h') /\ SP w h /\
                   (!u. adj w u ==> IMAGE h (r w u) = r' w u) /\
                   (!u x. u IN S /\ adj w u /\ x IN r w u ==> h x = g x))
     ==> ?g g'. pl_homeomorphism (UNIONS (IMAGE a V),UNIONS (IMAGE a' V)) (g,g') /\
                (!v. v IN V ==> IMAGE g (a v) = a' v /\ SP v g /\
                                (!u. adj v u ==> IMAGE g (r v u) = r' v u))`;;

let MOI_S3MT_PASTE = prove
 (MOI_S3MT_PASTE_BODY,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["FIN";"CL";"ADJ";"INT";"LOC";"STEP"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `!v u. (adj:A->A->bool) v u ==> (r:A->A->real^3->bool) v u SUBSET (a:A->real^3->bool) v`
  (LABEL_TAC "RSUB") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ADJ" (STRIP_ASSUME_TAC o C MP (ASSUME `(adj:A->A->bool) v u`) o SPECL [`v:A`; `u:A`]) THEN
    USE_THEN "INT" (MP_TAC o SPECL [`v:A`; `u:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S. FINITE S ==> S SUBSET V ==>
        ?g g'. pl_homeomorphism (UNIONS (IMAGE (a:A->real^3->bool) S),
                                 UNIONS (IMAGE (a':A->real^3->bool) S)) (g,g') /\
               (!v. v IN S ==> IMAGE g (a v) = a' v /\ (SP:A->(real^3->real^3)->bool) v g /\
                               (!u. (adj:A->A->bool) v u
                                    ==> IMAGE g ((r:A->A->real^3->bool) v u) =
                                        (r':A->A->real^3->bool) v u))`
  (fun th -> MP_TAC(SPEC `V:A->bool` th) THEN USE_THEN "FIN" (fun fth ->
               REWRITE_TAC[fth; SUBSET_REFL])) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; NOT_IN_EMPTY] THEN
    REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MESON_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `S:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  USE_THEN "IH" (MP_TAC o C MP (ASSUME `(S:A->bool) SUBSET V`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GI")))) THEN
  USE_THEN "STEP" (MP_TAC o SPECL [`S:A->bool`; `w:A`; `g:real^3->real^3`; `g':real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "HR") (LABEL_TAC "HG")))))) THEN
  SUBGOAL_THEN
   `!v. v IN S ==> IMAGE (g:real^3->real^3) ((a:A->real^3->bool) v INTER a w) =
                   (a':A->real^3->bool) v INTER a' w /\
                   (!x. x IN a v INTER a w ==> g x = (h:real^3->real^3) x)`
  (LABEL_TAC "PV") THENL
   [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((v:A) = w) /\ v IN V` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(v:A) IN S` THEN UNDISCH_TAC `~((w:A) IN S)` THEN
      UNDISCH_TAC `(S:A->bool) SUBSET V` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "INT" (MP_TAC o SPECL [`v:A`; `w:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
    USE_THEN "ADJ" (STRIP_ASSUME_TAC o C MP (ASSUME `(adj:A->A->bool) v w`) o
      SPECL [`v:A`; `w:A`]) THEN
    CONJ_TAC THENL
     [USE_THEN "GI" (MP_TAC o SPEC `w:A` o CONJUNCT2 o CONJUNCT2 o
        C MP (ASSUME `(v:A) IN S`) o SPEC `v:A`) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "HG" MATCH_MP_TAC THEN EXISTS_TAC `v:A` THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (IMAGE (a:A->real^3->bool) S)) /\
                closed (UNIONS (IMAGE (a':A->real^3->bool) S)) /\
                closed ((a:A->real^3->bool) w) /\ closed ((a':A->real^3->bool) w)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!v. v IN S ==> closed ((a:A->real^3->bool) v) /\ closed ((a':A->real^3->bool) v)`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:A` THEN DISCH_TAC THEN USE_THEN "CL" MATCH_MP_TAC THEN
      UNDISCH_TAC `(v:A) IN S` THEN UNDISCH_TAC `(S:A->bool) SUBSET V` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
      MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
      USE_THEN "CL" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN SIMP_TAC[];
      USE_THEN "CL" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN UNIONS (IMAGE (a:A->real^3->bool) S) INTER a w
                    ==> (g:real^3->real^3) x = (h:real^3->real^3) x` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "PV" (MP_TAC o C MP (ASSUME `(v:A) IN S`) o SPEC `v:A`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (UNIONS (IMAGE (a:A->real^3->bool) S) INTER a w) =
                UNIONS (IMAGE (a':A->real^3->bool) S) INTER a' w` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!v. v IN S ==> !z. z IN (a':A->real^3->bool) v /\ z IN a' w <=>
                         ?x. z = (g:real^3->real^3) x /\ x IN (a:A->real^3->bool) v /\ x IN a w`
    MP_TAC THENL
     [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
      USE_THEN "PV" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(v:A) IN S`) o SPEC `v:A`) THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (IMAGE (a:A->real^3->bool) S)`; `(a:A->real^3->bool) w`;
                 `UNIONS (IMAGE (a':A->real^3->bool) S)`; `(a':A->real^3->bool) w`;
                 `g:real^3->real^3`; `g':real^3->real^3`; `h:real^3->real^3`;
                 `h':real^3->real^3`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x. if x IN UNIONS (IMAGE (a:A->real^3->bool) S) then (g:real^3->real^3) x else h x`;
    `\y. if y IN UNIONS (IMAGE (a':A->real^3->bool) S) then (g':real^3->real^3) y else h' y`] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `UNIONS (IMAGE (a:A->real^3->bool) (w INSERT S)) = UNIONS (IMAGE a S) UNION a w /\
                  UNIONS (IMAGE (a':A->real^3->bool) (w INSERT S)) = UNIONS (IMAGE a' S) UNION a' w`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:A` THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `!x. x IN (a:A->real^3->bool) w
                      ==> (\x. if x IN UNIONS (IMAGE a S) then (g:real^3->real^3) x
                               else (h:real^3->real^3) x) x = h x` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!x. x IN UNIONS (IMAGE (a:A->real^3->bool) S) INTER a w
                               ==> (g:real^3->real^3) x = (h:real^3->real^3) x`) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (h:real^3->real^3) ((a:A->real^3->bool) w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `pl_homeomorphism ((a:A->real^3->bool) w,(a':A->real^3->bool) w)
                                      ((h:real^3->real^3),(h':real^3->real^3))` THEN
        SIMP_TAC[pl_homeomorphism; homeomorphism]];
      USE_THEN "LOC" (MP_TAC o SPECL
       [`w:A`; `\x. if x IN UNIONS (IMAGE (a:A->real^3->bool) S) then (g:real^3->real^3) x
                    else (h:real^3->real^3) x`; `h:real^3->real^3`]) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (h:real^3->real^3) ((r:A->A->real^3->bool) w u)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        USE_THEN "RSUB" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w u`) o SPECL [`w:A`; `u:A`]) THEN
        UNDISCH_TAC `(y:real^3) IN (r:A->A->real^3->bool) w u` THEN SET_TAC[];
        USE_THEN "HR" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    SUBGOAL_THEN `(a:A->real^3->bool) v SUBSET UNIONS (IMAGE a S)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN (a:A->real^3->bool) v
                      ==> (\x. if x IN UNIONS (IMAGE a S) then (g:real^3->real^3) x
                               else (h:real^3->real^3) x) x = g x` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN UNIONS (IMAGE (a:A->real^3->bool) S)`
        (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:real^3) IN (a:A->real^3->bool) v` THEN
      UNDISCH_TAC `(a:A->real^3->bool) v SUBSET UNIONS (IMAGE a S)` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "GI" (MP_TAC o C MP (ASSUME `(v:A) IN S`) o SPEC `v:A`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GR"))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (g:real^3->real^3) ((a:A->real^3->bool) v)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      USE_THEN "LOC" (MP_TAC o SPECL
       [`v:A`; `\x. if x IN UNIONS (IMAGE (a:A->real^3->bool) S) then (g:real^3->real^3) x
                    else (h:real^3->real^3) x`; `g:real^3->real^3`]) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^3->real^3) ((r:A->A->real^3->bool) v u)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        USE_THEN "RSUB" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) v u`) o SPECL [`v:A`; `u:A`]) THEN
        UNDISCH_TAC `(y:real^3) IN (r:A->A->real^3->bool) v u` THEN SET_TAC[];
        USE_THEN "GR" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Side preservation, surfaces and sides as constants (abbreviations of the  *)
(* inline forms in the sorient terms of pc_moi_s33_sorstmt), the locality    *)
(* of side preservation, and the sorient terms folded with them.             *)
(* ------------------------------------------------------------------------- *)

let moi_s3mt_sp = new_definition
 `moi_s3mt_sp (i:real^3->bool) (i':real^3->bool) (A:real^3->bool) (f:real^3->real^3) <=>
   !a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
           (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                    ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c) /\
           ~collinear {f a,f b,f c}
           ==> ((?p d. p IN relative_interior(convex hull {f a,f b,f c}) /\ &0 < d /\
                      !z. z IN ball(p,d) /\ &0 < ((f b - f a) cross (f c - f a)) dot (z - p)
                          ==> z IN i') <=>
                (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                       !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                           ==> z IN i))`;;

let moi_s3mt_surf = new_definition
 `moi_s3mt_surf (s:real^3->bool) <=>
    ?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = s`;;

let moi_s3mt_sided = new_definition
 `moi_s3mt_sided (s:real^3->bool) (i:real^3->bool) <=>
    ?e. open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF s /\
        frontier i = s /\ frontier e = s`;;

let MOI_S3MT_SP_LOCAL = prove
 (`!(i:real^3->bool) i' A (f:real^3->real^3) g.
     (!x. x IN A ==> f x = g x) ==> (moi_s3mt_sp i i' A f <=> moi_s3mt_sp i i' A g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s3mt_sp] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `convex hull {a,b,c} SUBSET (A:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN convex hull {a,b,c} ==> (f:real^3->real^3) y = g y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {a,b,c} SUBSET (A:real^3->bool)` THEN
    UNDISCH_TAC `!x:real^3. x IN A ==> (f:real^3->real^3) x = g x` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) a = g a /\ f b = g b /\ f c = g c` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
            ==> (f:real^3->real^3) (u % a + v % b + w % c) = g (u % a + v % b + w % c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`; `w:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
             ==> (f:real^3->real^3) (u % a + v % b + w % c) = u % g a + v % g b + w % g c) <=>
    (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
             ==> (g:real^3->real^3) (u % a + v % b + w % c) = u % g a + v % g b + w % g c)`
  (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(f:real^3->real^3) (u % a + v % b + w % c)` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `g:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `f:real^3->real^3`)) (concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "%")) (concl th) &&
        not (can (find_term (fun u -> is_const u && fst(dest_const u) = "+") o rhs o snd o
               dest_imp o snd o strip_forall) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(g:real^3->real^3) (u % a + v % b + w % c)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `g:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `f:real^3->real^3`)) (concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "%")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The statement terms of pc_moi_s33_msides: SIDES (the two surfaces are    *)
(* triangulated and two-sided), VDATA (per-vertex charts and labels), PCS   *)
(* (pieces, overlaps, covers, neighbourhoods).  They are mk_imp antecedents *)
(* of MOI_S3MT_MATCH_COND, discharged in MATCH by MP from MOI_S3MS_SIDES,   *)
(* VDATA and PCS.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_SIDES_TERM =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (bx:(real^3->bool)->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx
     ==> (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = derived_frontier t l) /\
         (?ee. open (interior (derived_nbhd t l)) /\ open ee /\
               DISJOINT (interior (derived_nbhd t l)) ee /\
               interior (derived_nbhd t l) UNION ee = (:real^3) DIFF derived_frontier t l /\
               frontier (interior (derived_nbhd t l)) = derived_frontier t l /\
               frontier ee = derived_frontier t l) /\
         (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = frontier (UNIONS x)) /\
         (?ee. open (interior (UNIONS x)) /\ open ee /\
               DISJOINT (interior (UNIONS x)) ee /\
               interior (UNIONS x) UNION ee = (:real^3) DIFF frontier (UNIONS x) /\
               frontier (interior (UNIONS x)) = frontier (UNIONS x) /\
               frontier ee = frontier (UNIONS x))`;;

let MOI_S3MT_VDATA_TERM =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (v:real^3).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_holed l e c x /\
     {v} IN l
     ==> ?d (nb:num->real^3) (G:real^2->real^3) (G':real^3->real^2)
           (G2:real^2->real^3) (G2':real^3->real^2).
           CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = d + 1 /\
           (!i. i <= d ==> ~(nb i = v) /\ segment[v,nb i] IN l) /\
           (!i j. i <= d /\ j <= d /\ nb i = nb j ==> i = j) /\
           (!u. ~(u = v) /\ segment[v,u] IN l ==> ?i. i <= d /\ u = nb i) /\
           pl_homeomorphism (holed_disk_model d,
                             derived_dual_cell t l v INTER derived_frontier t l) (G,G') /\
           pl_homeomorphism (holed_disk_model d,c v INTER frontier (UNIONS x)) (G2,G2') /\
           IMAGE G (frontier (holed_disk_model d)) =
           UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                   derived_frontier t l | i <= d} /\
           IMAGE G2 (frontier (holed_disk_model d)) =
           UNIONS {e(segment[v,nb i]) INTER frontier (UNIONS x) | i <= d} /\
           (!i. i <= d
                ==> pl_sphere 1 (derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                                 derived_frontier t l) /\
                    pl_sphere 1 (e(segment[v,nb i]) INTER frontier (UNIONS x))) /\
           (!i i'. i <= d /\ i' <= d /\ ~(i = i')
                   ==> DISJOINT (derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                                 derived_frontier t l)
                                (derived_dual_cell t l v INTER derived_dual_cell t l (nb i') INTER
                                 derived_frontier t l) /\
                       DISJOINT (e(segment[v,nb i]) INTER frontier (UNIONS x))
                                (e(segment[v,nb i']) INTER frontier (UNIONS x)))`;;

let MOI_S3MT_VDATA_STMT =
  mk_imp(inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE, MOI_S3MT_VDATA_TERM);;

let MOI_S3MT_PCS_TERM =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_holed l e c x
     ==> FINITE {v | {v} IN l} /\
         (!u v. ~(u = v) /\ segment[u,v] IN l ==> {u} IN l /\ {v} IN l) /\
         (!v. {v} IN l
              ==> compact (derived_dual_cell t l v INTER derived_frontier t l) /\
                  compact (c v INTER frontier (UNIONS x)) /\
                  locally_polyhedral (derived_dual_cell t l v INTER derived_frontier t l) /\
                  locally_polyhedral (c v INTER frontier (UNIONS x))) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v)
                ==> (derived_dual_cell t l u INTER derived_frontier t l) INTER
                    (derived_dual_cell t l v INTER derived_frontier t l) =
                    (if segment[u,v] IN l
                     then derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                          derived_frontier t l
                     else {}) /\
                    (c u INTER frontier (UNIONS x)) INTER (c v INTER frontier (UNIONS x)) =
                    (if segment[u,v] IN l then e(segment[u,v]) INTER frontier (UNIONS x)
                     else {})) /\
         UNIONS {derived_dual_cell t l v INTER derived_frontier t l | v | {v} IN l} =
         derived_frontier t l /\
         UNIONS {c v INTER frontier (UNIONS x) | v | {v} IN l} = frontier (UNIONS x) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> (?U. open U /\
                         derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                         derived_frontier t l SUBSET U /\
                         derived_frontier t l INTER U SUBSET
                         (derived_dual_cell t l u INTER derived_frontier t l) UNION
                         (derived_dual_cell t l v INTER derived_frontier t l)) /\
                    (?U'. open U' /\
                          e(segment[u,v]) INTER frontier (UNIONS x) SUBSET U' /\
                          frontier (UNIONS x) INTER U' SUBSET
                          (c u INTER frontier (UNIONS x)) UNION
                          (c v INTER frontier (UNIONS x))))`;;

let MOI_S3MT_PCS_STMT =
  mk_imp(inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE, MOI_S3MT_PCS_TERM);;

(* The sorient terms and the msides terms folded with the constants above. *)

let MOI_S3MT_FOLD_CONV =
  REWRITE_CONV[GSYM moi_s3mt_sp; GSYM moi_s3mt_surf; GSYM moi_s3mt_sided;
               GSYM moi_s3ci_cyc3; GSYM moi_s3ci_cyc; GSYM moi_s3ci_cycpres; ETA_AX];;

let MOI_S3MT_DICHOT_FOLD = MOI_S3MT_FOLD_CONV MOI_S3MT_SORIENT_DICHOT_TERM;;
let MOI_S3MT_CONST_FOLD = MOI_S3MT_FOLD_CONV MOI_S3MT_SORIENT_CONST_TERM;;
let MOI_S3MT_DIR_FOLD = MOI_S3MT_FOLD_CONV MOI_S3MT_SORIENT_DIR_TERM;;
let MOI_S3MT_SIDES_FOLD = MOI_S3MT_FOLD_CONV MOI_S3MT_SIDES_TERM;;

let MOI_S3MT_DICHOT_F = rhs(concl MOI_S3MT_DICHOT_FOLD);;
let MOI_S3MT_CONST_F = rhs(concl MOI_S3MT_CONST_FOLD);;
let MOI_S3MT_DIR_F = rhs(concl MOI_S3MT_DIR_FOLD);;

(* ------------------------------------------------------------------------- *)
(* The induction step for the pasting: a new piece a w is mapped by O5 from *)
(* its holed-disk charts, with P = side preservation on a w.  P1, P2, P3 of *)
(* O5 come from the folded sorient terms DICHOT, CONST and DIR; the pre-    *)
(* mapped circles are the rims shared with the pieces already mapped, where *)
(* the old map is restricted (MOI_CEL_PLH_RESTRICT).  Abstract over the      *)
(* vertex type, the two surfaces with their sides, the pieces and the rims. *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_STEP_BODY =
 `!(s:real^3->bool) (i:real^3->bool) (s':real^3->bool) (i':real^3->bool)
   (V:A->bool) (a:A->real^3->bool) (a':A->real^3->bool) (adj:A->A->bool)
   (r:A->A->real^3->bool) (r':A->A->real^3->bool).
     moi_s3mt_surf s /\ moi_s3mt_surf s' /\ moi_s3mt_sided s i /\ moi_s3mt_sided s' i' /\
     (!v. v IN V ==> a v SUBSET s /\ a' v SUBSET s' /\ locally_polyhedral (a v)) /\
     (!u v. adj u v ==> u IN V /\ v IN V /\ ~(u = v) /\ adj v u /\
                        r u v = r v u /\ r' u v = r' v u) /\
     (!u v. u IN V /\ v IN V /\ ~(u = v)
            ==> a u INTER a v = (if adj u v then r u v else {}) /\
                a' u INTER a' v = (if adj u v then r' u v else {})) /\
     (!u v. adj u v
            ==> (?U. open U /\ r u v SUBSET U /\ s INTER U SUBSET a u UNION a v) /\
                (?U'. open U' /\ r' u v SUBSET U' /\ s' INTER U' SUBSET a' u UNION a' v)) /\
     (!v. v IN V
          ==> ?d (nb:num->A) (G:real^2->real^3) (G':real^3->real^2)
                (G2:real^2->real^3) (G2':real^3->real^2).
                (!j. j <= d ==> adj v (nb j)) /\
                (!j k. j <= d /\ k <= d /\ nb j = nb k ==> j = k) /\
                (!u. adj v u ==> ?j. j <= d /\ u = nb j) /\
                pl_homeomorphism (holed_disk_model d,a v) (G,G') /\
                pl_homeomorphism (holed_disk_model d,a' v) (G2,G2') /\
                IMAGE G (frontier (holed_disk_model d)) = UNIONS {r v (nb j) | j <= d} /\
                IMAGE G2 (frontier (holed_disk_model d)) = UNIONS {r' v (nb j) | j <= d} /\
                (!j. j <= d ==> pl_sphere 1 (r v (nb j)) /\ pl_sphere 1 (r' v (nb j))) /\
                (!j k. j <= d /\ k <= d /\ ~(j = k)
                       ==> DISJOINT (r v (nb j)) (r v (nb k)) /\
                           DISJOINT (r' v (nb j)) (r' v (nb k))))
     ==> !S w (g:real^3->real^3) g'.
           S SUBSET V /\ w IN V /\ ~(w IN S) /\
           pl_homeomorphism (UNIONS (IMAGE a S),UNIONS (IMAGE a' S)) (g,g') /\
           (!v. v IN S ==> IMAGE g (a v) = a' v /\ moi_s3mt_sp i i' (a v) g /\
                           (!u. adj v u ==> IMAGE g (r v u) = r' v u))
           ==> ?h h'. pl_homeomorphism (a w,a' w) (h,h') /\ moi_s3mt_sp i i' (a w) h /\
                      (!u. adj w u ==> IMAGE h (r w u) = r' w u) /\
                      (!u x. u IN S /\ adj w u /\ x IN r w u ==> h x = g x)`;;

let MOI_S3MT_STEP_STMT =
  mk_imp(list_mk_conj [MOI_S3MT_DICHOT_F; MOI_S3MT_CONST_F; MOI_S3MT_DIR_F;
                       inst [`:3`,`:N`; `:3`,`:M`] MOI_S33_HOLED_EXT],
         MOI_S3MT_STEP_BODY);;

let MOI_S3MT_STEP = prove
 (MOI_S3MT_STEP_STMT,
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["DICHOT";"CONST";"DIR";"HEXT"] (CONJUNCTS th))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["SURF";"SURF'";"SIDED";"SIDED'";"PC";"ADJ";"INT";"NB";"VD"] (CONJUNCTS th))) THEN
  MAP_EVERY X_GEN_TAC [`S:A->bool`; `w:A`; `g:real^3->real^3`; `g':real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GI"))))) THEN
  USE_THEN "VD" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `nb:num->A`
    (X_CHOOSE_THEN `G:real^2->real^3` (X_CHOOSE_THEN `G':real^3->real^2`
    (X_CHOOSE_THEN `G2:real^2->real^3` (X_CHOOSE_THEN `G2':real^3->real^2`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["W1";"W2";"W3";"WG";"WG2";"WF";"WF2";"WS";"WD"] (CONJUNCTS th))))))))) THEN
  SUBGOAL_THEN
   `!u. u IN S
        ==> pl_homeomorphism ((a:A->real^3->bool) u,(a':A->real^3->bool) u)
                             ((g:real^3->real^3),(g':real^3->real^3)) /\
            ((adj:A->A->bool) w u
             ==> pl_homeomorphism ((r:A->A->real^3->bool) w u,(r':A->A->real^3->bool) w u)
                                  (g,g') /\
                 IMAGE g (r w u) = r' w u)`
  (LABEL_TAC "GU") THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:A) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:A) IN S` THEN UNDISCH_TAC `(S:A->bool) SUBSET V` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "GI" (MP_TAC o C MP (ASSUME `(u:A) IN S`) o SPEC `u:A`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GIu"))) THEN
    SUBGOAL_THEN `(a:A->real^3->bool) u SUBSET UNIONS (IMAGE a S)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if concl th = `IMAGE (g:real^3->real^3) ((a:A->real^3->bool) u) =
                                            (a':A->real^3->bool) u`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
      EXISTS_TAC `UNIONS (IMAGE (a:A->real^3->bool) S)` THEN
      EXISTS_TAC `UNIONS (IMAGE (a':A->real^3->bool) S)` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "PC" (MP_TAC o C MP (ASSUME `(u:A) IN V`) o SPEC `u:A`) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "ADJ" (STRIP_ASSUME_TAC o C MP (ASSUME `(adj:A->A->bool) w u`) o
      SPECL [`w:A`; `u:A`]) THEN
    SUBGOAL_THEN `IMAGE (g:real^3->real^3) ((r:A->A->real^3->bool) w u) =
                  (r':A->A->real^3->bool) w u` ASSUME_TAC THENL
     [USE_THEN "GIu" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) u w`) o SPEC `w:A`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    FIRST_ASSUM(fun th -> if concl th = `IMAGE (g:real^3->real^3) ((r:A->A->real^3->bool) w u) =
                                          (r':A->A->real^3->bool) w u`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
    EXISTS_TAC `UNIONS (IMAGE (a:A->real^3->bool) S)` THEN
    EXISTS_TAC `UNIONS (IMAGE (a':A->real^3->bool) S)` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "INT" (MP_TAC o SPECL [`u:A`; `w:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(a:A->real^3->bool) u SUBSET UNIONS (IMAGE a S)` THEN SET_TAC[];
      USE_THEN "W3" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w u`) o SPEC `u:A`) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
      USE_THEN "WS" (MP_TAC o C MP (ASSUME `j:num <= d`) o SPEC `j:num`) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `u:A`)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* O5 for the new piece *)
  USE_THEN "HEXT" (MP_TAC o MATCH_MP MOI_S3MT_O5) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`d:num`; `G:real^2->real^3`; `G':real^3->real^2`; `(a:A->real^3->bool) w`;
    `(a':A->real^3->bool) w`; `G2:real^2->real^3`; `G2':real^3->real^2`;
    `\j. (r:A->A->real^3->bool) w ((nb:num->A) j)`;
    `\j. (r':A->A->real^3->bool) w ((nb:num->A) j)`;
    `{j | j <= d /\ (nb:num->A) j IN S}`;
    `\j:num. (g:real^3->real^3)`; `\j:num. (g':real^3->real^3)`;
    `moi_s3mt_sp i i' ((a:A->real^3->bool) w)`]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "WG" ACCEPT_TAC;
      USE_THEN "WG2" ACCEPT_TAC;
      USE_THEN "WF" ACCEPT_TAC;
      USE_THEN "WF2" ACCEPT_TAC;
      USE_THEN "WS" ACCEPT_TAC;
      USE_THEN "WD" ACCEPT_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "GU" (MP_TAC o C MP (ASSUME `(nb:num->A) j IN S`) o SPEC `(nb:num->A) j`) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      USE_THEN "W1" (MP_TAC o C MP (ASSUME `j:num <= d`) o SPEC `j:num`) THEN
      MESON_TAC[];
      (* P1 from DICHOT *)
      MAP_EVERY X_GEN_TAC [`h:real^3->real^3`; `h':real^3->real^3`] THEN DISCH_TAC THEN
        USE_THEN "DICHOT" (MP_TAC o SPECL
         [`s:real^3->bool`; `i:real^3->bool`; `s':real^3->bool`; `i':real^3->bool`; `d:num`;
          `G:real^2->real^3`; `G':real^3->real^2`; `(a:A->real^3->bool) w`;
          `(a':A->real^3->bool) w`; `h:real^3->real^3`; `h':real^3->real^3`;
          `\x. (h:real^3->real^3) ((G:real^2->real^3)
                 (vector [((G':real^3->real^2) x)$1; &4 - (G' x)$2]))`]) THEN
        ANTS_TAC THENL
         [USE_THEN "PC" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[];
          DISCH_THEN ACCEPT_TAC];
      (* P2 from CONST *)
      MAP_EVERY X_GEN_TAC [`f1:real^3->real^3`; `f1':real^3->real^3`; `g1:real^3->real^3`;
                             `g1':real^3->real^3`; `U:real^3->bool`] THEN STRIP_TAC THEN
        USE_THEN "CONST" (MP_TAC o SPECL
         [`s:real^3->bool`; `i:real^3->bool`; `s':real^3->bool`; `i':real^3->bool`; `d:num`;
          `G:real^2->real^3`; `G':real^3->real^2`; `(a:A->real^3->bool) w`;
          `(a':A->real^3->bool) w`; `f1:real^3->real^3`; `f1':real^3->real^3`;
          `g1:real^3->real^3`; `g1':real^3->real^3`; `U:real^3->bool`]) THEN
        ANTS_TAC THENL
         [USE_THEN "PC" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[];
          DISCH_THEN ACCEPT_TAC];
      (* P3 from DIR *)
      MAP_EVERY X_GEN_TAC [`j:num`; `h:real^3->real^3`; `h':real^3->real^3`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(adj:A->A->bool) w ((nb:num->A) j)` ASSUME_TAC THENL
         [USE_THEN "W1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(nb:num->A) j IN V /\ (adj:A->A->bool) ((nb:num->A) j) w` STRIP_ASSUME_TAC THENL
         [USE_THEN "ADJ" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w ((nb:num->A) j)`) o
            SPECL [`w:A`; `(nb:num->A) j`]) THEN SIMP_TAC[];
          ALL_TAC] THEN
        USE_THEN "VD" (MP_TAC o C MP (ASSUME `(nb:num->A) j IN V`) o SPEC `(nb:num->A) j`) THEN
        DISCH_THEN(X_CHOOSE_THEN `du:num` (X_CHOOSE_THEN `nbu:num->A`
          (X_CHOOSE_THEN `Gu:real^2->real^3` (X_CHOOSE_THEN `Gu':real^3->real^2`
          (X_CHOOSE_THEN `G2u:real^2->real^3` (X_CHOOSE_THEN `G2u':real^3->real^2`
          (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
            (zip ["U1";"U2";"U3";"UG";"UG2";"UF";"UF2";"US";"UD"] (CONJUNCTS th))))))))) THEN
        USE_THEN "GU" (MP_TAC o C MP (ASSUME `(nb:num->A) j IN S`) o SPEC `(nb:num->A) j`) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w ((nb:num->A) j)`))) THEN STRIP_TAC THEN
        USE_THEN "GI" (MP_TAC o C MP (ASSUME `(nb:num->A) j IN S`) o SPEC `(nb:num->A) j`) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GIu"))) THEN
        SUBGOAL_THEN `(a:A->real^3->bool) w SUBSET s /\ (a':A->real^3->bool) w SUBSET s' /\
                      a ((nb:num->A) j) SUBSET s /\ a' (nb j) SUBSET s'` STRIP_ASSUME_TAC THENL
         [USE_THEN "PC" (MP_TAC o C MP (ASSUME `(w:A) IN V`) o SPEC `w:A`) THEN
          USE_THEN "PC" (MP_TAC o C MP (ASSUME `(nb:num->A) j IN V`) o SPEC `(nb:num->A) j`) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(a:A->real^3->bool) w INTER a ((nb:num->A) j) = (r:A->A->real^3->bool) w (nb j) /\
                      (a':A->real^3->bool) w INTER a' (nb j) = (r':A->A->real^3->bool) w (nb j)`
        STRIP_ASSUME_TAC THENL
         [USE_THEN "INT" (MP_TAC o SPECL [`w:A`; `(nb:num->A) j`]) THEN
          ANTS_TAC THENL
           [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
            USE_THEN "ADJ" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w ((nb:num->A) j)`) o
              SPECL [`w:A`; `(nb:num->A) j`]) THEN SIMP_TAC[];
            ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `pl_sphere 1 ((r:A->A->real^3->bool) w ((nb:num->A) j))` ASSUME_TAC THENL
         [USE_THEN "WS" (MP_TAC o C MP (ASSUME `j:num <= d`) o SPEC `j:num`) THEN SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(r:A->A->real^3->bool) w ((nb:num->A) j) SUBSET
                      IMAGE (G:real^2->real^3) (frontier (holed_disk_model d))` ASSUME_TAC THENL
         [USE_THEN "WF" SUBST1_TAC THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
          EXISTS_TAC `(r:A->A->real^3->bool) w ((nb:num->A) j)` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(r:A->A->real^3->bool) w ((nb:num->A) j) SUBSET
                      IMAGE (Gu:real^2->real^3) (frontier (holed_disk_model du))` ASSUME_TAC THENL
         [USE_THEN "UF" SUBST1_TAC THEN
          USE_THEN "U3" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) ((nb:num->A) j) w`) o SPEC `w:A`) THEN
          DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(r:A->A->real^3->bool) w ((nb:num->A) j) = r (nb j) w` SUBST1_TAC THENL
           [USE_THEN "ADJ" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w ((nb:num->A) j)`) o
              SPECL [`w:A`; `(nb:num->A) j`]) THEN SIMP_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
          EXISTS_TAC `(r:A->A->real^3->bool) ((nb:num->A) j) w` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        USE_THEN "NB" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w ((nb:num->A) j)`) o
          SPECL [`w:A`; `(nb:num->A) j`]) THEN
        DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
        USE_THEN "DIR" (MP_TAC o SPECL
         [`s:real^3->bool`; `i:real^3->bool`; `s':real^3->bool`; `i':real^3->bool`;
          `(a:A->real^3->bool) w`; `(a:A->real^3->bool) ((nb:num->A) j)`;
          `(a':A->real^3->bool) w`; `(a':A->real^3->bool) ((nb:num->A) j)`;
          `(r:A->A->real^3->bool) w ((nb:num->A) j)`; `(r':A->A->real^3->bool) w ((nb:num->A) j)`;
          `d:num`; `du:num`; `G:real^2->real^3`; `G':real^3->real^2`;
          `Gu:real^2->real^3`; `Gu':real^3->real^2`;
          `h:real^3->real^3`; `h':real^3->real^3`; `g:real^3->real^3`; `g':real^3->real^3`]) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          DISCH_THEN ACCEPT_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "HI") (LABEL_TAC "HA")))))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `h':real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    USE_THEN "W3" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w u`) o SPEC `u:A`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "HI" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`u:A`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "W3" (MP_TAC o C MP (ASSUME `(adj:A->A->bool) w u`) o SPEC `u:A`) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "HA" MATCH_MP_TAC THEN EXISTS_TAC `j:num` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `u:A`)) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MATCH (Moise 33.1 Lemma 13) from PASTE and STEP, with the vertex set     *)
(* (all v with {v} IN l), the source pieces C_v INTER Bd N, the targets      *)
(* c v INTER Bd X, the rims and the traces, and side preservation for the   *)
(* inner sides interior N and interior X.  The sorient terms (DICHOT,       *)
(* CONST, DIR) and the msides terms (SIDES, VDATA, PCS) are mk_imp          *)
(* antecedents; the antecedents of MOI_S33_MATCH are kept (MOISE_268 and    *)
(* TUBE_FACTS unused).                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MT_MATCH_STMT =
  mk_imp(list_mk_conj [MOI_S3MT_SORIENT_DICHOT_TERM; MOI_S3MT_SORIENT_CONST_TERM;
                       MOI_S3MT_SORIENT_DIR_TERM; MOI_S3MT_SIDES_TERM;
                       MOI_S3MT_VDATA_STMT; MOI_S3MT_PCS_STMT],
         MOI_S33_MATCH);;

(* Concrete data, as terms with the free variables of the proof below. *)
let moi_s3mt_m_V = `{v:real^3 | {v} IN (l:(real^3->bool)->bool)}`;;
let moi_s3mt_m_a = `\v:real^3. derived_dual_cell (t:(real^3->bool)->bool) (l:(real^3->bool)->bool) v INTER derived_frontier t l`;;
let moi_s3mt_m_a' = `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS (x:(real^3->bool)->bool))`;;
let moi_s3mt_m_adj = `\u v:real^3. ~(u = v) /\ segment[u,v] IN (l:(real^3->bool)->bool)`;;
let moi_s3mt_m_r = `\u v:real^3. derived_dual_cell (t:(real^3->bool)->bool) (l:(real^3->bool)->bool) u INTER derived_dual_cell t l v INTER derived_frontier t l`;;
let moi_s3mt_m_r' = `\u v:real^3. (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER frontier (UNIONS (x:(real^3->bool)->bool))`;;
let moi_s3mt_m_SP = `\v:real^3. moi_s3mt_sp (interior (derived_nbhd (t:(real^3->bool)->bool) (l:(real^3->bool)->bool))) (interior (UNIONS (x:(real^3->bool)->bool))) (derived_dual_cell t l v INTER derived_frontier t l)`;;
let moi_s3mt_m_s = `derived_frontier (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)`;;
let moi_s3mt_m_i = `interior (derived_nbhd (t:(real^3->bool)->bool) (l:(real^3->bool)->bool))`;;
let moi_s3mt_m_s' = `frontier (UNIONS (x:(real^3->bool)->bool))`;;
let moi_s3mt_m_i' = `interior (UNIONS (x:(real^3->bool)->bool))`;;

let MOI_S3MT_MATCH_COND = prove
 (MOI_S3MT_MATCH_STMT,
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["DICHOT0";"CONST0";"DIR0";"MSIDES";"VDATA";"PCS"] (CONJUNCTS th))) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["M268";"HEXT";"TRIPLE";"TFACTS"] (CONJUNCTS th))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
    `bx:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  USE_THEN "MSIDES" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] o EQ_MP MOI_S3MT_SIDES_FOLD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["SURF";"SIDED";"SURF'";"SIDED'"] (CONJUNCTS th))) THEN
  USE_THEN "TRIPLE" (fun tr -> USE_THEN "PCS" (fun th ->
    MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`] (MP th tr)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["P_FIN";"P_END";"P_CPT";"P_INT";"P_COVN";"P_COVX";"P_NB"] (CONJUNCTS th))) THEN
  USE_THEN "TRIPLE" (fun tr -> USE_THEN "VDATA" (fun th ->
    LABEL_TAC "VD0" (SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`] (MP th tr)))) THEN
  MP_TAC(ISPECL [moi_s3mt_m_V; moi_s3mt_m_a; moi_s3mt_m_a'; moi_s3mt_m_adj; moi_s3mt_m_r;
                 moi_s3mt_m_r'; moi_s3mt_m_SP] MOI_S3MT_PASTE) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!u v. ~(u = v) /\ segment [u,v] IN (l:(real^3->bool)->bool)
          ==> {u} IN l /\ {v} IN l /\ ~(u = v) /\ (~(v = u) /\ segment [v,u] IN l) /\
              derived_dual_cell t l u INTER derived_dual_cell t l v INTER derived_frontier t l =
              derived_dual_cell t l v INTER derived_dual_cell t l u INTER derived_frontier t l /\
              (e:(real^3->bool)->real^3->bool) (segment [u,v]) INTER frontier (UNIONS x) =
              e (segment [v,u]) INTER frontier (UNIONS x)`
  (LABEL_TAC "ADJF") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[v:real^3,u] = segment[u,v]` ASSUME_TAC THENL
     [MATCH_ACCEPT_TAC (CONJUNCT1 SEGMENT_SYM); ALL_TAC] THEN
    SUBGOAL_THEN `~(v:real^3 = u)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(u:real^3 = v)` THEN MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "P_END" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "P_FIN" ACCEPT_TAC;
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
            USE_THEN "P_CPT" (MP_TAC o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN
            SIMP_TAC[COMPACT_IMP_CLOSED];
      USE_THEN "ADJF" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            USE_THEN "P_INT" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3MT_SP_LOCAL THEN
            FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "DICHOT0" (fun d0 -> USE_THEN "CONST0" (fun c0 -> USE_THEN "DIR0" (fun r0 ->
          USE_THEN "HEXT" (fun hx ->
          MP_TAC(ISPECL [moi_s3mt_m_s; moi_s3mt_m_i; moi_s3mt_m_s'; moi_s3mt_m_i'; moi_s3mt_m_V;
                         moi_s3mt_m_a; moi_s3mt_m_a'; moi_s3mt_m_adj; moi_s3mt_m_r; moi_s3mt_m_r']
            (MP MOI_S3MT_STEP (CONJ (EQ_MP MOI_S3MT_DICHOT_FOLD d0)
               (CONJ (EQ_MP MOI_S3MT_CONST_FOLD c0) (CONJ (EQ_MP MOI_S3MT_DIR_FOLD r0) hx))))))))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [USE_THEN "SURF" ACCEPT_TAC;
            USE_THEN "SURF'" ACCEPT_TAC;
            USE_THEN "SIDED" ACCEPT_TAC;
            USE_THEN "SIDED'" ACCEPT_TAC;
            X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN
            USE_THEN "P_CPT" (MP_TAC o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN
            SIMP_TAC[];
            USE_THEN "ADJF" ACCEPT_TAC;
            MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            USE_THEN "P_INT" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
            USE_THEN "P_NB" ACCEPT_TAC;
            X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
            USE_THEN "VD0" (MP_TAC o SPEC `v:real^3`) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
            DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `nb:num->real^3`
              (X_CHOOSE_THEN `G:real^2->real^3` (X_CHOOSE_THEN `G':real^3->real^2`
              (X_CHOOSE_THEN `G2:real^2->real^3` (X_CHOOSE_THEN `G2':real^3->real^2`
               STRIP_ASSUME_TAC)))))) THEN
            MAP_EVERY EXISTS_TAC [`d:num`; `nb:num->real^3`; `G:real^2->real^3`;
              `G':real^3->real^2`; `G2:real^2->real^3`; `G2':real^3->real^2`] THEN
            REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
             [UNDISCH_TAC `!i. i <= d ==> ~((nb:num->real^3) i = v) /\ segment[v,nb i] IN l` THEN
              MESON_TAC[];
              UNDISCH_TAC `!u. ~(u = v) /\ segment[v,u] IN l ==> ?i. i <= d /\ u = (nb:num->real^3) i` THEN
              MESON_TAC[]]];
          DISCH_THEN ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\v:real^3. derived_dual_cell t l v INTER derived_frontier t l) {v | {v} IN l} =
    {derived_dual_cell t l v INTER derived_frontier t l | v | {v} IN l} /\
    IMAGE (\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)) {v | {v} IN l} =
    {c v INTER frontier (UNIONS x) | v | {v} IN l}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "P_COVN" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "P_COVX" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GV")))) THEN
  EXISTS_TAC `g:real^3->real^3` THEN REWRITE_TAC[moi_s33_match] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `g':real^3->real^3` THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "GV" (MP_TAC o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "P_END" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "GV" (MP_TAC o C MP (ASSUME `{u:real^3} IN l`) o SPEC `u:real^3`) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MATCH (Moise 33.1 Lemma 13): the antecedents of MOI_S3MT_MATCH_COND      *)
(* discharged by the theorems of pc_moi_s33_sorient (MOI_S3SO_DICHOT,       *)
(* CONST, DIR) and pc_moi_s33_msides (MOI_S3MS_SIDES, VDATA, PCS).  The     *)
(* antecedents of the result are exactly those of MOI_S33_MATCH.            *)
(* ------------------------------------------------------------------------- *)

let MATCH = prove
 (MOI_S33_MATCH,
  MATCH_ACCEPT_TAC(MP MOI_S3MT_MATCH_COND
    (end_itlist CONJ [MOI_S3SO_DICHOT; MOI_S3SO_CONST; MOI_S3SO_DIR;
                MOI_S3MS_SIDES; MOI_S3MS_VDATA; MOI_S3MS_PCS])));;

