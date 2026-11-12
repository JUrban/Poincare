(* ========================================================================= *)
(* pc_moi_fnd_tubed: foundations of the Moise PL core, the product          *)
(* structure and the Euler count of the graph tube (Moise GTM 47, 33.1      *)
(* Lemma 10 p.235, Lemma 12 p.236).  Main theorems (proving the statement   *)
(* terms of pc_moi_fnd_stmt.ml):                                             *)
(*   GRAPH_TUBE_PRODUCT        = MOI_FND_GRAPH_TUBE_PRODUCT                  *)
(*   GRAPH_NBHD_BOUNDARY_EULER = MOI_FND_GRAPH_NBHD_EULER                    *)
(* and (pc_moi_s3032_stmt.ml)                                                *)
(*   EULER_EVEN                = MOI_S30_EULER_EVEN                          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* For a finite combinatorial 3-manifold with boundary c,                   *)
(* chi(boundary_complex c) = 2 chi(c) (an incidence count in the manner of  *)
(* Dehn-Sommerville).  With f_k the number of k-simplices and the subscript *)
(* b for the boundary complex:                                              *)
(*   sum over vertices of chi(link) = 2 f1 - 3 f2 + 4 f3   (double count)   *)
(*   chi(link v) = 2 inside, 1 on the boundary   (COMPLEX_EULER_VALUES)     *)
(*   4 f3 = 2 f2 - f2b   (a 2-simplex has 1 or 2 three-dimensional cofaces) *)
(*   3 f2b = 2 f1b   (the boundary is a closed combinatorial surface)       *)
(* and the result is linear arithmetic.                                     *)
(* ========================================================================= *)

(* The Euler characteristic of a finite complex of dimension at most 3. *)

let MOI_FTD_SUM_0_3 = prove
 (`!f:num->real. sum(0..3) f = f 0 + f 1 + f 2 + f 3`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[LE_0] THEN REAL_ARITH_TAC);;

let MOI_FTD_EULER_DIM3 = prove
 (`!c:(real^N->bool)->bool.
     (!s. s IN c ==> aff_dim s <= &3)
     ==> complex_euler c =
         &(CARD {s | s IN c /\ aff_dim s = &0}) -
         &(CARD {s | s IN c /\ aff_dim s = &1}) +
         &(CARD {s | s IN c /\ aff_dim s = &2}) -
         &(CARD {s | s IN c /\ aff_dim s = &3})`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[complex_euler] THEN
  SUBGOAL_THEN `!k. 3 < k ==> {s:real^N->bool | s IN c /\ aff_dim s = &k} = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. dimindex(:N) < k ==> {s:real^N->bool | s IN c /\ aff_dim s = &k} = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (0..MAX (dimindex(:N)) 3)
                  (\k. --(&1) pow k * &(CARD {s:real^N->bool | s IN c /\ aff_dim s = &k}))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dimindex(:N) < k` (fun th -> ASM_SIMP_TAC[th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[CARD_CLAUSES; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (0..3)
                  (\k. --(&1) pow k * &(CARD {s:real^N->bool | s IN c /\ aff_dim s = &k}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `3 < k` (fun th -> ASM_SIMP_TAC[th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[CARD_CLAUSES; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_FTD_SUM_0_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; real_sub; REAL_ADD_AC]);;

(* k-simplices of the link of v correspond to the (k+1)-simplices at v. *)

let MOI_FTD_LINK_COUNT = prove
 (`!c (v:real^N) k.
     lf_simplicial_complex c /\ {v} IN c
     ==> CARD {e | e IN simplicial_link c v /\ aff_dim e = &k} =
         CARD {s | s IN c /\ aff_dim s = &(k + 1) /\ v IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{s | s IN c /\ aff_dim s = &(k + 1) /\ (v:real^N) IN s} =
    IMAGE (\e. convex hull (v INSERT e))
          {e | e IN simplicial_link c v /\ aff_dim e = &k}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_FM3_LINK_OPP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `aff_dim (s:real^N->bool) = &(k + 1)` THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FM3_LINK_JOIN_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `simplicial_link c (v:real^N)` THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_FINITE] THEN SET_TAC[]]);;

(* An m-simplex of a complex has m + 1 vertices in the complex. *)

let MOI_FTD_AFF_INDEP_CARD = prove
 (`!(e:real^N->bool) m.
     ~affine_dependent e /\ aff_dim (convex hull e) = &m
     ==> FINITE e /\ CARD e = m + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (e:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_IMP_FINITE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim (convex hull e:real^N->bool) = &m` THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC);;

let MOI_FTD_SIMPLEX_VERTEX_CARD = prove
 (`!c (s:real^N->bool) m.
     lf_simplicial_complex c /\ s IN c /\ aff_dim s = &m
     ==> FINITE {v | {v} IN c /\ v IN s} /\ CARD {v | {v} IN c /\ v IN s} = m + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v | {v} IN c /\ (v:real^N) IN s} = {v | v extreme_point_of s}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
      DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
        UNDISCH_TAC `(v:real^N) extreme_point_of s` THEN
        REWRITE_TAC[extreme_point_of] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP MOI_FTD_AFF_INDEP_CARD
      (CONJ (CONJUNCT1 th)
            (TRANS (AP_TERM `aff_dim:(real^N->bool)->int` (SYM (CONJUNCT2 th)))
                   (ASSUME `aff_dim (s:real^N->bool) = &m`))))) THEN
  SIMP_TAC[]);;

(* Each m-simplex has m + 1 vertices: the vertex-simplex incidences. *)

let MOI_FTD_VERTEX_INCIDENCE = prove
 (`!c:(real^N->bool)->bool m.
     FINITE c /\ lf_simplicial_complex c
     ==> nsum {v | {v} IN c} (\v. CARD {s | s IN c /\ aff_dim s = &m /\ v IN s}) =
         (m + 1) * CARD {s | s IN c /\ aff_dim s = &m}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^N | {v} IN c} /\
                FINITE {s:real^N->bool | s IN c /\ aff_dim s = &m}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(v:real^N) (s:real^N->bool). v IN s`; `{v:real^N | {v} IN c}`;
                 `{s:real^N->bool | s IN c /\ aff_dim s = &m}`] MOI_FRN_SA_DOUBLE_COUNT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {s:real^N->bool | s IN c /\ aff_dim s = &m} (\s. m + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `m:num`]
      MOI_FTD_SIMPLEX_VERTEX_CARD) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[NSUM_CONST; MULT_SYM]]);;

(* The Euler characteristic of a vertex link: 2 inside, 1 on the boundary. *)

let MOI_FTD_LINK_CHI = prove
 (`!c (v:real^N).
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c
     ==> complex_euler (simplicial_link c v) =
         if v IN complex_boundary c then &1 else &2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link c (v:real^N)` COMPLEX_EULER_VALUES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FM3_LINK_DIM_LE_2 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(v:real^N) IN complex_boundary c` THEN ASM_MESON_TAC[];
    STRIP_TAC] THEN
  ASM_CASES_TAC `(v:real^N) IN complex_boundary c` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* The Euler characteristic of a vertex link by the simplices at v. *)

let MOI_FTD_LINK_CHI_COUNT = prove
 (`!c (v:real^N).
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c
     ==> complex_euler (simplicial_link c v) =
         &(CARD {s | s IN c /\ aff_dim s = &1 /\ v IN s}) -
         &(CARD {s | s IN c /\ aff_dim s = &2 /\ v IN s}) +
         &(CARD {s | s IN c /\ aff_dim s = &3 /\ v IN s})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link c (v:real^N)` MOI_FTD_EULER_DIM3) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(INT_ARITH `(x:int) <= &2 ==> x <= &3`) THEN
    MATCH_MP_TAC MOI_FM3_LINK_DIM_LE_2 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(v:real^N) IN complex_boundary c` THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `0`] MOI_FTD_LINK_COUNT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `1`] MOI_FTD_LINK_COUNT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `2`] MOI_FTD_LINK_COUNT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `3`] MOI_FTD_LINK_COUNT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  SUBGOAL_THEN `{s | s IN c /\ aff_dim s = &4 /\ (v:real^N) IN s} = {}`
  (fun th -> REWRITE_TAC[th; CARD_CLAUSES]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `s:real^N->bool` (MATCH_MP CM_WB_DIM
      (ASSUME `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)`))) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_sub; REAL_ADD_AC]);;

(* The sum of the link Euler characteristics: 2 f1 - 3 f2 + 4 f3. *)

let MOI_FTD_LINK_SUM = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> sum {v | {v} IN c} (\v. complex_euler (simplicial_link c v)) =
         &2 * &(CARD {s | s IN c /\ aff_dim s = &1}) -
         &3 * &(CARD {s | s IN c /\ aff_dim s = &2}) +
         &4 * &(CARD {s | s IN c /\ aff_dim s = &3})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  SUBGOAL_THEN `FINITE {v:real^N | {v} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {v:real^N | {v} IN c}
      (\v. &(CARD {s | s IN c /\ aff_dim s = &1 /\ v IN s}) -
           &(CARD {s | s IN c /\ aff_dim s = &2 /\ v IN s}) +
           &(CARD {s | s IN c /\ aff_dim s = &3 /\ v IN s}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC MOI_FTD_LINK_CHI_COUNT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_SUB; GSYM REAL_OF_NUM_SUM] THEN
  ASM_SIMP_TAC[MOI_FTD_VERTEX_INCIDENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL]);;

(* The same sum by the link values: 2 per vertex, minus 1 per boundary vertex. *)

let MOI_FTD_LINK_SUM_BOUNDARY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> sum {v | {v} IN c} (\v. complex_euler (simplicial_link c v)) =
         &2 * &(CARD {v | {v} IN c}) -
         &(CARD {v | {v} IN c /\ v IN complex_boundary c})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  SUBGOAL_THEN `FINITE {v:real^N | {v} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {v:real^N | {v} IN c}
                  (\v. &2 - (if v IN complex_boundary c then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[MOI_FTD_LINK_CHI] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_CONST; GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RID] THEN REWRITE_TAC[REAL_MUL_SYM]);;

(* A 2-simplex of a combinatorial 3-manifold with boundary has one or two   *)
(* three-dimensional cofaces (the two-point or one-point link of an edge of *)
(* a vertex link).                                                           *)

let MOI_FTD_TRIANGLE_COFACES = prove
 (`!c (s:real^N->bool).
     combinatorial_manifold_with_boundary 3 c /\ s IN c /\ aff_dim s = &2
     ==> FINITE {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} /\
         1 <= CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} /\
         CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | t IN c /\ (v:real^N) IN t}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      UNDISCH_TAC `(v:real^N) IN s` THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `aff_dim (e:real^N->bool) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`; `&2:int`; `&3:int`]
    MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `convex hull ((v:real^N) INSERT e) = s`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FRN_LINK_EDGE_COFACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[]]);;

(* A 2-simplex lies in the boundary iff it has exactly one 3-coface. *)

let MOI_FTD_TRIANGLE_BOUNDARY = prove
 (`!c (s:real^N->bool).
     combinatorial_manifold_with_boundary 3 c /\ s IN c /\ aff_dim s = &2
     ==> (s SUBSET complex_boundary c <=>
          CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  EQ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN REWRITE_TAC[complex_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!(x:real^N->bool) f. x IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^N) IN relative_interior s`;
                           `(s:real^N->bool) SUBSET complex_boundary c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) = s'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(s INTER s') face_of (s:real^N->bool) /\ (s INTER s') face_of s'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER s' = (s:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `s INTER s':real^N->bool`]
      FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
    ASM_REWRITE_TAC[relative_frontier] THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^N) IN relative_interior s`; `(x:real^N) IN s'`] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1) THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* A 3-simplex has exactly four 2-dimensional faces. *)

let MOI_FTD_THREE_OF_FOUR = prove
 (`!(w:A->bool) a b c d.
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
     w SUBSET {a,b,c,d} /\ FINITE w /\ CARD w = 3
     ==> w = {b,c,d} \/ w = {a,c,d} \/ w = {a,b,d} \/ w = {a,b,c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD {a:A,b,c,d} = 4` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:A. x IN {a,b,c,d} /\ ~(x IN w)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~({a:A,b,c,d} SUBSET w)` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`{a:A,b,c,d}`; `w:A->bool`] CARD_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w = {a:A,b,c,d} DELETE x` SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN
    REWRITE_TAC[FINITE_DELETE; FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(w:A->bool) SUBSET {a,b,c,d}`; `~((x:A) IN w)`] THEN SET_TAC[];
      MP_TAC(ISPECL [`x:A`; `{a:A,b,c,d}`] CARD_DELETE) THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:A) IN {a,b,c,d}` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[DELETE_INSERT; EMPTY_DELETE]);;

let MOI_FTD_CARD_FOUR = prove
 (`!(a:A) b c d.
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> CARD {a,b,c,d} = 4 /\ CARD {b,c,d} = 3 /\ CARD {a,c,d} = 3 /\
         CARD {a,b,d} = 3 /\ CARD {a,b,c} = 3`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_FTD_SUBHULL_DIM = prove
 (`!a b c d (w:real^N->bool).
     ~affine_dependent {a,b,c,d} /\ w SUBSET {a,b,c,d}
     ==> ~affine_dependent w /\ FINITE w /\
         aff_dim (convex hull w) = &(CARD w) - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (w:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `{a:real^N,b,c,d}` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT;
                 AFFINE_INDEPENDENT_IMP_FINITE]]);;

(* One case of the four 2-faces: the hull of a 3-subset is a 2-face. *)

let MOI_FTD_FACE_CASE_TAC : tactic = fun (asl,w) ->
  let s = rand(rand(lhand(rand w))) in
  (CONJ_TAC THENL
    [EXISTS_TAC s THEN REWRITE_TAC[] THEN SET_TAC[];
     MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`; s]
       MOI_FTD_SUBHULL_DIM) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; STRIP_TAC] THEN
     ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]) (asl,w);;

let MOI_FTD_TET_FACES = prove
 (`!a b c d:real^N.
     ~affine_dependent {a,b,c,d} /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> {f | f face_of convex hull {a,b,c,d} /\ aff_dim f = &2} =
         {convex hull {b,c,d}, convex hull {a,c,d}, convex hull {a,b,d},
          convex hull {a,b,c}}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] MOI_FTD_CARD_FOUR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)
      MP_TAC) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`; `w:real^N->bool`]
      MOI_FTD_SUBHULL_DIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INT_ARITH `x - &1:int = &2 <=> x = &3`; INT_OF_NUM_EQ] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]
      MOI_FTD_THREE_OF_FOUR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC))) THEN
    MOI_FTD_FACE_CASE_TAC]);;


let MOI_FTD_HULL_INJ = prove
 (`!s t:real^N->bool.
     ~affine_dependent s /\ ~affine_dependent t /\ convex hull s = convex hull t
     ==> s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPEC `t:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_FTD_TET_FACES2 = prove
 (`!r:real^N->bool.
     &3 simplex r
     ==> FINITE {f | f face_of r /\ aff_dim f = &2} /\
         CARD {f | f face_of r /\ aff_dim f = &2} = 4`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vv:real^N->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `(&(CARD (vv:real^N->bool)):int) = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] MOI_FTD_TET_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool. s SUBSET {a,b,c,d} /\ t SUBSET {a,b,c,d} /\ ~(s = t)
                       ==> ~(convex hull s = convex hull t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] MOI_FTD_HULL_INJ) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{a:real^N,b,c,d}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(convex hull {b,c,d} = convex hull {a:real^N,c,d}) /\
    ~(convex hull {b,c,d} = convex hull {a:real^N,b,d}) /\
    ~(convex hull {b,c,d} = convex hull {a:real^N,b,c}) /\
    ~(convex hull {a,c,d} = convex hull {a:real^N,b,d}) /\
    ~(convex hull {a,c,d} = convex hull {a:real^N,b,c}) /\
    ~(convex hull {a,b,d} = convex hull {a:real^N,b,c})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
    (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The 2-simplices of c lying in a 3-simplex r of c are its four 2-faces. *)

let MOI_FTD_TET_FACES_IN = prove
 (`!c (r:real^N->bool).
     lf_simplicial_complex c /\ r IN c /\ aff_dim r = &3
     ==> FINITE {s | s IN c /\ aff_dim s = &2 /\ s SUBSET r} /\
         CARD {s | s IN c /\ aff_dim s = &2 /\ s SUBSET r} = 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 simplex (r:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    MP_TAC(ISPECL [`r:real^N->bool`; `n:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{s | s IN c /\ aff_dim s = &2 /\ s SUBSET r} =
                {f | f face_of (r:real^N->bool) /\ aff_dim f = &2}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s INTER r = (s:real^N->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `r:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]];
    MATCH_MP_TAC MOI_FTD_TET_FACES2 THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The 2-simplex-tetrahedron incidences: 4 f3 = 2 f2 - f2b. *)

let MOI_FTD_COFACE_COUNT = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> &4 * &(CARD {s | s IN c /\ aff_dim s = &3}) =
         &2 * &(CARD {s | s IN c /\ aff_dim s = &2}) -
         &(CARD {s | s IN c /\ aff_dim s = &2 /\ s SUBSET complex_boundary c})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  SUBGOAL_THEN
   `{s | s IN c /\ aff_dim s = &2 /\ s SUBSET complex_boundary c} =
    {s | s IN {s:real^N->bool | s IN c /\ aff_dim s = &2} /\ s SUBSET complex_boundary c}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `S2 = {s:real^N->bool | s IN c /\ aff_dim s = &2}` THEN
  ABBREV_TAC `S3 = {s:real^N->bool | s IN c /\ aff_dim s = &3}` THEN
  SUBGOAL_THEN `FINITE (S2:(real^N->bool)->bool) /\ FINITE (S3:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S2"; "S3"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN S3 ==> CARD {x | x IN S2 /\ x SUBSET r} = 4`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN EXPAND_TAC "S3" THEN EXPAND_TAC "S2" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FTD_TET_FACES_IN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN S2
        ==> &(CARD {y | y IN S3 /\ s SUBSET y}) =
            &2 - (if s SUBSET complex_boundary c then &1 else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN EXPAND_TAC "S3" THEN EXPAND_TAC "S2" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FTD_TRIANGLE_COFACES) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FTD_TRIANGLE_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `k = CARD {r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REAL_ARITH_TAC;
      SUBGOAL_THEN `k = 2` SUBST1_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(s:real^N->bool) (r:real^N->bool). s SUBSET r`;
                 `S2:(real^N->bool)->bool`; `S3:(real^N->bool)->bool`]
    MOI_FRN_SA_DOUBLE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nsum (S3:(real^N->bool)->bool) (\y. CARD {x | x IN S2 /\ x SUBSET y}) = CARD S3 * 4`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum (S3:(real^N->bool)->bool) (\y. 4)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[NSUM_CONST]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUM] THEN
  SUBGOAL_THEN
   `sum (S2:(real^N->bool)->bool) (\x. &(CARD {y | y IN S3 /\ x SUBSET y})) =
    sum S2 (\x. &2 - (if x SUBSET complex_boundary c then &1 else &0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_CONST; GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; GSYM REAL_OF_NUM_MUL] THEN
  ABBREV_TAC `b = CARD {s:real^N->bool | s IN S2 /\ s SUBSET complex_boundary c}` THEN
  REAL_ARITH_TAC);;

(* Faces of a simplex by dimension: an n-simplex has binom(n+1,k+1) k-faces. *)

let MOI_FTD_SUBHULL_DIM_GEN = prove
 (`!vv w:real^N->bool.
     ~affine_dependent vv /\ w SUBSET vv
     ==> ~affine_dependent w /\ FINITE w /\
         aff_dim (convex hull w) = &(CARD w) - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (w:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `vv:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT;
                 AFFINE_INDEPENDENT_IMP_FINITE]]);;

let MOI_FTD_SIMPLEX_FACES_HAS_SIZE = prove
 (`!(s:real^N->bool) n k.
     &n simplex s
     ==> {f | f face_of s /\ aff_dim f = &k} HAS_SIZE binom(n + 1,k + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `(vv:real^N->bool) HAS_SIZE (n + 1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `(&(CARD (vv:real^N->bool)):int) = &n + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{f | f face_of convex hull vv /\ aff_dim f = &k} =
    IMAGE (\w:real^N->bool. convex hull w) {w | w SUBSET vv /\ w HAS_SIZE (k + 1)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_IMAGE; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)
        MP_TAC) THEN
      MP_TAC(ISPECL [`vv:real^N->bool`; `w:real^N->bool`] MOI_FTD_SUBHULL_DIM_GEN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
      UNDISCH_TAC `&(CARD (w:real^N->bool)) - &1:int = &k` THEN
      REWRITE_TAC[INT_ARITH `x - &1:int = y <=> x = y + &1`; INT_OF_NUM_ADD;
                  INT_OF_NUM_EQ];
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`vv:real^N->bool`; `w:real^N->bool`] MOI_FTD_SUBHULL_DIM_GEN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL [EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^N->bool) HAS_SIZE (k + 1)` THEN
      SIMP_TAC[HAS_SIZE; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ASM_SIMP_TAC[HAS_SIZE_RESTRICTED_POWERSET] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FTD_HULL_INJ THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
  EXISTS_TAC `vv:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* The k-simplices of an lf complex c inside an n-simplex r of c. *)

let MOI_FTD_FACES_IN_HAS_SIZE = prove
 (`!c (r:real^N->bool) n k.
     lf_simplicial_complex c /\ r IN c /\ aff_dim r = &n
     ==> {s | s IN c /\ aff_dim s = &k /\ s SUBSET r} HAS_SIZE binom(n + 1,k + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&n simplex (r:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:int`) THEN
    MP_TAC(ISPECL [`r:real^N->bool`; `m:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{s | s IN c /\ aff_dim s = &k /\ s SUBSET r} =
                {f | f face_of (r:real^N->bool) /\ aff_dim f = &k}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s INTER r = (s:real^N->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `r:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]];
    MATCH_MP_TAC MOI_FTD_SIMPLEX_FACES_HAS_SIZE THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_FTD_TRI_EDGES_IN = prove
 (`!c (t:real^N->bool).
     lf_simplicial_complex c /\ t IN c /\ aff_dim t = &2
     ==> FINITE {e | e IN c /\ aff_dim e = &1 /\ e SUBSET t} /\
         CARD {e | e IN c /\ aff_dim e = &1 /\ e SUBSET t} = 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `2`; `1`]
    MOI_FTD_FACES_IN_HAS_SIZE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  SUBGOAL_THEN `binom(2 + 1,1 + 1) = 3` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 + 1 = SUC 2 /\ 1 + 1 = 2`; BINOM_PENULT] THEN ARITH_TAC;
    REWRITE_TAC[]]);;

(* A finite combinatorial surface: 3 f2 = 2 f1 (each edge in two triangles). *)

let MOI_FTD_SURFACE_COUNT = prove
 (`!L:(real^N->bool)->bool.
     FINITE L /\ combinatorial_manifold 2 L
     ==> 3 * CARD {t | t IN L /\ aff_dim t = &2} =
         2 * CARD {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[combinatorial_manifold]) THEN
  ABBREV_TAC `E = {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
  ABBREV_TAC `T2 = {t:real^N->bool | t IN L /\ aff_dim t = &2}` THEN
  SUBGOAL_THEN `FINITE (E:(real^N->bool)->bool) /\ FINITE (T2:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "T2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(e:real^N->bool) (t:real^N->bool). e SUBSET t`;
                 `E:(real^N->bool)->bool`; `T2:(real^N->bool)->bool`]
    MOI_FRN_SA_DOUBLE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nsum (E:(real^N->bool)->bool) (\x. CARD {y | y IN T2 /\ x SUBSET y}) = CARD E * 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum (E:(real^N->bool)->bool) (\x. 2)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[NSUM_CONST]] THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `e:real^N->bool` THEN
    EXPAND_TAC "E" THEN EXPAND_TAC "T2" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FRN_SA_CM_EDGE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum (T2:(real^N->bool)->bool) (\y. CARD {x | x IN E /\ x SUBSET y}) = CARD T2 * 3`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum (T2:(real^N->bool)->bool) (\y. 3)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[NSUM_CONST]] THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:real^N->bool` THEN
    EXPAND_TAC "E" THEN EXPAND_TAC "T2" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FTD_TRI_EDGES_IN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ARITH_TAC);;

(* Vertices as 0-simplices. *)

let MOI_FTD_VERTEX_CARD = prove
 (`!c (b:real^N->bool).
     FINITE c
     ==> CARD {s | s IN c /\ aff_dim s = &0 /\ s SUBSET b} =
         CARD {v | {v} IN c /\ v IN b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{s | s IN c /\ aff_dim s = &0 /\ s SUBSET b} =
                IMAGE (\v:real^N. {v}) {v | {v} IN c /\ v IN b}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `a:real^N` THEN
      UNDISCH_TAC `s:real^N->bool = {a}` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:real^N | {v} IN c}` THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MP_TAC(ISPECL [`\v:real^N. {v}`; `c:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[]]);;

(* Dehn-Sommerville: chi(boundary) = 2 chi for a finite combinatorial      *)
(* 3-manifold with boundary.                                               *)

let MOI_FTD_EULER_BOUNDARY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> complex_euler (boundary_complex c) = &2 * complex_euler c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (boundary_complex c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (boundary_complex c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [MATCH_MP_TAC CM_WB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN boundary_complex c ==> aff_dim s <= &3`
  ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN c /\ aff_dim s = &3 /\ s SUBSET complex_boundary c} =
    ({}:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN boundary_complex c` ASSUME_TAC THENL
     [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FRN_SA_CM_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. {s | s IN boundary_complex c /\ aff_dim s = &k} =
        {s:real^N->bool | s IN c /\ aff_dim s = &k /\ s SUBSET complex_boundary c}`
  ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `boundary_complex c:(real^N->bool)->bool` MOI_FTD_EULER_DIM3) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_EULER_DIM3) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_LINK_SUM) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_LINK_SUM_BOUNDARY) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FTD_COFACE_COUNT) THEN
  MP_TAC(ISPEC `boundary_complex c:(real^N->bool)->bool` MOI_FTD_SURFACE_COUNT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `complex_boundary c:real^N->bool`]
    MOI_FTD_VERTEX_CARD) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(:real^N)`] MOI_FTD_VERTEX_CARD) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN REWRITE_TAC[CARD_CLAUSES] THEN
  ABBREV_TAC `sl = sum {v:real^N | {v} IN c} (\v. complex_euler (simplicial_link c v))` THEN
  ABBREV_TAC `f0 = CARD {v:real^N | {v} IN c}` THEN
  ABBREV_TAC `f0b = CARD {v:real^N | {v} IN c /\ v IN complex_boundary c}` THEN
  ABBREV_TAC `g0 = CARD {s:real^N->bool | s IN c /\ aff_dim s = &0}` THEN
  ABBREV_TAC `g0b = CARD {s:real^N->bool | s IN c /\ aff_dim s = &0 /\
                                          s SUBSET complex_boundary c}` THEN
  ABBREV_TAC `f1 = CARD {s:real^N->bool | s IN c /\ aff_dim s = &1}` THEN
  ABBREV_TAC `f2 = CARD {s:real^N->bool | s IN c /\ aff_dim s = &2}` THEN
  ABBREV_TAC `f3 = CARD {s:real^N->bool | s IN c /\ aff_dim s = &3}` THEN
  ABBREV_TAC `f1b = CARD {s:real^N->bool | s IN c /\ aff_dim s = &1 /\
                                          s SUBSET complex_boundary c}` THEN
  ABBREV_TAC `f2b = CARD {s:real^N->bool | s IN c /\ aff_dim s = &2 /\
                                          s SUBSET complex_boundary c}` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

(* The statement term MOI_S30_EULER_EVEN (pc_moi_s3032_stmt.ml) is the same  *)
(* statement.                                                                *)

let EULER_EVEN = prove
 (MOI_S30_EULER_EVEN,
  ACCEPT_TAC MOI_FTD_EULER_BOUNDARY);;

(* ========================================================================= *)
(* The derived neighbourhood complex N_c of a graph is a                    *)
(* combinatorial 3-manifold with boundary, with complex boundary Bd N.      *)
(* Localisation at the closed stars S_v of the vertices of l (cones over    *)
(* 2-sphere links, hence cm_wb 3), where DERIVED_NBHD_COMBINATORIAL of      *)
(* pc_moi_fnd_rn applies; every point of N lies in an open star of a        *)
(* vertex of l.                                                              *)
(* ========================================================================= *)

let MOI_FTD_NBHD_IN_OPEN_STAR = prove
 (`!(t:(real^N->bool)->bool) l x.
     graph_in_complex t l /\ x IN derived_nbhd t l
     ==> ?v. {v} IN l /\ x IN moi_sta_open_star t v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_NBHD_UNION_CELLS] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l v` THEN
  REWRITE_TAC[derived_dual_cell; IN_INTER] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_STAR1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `s:real^N->bool`; `x:real^N`] MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `h INTER {u:real^N->bool | u face_of s} = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_bar_chain t (h:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN u` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `{v:real^N}`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(u:real^N->bool = {})` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]]);;

(* The closed star of a vertex of l is a 3-ball triangulation. *)

let MOI_FTD_STAR_CMWB = prove
 (`!(t:(real^N->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l
     ==> FINITE (moi_fta_cstar t v) /\
         combinatorial_manifold_with_boundary 3 (moi_fta_cstar t v) /\
         simplicial_subcomplex (moi_fta_cstar t v) t /\
         simplicial_subcomplex (l INTER moi_fta_cstar t v) (moi_fta_cstar t v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_CSTAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`moi_fta_cstar t (v:real^N)`;
                   `UNIONS (simplicial_link t (v:real^N))`]
      PL_BALL_TRIANGULATION_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MOI_FTA_STAR_CELL THEN ASM_SIMP_TAC[];
      SIMP_TAC[]];
    REWRITE_TAC[simplicial_subcomplex; INTER_SUBSET; IN_INTER] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex];
      UNDISCH_TAC `simplicial_subcomplex (moi_fta_cstar t (v:real^N)) t` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM_MESON_TAC[]]]);;

(* Simplices of a barycentric subdivision inside a subcomplex. *)

let MOI_FTD_SD_RESTRICT = prove
 (`!(c:(real^N->bool)->bool) m r.
     moi_bar_complex c /\ simplicial_subcomplex m c /\
     r IN barycentric_subdivision c /\ r SUBSET UNIONS m
     ==> r IN barycentric_subdivision m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
       ASSUME_TAC))) THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET c` THEN
    UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[];
    ASM_MESON_TAC[];
    UNDISCH_TAC `r SUBSET UNIONS (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]);;

let MOI_FTD_SD2_RESTRICT = prove
 (`!(t:(real^N->bool)->bool) m r.
     lf_simplicial_complex t /\ simplicial_subcomplex m t /\
     r IN barycentric_subdivision (barycentric_subdivision t) /\ r SUBSET UNIONS m
     ==> r IN barycentric_subdivision (barycentric_subdivision m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `m:(real^N->bool)->bool`] MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FTD_SD_RESTRICT THEN
  EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_FTA_BS_FACTS]);;

let MOI_FTD_NBHD_MONO = prove
 (`!(t:(real^N->bool)->bool) l m l'.
     lf_simplicial_complex t /\ simplicial_subcomplex m t /\ l' SUBSET l
     ==> derived_nbhd_complex m l' SUBSET derived_nbhd_complex t l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `barycentric_subdivision (barycentric_subdivision m) SUBSET
                barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `m:(real^N->bool)->bool`] MOI_FTA_SUB_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `barycentric_subdivision m:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd_complex; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m)` THEN
    UNDISCH_TAC `barycentric_subdivision (barycentric_subdivision m) SUBSET
                barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    SET_TAC[];
    UNDISCH_TAC `~(r INTER UNIONS l' = {}:real^N->bool)` THEN
    UNDISCH_TAC `(l':(real^N->bool)->bool) SUBSET l` THEN SET_TAC[]]);;

(* A simplex of N_c through a point of the open star of v lies in the      *)
(* derived neighbourhood complex of l INTER S_v in S_v.                    *)

let MOI_FTD_NBHD_LOCAL = prove
 (`!(t:(real^N->bool)->bool) l v rho x.
     graph_in_complex t l /\ {v} IN l /\
     rho IN derived_nbhd_complex t l /\ x IN rho /\ x IN moi_sta_open_star t v
     ==> rho IN derived_nbhd_complex (moi_fta_cstar t v) (l INTER moi_fta_cstar t v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTD_STAR_CMWB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(rho:real^N->bool) IN derived_nbhd_complex t l` THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN t /\ r SUBSET s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision t:(real^N->bool)->bool`
      BARYCENTRIC_SUBDIVISION_REFINES) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^N) IN r` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `t:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(r:real^N->bool) SUBSET q` THEN UNDISCH_TAC `(x:real^N) IN r` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:real^N->bool) SUBSET q` THEN
    UNDISCH_TAC `(q:real^N->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_sta_open_star t v` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:real^N->bool) SUBSET s` THEN UNDISCH_TAC `(x:real^N) IN r` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN moi_fta_cstar t v` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTD_SD2_RESTRICT THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_fta_cstar t v` THEN
    UNDISCH_TAC `(r:real^N->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(r INTER UNIONS l = {}:real^N->bool)` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `lam:real^N->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `s INTER lam:real^N->bool` THEN
  SUBGOAL_THEN `(s INTER lam:real^N->bool) face_of s /\ (s INTER lam) face_of lam`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex];
    REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(r:real^N->bool) SUBSET s` THEN UNDISCH_TAC `(y:real^N) IN r` THEN
    UNDISCH_TAC `(y:real^N) IN lam` THEN SET_TAC[]]);;

(* Links agree when two complexes have the same simplices through w. *)

let MOI_FTD_LINK_EQ = prove
 (`!(c1:(real^N->bool)->bool) c2 w.
     c1 SUBSET c2 /\ (!s. s IN c2 /\ w IN s ==> s IN c1) /\
     (!s f. s IN c1 /\ f face_of s ==> f IN c1)
     ==> simplicial_link c1 w = simplicial_link c2 w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_link] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]);;

let MOI_FTD_NBHD_CMWB = prove
 (`!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FDN_DERIVED_NBHD_COMPLEX_LF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN derived_nbhd t l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `UNIONS (derived_nbhd_complex t l) =
                 derived_nbhd t (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `w:real^N`]
    MOI_FTD_NBHD_IN_OPEN_STAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTD_STAR_CMWB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simplicial_link (derived_nbhd_complex (moi_fta_cstar t v)
                       (l INTER moi_fta_cstar t v)) w =
    simplicial_link (derived_nbhd_complex t l) (w:real^N)`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC MOI_FTD_LINK_EQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTD_NBHD_MONO THEN ASM_REWRITE_TAC[INTER_SUBSET];
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FTD_NBHD_LOCAL THEN EXISTS_TAC `w:real^N` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_TRANS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fta_cstar t (v:real^N)`; `l INTER moi_fta_cstar t (v:real^N)`]
    DERIVED_NBHD_COMBINATORIAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC MOI_FTD_NBHD_LOCAL THEN EXISTS_TAC `w:real^N` THEN
  ASM_REWRITE_TAC[IN_SING]);;

(* Every point of N is a manifold point of UNIONS t. *)

let MOI_FTD_NBHD_MINT = prove
 (`!(t:(real^N->bool)->bool) l x.
     graph_in_complex t l /\ x IN derived_nbhd t l
     ==> moi_fmb_mint (UNIONS t) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_NBHD_IN_OPEN_STAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FMB_STAR_SPHERE_CHART) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `q:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_fmb_mint] THEN
  MAP_EVERY EXISTS_TAC [`moi_sta_open_star t (v:real^N)`;
                        `IMAGE (p:real^N->real^3) (moi_sta_open_star t v)`] THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
  REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->real^3`; `q:real^3->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* The complex boundary of N_c is the frontier of N in UNIONS t (the        *)
(* argument of MOI_FRN_NBHD_BOUNDARY, with every point of N interior).     *)

let MOI_FTD_NBHD_BOUNDARY = prove
 (`!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> complex_boundary (derived_nbhd_complex t l) = derived_frontier t l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTD_NBHD_CMWB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN derived_nbhd t l` THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `derived_nbhd_complex t l:(real^N->bool)->bool`
        MOI_FMB_CB_SUBSET) THEN ASM_REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS t):(real^N)topology`;
                     `derived_nbhd t l:real^N->bool`]
        FRONTIER_OF_SUBSET_CLOSED_IN) THEN
      ASM_REWRITE_TAC[derived_frontier; SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS t` ASSUME_TAC THENL
   [UNDISCH_TAC `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_nbhd_complex t l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FMB_MINT_CB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN derived_frontier t l <=>
    ~(?u. open_in (subtopology euclidean (UNIONS t)) u /\ x IN u /\
          u SUBSET derived_nbhd t l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF; interior_of;
                IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS t):(real^N)topology`;
                   `derived_nbhd t l:real^N->bool`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS t) (x:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTD_NBHD_MINT THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_MINT_INTERIOR THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_MINT_MONO THEN
    MAP_EVERY EXISTS_TAC [`UNIONS t:real^N->bool`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* chi(N_c) = chi(l) for a finite subcomplex l of an lf complex t.          *)
(* Simplices of N_c are the hulls H g of chains g of c = sd t that extend   *)
(* by a simplex of k = sd l; those of l'' = sd k are the chains in k.  On   *)
(* the other chains the map g -> g symdiff {F g}, F g the trace on UNIONS l *)
(* of the least element of g outside k, is an involution changing CARD g    *)
(* by one, so their signed count vanishes.                                   *)
(* ========================================================================= *)

let MOI_FTD_SUM_INVOLUTION = prove
 (`!(f:A->real) i s.
     FINITE s /\
     (!x. x IN s ==> i x IN s /\ i (i x) = x /\ f (i x) = --(f x))
     ==> sum s f = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `i:A->A`; `s:A->bool`] SUM_BIJECTION) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `(i:A->A) y` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum s ((f:A->real) o i) = sum s (\x. --(f x))` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  REWRITE_TAC[SUM_NEG] THEN REAL_ARITH_TAC);;

let MOI_FTD_POW_PRED = prove
 (`!n. 1 <= n ==> (-- &1) pow (n - 1) = --((-- &1) pow n)`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; SUC_SUB1; real_pow] THEN REAL_ARITH_TAC);;

let MOI_FTD_CHAIN_SIGN = prove
 (`!(c:(real^N->bool)->bool) g.
     moi_bar_complex c /\ moi_bar_chain c g /\ ~(g = {})
     ==> (-- &1) pow (num_of_int (aff_dim (convex hull (IMAGE simplex_barycentre g)))) =
         --((-- &1) pow (CARD g))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  SUBGOAL_THEN `CARD (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) = CARD g`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_BARYCENTRE_INJ]; ASM_MESON_TAC[moi_bar_chain]];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= CARD (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_MESON_TAC[CARD_EQ_0; moi_bar_chain];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; NUM_OF_INT_OF_NUM; MOI_FTD_POW_PRED]);;

(* Simplices of N_c as hulls of extendable chains of the first derived. *)

let MOI_FTD_NC_CHAINS = prove
 (`!(t:(real^N->bool)->bool) l rho.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (rho IN derived_nbhd_complex t l <=>
          ?g. moi_bar_chain (barycentric_subdivision t) g /\
              (?m. m IN barycentric_subdivision l /\
                   moi_bar_chain (barycentric_subdivision t) (m INSERT g)) /\
              rho = convex hull (IMAGE simplex_barycentre g))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FRN_IN_NBHD_COMPLEX] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) MP_TAC))) THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{s:real^N->bool | s IN f /\ simplex_barycentre s IN w}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `w SUBSET IMAGE simplex_barycentre (f:(real^N->bool)->bool)` THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) SUBST1_TAC))) THEN
    EXISTS_TAC `(m:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[IN_INSERT];
      MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                     `(m:real^N->bool) INSERT g`] MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `IMAGE simplex_barycentre (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[] THEN SET_TAC[]]]);;

(* The involution. *)

let moi_ftd_tf = new_definition
 `moi_ftd_tf (k:(real^N->bool)->bool) (u:real^N->bool) (g:(real^N->bool)->bool) =
    INTERS (g DIFF k) INTER u`;;

let moi_ftd_inv = new_definition
 `moi_ftd_inv (k:(real^N->bool)->bool) (u:real^N->bool) (g:(real^N->bool)->bool) =
    if moi_ftd_tf k u g IN g then g DELETE moi_ftd_tf k u g
    else moi_ftd_tf k u g INSERT g`;;

let moi_ftd_gp = new_definition
 `moi_ftd_gp (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    {g | moi_bar_chain (barycentric_subdivision t) g /\
         ~(g SUBSET barycentric_subdivision l) /\
         ?m. m IN barycentric_subdivision l /\
             moi_bar_chain (barycentric_subdivision t) (m INSERT g)}`;;

let MOI_FTD_TF_EQ = prove
 (`!k u (g:(real^N->bool)->bool) h.
     h DIFF k = g DIFF k ==> moi_ftd_tf k u h = moi_ftd_tf k u g`,
  SIMP_TAC[moi_ftd_tf]);;

let MOI_FTD_CHAIN_INSERT = prove
 (`!c g (x:real^N->bool).
     moi_bar_chain c g /\ x IN c /\ ~(x = {}) /\
     (!e. e IN g ==> e SUBSET x \/ x SUBSET e)
     ==> moi_bar_chain c (x INSERT g)`,
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_REFL]);;

let MOI_FTD_GP_FACTS = prove
 (`!(t:(real^N->bool)->bool) l g m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) g /\
     ~(g SUBSET barycentric_subdivision l) /\
     m IN barycentric_subdivision l /\
     moi_bar_chain (barycentric_subdivision t) (m INSERT g)
     ==> INTERS (g DIFF barycentric_subdivision l) IN g /\
         ~(INTERS (g DIFF barycentric_subdivision l) IN barycentric_subdivision l) /\
         moi_ftd_tf (barycentric_subdivision l) (UNIONS l) g IN
           barycentric_subdivision l /\
         ~(moi_ftd_tf (barycentric_subdivision l) (UNIONS l) g = {}) /\
         moi_bar_chain (barycentric_subdivision t)
           (moi_ftd_tf (barycentric_subdivision l) (UNIONS l) g INSERT g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_bar_chain (barycentric_subdivision t) (g DIFF barycentric_subdivision l) /\
    ~(g DIFF barycentric_subdivision l = {}:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC `~(g SUBSET barycentric_subdivision (l:(real^N->bool)->bool))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g DIFF barycentric_subdivision l:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0 = INTERS (g DIFF barycentric_subdivision l:(real^N->bool)->bool)` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_ftd_tf] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:(real^N->bool)->bool) SUBSET barycentric_subdivision t /\ FINITE g /\
                ~({} IN g) /\
                (!s s'. s IN g /\ s' IN g ==> s SUBSET s' \/ s' SUBSET s)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `(m0:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN barycentric_subdivision l /\ e IN barycentric_subdivision t /\
                     (e SUBSET m0 \/ m0 SUBSET e) ==> e SUBSET m0`
  (LABEL_TAC "below") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((m0:real^N->bool) IN barycentric_subdivision l)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m0 = m0 INTER (e:real^N->bool)` SUBST1_TAC THENL
     [UNDISCH_TAC `(m0:real^N->bool) SUBSET e` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`m0:real^N->bool`; `e:real^N->bool`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET m0 /\ ~(m = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) ((m:real^N->bool) INSERT g)` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; IN_INSERT] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (barycentric_subdivision l) SUBSET UNIONS (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS (barycentric_subdivision l) SUBSET UNIONS (l:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision l` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `m0 INTER UNIONS l IN barycentric_subdivision (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `m0:real^N->bool`]
      MOI_FRN_FULL) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m0 INTER UNIONS l:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(m:real^N->bool = {})` THEN UNDISCH_TAC `(m:real^N->bool) SUBSET m0` THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET UNIONS l` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN g ==> e SUBSET m0 INTER UNIONS l \/ m0 INTER UNIONS l SUBSET e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(e:real^N->bool) IN barycentric_subdivision l` THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `(e:real^N->bool) SUBSET m0` ASSUME_TAC THENL
       [USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `UNIONS (barycentric_subdivision l) SUBSET UNIONS (l:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(e:real^N->bool) IN barycentric_subdivision l` THEN
      UNDISCH_TAC `(e:real^N->bool) SUBSET m0` THEN SET_TAC[];
      DISJ2_TAC THEN
      SUBGOAL_THEN `(m0:real^N->bool) SUBSET e` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `m0:real^N->bool`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTD_CHAIN_INSERT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                 (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
  REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let MOI_FTD_INVOL = prove
 (`!(t:(real^N->bool)->bool) l g.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ g IN moi_ftd_gp t l
     ==> moi_ftd_inv (barycentric_subdivision l) (UNIONS l) g IN moi_ftd_gp t l /\
         moi_ftd_inv (barycentric_subdivision l) (UNIONS l)
           (moi_ftd_inv (barycentric_subdivision l) (UNIONS l) g) = g /\
         (-- &1) pow (CARD (moi_ftd_inv (barycentric_subdivision l) (UNIONS l) g)) =
         --((-- &1) pow (CARD g))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[moi_ftd_gp; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`; `m:real^N->bool`] MOI_FTD_GP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `fz = moi_ftd_tf (barycentric_subdivision l) (UNIONS l)
                     (g:(real^N->bool)->bool)` THEN
  ABBREV_TAC `m0 = INTERS (g DIFF barycentric_subdivision l:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `~((m0:real^N->bool) = fz)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_ftd_inv] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(fz:real^N->bool) IN g` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `moi_ftd_tf (barycentric_subdivision l) (UNIONS l)
                   (g DELETE (fz:real^N->bool)) = fz` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `moi_ftd_tf (barycentric_subdivision l) (UNIONS l)
                    (g:(real^N->bool)->bool)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC MOI_FTD_TF_EQ THEN
      UNDISCH_TAC `(fz:real^N->bool) IN barycentric_subdivision l` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[INSERT_DELETE; CARD_DELETE] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[DELETE_SUBSET];
      REWRITE_TAC[SUBSET; IN_DELETE] THEN DISCH_THEN(MP_TAC o SPEC `m0:real^N->bool`) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `fz:real^N->bool` THEN ASM_SIMP_TAC[INSERT_DELETE];
      MATCH_MP_TAC MOI_FTD_POW_PRED THEN
      MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
      UNDISCH_TAC `(fz:real^N->bool) IN g` THEN SET_TAC[]];
    SUBGOAL_THEN `moi_ftd_tf (barycentric_subdivision l) (UNIONS l)
                   ((fz:real^N->bool) INSERT g) = fz` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `moi_ftd_tf (barycentric_subdivision l) (UNIONS l)
                    (g:(real^N->bool)->bool)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC MOI_FTD_TF_EQ THEN
      UNDISCH_TAC `(fz:real^N->bool) IN barycentric_subdivision l` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_SIMP_TAC[SET_RULE `~((x:real^N->bool) IN s) ==> (x INSERT s) DELETE x = s`;
                 CARD_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT] THEN DISCH_THEN(MP_TAC o SPEC `m0:real^N->bool`) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `fz:real^N->bool` THEN
      ASM_REWRITE_TAC[SET_RULE `(x:real^N->bool) INSERT x INSERT s = x INSERT s`];
      REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC]]);;

(* chi(N_c) = chi(l). *)

let MOI_FTD_NBHD_EULER = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l
     ==> complex_euler (derived_nbhd_complex t l) = complex_euler l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN
    ASM_MESON_TAC[MOI_FTA_SUB_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision
                  (barycentric_subdivision l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (barycentric_subdivision
                  (barycentric_subdivision l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (barycentric_subdivision (barycentric_subdivision l)) =
                complex_euler (l:(real^N->bool)->bool)` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_SAME_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION];
    ALL_TAC] THEN
  SUBGOAL_THEN `barycentric_subdivision l SUBSET
                barycentric_subdivision (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. moi_bar_chain (barycentric_subdivision l) g <=>
        moi_bar_chain (barycentric_subdivision t) g /\
        g SUBSET barycentric_subdivision (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g g'. moi_bar_chain (barycentric_subdivision t) g /\
           moi_bar_chain (barycentric_subdivision t) g' /\
           convex hull (IMAGE simplex_barycentre g) =
           convex hull (IMAGE simplex_barycentre g')
           ==> g = (g':(real^N->bool)->bool)`
  (LABEL_TAC "hinj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_HULL_INJ THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN barycentric_subdivision (barycentric_subdivision l) /\ ~(s = {})} SUBSET
    {s:real^N->bool | s IN derived_nbhd_complex t l /\ ~(s = {})}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `rho:real^N->bool` THEN
    ASM_SIMP_TAC[MOI_FTD_NC_CHAINS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:(real^N->bool)->bool`
      STRIP_ASSUME_TAC o REWRITE_RULE[MOI_BAR_IN_SUBDIVISION]) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool) /\
                  g SUBSET barycentric_subdivision l` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision l) (g:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(rho:real^N->bool = {})` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `UNIONS g:real^N->bool` THEN
    ASM_SIMP_TAC[SET_RULE `(x:real^N->bool) IN s ==> x INSERT s = s`] THEN
    UNDISCH_TAC `(g:(real^N->bool)->bool) SUBSET barycentric_subdivision l` THEN
    UNDISCH_TAC `(UNIONS g:real^N->bool) IN g` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN derived_nbhd_complex t l /\ ~(s = {})} DIFF
    {s | s IN barycentric_subdivision (barycentric_subdivision l) /\ ~(s = {})} =
    IMAGE (\g. convex hull (IMAGE simplex_barycentre g)) (moi_ftd_gp t l)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `rho:real^N->bool` THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_IMAGE; moi_ftd_gp] THEN
    ASM_SIMP_TAC[MOI_FTD_NC_CHAINS] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `~(convex hull (IMAGE simplex_barycentre g) IN
                       barycentric_subdivision
                         (barycentric_subdivision (l:(real^N->bool)->bool)))` THEN
        REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` (CONJUNCTS_THEN2 SUBST1_TAC
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `~(convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) = {})`
      ASSUME_TAC THENL
       [UNDISCH_TAC `~(g SUBSET barycentric_subdivision (l:(real^N->bool)->bool))` THEN
        REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        DISCH_THEN(X_CHOOSE_THEN `g':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `~(g SUBSET barycentric_subdivision (l:(real^N->bool)->bool))` THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g':(real^N->bool)->bool) /\
                      g' SUBSET barycentric_subdivision l` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision l) (g':(real^N->bool)->bool)` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `g = (g':(real^N->bool)->bool)` (fun th -> ASM_REWRITE_TAC[th]) THEN
        USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN moi_ftd_gp t l /\ y IN moi_ftd_gp t l /\
          (\g. convex hull (IMAGE simplex_barycentre g)) x =
          (\g. convex hull (IMAGE simplex_barycentre g)) y
          ==> x = (y:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftd_gp; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (moi_ftd_gp (t:(real^N->bool)->bool) l)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\g:(real^N->bool)->bool. convex hull (IMAGE simplex_barycentre g)`;
                   `moi_ftd_gp (t:(real^N->bool)->bool) l`] FINITE_IMAGE_INJ_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `{s:real^N->bool | s IN derived_nbhd_complex t l /\ ~(s = {})} DIFF
      {s | s IN barycentric_subdivision (barycentric_subdivision l) /\ ~(s = {})} =
      IMAGE (\g. convex hull (IMAGE simplex_barycentre g)) (moi_ftd_gp t l)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FINITE_DIFF THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (IMAGE (\g. convex hull (IMAGE simplex_barycentre g)) (moi_ftd_gp t l))
        (\s:real^N->bool. (-- &1) pow (num_of_int (aff_dim s))) = &0`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum (moi_ftd_gp (t:(real^N->bool)->bool) l)
                    (\g. --((-- &1) pow (CARD g)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[moi_ftd_gp; IN_ELIM_THM] THEN
      X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC MOI_FTD_CHAIN_SIGN THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(g SUBSET barycentric_subdivision (l:(real^N->bool)->bool))` THEN
      SET_TAC[];
      REWRITE_TAC[SUM_NEG; REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC MOI_FTD_SUM_INVOLUTION THEN
      EXISTS_TAC `moi_ftd_inv (barycentric_subdivision l)
                    (UNIONS (l:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:(real^N->bool)->bool` THEN DISCH_TAC THEN
      BETA_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:(real^N->bool)->bool`] MOI_FTD_INVOL) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^N->bool. (-- &1) pow (num_of_int (aff_dim s))`;
                 `{s:real^N->bool | s IN derived_nbhd_complex t l /\ ~(s = {})}`;
                 `{s:real^N->bool | s IN barycentric_subdivision
                                      (barycentric_subdivision l) /\ ~(s = {})}`]
    SUM_DIFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `derived_nbhd_complex t (l:(real^N->bool)->bool)`
    MOI_FEU_COMPLEX_EULER_SUM) THEN
  MP_TAC(ISPEC `barycentric_subdivision (barycentric_subdivision (l:(real^N->bool)->bool))`
    MOI_FEU_COMPLEX_EULER_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `a = sum {s:real^N->bool | s IN derived_nbhd_complex t l /\ ~(s = {})}
                      (\s. (-- &1) pow (num_of_int (aff_dim s)))` THEN
  ABBREV_TAC `b = sum {s:real^N->bool | s IN barycentric_subdivision
                                          (barycentric_subdivision l) /\ ~(s = {})}
                      (\s. (-- &1) pow (num_of_int (aff_dim s)))` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The theorem GRAPH_NBHD_BOUNDARY_EULER (Moise 33.1 Lemma 12,              *)
(* p.236): N_c is a combinatorial 3-manifold with boundary Bd N, and        *)
(* chi(Bd N) = 2 chi(N_c) = 2 chi(l).                                        *)
(* ========================================================================= *)

let GRAPH_NBHD_BOUNDARY_EULER = prove
 (MOI_FND_GRAPH_NBHD_EULER,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
                  (derived_nbhd_complex t (l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTD_NBHD_CMWB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTD_NBHD_BOUNDARY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `complex_euler (l:(real^N->bool)->bool) =
                complex_euler (derived_nbhd_complex t l)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTD_NBHD_EULER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTD_EULER_BOUNDARY THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Barycentric coordinates. Simplex coordinates moi_ftd_bc, the same as      *)
(* moi_s4a_bc of pc_moi_s34_scella (with the lemma names changed from        *)
(* MOI_S4A to MOI_FTD), which this file does not load. Then the coordinates  *)
(* moi_ftd_lc of a point in a simplex (0 off its vertices), their            *)
(* compatibility with faces, and global coordinates moi_ftd_co on a complex. *)
(* ========================================================================= *)

let moi_ftd_bc = new_definition
 `moi_ftd_bc (V:real^N->bool) (a:real^N) =
    @f:real^N->real. (?w k. !x. f x = w dot x + k) /\
                     (!b. b IN V ==> f b = if b = a then &1 else &0)`;;

let MOI_FTD_BC_EXISTS = prove
 (`!(V:real^N->bool) (a:real^N).
     ~affine_dependent V
     ==> ?w k. !b. b IN V ==> w dot b + k = if b = a then &1 else &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`;
                 `\b:real^N. if b = a then vec 1:real^1 else vec 0`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[LINEAR_TO_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^1` (X_CHOOSE_THEN `y:real^1`
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:real^N`) ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)))) THEN
  MAP_EVERY EXISTS_TAC [`w:real^N`; `drop y`] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC]);;

let MOI_FTD_BC = prove
 (`!(V:real^N->bool) (a:real^N).
     ~affine_dependent V
     ==> (?w k. !x. moi_ftd_bc V a x = w dot x + k) /\
         (!b. b IN V ==> moi_ftd_bc V a b = if b = a then &1 else &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    SPEC `a:real^N` o MATCH_MP MOI_FTD_BC_EXISTS) THEN
  SUBGOAL_THEN
   `?f:real^N->real. (?w k. !x. f x = w dot x + k) /\
                     (!b. b IN V ==> f b = if b = (a:real^N) then &1 else &0)`
  MP_TAC THENL
   [EXISTS_TAC `\x:real^N. (w:real^N) dot x + k` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`w:real^N`; `k:real`] THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM moi_ftd_bc]]);;

(* Dot forms of all coordinates at once. *)

let MOI_FTD_BC_DOT = prove
 (`!(V:real^N->bool).
     ~affine_dependent V
     ==> ?w k. !a x. a IN V ==> moi_ftd_bc V a x = w a dot x + k a`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. ?w k. a IN V ==> !x. moi_ftd_bc V a x = w dot x + k`
  MP_TAC THENL
   [X_GEN_TAC `a:real^N` THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`] MOI_FTD_BC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[]]);;

let MOI_FTD_BC_AFFINE = prove
 (`!(V:real^N->bool) a x y u.
     ~affine_dependent V
     ==> moi_ftd_bc V a ((&1 - u) % x + u % y) =
         (&1 - u) * moi_ftd_bc V a x + u * moi_ftd_bc V a y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    CONJUNCT1 o SPEC `a:real^N` o MATCH_MP MOI_FTD_BC) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* The coordinates of an affine combination of the points of V.            *)

let MOI_FTD_BC_AFF = prove
 (`!(V:real^N->bool) (u:real^N->real) a.
     ~affine_dependent V /\ a IN V /\ sum V u = &1
     ==> moi_ftd_bc V a (vsum V (\v. u v % v)) = u a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^N` o MATCH_MP MOI_FTD_BC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`))
    (LABEL_TAC "val")) THEN
  SUBGOAL_THEN
   `!v:real^N. v IN V ==> (w:real^N) dot v + k = if v = a then &1 else &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DOT_RSUM; DOT_RMUL] THEN
  SUBGOAL_THEN
   `sum V (\v:real^N. (u:real^N->real) v * ((w:real^N) dot v)) + k =
    sum V (\v. u v * (w dot v + k))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ADD_LDISTRIB; SUM_ADD; SUM_RMUL] THEN
    REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum V (\v:real^N. (u:real^N->real) v * ((w:real^N) dot v + k)) =
    sum V (\v. if v = a then u a else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_DELTA]]);;

let MOI_FTD_BC_VSUM = prove
 (`!(V:real^N->bool) a (s:real^N->bool) (u:real^N->real).
     ~affine_dependent V /\ FINITE s /\ sum s u = &1
     ==> moi_ftd_bc V a (vsum s (\y. u y % y)) =
         sum s (\y. u y * moi_ftd_bc V a y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    CONJUNCT1 o SPEC `a:real^N` o MATCH_MP MOI_FTD_BC) THEN
  ASM_SIMP_TAC[DOT_RSUM; DOT_RMUL; REAL_ADD_LDISTRIB; SUM_ADD; SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Coordinates of a point in a simplex s at the points v (0 unless v is a    *)
(* vertex of s).                                                             *)
(* ------------------------------------------------------------------------- *)

let moi_ftd_lc = new_definition
 `moi_ftd_lc (s:real^N->bool) (x:real^N) (v:real^N) =
    if v extreme_point_of s then moi_ftd_bc {w | w extreme_point_of s} v x else &0`;;

let MOI_FTD_LC_UNIQUE = prove
 (`!(s:real^N->bool) x u.
     (?n. n simplex s) /\
     sum {v | v extreme_point_of s} u = &1 /\
     vsum {v | v extreme_point_of s} (\v. u v % v) = x
     ==> !v. v extreme_point_of s ==> moi_ftd_lc s x v = u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[moi_ftd_lc] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq (concl th) && rhs (concl th) = `x:real^N`)) THEN
  MATCH_MP_TAC MOI_FTD_BC_AFF THEN ASM_REWRITE_TAC[IN_ELIM_THM]);;

let MOI_FTD_LC_REP = prove
 (`!(s:real^N->bool) x.
     (?n. n simplex s) /\ x IN s
     ==> (!v. &0 <= moi_ftd_lc s x v) /\
         (!v. ~(v extreme_point_of s) ==> moi_ftd_lc s x v = &0) /\
         sum {v | v extreme_point_of s} (moi_ftd_lc s x) = &1 /\
         vsum {v | v extreme_point_of s} (\v. moi_ftd_lc s x v % v) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of s}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?u. (!v:real^N. v IN {v | v extreme_point_of s} ==> &0 <= u v) /\
        sum {v | v extreme_point_of s} u = &1 /\
        vsum {v | v extreme_point_of s} (\v. u v % v) = x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `{v:real^N | v extreme_point_of s}` CONVEX_HULL_FINITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\a:real^N->bool. (x:real^N) IN a`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `u:real^N->real`] MOI_FTD_LC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!v:real^N. ~(v extreme_point_of s) ==> moi_ftd_lc s x v = &0`
  ASSUME_TAC THENL [SIMP_TAC[moi_ftd_lc]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `(v:real^N) extreme_point_of s` THENL
     [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_SIMP_TAC[REAL_LE_REFL]];
    TRANS_TAC EQ_TRANS `sum {v:real^N | v extreme_point_of s} u` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[]];
    TRANS_TAC EQ_TRANS `vsum {v:real^N | v extreme_point_of s} (\v. u v % v)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[]]]);;

(* Coordinates in a face agree with those in the simplex. *)

let MOI_FTD_LC_FACE = prove
 (`!(s:real^N->bool) f x.
     (?n. n simplex s) /\ f face_of s /\ x IN f
     ==> !v. moi_ftd_lc s x v = moi_ftd_lc f x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?m. m simplex (f:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_FACE_OF_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of f} SUBSET {v | v extreme_point_of s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of s}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->bool`; `x:real^N`] MOI_FTD_LC_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `moi_ftd_lc (f:real^N->bool) x`]
    MOI_FTD_LC_UNIQUE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS `sum {v:real^N | v extreme_point_of f} (moi_ftd_lc f x)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      TRANS_TAC EQ_TRANS
       `vsum {v:real^N | v extreme_point_of f} (\v. moi_ftd_lc f x v % v)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `v:real^N` THEN
  ASM_CASES_TAC `(v:real^N) extreme_point_of s` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `~((v:real^N) extreme_point_of f)` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  ASM_SIMP_TAC[moi_ftd_lc]);;

let MOI_FTD_LC_CONT = prove
 (`!(s:real^N->bool) v t.
     (?n. n simplex s) ==> (lift o (\x. moi_ftd_lc s x v)) continuous_on t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_ftd_lc] THEN
  ASM_CASES_TAC `(v:real^N) extreme_point_of s` THEN
  ASM_REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST] THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`{w:real^N | w extreme_point_of s}`; `v:real^N`] MOI_FTD_BC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT]);;

(* ------------------------------------------------------------------------- *)
(* Global coordinates on a complex.                                          *)
(* ------------------------------------------------------------------------- *)

let moi_ftd_co = new_definition
 `moi_ftd_co (c:(real^N->bool)->bool) (x:real^N) (v:real^N) =
    moi_ftd_lc (@s. s IN c /\ x IN s) x v`;;

let MOI_FTD_CO_LOCAL = prove
 (`!(c:(real^N->bool)->bool) s x.
     moi_bar_complex c /\ s IN c /\ x IN s
     ==> !v. moi_ftd_co c x v = moi_ftd_lc s x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftd_co] THEN
  ABBREV_TAC `s0 = @s:real^N->bool. s IN c /\ x IN s` THEN
  SUBGOAL_THEN `(s0:real^N->bool) IN c /\ x IN s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER s0:real^N->bool) face_of s /\ (s INTER s0) face_of s0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s INTER s0:real^N->bool`; `x:real^N`]
    MOI_FTD_LC_FACE) THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `s INTER s0:real^N->bool`; `x:real^N`]
    MOI_FTD_LC_FACE) THEN
  ASM_SIMP_TAC[IN_INTER]);;

(* A convex combination of the vertices of a simplex of c: its global      *)
(* coordinates.                                                              *)

let MOI_FTD_CO_REP = prove
 (`!(c:(real^N->bool)->bool) s x u.
     moi_bar_complex c /\ s IN c /\
     (!v. v extreme_point_of s ==> &0 <= u v) /\
     sum {v | v extreme_point_of s} u = &1 /\
     vsum {v | v extreme_point_of s} (\v. u v % v) = x
     ==> x IN s /\
         !v. moi_ftd_co c x v = if v extreme_point_of s then u v else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of s}` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
    MOI_FTD_CO_LOCAL) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `u:real^N->real`] MOI_FTD_LC_UNIQUE) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[moi_ftd_lc]]);;

(* ========================================================================= *)
(* The global functions of the product structure on the first              *)
(* derived c = sd t, with u = UNIONS l: the weight pw and the part pp of a  *)
(* point at the vertices in u, and the largest coordinates mf (at vertices  *)
(* in u) and mg (at the others).  N = {mg <= mf}, UNIONS l = {mg = 0},      *)
(* Bd N = {mf = mg}.  The pasting lemma MOI_FTD_PASTE is MOI_S3CL_PASTE of  *)
(* pc_moi_s32_cell, which this file does not load.                          *)
(* ========================================================================= *)

let MOI_FTD_PASTE = prove
 (`!(f:K->real^M->real^N) g t k s.
     (!x. x IN s ==> ?u. open u /\ x IN u /\ FINITE {i | i IN k /\ ~(t i INTER u = {})}) /\
     (!i. i IN k ==> closed_in (subtopology euclidean s) (t i) /\ f i continuous_on t i) /\
     (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j ==> f i x = f j x) /\
     (!x. x IN s ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
     ==> g continuous_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC PASTING_LEMMA_LOCALLY_FINITE THEN
  MAP_EVERY EXISTS_TAC [`f:K->real^M->real^N`; `t:K->real^M->bool`; `k:K->bool`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(x:real^M) IN s`) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "FINITE")) (concl th))) THEN
    EXISTS_TAC `s INTER u:real^M->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i | i IN k /\ ~((t:K->real^M->bool) i INTER u = {})}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:K) IN k`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_in")) (concl th))) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (SET_RULE `!s t:real^M->bool. t SUBSET s ==> s INTER t = t`) th]) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN]]);;

let MOI_FTD_PASTE_LF = prove
 (`!(c:(real^N->bool)->bool) (h:real^N->real^M) (f:(real^N->bool)->real^N->real^M).
     lf_simplicial_complex c /\
     (!s. s IN c ==> (f s) continuous_on s) /\
     (!s x. s IN c /\ x IN s ==> h x = f s x)
     ==> h continuous_on UNIONS c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(real^N->bool)->real^N->real^M`; `h:real^N->real^M`;
                 `\s:real^N->bool. s`; `c:(real^N->bool)->bool`;
                 `UNIONS c:real^N->bool`] MOI_FTD_PASTE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) IN c` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ASM_MESON_TAC[IN_INTER];
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]]);;

let MOI_FTD_CONT_MAX = prove
 (`!(f:real^M->real) g t.
     (lift o f) continuous_on t /\ (lift o g) continuous_on t
     ==> (lift o (\x. max (f x) (g x))) continuous_on t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (f:real^M->real)`; `lift o (g:real^M->real)`; `t:real^M->bool`]
    CONTINUOUS_ON_MAX) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FUN_EQ_THM; o_THM] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP]);;

let MOI_FTD_CONT_SUP = prove
 (`!(f:A->real^M->real) t S.
     FINITE S /\ (!v. v IN S ==> (lift o f v) continuous_on t)
     ==> (lift o (\x. sup (&0 INSERT IMAGE (\v. f v x) S))) continuous_on t`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; SUP_SING; o_DEF; CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `S:A->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. sup (&0 INSERT IMAGE (\v. (f:A->real^M->real) v x) (a INSERT S)) =
        max (f a x) (sup (&0 INSERT IMAGE (\v. f v x) S))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
    ONCE_REWRITE_TAC[SET_RULE `(&0:real) INSERT b INSERT s = b INSERT &0 INSERT s`] THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTD_CONT_MAX THEN ASM_SIMP_TAC[ETA_AX]);;

(* The four functions. *)

let moi_ftd_pw = new_definition
 `moi_ftd_pw (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    sum u (moi_ftd_co c x)`;;

let moi_ftd_pp = new_definition
 `moi_ftd_pp (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    vsum u (\v. moi_ftd_co c x v % v)`;;

let moi_ftd_mf = new_definition
 `moi_ftd_mf (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    sup (&0 INSERT IMAGE (moi_ftd_co c x) u)`;;

let moi_ftd_mg = new_definition
 `moi_ftd_mg (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    sup (&0 INSERT IMAGE (moi_ftd_co c x) ((:real^N) DIFF u))`;;

let MOI_FTD_FN_LOCAL = prove
 (`!(c:(real^N->bool)->bool) u s x.
     moi_bar_complex c /\ s IN c /\ x IN s
     ==> moi_ftd_pw c u x =
         sum {v | v extreme_point_of s /\ v IN u} (moi_ftd_lc s x) /\
         moi_ftd_pp c u x =
         vsum {v | v extreme_point_of s /\ v IN u} (\v. moi_ftd_lc s x v % v) /\
         moi_ftd_mf c u x =
         sup (&0 INSERT IMAGE (moi_ftd_lc s x) {v | v extreme_point_of s /\ v IN u}) /\
         moi_ftd_mg c u x =
         sup (&0 INSERT IMAGE (moi_ftd_lc s x)
                {v | v extreme_point_of s /\ ~(v IN u)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_ftd_co c (x:real^N) = moi_ftd_lc s x` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MOI_FTD_CO_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. ~((v:real^N) extreme_point_of s) ==> moi_ftd_lc s x v = &0`
  ASSUME_TAC THENL [SIMP_TAC[moi_ftd_lc]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_ftd_pw; moi_ftd_pp; moi_ftd_mf; moi_ftd_mg] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC VSUM_SUPERSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[VECTOR_MUL_LZERO];
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    ASM_MESON_TAC[]]);;

let MOI_FTD_FN_CONT = prove
 (`!(c:(real^N->bool)->bool) u.
     lf_simplicial_complex c
     ==> (lift o moi_ftd_pw c u) continuous_on UNIONS c /\
         moi_ftd_pp c u continuous_on UNIONS c /\
         (lift o moi_ftd_mf c u) continuous_on UNIONS c /\
         (lift o moi_ftd_mg c u) continuous_on UNIONS c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN c
      ==> (?n. n simplex s) /\ FINITE {v | v extreme_point_of s /\ v IN u} /\
          FINITE {v | v extreme_point_of s /\ ~(v IN u)}`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`n:int`; `s:real^N->bool`] SIMPLEX_EXTREME_POINTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  let pre =
    ASM_SIMP_TAC[o_THM; MOI_FTD_FN_LOCAL] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC in
  let lcc =
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF] `lift o (\x:real^N. moi_ftd_lc s x v)`)] THEN
    MATCH_MP_TAC MOI_FTD_LC_CONT THEN ASM_MESON_TAC[] in
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTD_PASTE_LF THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\s x. lift (sum {v | v extreme_point_of s /\ v IN u}
                                 (moi_ftd_lc s (x:real^N)))` THEN
    pre THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[] THEN lcc;
    EXISTS_TAC `\s x. vsum {v | v extreme_point_of s /\ v IN u}
                           (\v. moi_ftd_lc s (x:real^N) v % v)` THEN
    pre THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC MOI_FTD_LC_CONT THEN ASM_MESON_TAC[];
    EXISTS_TAC `\s x. lift (sup (&0 INSERT IMAGE (moi_ftd_lc s (x:real^N))
                                   {v | v extreme_point_of s /\ v IN u}))` THEN
    pre THEN
    MP_TAC(ISPECL [`\v (x:real^N). moi_ftd_lc s x v`; `s:real^N->bool`;
                   `{v:real^N | v extreme_point_of s /\ v IN u}`] MOI_FTD_CONT_SUP) THEN
    REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    lcc;
    EXISTS_TAC `\s x. lift (sup (&0 INSERT IMAGE (moi_ftd_lc s (x:real^N))
                                   {v | v extreme_point_of s /\ ~(v IN u)}))` THEN
    pre THEN
    MP_TAC(ISPECL [`\v (x:real^N). moi_ftd_lc s x v`; `s:real^N->bool`;
                   `{v:real^N | v extreme_point_of s /\ ~(v IN u)}`] MOI_FTD_CONT_SUP) THEN
    REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    lcc]);;

(* Finite sups with 0. *)

let MOI_FTD_SUP_FIN = prove
 (`!(f:A->real) S.
     FINITE S
     ==> &0 <= sup (&0 INSERT IMAGE f S) /\
         (!v. v IN S ==> f v <= sup (&0 INSERT IMAGE f S)) /\
         (sup (&0 INSERT IMAGE f S) = &0 \/
          ?a. a IN S /\ sup (&0 INSERT IMAGE f S) = f a) /\
         (!b. &0 <= b /\ (!v. v IN S ==> f v <= b)
              ==> sup (&0 INSERT IMAGE f S) <= b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `&0 INSERT IMAGE (f:A->real) S` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let MOI_FTD_SUP_SCALE = prove
 (`!(f:A->real) S a.
     FINITE S /\ &0 <= a
     ==> sup (&0 INSERT IMAGE (\v. a * f v) S) = a * sup (&0 INSERT IMAGE f S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `S:A->bool`] MOI_FTD_SUP_FIN) THEN
  MP_TAC(ISPECL [`\v. a * (f:A->real) v`; `S:A->bool`] MOI_FTD_SUP_FIN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = sup (&0 INSERT IMAGE (\v. a * (f:A->real) v) S)` THEN
  ABBREV_TAC `m = sup (&0 INSERT IMAGE (f:A->real) S)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "bM")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "bm")))) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [USE_THEN "bM" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_LMUL];
    ASM_CASES_TAC `a = &0` THENL [ASM_REWRITE_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
    USE_THEN "bm" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `v:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[]]);;

(* A point of UNIONS t: a simplex of c = sd t through it, its coordinates,  *)
(* and the local forms of the four functions.                               *)

let MOI_FTD_PT_SETUP = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t
     ==> ?s. s IN barycentric_subdivision t /\ x IN s /\ (?n. n simplex s) /\
             FINITE {v | v extreme_point_of s} /\
             FINITE {v | v extreme_point_of s /\ v IN UNIONS l} /\
             FINITE {v | v extreme_point_of s /\ ~(v IN UNIONS l)} /\
             (!v. &0 <= moi_ftd_lc s x v) /\
             (!v. ~(v extreme_point_of s) ==> moi_ftd_lc s x v = &0) /\
             sum {v | v extreme_point_of s} (moi_ftd_lc s x) = &1 /\
             vsum {v | v extreme_point_of s} (\v. moi_ftd_lc s x v % v) = x /\
             moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x =
             sum {v | v extreme_point_of s /\ v IN UNIONS l} (moi_ftd_lc s x) /\
             moi_ftd_pp (barycentric_subdivision t) (UNIONS l) x =
             vsum {v | v extreme_point_of s /\ v IN UNIONS l}
                  (\v. moi_ftd_lc s x v % v) /\
             moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x =
             sup (&0 INSERT IMAGE (moi_ftd_lc s x)
                    {v | v extreme_point_of s /\ v IN UNIONS l}) /\
             moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x =
             sup (&0 INSERT IMAGE (moi_ftd_lc s x)
                    {v | v extreme_point_of s /\ ~(v IN UNIONS l)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN barycentric_subdivision t /\ x IN s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS t` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of s}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] MOI_FTD_LC_REP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTD_FN_LOCAL THEN ASM_REWRITE_TAC[]);;

let MOI_FTD_FN_BASIC = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t
     ==> &0 <= moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x /\
         &0 <= moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x /\
         moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x <=
         moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x /\
         moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x <= &1 /\
         ~(moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x = &0 /\
           moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_PT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mu = moi_ftd_lc s (x:real^N)` THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ v IN UNIONS l}`] MOI_FTD_SUP_FIN) THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}`] MOI_FTD_SUP_FIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "bG")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "bF")))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum {v:real^N | v extreme_point_of s} mu =
    sum {v | v extreme_point_of s /\ v IN UNIONS l} mu +
    sum {v | v extreme_point_of s /\ ~(v IN UNIONS l)} mu`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{v:real^N | v extreme_point_of s} =
      {v | v extreme_point_of s /\ v IN UNIONS l} UNION
      {v | v extreme_point_of s /\ ~(v IN UNIONS l)}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum {v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)} mu /\
    &0 <= sum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} mu`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "bF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {v:real^N} mu` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_SING; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^N) IN {v | v extreme_point_of s /\ v IN UNIONS l}` THEN
    SET_TAC[];
    ABBREV_TAC `sF = sum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} mu` THEN
    ABBREV_TAC `sG = sum {v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)} mu` THEN
    ABBREV_TAC `sV = sum {v:real^N | v extreme_point_of s} mu` THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `!v:real^N. v extreme_point_of s ==> mu v = &0` ASSUME_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(v:real^N) IN UNIONS l` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
          can (find_term ((=) `UNIONS (l:(real^N->bool)->bool)`)) (concl th) &&
          is_forall (concl th) && not (can (find_term ((=) `~`)) (concl th))));
        FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
          can (find_term ((=) `UNIONS (l:(real^N->bool)->bool)`)) (concl th) &&
          is_forall (concl th) && can (find_term ((=) `~`)) (concl th)))] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `&0 <= (mu:real^N->real) v`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `sum {v:real^N | v extreme_point_of s} mu = &1` THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[IN_ELIM_THM]]);;

(* The membership tests for N and UNIONS l. *)

let MOI_FTD_N_IFF = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t
     ==> (x IN derived_nbhd t l <=>
          moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x <=
          moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_PT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_FN_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mu = moi_ftd_lc s (x:real^N)` THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mG = sup (&0 INSERT IMAGE (mu:real^N->real)
                         {v | v extreme_point_of s /\ ~(v IN UNIONS l)})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uG")
    (CONJUNCTS_THEN2 (LABEL_TAC "cG") (LABEL_TAC "bG")))) THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ v IN UNIONS l}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mF = sup (&0 INSERT IMAGE (mu:real^N->real)
                         {v | v extreme_point_of s /\ v IN UNIONS l})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uF")
    (CONJUNCTS_THEN2 (LABEL_TAC "cF") (LABEL_TAC "bF")))) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`; `mu:real^N->real`] MOI_FRN_NBHD_IMP_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(mu:real^N->real) a` THEN CONJ_TAC THENL
     [USE_THEN "bG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      USE_THEN "uF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    DISCH_TAC THEN
    USE_THEN "cF" (DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THENL
     [UNDISCH_TAC `~(mF = &0 /\ mG = &0)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(a:real^N) IN {v | v extreme_point_of s /\ v IN UNIONS l}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`; `mu:real^N->real`; `a:real^N`] MOI_FRN_MAX_IMP_NBHD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(v:real^N) IN UNIONS l` THENL
     [UNDISCH_TAC `mF = (mu:real^N->real) a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "uF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mG:real` THEN CONJ_TAC THENL
       [USE_THEN "uG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        ASM_MESON_TAC[]]]]);;

let MOI_FTD_L_IFF = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t
     ==> (x IN UNIONS l <=>
          moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_PT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`moi_ftd_lc s (x:real^N)`;
                 `{v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mG = sup (&0 INSERT IMAGE (moi_ftd_lc s (x:real^N))
                         {v | v extreme_point_of s /\ ~(v IN UNIONS l)})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uG")
    (CONJUNCTS_THEN2 (LABEL_TAC "cG") (LABEL_TAC "bG")))) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "bG" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `s INTER UNIONS l:real^N->bool`; `x:real^N`]
      MOI_FTD_LC_FACE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `~((v:real^N) extreme_point_of (s INTER UNIONS l))` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [extreme_point_of]) THEN
      UNDISCH_TAC `~((v:real^N) IN UNIONS l)` THEN SET_TAC[];
      ASM_REWRITE_TAC[moi_ftd_lc; REAL_LE_REFL]];
    DISCH_TAC THEN
    SUBGOAL_THEN `!v:real^N. v extreme_point_of s /\ ~(v IN UNIONS l)
                             ==> moi_ftd_lc s x v = &0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mG = &0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "uG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ABBREV_TAC `E = {v:real^N | v extreme_point_of s /\ v IN UNIONS l}` THEN
    MP_TAC(ISPEC `s:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
    SUBGOAL_THEN `(E:real^N->bool) SUBSET {v | v extreme_point_of s}` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull E` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
      EXISTS_TAC `moi_ftd_lc s (x:real^N)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS `sum {v:real^N | v extreme_point_of s} (moi_ftd_lc s x)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        TRANS_TAC EQ_TRANS
         `vsum {v:real^N | v extreme_point_of s} (\v. moi_ftd_lc s x v % v)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[VECTOR_MUL_LZERO]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(convex hull E:real^N->bool) face_of s` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`{v:real^N | v extreme_point_of s}`; `convex hull E:real^N->bool`]
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull E IN barycentric_subdivision (l:(real^N->bool)->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_BS_FULL THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
        REWRITE_TAC[moi_bar_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `a:real^N` THEN
        DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
        EXPAND_TAC "E" THEN SIMP_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull E:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Moving x along its join line: the point a pp(x) + b (x - pp(x)) has the  *)
(* coordinates of x scaled by a at the vertices in UNIONS l and by b at the *)
(* others.                                                                   *)

let MOI_FTD_SCALE = prove
 (`!(t:(real^N->bool)->bool) l x a b z.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t /\
     &0 <= a /\ &0 <= b /\
     a * moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x +
     b * (&1 - moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x) = &1 /\
     z = a % moi_ftd_pp (barycentric_subdivision t) (UNIONS l) x +
         b % (x - moi_ftd_pp (barycentric_subdivision t) (UNIONS l) x)
     ==> z IN UNIONS t /\
         moi_ftd_pw (barycentric_subdivision t) (UNIONS l) z =
         a * moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x /\
         moi_ftd_pp (barycentric_subdivision t) (UNIONS l) z =
         a % moi_ftd_pp (barycentric_subdivision t) (UNIONS l) x /\
         moi_ftd_mf (barycentric_subdivision t) (UNIONS l) z =
         a * moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x /\
         moi_ftd_mg (barycentric_subdivision t) (UNIONS l) z =
         b * moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq (concl th) && lhs (concl th) = `z:real^N`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_PT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `mu = moi_ftd_lc s (x:real^N)` THEN
  ABBREV_TAC `nu = \v:real^N. if v IN UNIONS l then a * mu v else b * mu v` THEN
  SUBGOAL_THEN
   `sum {v:real^N | v extreme_point_of s} mu =
    sum {v | v extreme_point_of s /\ v IN UNIONS l} mu +
    sum {v | v extreme_point_of s /\ ~(v IN UNIONS l)} mu /\
    vsum {v:real^N | v extreme_point_of s} (\v. mu v % v) =
    vsum {v | v extreme_point_of s /\ v IN UNIONS l} (\v. mu v % v) +
    vsum {v | v extreme_point_of s /\ ~(v IN UNIONS l)} (\v. mu v % v) /\
    sum {v:real^N | v extreme_point_of s} nu =
    a * sum {v | v extreme_point_of s /\ v IN UNIONS l} mu +
    b * sum {v | v extreme_point_of s /\ ~(v IN UNIONS l)} mu /\
    vsum {v:real^N | v extreme_point_of s} (\v. nu v % v) =
    a % vsum {v | v extreme_point_of s /\ v IN UNIONS l} (\v. mu v % v) +
    b % vsum {v | v extreme_point_of s /\ ~(v IN UNIONS l)} (\v. mu v % v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`{v:real^N | v extreme_point_of s}`; `\v:real^N. v IN UNIONS l`;
                     `mu:real^N->real`; `mu:real^N->real`] SUM_CASES) THEN
      ASM_REWRITE_TAC[COND_ID; ETA_AX] THEN REWRITE_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`{v:real^N | v extreme_point_of s}`; `\v:real^N. v IN UNIONS l`;
                     `\v:real^N. mu v % v`; `\v:real^N. mu v % v`] VSUM_CASES) THEN
      ASM_REWRITE_TAC[COND_ID; ETA_AX] THEN REWRITE_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`{v:real^N | v extreme_point_of s}`; `\v:real^N. v IN UNIONS l`;
                     `\v:real^N. a * mu v`; `\v:real^N. b * mu v`] SUM_CASES) THEN
      ASM_REWRITE_TAC[SUM_LMUL] THEN EXPAND_TAC "nu" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      TRANS_TAC EQ_TRANS
       `vsum {v:real^N | v extreme_point_of s}
             (\v. if v IN UNIONS l then a % (mu v % v) else b % (mu v % v))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
        EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC];
        MP_TAC(ISPECL [`{v:real^N | v extreme_point_of s}`; `\v:real^N. v IN UNIONS l`;
                       `\v:real^N. a % (mu v % v)`; `\v:real^N. b % (mu v % v)`]
          VSUM_CASES) THEN
        ASM_REWRITE_TAC[VSUM_LMUL] THEN REWRITE_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  ABBREV_TAC `sF = sum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} mu` THEN
  ABBREV_TAC `sG = sum {v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)} mu` THEN
  ABBREV_TAC `pF = vsum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} (\v. mu v % v)` THEN
  ABBREV_TAC `pG = vsum {v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}
                        (\v. mu v % v)` THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of s ==> &0 <= nu v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {v:real^N | v extreme_point_of s} nu = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sG = &1 - sF` SUBST1_TAC THENL
     [UNDISCH_TAC `sum {v:real^N | v extreme_point_of s} mu = &1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `a * moi_ftd_pw (barycentric_subdivision t) (UNIONS l) (x:real^N) +
                 b * (&1 - moi_ftd_pw (barycentric_subdivision t) (UNIONS l) x) = &1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vsum {v:real^N | v extreme_point_of s} (\v. nu v % v) = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a % moi_ftd_pp (barycentric_subdivision t) (UNIONS l) x +
                 b % (x - moi_ftd_pp (barycentric_subdivision t) (UNIONS l) (x:real^N)) = z` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `vsum {v:real^N | v extreme_point_of s} (\v. mu v % v) = x` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `s:real^N->bool`;
                 `z:real^N`; `nu:real^N->real`] MOI_FTD_CO_REP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`; `nu:real^N->real`] MOI_FTD_LC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `UNIONS l:real^N->bool`;
                 `s:real^N->bool`; `z:real^N`] MOI_FTD_FN_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `(!v:real^N. v IN {v | v extreme_point_of s /\ v IN UNIONS l}
               ==> moi_ftd_lc s z v = a * mu v) /\
    (!v:real^N. v IN {v | v extreme_point_of s /\ ~(v IN UNIONS l)}
               ==> moi_ftd_lc s z v = b * mu v)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "nu" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    TRANS_TAC EQ_TRANS
     `sum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} (\v. a * mu v)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[SUM_LMUL]];
    TRANS_TAC EQ_TRANS
     `vsum {v:real^N | v extreme_point_of s /\ v IN UNIONS l} (\v. a % (mu v % v))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[VECTOR_MUL_ASSOC];
      ASM_REWRITE_TAC[VSUM_LMUL]];
    TRANS_TAC EQ_TRANS
     `sup (&0 INSERT IMAGE (\v:real^N. a * mu v)
                  {v | v extreme_point_of s /\ v IN UNIONS l})` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = g x)
                             ==> IMAGE f s = IMAGE (g:real^N->real) s`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[MOI_FTD_SUP_SCALE]];
    TRANS_TAC EQ_TRANS
     `sup (&0 INSERT IMAGE (\v:real^N. b * mu v)
                  {v | v extreme_point_of s /\ ~(v IN UNIONS l)})` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = g x)
                             ==> IMAGE f s = IMAGE (g:real^N->real) s`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[MOI_FTD_SUP_SCALE]]]);;

(* Points with mf = mg are not interior to N in UNIONS t: moving towards a  *)
(* vertex outside UNIONS l with the largest coordinate leaves N.            *)

let MOI_FTD_BD_NOT_INT = prove
 (`!(t:(real^N->bool)->bool) l x w.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ x IN UNIONS t /\
     moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x <=
     moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x /\
     open_in (subtopology euclidean (UNIONS t)) w /\ x IN w
     ==> ~(w SUBSET derived_nbhd t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_FN_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_PT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `mu = moi_ftd_lc s (x:real^N)` THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mG = sup (&0 INSERT IMAGE (mu:real^N->real)
                         {v | v extreme_point_of s /\ ~(v IN UNIONS l)})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uG")
    (CONJUNCTS_THEN2 (LABEL_TAC "cG") (LABEL_TAC "bG")))) THEN
  MP_TAC(ISPECL [`mu:real^N->real`;
                 `{v:real^N | v extreme_point_of s /\ v IN UNIONS l}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mF = sup (&0 INSERT IMAGE (mu:real^N->real)
                         {v | v extreme_point_of s /\ v IN UNIONS l})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uF")
    (CONJUNCTS_THEN2 (LABEL_TAC "cF") (LABEL_TAC "bF")))) THEN
  SUBGOAL_THEN `mF <= mG /\ &0 < mG` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_ftd_mf (barycentric_subdivision t) (UNIONS l) (x:real^N) <=
                 moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x` THEN
    UNDISCH_TAC `~(moi_ftd_mf (barycentric_subdivision t) (UNIONS l) (x:real^N) = &0 /\
                   moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x = &0)` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= mG` THEN UNDISCH_TAC `&0 <= mF` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cG" (DISJ_CASES_THEN2
    (fun th -> UNDISCH_TAC `&0 < mG` THEN REWRITE_TAC[th; REAL_LT_REFL])
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(b:real^N) IN {v | v extreme_point_of s /\ ~(v IN UNIONS l)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS t)) (w:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(x:real^N,r) SUBSET o1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[OPEN_CONTAINS_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(b - x:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b - x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e = min (&1 / &2) (r / (norm(b - x:real^N) + &1))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 / &2 /\ e * norm(b - x:real^N) < r`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r / (norm(b - x:real^N) + &1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `e * (norm(b - x:real^N) + &1) <= r` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN EXPAND_TAC "e" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < r / (norm(b - x:real^N) + &1)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = (&1 - e) % x + e % (b:real^N)` THEN
  ABBREV_TAC `nu = \v:real^N. (&1 - e) * mu v + (if v = b then e else &0)` THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of s ==> &0 <= nu v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {v:real^N | v extreme_point_of s} nu = &1` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_DELTA] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vsum {v:real^N | v extreme_point_of s} (\v. nu v % v) = y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN EXPAND_TAC "nu" THEN REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[VSUM_ADD] THEN
    SUBGOAL_THEN
     `vsum {v:real^N | v extreme_point_of s} (\v. ((&1 - e) * mu v) % v) =
      (&1 - e) % x /\
      vsum {v:real^N | v extreme_point_of s} (\v. (if v = b then e else &0) % v) =
      e % b`
    ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL];
        TRANS_TAC EQ_TRANS
         `vsum {v:real^N | v extreme_point_of s} (\v. if v = b then e % b else vec 0)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
          ASM_REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM]]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `s:real^N->bool`;
                 `y:real^N`; `nu:real^N->real`] MOI_FTD_CO_REP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `y:real^N`; `nu:real^N->real`] MOI_FTD_LC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS t` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `ball(x:real^N,r) SUBSET o1` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
    UNDISCH_TAC `(&1 - e) % x + e % b = (y:real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_ARITH `x - ((&1 - e) % x + e % b):real^N = e % (x - b)`] THEN
    REWRITE_TAC[NORM_MUL] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN derived_nbhd t l` MP_TAC THENL
   [UNDISCH_TAC `(w:real^N->bool) SUBSET derived_nbhd t l` THEN
    UNDISCH_TAC `(y:real^N) IN w` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
    MOI_FTD_N_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `UNIONS l:real^N->bool`;
                 `s:real^N->bool`; `y:real^N`] MOI_FTD_FN_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`moi_ftd_lc s (y:real^N)`;
                 `{v:real^N | v extreme_point_of s /\ ~(v IN UNIONS l)}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`moi_ftd_lc s (y:real^N)`;
                 `{v:real^N | v extreme_point_of s /\ v IN UNIONS l}`] MOI_FTD_SUP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(&1 - e) * mF` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(v:real^N = b)` (fun th -> REWRITE_TAC[th; REAL_ADD_RID]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "uF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `mG = (mu:real^N->real) b` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN
  SUBGOAL_THEN `(&1 - e) * mF <= (&1 - e) * mG` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = sup (&0 INSERT IMAGE (moi_ftd_lc s (y:real^N))
                        {v | v extreme_point_of s /\ v IN UNIONS l})` THEN
  ABBREV_TAC `q' = sup (&0 INSERT IMAGE (moi_ftd_lc s (y:real^N))
                         {v | v extreme_point_of s /\ ~(v IN UNIONS l)})` THEN
  REAL_ARITH_TAC);;

(* The frontier of N in UNIONS t: mf = mg. *)

let MOI_FTD_BD_IFF = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (x IN derived_frontier t l <=>
          x IN UNIONS t /\
          moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x =
          moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF] THEN
  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN] THEN
  ASM_CASES_TAC `(x:real^N) IN UNIONS t` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `~((x:real^N) IN UNIONS t)` THEN SET_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_N_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN subtopology euclidean (UNIONS t) interior_of derived_nbhd t l <=>
    moi_ftd_mg (barycentric_subdivision t) (UNIONS l) x <
    moi_ftd_mf (barycentric_subdivision t) (UNIONS l) x`
  SUBST1_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`;
                   `w:real^N->bool`] MOI_FTD_BD_NOT_INT) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `{y:real^N | y IN UNIONS t /\
                            moi_ftd_mg (barycentric_subdivision t) (UNIONS l) y <
                            moi_ftd_mf (barycentric_subdivision t) (UNIONS l) y}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`lift o (\y:real^N.
                         moi_ftd_mf (barycentric_subdivision t) (UNIONS l) y -
                         moi_ftd_mg (barycentric_subdivision t) (UNIONS l) y)`;
                     `UNIONS t:real^N->bool`; `{z:real^1 | z$1 > &0}`]
        CONTINUOUS_OPEN_IN_PREIMAGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
        MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                       `UNIONS l:real^N->bool`] MOI_FTD_FN_CONT) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN
        REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop; LIFT_DROP; real_gt] THEN
        REWRITE_TAC[REAL_SUB_LT]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
        MOI_FTD_N_IFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The product structure N DIFF UNIONS l = Bd N x [0,1) (Moise              *)
(* 33.1 Lemma 10, p.235).  pi(x) = pp(x)/pw(x) is the end in UNIONS l of    *)
(* the join line of x; f(y,s) = (1 - s) y + s pi(y), and the inverse sends  *)
(* x to the point of Bd N on its join line and the parameter 1 - 1/r.       *)
(* ========================================================================= *)

let moi_ftd_pi = new_definition
 `moi_ftd_pi (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    inv(moi_ftd_pw c u x) % moi_ftd_pp c u x`;;

let moi_ftd_rr = new_definition
 `moi_ftd_rr (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    moi_ftd_mf c u x /
    (moi_ftd_mf c u x * (&1 - moi_ftd_pw c u x) + moi_ftd_pw c u x * moi_ftd_mg c u x)`;;

let moi_ftd_pf = new_definition
 `moi_ftd_pf (c:(real^N->bool)->bool) (u:real^N->bool) (z:real^(N,1)finite_sum) =
    (&1 - drop(sndcart z)) % fstcart z + drop(sndcart z) % moi_ftd_pi c u (fstcart z)`;;

let moi_ftd_pg = new_definition
 `moi_ftd_pg (c:(real^N->bool)->bool) (u:real^N->bool) (x:real^N) =
    pastecart (moi_ftd_pi c u x + moi_ftd_rr c u x % (x - moi_ftd_pi c u x))
              (lift (&1 - inv (moi_ftd_rr c u x)))`;;

(* The forward map on a point of Bd N. *)

let MOI_FTD_PF_PROP = prove
 (`!(t:(real^N->bool)->bool) l y s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     y IN derived_frontier t l /\ &0 <= s /\ s < &1
     ==> (&1 - s) % y + s % moi_ftd_pi (barycentric_subdivision t) (UNIONS l) y IN
         derived_nbhd t l DIFF UNIONS l /\
         moi_ftd_pg (barycentric_subdivision t) (UNIONS l)
           ((&1 - s) % y + s % moi_ftd_pi (barycentric_subdivision t) (UNIONS l) y) =
         pastecart y (lift s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
    MOI_FTD_BD_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
    MOI_FTD_FN_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = moi_ftd_pw (barycentric_subdivision t) (UNIONS l) (y:real^N)` THEN
  ABBREV_TAC `m = moi_ftd_mg (barycentric_subdivision t) (UNIONS l) (y:real^N)` THEN
  ABBREV_TAC `q = moi_ftd_pp (barycentric_subdivision t) (UNIONS l) (y:real^N)` THEN
  SUBGOAL_THEN `&0 < m /\ &0 < p` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_ftd_pi] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x = (&1 - s) % y + s % inv p % (q:real^N)` THEN
  ABBREV_TAC `a = &1 - s + s * inv p` THEN
  ABBREV_TAC `b = &1 - s` THEN
  SUBGOAL_THEN `&0 < b /\ b <= a /\ &0 < a /\ a * p + b * (&1 - p) = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SUBGOAL_THEN `&0 <= s * inv p` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `s = &1 - b` ASSUME_TAC THENL [EXPAND_TAC "b" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a % q + b % (y - q:real^N) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `b % y + s % inv p % q = (x:real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `b + s * inv p = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`;
                 `a:real`; `b:real`; `x:real^N`] MOI_FTD_SCALE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_N_IFF) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_L_IFF) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftd_pg; moi_ftd_pi; moi_ftd_rr] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv (a * p) % a % q = inv p % (q:real^N)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a * m) / ((a * m) * (&1 - a * p) + (a * p) * (b * m)) = inv b`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 - a * p = b * (&1 - p)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < b` THEN UNDISCH_TAC `&0 < m` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[PASTECART_INJ; REAL_INV_INV] THEN REPEAT CONJ_TAC THEN
  TRY(AP_TERM_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  UNDISCH_TAC `b % y + s % inv p % q = (x:real^N)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(b % y + (&1 - b) % z) - z:real^N = b % (y - z)`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;

(* The inverse map on a point of N DIFF UNIONS l. *)

let MOI_FTD_PG_PROP = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     x IN derived_nbhd t l DIFF UNIONS l
     ==> fstcart (moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x) IN
         derived_frontier t l /\
         &0 <= drop (sndcart (moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x)) /\
         drop (sndcart (moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x)) < &1 /\
         moi_ftd_pf (barycentric_subdivision t) (UNIONS l)
           (moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_N_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_L_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTD_FN_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = moi_ftd_pw (barycentric_subdivision t) (UNIONS l) (x:real^N)` THEN
  ABBREV_TAC `mF = moi_ftd_mf (barycentric_subdivision t) (UNIONS l) (x:real^N)` THEN
  ABBREV_TAC `mG = moi_ftd_mg (barycentric_subdivision t) (UNIONS l) (x:real^N)` THEN
  ABBREV_TAC `q = moi_ftd_pp (barycentric_subdivision t) (UNIONS l) (x:real^N)` THEN
  SUBGOAL_THEN `&0 < mG /\ &0 < mF /\ &0 < p` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = mF * (&1 - p) + p * mG` THEN
  SUBGOAL_THEN `&0 < D /\ D <= mF` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL]];
      SUBGOAL_THEN `p * mG <= p * mF` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `r = mF / D` THEN
  SUBGOAL_THEN `&1 <= r /\ r * D = mF /\ &0 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ;
                                    REAL_LT_DIV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = (&1 - r + r * p) * inv p` THEN
  SUBGOAL_THEN `&0 < a /\ a * p + r * (&1 - p) = &1 /\ a * mF = r * mG`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
      SUBGOAL_THEN `r * (&1 - p) < &1` MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `(r * (&1 - p)) * D < &1 * D` MP_TAC THENL
       [UNDISCH_TAC `r * D = mF` THEN
        REWRITE_TAC[REAL_ARITH `(r * a) * D = (r * D) * a`; REAL_MUL_LID] THEN
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "D" THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < b ==> a < a + b`) THEN ASM_SIMP_TAC[REAL_LT_MUL];
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
      UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `r * D = mF` THEN EXPAND_TAC "D" THEN
      UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftd_pg; moi_ftd_pi; moi_ftd_rr; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = inv p % q + r % (x - inv p % q:real^N)` THEN
  SUBGOAL_THEN `a % q + r % (x - q:real^N) = z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[VECTOR_ARITH `(c * d) % q:real^N = c % d % q`] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - r + r * p) % inv p % q + r % (x - q) =
      inv p % q + r % (x - inv p % q) + (r * p) % inv p % q - r % q:real^N`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ARITH `(r * p) * i = r * (p * i)`] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID; ASSUME `&0 < p`] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`;
                 `a:real`; `r:real`; `z:real^N`] MOI_FTD_SCALE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `z:real^N`]
      MOI_FTD_BD_IFF) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ARITH `&1 - x < &1 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    REWRITE_TAC[moi_ftd_pf; moi_ftd_pi; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv (a * p) % a % q = inv p % (q:real^N)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
    UNDISCH_TAC `inv p % q + r % (x - inv p % q:real^N) = z` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; ASSUME `&0 < r`] THEN VECTOR_ARITH_TAC]);;

(* Continuity of the two maps. *)

let MOI_FTD_CONT_RMUL = prove
 (`!(f:real^M->real) g s.
     (lift o f) continuous_on s /\ (lift o g) continuous_on s
     ==> (lift o (\x. f x * g x)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`; `lift o (g:real^M->real)`]
    CONTINUOUS_ON_MUL) THEN
  ASM_REWRITE_TAC[o_DEF; GSYM LIFT_CMUL]);;

let MOI_FTD_CONT_RDIV = prove
 (`!(f:real^M->real) g s.
     (lift o f) continuous_on s /\ (lift o g) continuous_on s /\
     (!x. x IN s ==> ~(g x = &0))
     ==> (lift o (\x. f x / g x)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC MOI_FTD_CONT_RMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^M->real`; `s:real^M->bool`] CONTINUOUS_ON_INV) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let MOI_FTD_COMP_FST = prove
 (`!(h:real^N->real^M) S (D:real^(N,1)finite_sum->bool).
     h continuous_on S /\ IMAGE fstcart D SUBSET S
     ==> (\z. h (fstcart z)) continuous_on D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(N,1)finite_sum. (h:real^N->real^M) (fstcart z)) = h o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]);;

let MOI_FTD_FN_CONT_T = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (lift o moi_ftd_pw (barycentric_subdivision t) (UNIONS l)) continuous_on
         UNIONS t /\
         moi_ftd_pp (barycentric_subdivision t) (UNIONS l) continuous_on UNIONS t /\
         (lift o moi_ftd_mf (barycentric_subdivision t) (UNIONS l)) continuous_on
         UNIONS t /\
         (lift o moi_ftd_mg (barycentric_subdivision t) (UNIONS l)) continuous_on
         UNIONS t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `UNIONS l:real^N->bool`]
    MOI_FTD_FN_CONT) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTD_PF_CONT = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> moi_ftd_pf (barycentric_subdivision t) (UNIONS l) continuous_on
         (derived_frontier t l PCROSS {s:real^1 | &0 <= drop s /\ drop s < &1})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FTD_FN_CONT_T) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `DD = derived_frontier (t:(real^N->bool)->bool) l PCROSS
                   {s:real^1 | &0 <= drop s /\ drop s < &1}` THEN
  SUBGOAL_THEN `IMAGE fstcart (DD:real^(N,1)finite_sum->bool) SUBSET UNIONS (t:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "DD" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    ASM_MESON_TAC[MOI_FTD_BD_IFF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. z IN DD
        ==> ~(moi_ftd_pw (barycentric_subdivision t) (UNIONS l) (fstcart z) = &0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "DD" THEN REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `s:real^1`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
      MOI_FTD_BD_IFF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
      MOI_FTD_FN_BASIC) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[moi_ftd_pf; moi_ftd_pi] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z:real^(N,1)finite_sum.
                        moi_ftd_pw (barycentric_subdivision t) (UNIONS l) (fstcart z)`;
                     `DD:real^(N,1)finite_sum->bool`] CONTINUOUS_ON_INV) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`lift o moi_ftd_pw (barycentric_subdivision (t:(real^N->bool)->bool))
                                         (UNIONS l)`;
                     `UNIONS t:real^N->bool`; `DD:real^(N,1)finite_sum->bool`]
        MOI_FTD_COMP_FST) THEN
      ASM_REWRITE_TAC[o_THM];
      MATCH_MP_TAC MOI_FTD_COMP_FST THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
      ASM_REWRITE_TAC[ETA_AX]]]);;

let MOI_FTD_PG_CONT = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> moi_ftd_pg (barycentric_subdivision t) (UNIONS l) continuous_on
         (derived_nbhd t l DIFF UNIONS l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FTD_FN_CONT_T) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `E = derived_nbhd (t:(real^N->bool)->bool) l DIFF UNIONS l` THEN
  SUBGOAL_THEN `(E:real^N->bool) SUBSET UNIONS t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "E" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `pw = moi_ftd_pw (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))` THEN
  ABBREV_TAC `pp = moi_ftd_pp (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))` THEN
  ABBREV_TAC `mf = moi_ftd_mf (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))` THEN
  ABBREV_TAC `mg = moi_ftd_mg (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN
   `!x:real^N. x IN E
      ==> &0 < pw x /\ &0 < mf x * (&1 - pw x) + pw x * mg x /\
          &0 < mf x / (mf x * (&1 - pw x) + pw x * mg x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN derived_nbhd t l /\ ~(x IN UNIONS l) /\ x IN UNIONS t`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN E` THEN EXPAND_TAC "E" THEN
      UNDISCH_TAC `(E:real^N->bool) SUBSET UNIONS t` THEN EXPAND_TAC "E" THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_N_IFF) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_L_IFF) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_FN_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (mg:real^N->real) x /\ &0 < pw x` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (mf:real^N->real) x * (&1 - pw x) + pw x * mg x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o pw) continuous_on E /\ (pp:real^N->real^N) continuous_on E /\
    (lift o mf) continuous_on E /\ (lift o mg) continuous_on E`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^N. inv (pw x) % (pp:real^N->real^N) x) continuous_on E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`pw:real^N->real`; `E:real^N->bool`] CONTINUOUS_ON_INV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o (\x:real^N. mf x / (mf x * (&1 - pw x) + pw x * mg x))) continuous_on E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTD_CONT_RDIV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ; ETA_AX] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
    ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF] `lift o (\x:real^N. f x * g x)`)] THEN
    MATCH_MP_TAC MOI_FTD_CONT_RMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  ASM_REWRITE_TAC[moi_ftd_pg; moi_ftd_pi; moi_ftd_rr] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MP_TAC(ISPECL [`\x:real^N. mf x / (mf x * (&1 - pw x) + pw x * mg x)`;
                   `E:real^N->bool`] CONTINUOUS_ON_INV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[o_DEF]]);;

(* The theorem GRAPH_TUBE_PRODUCT (Moise 33.1 Lemma 10, p.235). *)

let GRAPH_TUBE_PRODUCT = prove
 (MOI_FND_GRAPH_TUBE_PRODUCT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MAP_EVERY EXISTS_TAC
   [`moi_ftd_pf (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))`;
    `moi_ftd_pg (barycentric_subdivision t) (UNIONS (l:(real^N->bool)->bool))`] THEN
  SUBGOAL_THEN
   `!z. z IN derived_frontier t l PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}
        ==> moi_ftd_pf (barycentric_subdivision t) (UNIONS l) z IN
            derived_nbhd t l DIFF UNIONS (l:(real^N->bool)->bool) /\
            moi_ftd_pg (barycentric_subdivision t) (UNIONS l)
              (moi_ftd_pf (barycentric_subdivision t) (UNIONS l) z) = z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `s:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_ftd_pf; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`;
                   `drop s`] MOI_FTD_PF_PROP) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN derived_nbhd t l DIFF UNIONS (l:(real^N->bool)->bool)
        ==> moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x IN
            derived_frontier t l PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1} /\
            moi_ftd_pf (barycentric_subdivision t) (UNIONS l)
              (moi_ftd_pg (barycentric_subdivision t) (UNIONS l) x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTD_PG_PROP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN
    ASM_SIMP_TAC[MOI_FTD_PF_CONT; MOI_FTD_PG_CONT] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_ftd_pf; FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    VECTOR_ARITH_TAC]);;

