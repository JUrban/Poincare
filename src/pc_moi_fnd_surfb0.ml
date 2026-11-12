(* ========================================================================= *)
(* pc_moi_fnd_surfb0: boundary structure of finite combinatorial            *)
(* 2-manifolds with boundary, kept apart from pc_moi_fnd_surfb so that the  *)
(* files needing only the boundary circles do not load the planar           *)
(* machinery.  Results (no statement constant): MOI_FSB_BD_DEGREE (every    *)
(* boundary vertex lies on exactly two boundary edges) and                  *)
(* MOI_FSB_BD_CIRCLES (surface_boundary c has finitely many components,     *)
(* each a PL circle), with the chart, purity and dimension facts            *)
(* MOI_FSB_SC_CHARTS, MOI_FSB_DIM, MOI_FSB_PURE, MOI_FSB_VTRI used by        *)
(* pc_moi_fnd_surfb.                                                         *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_fnd_surfa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local facts of a finite combinatorial 2-manifold with boundary          *)
(* and its boundary circles.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_SC_CHARTS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> simplicial_complex c /\
         (!y. y IN UNIONS c
              ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; combinatorial_manifold_with_boundary];
    MP_TAC(ISPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN surface_boundary c` THEN ASM_SIMP_TAC[IN_DIFF]]);;

(* The Euler characteristic of a complex of dimension at most 1 (as         *)
(* MOI_FRN_SA_LK_CHI of pc_moi_fnd_rn, with the dimension bound as the      *)
(* hypothesis).                                                              *)

let MOI_FSB_EULER_1DIM = prove
 (`!L:(real^N->bool)->bool.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &1)
     ==> complex_euler L =
         &(CARD {u | {u} IN L}) - &(CARD {e | e IN L /\ aff_dim e = &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ ~(s = {})} =
    {s | s IN L /\ aff_dim s = &0} UNION {e | e IN L /\ aff_dim e = &1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN L` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term ((=) `&1:int`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN L /\ aff_dim s = &0}
             {e | e IN L /\ aff_dim e = &1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN L /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN L /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\s. -- &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN L}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN L}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

(* Degree counting in a complex of dimension at most 1 whose vertex degrees *)
(* are 1 or 2: the degree-1 vertices number twice V - E.                    *)

let MOI_FSB_DEG1_COUNT = prove
 (`!L:(real^N->bool)->bool.
     simplicial_complex L /\
     (!u. {u} IN L ==> CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1 \/
                       CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 2)
     ==> CARD {u | {u} IN L /\ CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1} +
         2 * CARD {e | e IN L /\ aff_dim e = &1} =
         2 * CARD {u | {u} IN L}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. FINITE {u:real^N | {u} IN L /\ P u}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{u:real^N | {u} IN L}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MOI_FRN_SA_LK_HANDSHAKE th)]) THEN
  SUBGOAL_THEN
   `CARD {u:real^N | {u} IN L /\ CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1} =
    nsum {u:real^N | {u} IN L}
      (\u. if CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1 then 1 else 0)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\u:real^N. CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1`;
                   `{u:real^N | {u} IN L}`; `\u:real^N. 1`] NSUM_RESTRICT_SET) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; MULT_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NSUM_ADD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {u:real^N | {u} IN L} (\u. 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `{u:real^N} IN L`)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC]);;

(* An edge of a simplicial complex through a vertex w is the hull of w and *)
(* a vertex a of the link of w.                                              *)

let MOI_FSB_EDGE_AT = prove
 (`!c e (w:real^N).
     simplicial_complex c /\ {w} IN c /\ e IN c /\ aff_dim e = &1 /\ w IN e
     ==> ?a. ~(a = w) /\ {a} IN c /\ {a} IN simplicial_link c w /\
             e = convex hull {w,a}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SEGMENT_CONVEX_HULL]) THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `!x:real^N. x extreme_point_of segment[p,q] ==> {x} IN c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    EXISTS_TAC `segment[p:real^N,q]` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of segment[p,q]` MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`segment[p:real^N,q]`; `{w:real^N}`] o el 3 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[p:real^N,q] INTER {w} = {w}` (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `(w:real^N) IN segment[p,q]` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
  SUBGOAL_THEN `{q:real^N} IN c /\ {p:real^N} IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} face_of segment[p,q] /\ {q:real^N} face_of segment[p,q]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN segment[p,q] /\ (q:real^N) IN segment[p,q]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
    EXISTS_TAC `segment[p:real^N,q]` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `segment[p:real^N,q]` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_SYM]]]);;

(* At a boundary vertex exactly two boundary edges meet: the vertex link    *)
(* has degrees 1 or 2 (MOI_S8TB_LINK_DEGREE, MOI_S8TB_EDGE_CARD), so its   *)
(* degree-1 vertices number 2 chi; a boundary edge gives a degree-1 vertex, *)
(* so the link is not a circle (chi = 0) but an arc (chi = 1).               *)

let MOI_FSB_BD_DEGREE = prove
 (`!c (w:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {w} IN c /\
     w IN surface_boundary c
     ==> CARD {e | e IN c /\ aff_dim e = &1 /\ w IN e /\
                   CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH")) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = simplicial_link (c:(real^N->bool)->bool) w` THEN
  SUBGOAL_THEN `simplicial_complex (L:(real^N->bool)->bool) /\
                (!s. s IN L ==> aff_dim s <= &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LINK_SC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_DIM THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `w:real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* degrees in the link *)
  SUBGOAL_THEN
   `!a:real^N. {a} IN L
      ==> ~(a = w) /\ convex hull {w,a} IN c /\ aff_dim (convex hull {w,a}) = &1 /\
          CARD {e | e IN L /\ aff_dim e = &1 /\ a IN e} =
          CARD {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} /\
          (CARD {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 1 \/
           CARD {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)`
  (LABEL_TAC "DEG") THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `a:real^N`] MOI_S8TB_LINK_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_S8TB_LINK_DEGREE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S8TB_EDGE_CARD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the degree-1 count *)
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FSB_DEG1_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `a:real^N` th) (ASSUME `{a:real^N} IN L`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  (* a boundary edge at w gives a degree-1 vertex a0 of the link *)
  SUBGOAL_THEN
   `?a0:real^N. {a0} IN L /\
       CARD {t | t IN c /\ aff_dim t = &2 /\ convex hull {w,a0} SUBSET t} = 1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN surface_boundary c` THEN
    REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `w:real^N`]
      MOI_FSB_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:real^N` THEN
    UNDISCH_TAC `CARD {t | t IN c /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t} = 1` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `A1 = {u:real^N | {u} IN L /\ CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1}` THEN
  SUBGOAL_THEN `FINITE (A1:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{u:real^N | {u} IN L}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a0:real^N) IN A1` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `a0:real^N` th) (ASSUME `{a0:real^N} IN L`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the link is an arc: chi = 1, so exactly two degree-1 vertices *)
  SUBGOAL_THEN `CARD (A1:real^N->bool) = 2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FSB_EULER_1DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `L:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INT_LE_TRANS; INT_ARITH `&1:int <= &2`];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      LABEL_TAC "E0" (el 0 cs) THEN LABEL_TAC "E1" (el 1 cs)) THEN
    SUBGOAL_THEN `~(CARD (A1:real^N->bool) = 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN UNDISCH_TAC `(a0:real^N) IN A1` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_S8TB_VERTEX_LINK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1) THENL
     [USE_THEN "E0" (MP_TAC o C MP (ASSUME `pl_sphere 1 (UNIONS (L:(real^N->bool)->bool))`));
      USE_THEN "E1" (MP_TAC o C MP (ASSUME `pl_ball 1 (UNIONS (L:(real^N->bool)->bool))`))] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `x - y = &0 <=> x = y`; REAL_ARITH `x - y = &1 <=> x = y + &1`;
                REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `~(CARD (A1:real^N->bool) = 0)` THEN
    UNDISCH_TAC
     `CARD (A1:real^N->bool) + 2 * CARD {e:real^N->bool | e IN L /\ aff_dim e = &1} =
      2 * CARD {u:real^N | {u} IN L}` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* the boundary edges at w are the hulls of w with the points of A1 *)
  SUBGOAL_THEN
   `{e | e IN c /\ aff_dim e = &1 /\ w IN e /\
         CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1} =
    IMAGE (\a:real^N. convex hull {w,a}) A1`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `w:real^N`]
        MOI_FSB_EDGE_AT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "A1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `a:real^N` th) (ASSUME `{a:real^N} IN L`))) THEN
      DISCH_THEN(SUBST1_TAC o el 3 o CONJUNCTS) THEN
      UNDISCH_TAC `CARD {r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      EXPAND_TAC "A1" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `a:real^N` th) (ASSUME `{a:real^N} IN L`))) THEN
      DISCH_THEN(fun th -> let cs = CONJUNCTS th in
        ASSUME_TAC (el 1 cs) THEN ASSUME_TAC (el 2 cs) THEN ASSUME_TAC (el 3 cs)) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN SET_TAC[];
        UNDISCH_TAC `CARD {e | e IN L /\ aff_dim e = &1 /\ (a:real^N) IN e} = 1` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `CARD (A1:real^N->bool)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN L /\ {b:real^N} IN L` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^N) IN A1` THEN UNDISCH_TAC `(b:real^N) IN A1` THEN
    EXPAND_TAC "A1" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = w) /\ ~(b:real^N = w)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `a:real^N` th) (ASSUME `{a:real^N} IN L`)));
      USE_THEN "DEG" (fun th -> MP_TAC(MP (SPEC `b:real^N` th) (ASSUME `{b:real^N} IN L`)))] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `convex hull {w:real^N,a} = convex hull {w,b}` THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; SEGMENT_EQ] THEN
  ASM SET_TAC[]);;

(* The boundary of a finite combinatorial 2-manifold with boundary is a     *)
(* finite disjoint union of PL circles (the boundary edges and their faces  *)
(* form a 1-complex with all degrees 2, MOI_S4L_CM1_CIRCLES).                *)

let MOI_FSB_BD_CIRCLES = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> FINITE (components (surface_boundary c)) /\
         (!j. j IN components (surface_boundary c) ==> pl_sphere 1 j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH")) THEN
  ASM_CASES_TAC `2 <= dimindex(:N)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `surface_boundary (c:(real^N->bool)->bool) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[surface_boundary; EMPTY_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      SUBGOAL_THEN `~({r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = {})`
      (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
       REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THENL
       [DISCH_TAC THEN UNDISCH_TAC
         `CARD {r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_LE_UNIV) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(2 <= dimindex(:N))` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
      REWRITE_TAC[COMPONENTS_EMPTY; FINITE_EMPTY; NOT_IN_EMPTY]]] THEN
  ABBREV_TAC
   `B = {s:real^N->bool | s IN c /\
                          ?e. e IN c /\ aff_dim e = &1 /\
                              CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1 /\
                              s face_of e}` THEN
  SUBGOAL_THEN `UNIONS B = surface_boundary (c:(real^N->bool)->bool)` (SUBST1_TAC o SYM)
  THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[surface_boundary] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4L_CM1_CIRCLES THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> convex s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      ASSUME_TAC (el 0 cs) THEN LABEL_TAC "SX" (el 1 cs) THEN
      LABEL_TAC "FC" (el 2 cs) THEN LABEL_TAC "IC" (el 3 cs)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; GEN_REWRITE_TAC I [SUBSET] THEN SIMP_TAC[IN_ELIM_THM]];
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "SX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [USE_THEN "FC" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN STRIP_TAC THEN
      USE_THEN "IC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim(e:real^N->bool) = &1`)) THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `s:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^N) IN surface_boundary c` ASSUME_TAC THENL
     [REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`e0:real^N->bool`; `{v:real^N}`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {e | e IN c /\ aff_dim e = &1 /\ (v:real^N) IN e /\
                         CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1}` THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC MOI_FSB_BD_DEGREE THEN ASM_REWRITE_TAC[]] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `e1:real^N->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `e:real^N->bool = e1` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`e:real^N->bool`; `e1:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ASM_REWRITE_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Dimension bound, purity and triangles at vertices, from the             *)
(* charts (MOI_S8TB_PURE, MOI_S8TB_DIM).                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_DIM = prove
 (`!c s:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S8TB_DIM) THEN ASM_SIMP_TAC[]);;

let MOI_FSB_PURE = prove
 (`!c s:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ s IN c /\ ~(s = {})
     ==> ?t. t IN c /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_PURE THEN ASM_REWRITE_TAC[]);;

let MOI_FSB_VTRI = prove
 (`!c v:real^N.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c
     ==> ?t. t IN c /\ aff_dim t = &2 /\ v IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`] MOI_FSB_PURE) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET]);;

