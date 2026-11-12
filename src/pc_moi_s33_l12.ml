(* ========================================================================= *)
(* pc_moi_s33_l12: Moise 33.1 Lemma 12 (GTM 47, p.236).  Main theorem       *)
(* S33_EULER : |- MOI_S33_EULER (pc_moi_s33_stmt.ml).                       *)
(* Route: Euler double counting over the pieces P v (the simplices of bx    *)
(* inside c v): a nonempty simplex lies in one piece, or in two exactly     *)
(* when it lies in a trace, and the trace complexes have chi 0.  With       *)
(* chi bx = chi (bc x) = 2 chi l = 2 V - 2 E and the planar bound           *)
(* chi + b <= 2 of each piece, all defects vanish: each piece is a disk     *)
(* with deg v - 1 holes.                                                     *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_fnd_tubed.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the graph l.  It is a finite simplicial complex with             *)
(* simplices of dimension at most 1; every vertex has an edge (connected    *)
(* union with an edge); the edges at v correspond to their far ends.        *)
(* ========================================================================= *)

let MOI_S3EU_TUBE_GRAPH = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> simplicial_complex l /\ FINITE l /\ lf_simplicial_complex l /\
         (!s. s IN l ==> aff_dim s <= &1) /\
         (!s f. s IN l /\ f face_of s ==> f IN l) /\
         connected (UNIONS l) /\ (?a. a IN l /\ aff_dim a = &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_tube; graph_in_complex; simplicial_subcomplex] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_MESON_TAC[]);;

(* Simplices of a locally finite complex are closed.                        *)

let MOI_S3EU_LF_CLOSED = prove
 (`!(l:(real^3->bool)->bool) s. lf_simplicial_complex l /\ s IN l ==> closed s`,
  REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]);;

(* A vertex of a connected graph with an edge lies on an edge.               *)

let MOI_S3EU_VERTEX_EDGE = prove
 (`!(l:(real^3->bool)->bool) v.
     FINITE l /\ lf_simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
     connected (UNIONS l) /\ (?a. a IN l /\ aff_dim a = &1) /\ {v} IN l
     ==> ?s. s IN l /\ aff_dim s = &1 /\ v IN s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a0:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC))))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN l /\ v IN r ==> r = {v}` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(aff_dim (r:real^3->bool) = -- &1)` ASSUME_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim (r:real^3->bool) = &1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (r:real^3->bool) = &0` MP_TAC THENL
     [MP_TAC(ISPEC `r:real^3->bool` AFF_DIM_GE) THEN
      SUBGOAL_THEN `aff_dim (r:real^3->bool) <= &1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(aff_dim (r:real^3->bool) = -- &1)` THEN
      UNDISCH_TAC `~(aff_dim (r:real^3->bool) = &1)` THEN INT_ARITH_TAC;
      REWRITE_TAC[AFF_DIM_EQ_0] THEN STRIP_TAC THEN
      UNDISCH_TAC `(v:real^3) IN r` THEN ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN a0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a0:real^3->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~connected (UNIONS l:real^3->bool)` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`{v:real^3}`; `UNIONS {r:real^3->bool | r IN l /\ ~(v IN r)}`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_SING];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_S3EU_LF_CLOSED]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_SING; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^3) IN r` THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `r = {v:real^3}` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN {v}` THEN REWRITE_TAC[IN_SING];
      DISJ2_TAC THEN EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_SING; IN_UNIONS] THEN
    EXISTS_TAC `v:real^3` THEN REWRITE_TAC[] THEN EXISTS_TAC `{v:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    UNDISCH_TAC `~(a0:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN EXISTS_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `a0:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3EU_DEG_POS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h /\ {v} IN l
     ==> 1 <= CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3EU_TUBE_GRAPH) THEN
  SUBGOAL_THEN `FINITE {s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MOI_S3EU_VERTEX_EDGE THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The edges at a vertex v and their far ends.                               *)

let MOI_S3EU_NBRS = prove
 (`!(l:(real^3->bool)->bool) v.
     simplicial_complex l /\ {v} IN l
     ==> FINITE {w | ~(w = v) /\ segment[v,w] IN l} /\
         {s | s IN l /\ aff_dim s = &1 /\ v IN s} =
         IMAGE (\w. segment[v,w]) {w | ~(w = v) /\ segment[v,w] IN l} /\
         CARD {w | ~(w = v) /\ segment[v,w] IN l} =
         CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `!w w'. w IN {w | ~(w = v) /\ segment[v,w] IN l} /\
                       w' IN {w | ~(w = v) /\ segment[v,w] IN l} /\
                       segment[v:real^3,w] = segment[v,w'] ==> w = w'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; SEGMENT_EQ] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s} =
                IMAGE (\w. segment[v,w]) {w | ~(w = v) /\ segment[v,w] IN l}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `s:real^3->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`; `s:real^3->bool`]
        MOI_FSA_EDGE_SEG) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `w:real^3` THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(v:real^3 = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {w | ~(w = v) /\ segment[v:real^3,w] IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^3. segment[v,w]`; `{w | ~(w = v) /\ segment[v:real^3,w] IN l}`]
      FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    UNDISCH_TAC `{s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s} =
                 IMAGE (\w. segment[v,w]) {w | ~(w = v) /\ segment[v,w] IN l}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `l:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  CONJ_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 2: the counts of the graph l: chi l is the number of vertices       *)
(* minus the number of edges, and the degrees sum to twice the number of    *)
(* edges (handshake, MOI_FTD_VERTEX_INCIDENCE at m = 1).                    *)
(* ========================================================================= *)

let MOI_S3EU_GRAPH_EULER = prove
 (`!l:(real^3->bool)->bool.
     FINITE l /\ (!s. s IN l ==> aff_dim s <= &1)
     ==> complex_euler l =
         &(CARD {v | {v} IN l}) - &(CARD {s | s IN l /\ aff_dim s = &1})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:(real^3->bool)->bool` MOI_FTD_EULER_DIM3) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INT_ARITH `x:int <= &1 ==> x <= &3`]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{s | s IN l /\ aff_dim (s:real^3->bool) = &2} = {} /\
                {s | s IN l /\ aff_dim (s:real^3->bool) = &3} = {}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[INT_ARITH `x:int <= &1 ==> ~(x = &2) /\ ~(x = &3)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `(:real^3)`] MOI_FTD_VERTEX_CARD) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CARD_CLAUSES; REAL_ADD_RID; REAL_SUB_RZERO]);;

let MOI_S3EU_HANDSHAKE = prove
 (`!l:(real^3->bool)->bool.
     FINITE l /\ lf_simplicial_complex l
     ==> FINITE {v | {v} IN l} /\
         sum {v | {v} IN l} (\v. &(CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s})) =
         &2 * &(CARD {s | s IN l /\ aff_dim s = &1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `1`] MOI_FTD_VERTEX_INCIDENCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN ARITH_TAC);;

(* ========================================================================= *)
(* Part 3: the hypotheses unpacked, and the traces at a vertex v.          *)
(* The traces are pairwise disjoint PL circles (disjoint pseudo-cells), so  *)
(* they are the components of their union, and there are deg v of them.     *)
(* ========================================================================= *)

let MOI_S3EU_HD_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> moi_s33_tube t l h /\
         (!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\ ~(s = s')
                 ==> DISJOINT (e s) (e s')) /\
         IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l} /\
         (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
                ==> c v INTER c w = (if segment[v,w] IN l then e(segment[v,w]) else {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S3EU_INV_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e x.
     moi_s33_inv t l h e x
     ==> FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
         UNIONS x SUBSET interior (IMAGE h (derived_nbhd t l)) /\
         frontier (UNIONS x) SUBSET UNIONS x /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> pl_sphere 1 (e(segment[u,v]) INTER frontier (UNIONS x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3D_BDX_SUBSET_W o CONJUNCT1 o
    REWRITE_RULE[moi_s33_inv]) THEN
  UNDISCH_TAC `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x` THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN MESON_TAC[]);;

let MOI_S3EU_TRACES = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x v.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ {v} IN l
     ==> FINITE {e(segment[v,w]) INTER frontier (UNIONS x) | w |
                 ~(w = v) /\ segment[v,w] IN l} /\
         components (UNIONS {e(segment[v,w]) INTER frontier (UNIONS x) | w |
                             ~(w = v) /\ segment[v,w] IN l}) =
         {e(segment[v,w]) INTER frontier (UNIONS x) | w | ~(w = v) /\ segment[v,w] IN l} /\
         CARD {e(segment[v,w]) INTER frontier (UNIONS x) | w |
               ~(w = v) /\ segment[v,w] IN l} =
         CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "edj")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3EU_TUBE_GRAPH) THEN
  MP_TAC(MATCH_MP MOI_S3EU_INV_FACTS (ASSUME
    `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tsp"))))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`] MOI_S3EU_NBRS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))) THEN
  SUBGOAL_THEN
   `{e(segment[v,w]) INTER frontier (UNIONS x) | w | ~(w = v) /\ segment[v,w] IN l} =
    IMAGE (\w. (e:(real^3->bool)->real^3->bool) (segment[v,w]) INTER frontier (UNIONS x))
          {w | ~(w = v) /\ segment[v:real^3,w] IN l}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w = v) /\ segment[v:real^3,w] IN l
        ==> closed ((e:(real^3->bool)->real^3->bool) (segment[v,w]) INTER
                    frontier (UNIONS x)) /\
            connected (e (segment[v,w]) INTER frontier (UNIONS x)) /\
            ~(e (segment[v,w]) INTER frontier (UNIONS x) = {})`
  (LABEL_TAC "sp") THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    USE_THEN "tsp" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[MOI_SLV_CIRCLE_CLOSED; MOI_FTA_PL_SPHERE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w w'. ~(w = v) /\ segment[v:real^3,w] IN l /\ ~(w' = v) /\ segment[v,w'] IN l /\
           ~(w = w')
           ==> DISJOINT ((e:(real^3->bool)->real^3->bool) (segment[v,w]) INTER
                         frontier (UNIONS x))
                        (e (segment[v,w']) INTER frontier (UNIONS x))`
  (LABEL_TAC "dj") THENL
   [MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(v:real^3 = w) /\ ~(v = w')` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool) (segment[v,w]))
                           (e (segment[v,w']))` MP_TAC THENL
     [USE_THEN "edj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
      ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE];
    MATCH_MP_TAC MOI_S5C_COMPONENTS_PARTITION THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      USE_THEN "sp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^3` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `w':real^3` THEN REPEAT DISCH_TAC THEN
      USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `w:real^3 = w'` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "dj" (MP_TAC o SPECL [`w:real^3`; `w':real^3`]) THEN
    REMOVE_THEN "sp" (MP_TAC o SPEC `w:real^3`) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 4: the simplices of bx and the pieces.  bx is a finite              *)
(* complex of dimension at most 2 triangulating Bd X, which lies in the     *)
(* union of the pieces c v.  Every nonempty simplex of bx lies in some c v  *)
(* (relative interior argument), and the number of pieces containing it is  *)
(* one more than the number of edges a with the simplex inside e a.         *)
(* ========================================================================= *)

let MOI_S3EU_BX_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx
     ==> simplicial_complex bx /\ FINITE bx /\ lf_simplicial_complex bx /\
         (!s. s IN bx ==> aff_dim s <= &2) /\
         UNIONS bx = frontier (UNIONS x) /\
         frontier (UNIONS x) SUBSET UNIONS {c v | {v} IN l}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
  MP_TAC(MATCH_MP MOI_S3EU_INV_FACTS (ASSUME
    `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x`)) THEN
  UNDISCH_TAC `moi_s33_pieces (l:(real^3->bool)->bool) e c x bx` THEN
  REWRITE_TAC[moi_s33_pieces] THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (bx:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_DIM];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
      UNDISCH_TAC `frontier (UNIONS x) SUBSET (UNIONS x:real^3->bool)` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]]]);;

let MOI_S3EU_COVER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx s.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\
     s IN bx /\ ~(s = {})
     ==> ?v. {v} IN l /\ s SUBSET c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_BX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^3. p IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (s:real^3->bool)` (fun th -> ASM_SIMP_TAC[th; RELATIVE_INTERIOR_EQ_EMPTY]) THEN
    UNDISCH_TAC `lf_simplicial_complex (bx:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS bx` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `?v. {v} IN l /\ (p:real^3) IN (c:real^3->real^3->bool) v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (UNIONS x) SUBSET UNIONS {(c:real^3->real^3->bool) v | {v} IN l}` THEN
    UNDISCH_TAC `(p:real^3) IN frontier (UNIONS x)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. r IN bx /\ r SUBSET (c:real^3->real^3->bool) v /\ (p:real^3) IN r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_pieces (l:(real^3->bool)->bool) e c x bx` THEN
    REWRITE_TAC[moi_s33_pieces] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^3->bool) INTER r = s` MP_TAC THENL
   [ALL_TAC; UNDISCH_TAC `(r:real^3->bool) SUBSET (c:real^3->real^3->bool) v` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `((s:real^3->bool) INTER r) face_of s` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (bx:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(s:real^3->bool) INTER r`; `s:real^3->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:real^3) IN relative_interior s` THEN
  UNDISCH_TAC `(p:real^3) IN r` THEN UNDISCH_TAC `(p:real^3) IN s` THEN SET_TAC[]);;

let MOI_S3EU_COUNT = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx s.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\
     s IN bx /\ ~(s = {})
     ==> CARD {v | {v} IN l /\ s SUBSET c v} =
         1 + CARD {a | a IN l /\ aff_dim a = &1 /\ s SUBSET e a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "edj")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cc")))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3EU_TUBE_GRAPH) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`; `s:real^3->bool`]
               MOI_S3EU_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!v w. {v} IN l /\ s SUBSET (c:real^3->real^3->bool) v /\ {w} IN l /\ s SUBSET c w /\
          ~(v = w)
          ==> segment[v,w] IN l /\ aff_dim (segment[v:real^3,w]) = &1 /\
              s SUBSET (e:(real^3->bool)->real^3->bool) (segment[v,w])`
  (LABEL_TAC "k1") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cc" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET (c:real^3->real^3->bool) v` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET (c:real^3->real^3->bool) w` THEN SET_TAC[];
      UNDISCH_TAC `~(s:real^3->bool = {})` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET (c:real^3->real^3->bool) v` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET (c:real^3->real^3->bool) w` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a a'. a IN l /\ aff_dim a = &1 /\ s SUBSET (e:(real^3->bool)->real^3->bool) a /\
           a' IN l /\ aff_dim a' = &1 /\ s SUBSET e a' ==> a = a'`
  (LABEL_TAC "k2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "edj" (MP_TAC o SPECL [`a:real^3->bool`; `a':real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(s:real^3->bool = {})` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET (e:(real^3->bool)->real^3->bool) a` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET (e:(real^3->bool)->real^3->bool) a'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN l /\ aff_dim a = &1 /\ s SUBSET (e:(real^3->bool)->real^3->bool) a
        ==> ?p q. ~(p = q) /\ a = segment[p,q] /\
                  {p} IN l /\ s SUBSET (c:real^3->real^3->bool) p /\
                  {q} IN l /\ s SUBSET c q`
  (LABEL_TAC "k3") THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `a:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cc" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[p:real^3,q] IN l` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET (e:(real^3->bool)->real^3->bool) a` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?a. a IN l /\ aff_dim a = &1 /\ s SUBSET (e:(real^3->bool)->real^3->bool) a`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `{a | a IN l /\ aff_dim a = &1 /\ s SUBSET (e:(real^3->bool)->real^3->bool) a} = {a}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `a':real^3->bool` THEN EQ_TAC THENL
       [STRIP_TAC THEN USE_THEN "k2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "k3" (MP_TAC o SPEC `a:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `{v | {v} IN l /\ s SUBSET (c:real^3->real^3->bool) v} = {p,q}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `u:real^3` THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_CASES_TAC `u:real^3 = p` THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `u:real^3 = q` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "k1" (MP_TAC o SPECL [`u:real^3`; `p:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "k2" (MP_TAC o SPECL [`segment[u:real^3,p]`; `segment[p:real^3,q]`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SEGMENT_EQ] THEN
        UNDISCH_TAC `~(u:real^3 = p)` THEN UNDISCH_TAC `~(u:real^3 = q)` THEN SET_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    SUBGOAL_THEN
     `{a | a IN l /\ aff_dim a = &1 /\ s SUBSET (e:(real^3->bool)->real^3->bool) a} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{v | {v} IN l /\ s SUBSET (c:real^3->real^3->bool) v} = {v0}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `u:real^3` THEN EQ_TAC THENL
       [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        USE_THEN "k1" (MP_TAC o SPECL [`u:real^3`; `v0:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[CARD_SING; CARD_CLAUSES] THEN ARITH_TAC]);;

(* ========================================================================= *)
(* Part 5: the trace complexes.  For an edge a = segment[p,q] the           *)
(* simplices of bx inside e a form a finite complex triangulating the trace *)
(* e a INTER Bd X (a point of the trace lies in simplices of both pieces    *)
(* c p and c q, and their common face lies in c p INTER c q = e a), a PL    *)
(* circle, so its Euler characteristic is 0.                                 *)
(* ========================================================================= *)

let MOI_S3EU_PIECE_POINT = prove
 (`!(l:(real^3->bool)->bool) e c x bx v (y:real^3).
     moi_s33_pieces l e c x bx /\ {v} IN l /\ y IN c v /\ y IN frontier (UNIONS x)
     ==> ?r. r IN bx /\ r SUBSET c v /\ y IN r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_pieces] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `v:real^3` o last o CONJUNCTS)
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S3EU_TRACE_EULER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx a.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\
     a IN l /\ aff_dim a = &1
     ==> complex_euler {s | s IN bx /\ s SUBSET e a} = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_BX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cc")))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3EU_TUBE_GRAPH) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(MATCH_MP MOI_S3EU_INV_FACTS (ASSUME
    `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x`)) THEN
  DISCH_THEN(LABEL_TAC "tsp" o last o CONJUNCTS) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `a:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `UNIONS {s | s IN bx /\ s SUBSET (e:(real^3->bool)->real^3->bool) (segment[p,q])} =
    e (segment[p,q]) INTER frontier (UNIONS x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:(real^3->bool)->real^3->bool) (segment[p,q]) = c p INTER c q`
    (LABEL_TAC "ecc") THENL
     [USE_THEN "cc" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        UNDISCH_TAC `UNIONS bx = frontier (UNIONS x:real^3->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]];
      STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN (c:real^3->real^3->bool) p /\ y IN c q` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool) (segment[p,q])` THEN
        USE_THEN "ecc" SUBST1_TAC THEN REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                     `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                     `bx:(real^3->bool)->bool`; `p:real^3`; `y:real^3`]
                    MOI_S3EU_PIECE_POINT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real^3->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                     `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                     `bx:(real^3->bool)->bool`; `q:real^3`; `y:real^3`]
                    MOI_S3EU_PIECE_POINT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r2:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(r1:real^3->bool) INTER r2` THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (bx:(real^3->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
        USE_THEN "ecc" SUBST1_TAC THEN
        UNDISCH_TAC `(r1:real^3->bool) SUBSET (c:real^3->real^3->bool) p` THEN
        UNDISCH_TAC `(r2:real^3->bool) SUBSET (c:real^3->real^3->bool) q` THEN SET_TAC[];
        ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{s | s IN bx /\ s SUBSET (e:(real^3->bool)->real^3->bool) (segment[p,q])}`
    COMPLEX_EULER_VALUES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `bx:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `bx:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
         [SET_TAC[];
          REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
           [UNDISCH_TAC `lf_simplicial_complex (bx:(real^3->bool)->bool)` THEN
            REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
            ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "tsp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 6: Euler additivity over the pieces.  Weighting each simplex        *)
(* by its sign, the sum over the vertices of chi of the pieces counts each  *)
(* nonempty simplex of bx once more than the number of trace complexes      *)
(* containing it; the trace complexes have chi 0, so the pieces sum to      *)
(* chi bx.  chi bx = chi (boundary_complex x) by PL invariance.              *)
(* ========================================================================= *)

let MOI_S3EU_SUM_SWAP_IND = prove
 (`!(V:A->bool) (bx:B->bool) (P:A->B->bool) (f:B->real).
     FINITE V /\ FINITE bx
     ==> sum V (\v. sum bx (\s. if P v s then f s else &0)) =
         sum bx (\s. &(CARD {v | v IN V /\ P v s}) * f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(v:A) (s:B). if P v s then (f:B->real) s else &0`; `V:A->bool`;
                 `bx:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM SUM_CONST; FINITE_RESTRICT] THEN REWRITE_TAC[SUM_RESTRICT_SET]);;

let MOI_S3EU_SUM_GEN = prove
 (`!(bx:(real^3->bool)->bool) (V:A->bool) (B:K->bool)
    (P:A->(real^3->bool)->bool) (Q:K->(real^3->bool)->bool).
     FINITE bx /\ FINITE V /\ FINITE B /\
     (!s. s IN bx /\ ~(s = {})
          ==> CARD {v | v IN V /\ P v s} = 1 + CARD {a | a IN B /\ Q a s})
     ==> sum V (\v. complex_euler {s | s IN bx /\ P v s}) =
         complex_euler bx + sum B (\a. complex_euler {s | s IN bx /\ Q a s})`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM_ALT; FINITE_RESTRICT; SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[MOI_S3EU_SUM_SWAP_IND] THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID]);;

let MOI_S3EU_PIECES_SUM = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx
     ==> sum {v | {v} IN l} (\v. complex_euler {s | s IN bx /\ s SUBSET c v}) =
         complex_euler bx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_BX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_TUBE_GRAPH (CONJUNCT1 (MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `{v:real^3 | {v} IN l}`;
                 `{a:real^3->bool | a IN l /\ aff_dim a = &1}`;
                 `\(v:real^3) (s:real^3->bool). s SUBSET (c:real^3->real^3->bool) v`;
                 `\(a:real^3->bool) (s:real^3->bool).
                     s SUBSET (e:(real^3->bool)->real^3->bool) a`]
                MOI_S3EU_SUM_GEN) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_S3EU_HANDSHAKE];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                    `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`; `s:real^3->bool`]
                   MOI_S3EU_COUNT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM CONJ_ASSOC]]];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC(REAL_ARITH `y = &0 ==> x + y = x`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3EU_TRACE_EULER THEN
  MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                        `h:real^3->real^3`; `c:real^3->real^3->bool`;
                        `x:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3EU_BX_EULER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx
     ==> complex_euler bx = complex_euler (boundary_complex x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_BX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`]
    (MP MOI_S3D_INV_BC (CONJ (INST_TYPE [`:3`,`:N`] BOUNDARY_COMPLEX_SURFACE)
                             COMPLEX_BOUNDARY_FRONTIER_3))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_SAME_POLYHEDRON THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
  ASM_MESON_TAC[combinatorial_manifold]);;

(* ========================================================================= *)
(* Part 7: the planar bound for each piece and S33_EULER.  Each piece       *)
(* P v is a finite connected nonempty surface with deg v boundary circles,  *)
(* so chi (P v) + deg v <= 2 (SURFACE_EULER_PLANAR at N = 3).  The defects  *)
(* sum to 2 V - chi bx - 2 E = 2 V - 2 chi l - 2 E = 0, so all vanish, and  *)
(* the equality clause gives the holed disks with d = deg v - 1.            *)
(* ========================================================================= *)

let MOI_S3EU_PLANAR3 = INST_TYPE [`:3`,`:N`] SURFACE_EULER_PLANAR;;

let MOI_S3EU_PIECE_PLANAR = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx v.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\ {v} IN l
     ==> FINITE {s | s IN bx /\ s SUBSET c v} /\
         combinatorial_manifold_with_boundary 2 {s | s IN bx /\ s SUBSET c v} /\
         connected (UNIONS {s | s IN bx /\ s SUBSET c v}) /\
         ~(UNIONS {s | s IN bx /\ s SUBSET c v} = {}) /\
         CARD (components (surface_boundary {s | s IN bx /\ s SUBSET c v})) =
         CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3EU_TUBE_GRAPH) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `v:real^3`] MOI_S3EU_TRACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (LABEL_TAC "card"))) THEN
  MP_TAC(ASSUME `moi_s33_pieces (l:(real^3->bool)->bool) e c x bx`) THEN
  REWRITE_TAC[moi_s33_pieces] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `v:real^3` o last o CONJUNCTS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb")))) THEN
  SUBGOAL_THEN `?w. ~(w = v) /\ segment[v:real^3,w] IN l` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                  `v:real^3`] MOI_S3EU_DEG_POS) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`] MOI_S3EU_NBRS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
      REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    ASM_REWRITE_TAC[];
    USE_THEN "un" SUBST1_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "un" SUBST1_TAC THEN
    SUBGOAL_THEN `{w:real^3} IN l` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP MOI_S3EU_TUBE_GRAPH (ASSUME
        `moi_s33_tube (t:(real^3->bool)->bool) l (h:real^3->real^3)`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`segment[v:real^3,w]`; `{w:real^3}`] o el 4 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:(real^3->bool)->real^3->bool) (segment[v,w]) SUBSET c v` MP_TAC THENL
     [MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
        `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `w:real^3`] o last o CONJUNCTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(w:real^3 = v)` THEN MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP MOI_S3EU_INV_FACTS (ASSUME
      `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `w:real^3`] o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `~(w:real^3 = v)` THEN MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_PL_SPHERE_NONEMPTY) THEN SET_TAC[];
    USE_THEN "sb" SUBST1_TAC THEN USE_THEN "comp" SUBST1_TAC THEN
    USE_THEN "card" ACCEPT_TAC]);;

let MOI_S3EU_PIECE_INEQ = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx v.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\ {v} IN l
     ==> complex_euler {s | s IN bx /\ s SUBSET c v} +
         &(CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}) <= &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3EU_PIECE_PLANAR) THEN
  DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    MP_TAC(MATCH_MP MOI_S3EU_PLANAR3
      (end_itlist CONJ [el 0 cs; el 1 cs; el 2 cs; el 3 cs])) THEN
    MP_TAC(el 4 cs)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN STRIP_TAC);;

let MOI_S3EU_PIECE_EQ = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\
     complex_euler (boundary_complex x) = &2 * complex_euler l
     ==> !v. {v} IN l
             ==> complex_euler {s | s IN bx /\ s SUBSET c v} +
                 &(CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}) = &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3EU_TUBE_GRAPH (CONJUNCT1 (MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
    `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  MP_TAC(ISPEC `l:(real^3->bool)->bool` MOI_S3EU_HANDSHAKE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l:(real^3->bool)->bool` MOI_S3EU_GRAPH_EULER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_PIECES_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_BX_EULER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\v:real^3. &2 - (complex_euler {s | s IN bx /\ s SUBSET (c:real^3->real^3->bool) v} +
                      &(CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s}))`;
    `{v:real^3 | {v} IN l}`] SUM_POS_EQ_0) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                    `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`; `v:real^3`]
                   MOI_S3EU_PIECE_INEQ) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> MATCH_ACCEPT_TAC(MATCH_MP
        (REAL_ARITH `!a. a <= &2 ==> &0 <= &2 - a`) th));
      ASM_SIMP_TAC[SUM_SUB; SUM_ADD; SUM_CONST] THEN
      ABBREV_TAC `nv = CARD {v:real^3 | {v} IN l}` THEN
      ABBREV_TAC `ne = CARD {s:real^3->bool | s IN l /\ aff_dim s = &1}` THEN
      REAL_ARITH_TAC];
    DISCH_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `!a. &2 - a = &0 <=> a = &2`]]);;

let S33_EULER = prove
 (MOI_S33_EULER,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s33_holed] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `dg = CARD {s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s}` THEN
  ABBREV_TAC `ch = complex_euler {s | s IN bx /\ s SUBSET (c:real^3->real^3->bool) v}` THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`] MOI_S3EU_PIECE_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `v:real^3`] MOI_S3EU_DEG_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP MOI_S3EU_HD_FACTS (ASSUME
      `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c`)) THEN
    SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`; `v:real^3`]
               MOI_S3EU_PIECE_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    MP_TAC(MATCH_MP MOI_S3EU_PLANAR3
      (end_itlist CONJ [el 0 cs; el 1 cs; el 2 cs; el 3 cs])) THEN
    ASSUME_TAC(el 4 cs)) THEN
  DISCH_THEN(MP_TAC o SPEC `dg - 1` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `1 <= dg` THEN ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      UNDISCH_TAC `ch + &dg = &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `g:real^3->real^2`; `dg - 1`] THEN
  MP_TAC(ASSUME `moi_s33_pieces (l:(real^3->bool)->bool) e c x bx`) THEN
  REWRITE_TAC[moi_s33_pieces] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sb")))) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `1 <= dg` THEN ARITH_TAC;
    USE_THEN "un" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "sb" ACCEPT_TAC]);;

