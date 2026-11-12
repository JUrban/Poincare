(* ========================================================================= *)
(* pc_moi_s33_l9: Moise Sec 33 Lemma 9, p.234.  Main theorem                *)
(* S39_L9_FROM : |- MOI_S39_L9_FROM of pc_moi_s33_l9stmt.ml, that is        *)
(* GP_BODY /\ PUSH_BODY ==> MOI_S33_L9: with the general position of        *)
(* loop theorem disks against the pseudo-cells and the push-off as inputs   *)
(* (pc_moi_s33_gp and pc_moi_s33_push), no loop theorem disk lies in Int    *)
(* N'.  Route (book p.234, DG section33_not_isLoopTheoremDisk): an LTD in   *)
(* general position meets the pseudo-cells in finitely many circles and     *)
(* arcs; an innermost circle bounds a disk in one piece, so by Lemma 8 its  *)
(* disk in the pseudo-cell misses the centre, and the swap with the push    *)
(* removes it; with no circles left an arc and an arc of the trace bound a  *)
(* minimal disk in the pseudo-cell, one of the two new disks is an LTD      *)
(* (theta lemma for null-homotopies), and the push removes the arc; a disk  *)
(* missing the pseudo-cells lies in one piece, against noltd.               *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s33_l9stmt.ml";;
needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_fnd_gpa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1. The handle decomposition: the union of the pseudo-cells, the    *)
(* clauses of moi_s33_hd one at a time, edges of the graph, pieces at the  *)
(* edges, and the components of N' minus the pseudo-cells (one per         *)
(* vertex).                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_HD_TUBE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool).
     moi_s33_hd t l h e c ==> moi_s33_tube t l h`,
  SIMP_TAC[moi_s33_hd]);;

let MOI_S3L9_HD_PC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> pseudo_cell (e(segment[u,v])) (moi_s33_rim t l h u v) (h(midpoint(u,v))) /\
         e(segment[u,v]) INTER IMAGE h (UNIONS l) = {h(midpoint(u,v))} /\
         e(segment[u,v]) INTER frontier (IMAGE h (derived_nbhd t l)) =
         moi_s33_rim t l h u v`,
  REWRITE_TAC[moi_s33_hd] THEN MESON_TAC[]);;

let MOI_S3L9_HD_DISJ = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) s s'.
     moi_s33_hd t l h e c /\ s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\
     ~(s = s')
     ==> DISJOINT (e s) (e s')`,
  REWRITE_TAC[moi_s33_hd] THEN MESON_TAC[]);;

let MOI_S3L9_HD_PIECE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) v.
     moi_s33_hd t l h e c /\ {v} IN l
     ==> c v = closure (connected_component
                 (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h v))`,
  REWRITE_TAC[moi_s33_hd; moi_s39_pcs] THEN MESON_TAC[]);;

let MOI_S3L9_HD_COVER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool).
     moi_s33_hd t l h e c
     ==> IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l}`,
  SIMP_TAC[moi_s33_hd]);;

let MOI_S3L9_HD_MEET = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) v w.
     moi_s33_hd t l h e c /\ {v} IN l /\ {w} IN l /\ ~(v = w)
     ==> c v INTER c w = (if segment[v,w] IN l then e(segment[v,w]) else {})`,
  REWRITE_TAC[moi_s33_hd] THEN MESON_TAC[]);;

(* The tube: l is a finite simplicial complex, its edges are segments, N    *)
(* and N' are compact, N is a finite union of simplices.                    *)

let MOI_S3L9_TUBE_BASIC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> FINITE l /\ simplicial_complex l /\
         FINITE (derived_nbhd_complex t l) /\
         UNIONS (derived_nbhd_complex t l) = derived_nbhd t l /\
         (!s. s IN derived_nbhd_complex t l ==> ?n. n simplex s) /\
         compact (derived_nbhd t l) /\ derived_nbhd t l SUBSET UNIONS t /\
         h continuous_on derived_nbhd t l /\
         compact (IMAGE h (derived_nbhd t l)) /\
         (!x y. x IN derived_nbhd t l /\ y IN derived_nbhd t l /\ h x = h y ==> x = y) /\
         (!s. s IN l /\ aff_dim s = &1
              ==> ?u v. ~(u = v) /\ s = segment[u,v] /\ {u} IN l /\ {v} IN l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_tube; graph_in_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_complex] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simplicial_subcomplex; lf_simplicial_complex; SUBSET]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:real^3->real^3) continuous_on derived_nbhd t l` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[lf_simplicial_complex]) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_EDGE THEN ASM_REWRITE_TAC[]]);;

(* Pieces at an edge: both ends are vertices, the pseudo-cell is the       *)
(* intersection of the two pieces.                                          *)

let MOI_S3L9_EDGE_PIECES = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> {u} IN l /\ {v} IN l /\ aff_dim(segment[u,v]) = &1 /\
         c u INTER c v = e(segment[u,v]) /\
         e(segment[u,v]) SUBSET c u /\ e(segment[u,v]) SUBSET c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{u:real^3} IN l /\ {v:real^3} IN l` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
    REWRITE_TAC[moi_s33_tube; graph_in_complex; simplicial_subcomplex] THEN
    STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `segment[u:real^3,v]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_HD_MEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[]);;

(* A piece meeting a pseudo-cell is a piece at one of its ends.             *)

let MOI_S3L9_PIECE_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) u v w.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l /\ {w} IN l /\
     ~(c w INTER e(segment[u,v]) = {})
     ==> w = u \/ w = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_EDGE_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `w:real^3`; `u:real^3`] MOI_S3L9_HD_MEET) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[w,u])) (e(segment[u:real^3,v]))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                     `c:real^3->real^3->bool`; `segment[w:real^3,u]`;
                     `segment[u:real^3,v]`] MOI_S3L9_HD_DISJ) THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ASM SET_TAC[]]);;

(* Edges are segments between vertices; pieces lie in N'; pseudo-cells    *)
(* are closed.                                                               *)

let MOI_S3L9_EDGE_SEG = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) s.
     moi_s33_hd t l h e c /\ s IN l /\ aff_dim s = &1
     ==> ?u v. ~(u = v) /\ s = segment[u,v] /\ {u} IN l /\ {v} IN l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3L9_TUBE_BASIC) THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]);;

let MOI_S3L9_PIECE_SUBSET = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) v.
     moi_s33_hd t l h e c /\ {v} IN l
     ==> c v SUBSET IMAGE h (derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3L9_HD_COVER) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S3L9_PC_CLOSED = prove
 (`!(e:real^3->bool) j p. pseudo_cell e j p ==> closed e`,
  REWRITE_TAC[pseudo_cell] THEN MESON_TAC[CLOSED_CLOSURE]);;

(* The pseudo-cells lie in N' and are compact; so is their union.            *)

let MOI_S3L9_PCS_BASIC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool).
     moi_s33_hd t l h e c
     ==> (!s. s IN l /\ aff_dim s = &1
              ==> e s SUBSET IMAGE h (derived_nbhd t l) /\ compact (e s)) /\
         moi_s39_pcs l e SUBSET IMAGE h (derived_nbhd t l) /\
         compact (moi_s39_pcs l e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_TUBE_BASIC) THEN
  SUBGOAL_THEN
   `!s. s IN l /\ aff_dim s = &1
        ==> e s SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l) /\ compact (e s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `s:real^3->bool`] MOI_S3L9_EDGE_SEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_EDGE_PIECES) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_HD_PC) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `u:real^3`] MOI_S3L9_PIECE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S3L9_PC_CLOSED o CONJUNCT1) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `e(segment[u:real^3,v]) SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s39_pcs] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (e:(real^3->bool)->real^3->bool) l` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2. Components of N' minus the pseudo-cells: N' is locally connected *)
(* (a homeomorphic image of a finite union of simplices), so each component *)
(* is open in N' and is the component of a vertex image; a connected set in *)
(* N' missing the pseudo-cells lies in one piece.  The loop theorem disks;  *)
(* the last step of Lemma 9 (a disk missing the pseudo-cells lies in a      *)
(* piece, against noltd).                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_NP_LOCCONN = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h ==> locally connected (IMAGE h (derived_nbhd t l))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_TUBE_BASIC) THEN
  SUBGOAL_THEN `locally connected (derived_nbhd (t:(real^3->bool)->bool) l)` MP_TAC THENL
   [SUBGOAL_THEN `derived_nbhd (t:(real^3->bool)->bool) l = UNIONS (derived_nbhd_complex t l)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_CONNECTED_CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED;
              CONVEX_IMP_LOCALLY_CONNECTED];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
  MATCH_MP_TAC HOMEOMORPHIC_LOCAL_CONNECTEDNESS THEN
  REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `h:real^3->real^3` THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[]);;

let MOI_S3L9_COMPONENT_VERTEX = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) y.
     moi_s33_hd t l h e c /\ y IN IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e
     ==> ?v. {v} IN l /\
             connected_component (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) y =
             connected_component (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `np = IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN
  ABBREV_TAC `pp = moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
  SUBGOAL_THEN `locally connected (np DIFF pp:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN EXISTS_TAC `np:real^3->bool` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "np" THEN MATCH_MP_TAC MOI_S3L9_NP_LOCCONN THEN
      ASM_MESON_TAC[MOI_S3L9_HD_TUBE];
      MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN EXPAND_TAC "pp" THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_MESON_TAC[MOI_S3L9_PCS_BASIC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean np) (connected_component (np DIFF pp) (y:real^3))`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `np DIFF pp:real^3->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED] THEN
    MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN EXPAND_TAC "pp" THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_MESON_TAC[MOI_S3L9_PCS_BASIC];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?v:real^3. {v} IN (l:(real^3->bool)->bool) /\ (y:real^3) IN (c:real^3->real^3->bool) v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN np DIFF pp` THEN EXPAND_TAC "np" THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3L9_HD_COVER) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^3) IN closure (connected_component (np DIFF pp) ((h:real^3->real^3) v))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`] MOI_S3L9_HD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN w` ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN connected_component (np DIFF pp) y` MP_TAC THENL
     [REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
      ASM_REWRITE_TAC[GSYM IN];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((w:real^3->bool) INTER connected_component (np DIFF pp) ((h:real^3->real^3) v) = {})`
  MP_TAC THENL
   [MP_TAC(ISPECL [`w:real^3->bool`;
                   `connected_component (np DIFF pp) ((h:real^3->real^3) v)`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN connected_component (np DIFF pp) y` ASSUME_TAC THENL
   [SUBGOAL_THEN `connected_component (np DIFF pp) ((h:real^3->real^3) v) SUBSET (np:real^3->bool)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`np DIFF pp:real^3->bool`; `h(v:real^3):real^3`]
        CONNECTED_COMPONENT_SUBSET) THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`np DIFF pp:real^3->bool`; `y:real^3`; `z:real^3`]
    CONNECTED_COMPONENT_EQ) THEN
  MP_TAC(ISPECL [`np DIFF pp:real^3->bool`; `h(v:real^3):real^3`; `z:real^3`]
    CONNECTED_COMPONENT_EQ) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S3L9_CONNECTED_PIECE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) s.
     moi_s33_hd t l h e c /\ connected s /\ ~(s = {}) /\
     s SUBSET IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e
     ==> ?v. {v} IN l /\ s SUBSET c v /\
             s SUBSET connected_component
                        (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `y:real^3`] MOI_S3L9_COMPONENT_VERTEX) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `s SUBSET connected_component
               (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF moi_s39_pcs l e) (h(v:real^3))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `v:real^3`] MOI_S3L9_HD_PIECE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS]);;

(* Loop theorem disks.                                                       *)

let MOI_S3L9_LTD_BASIC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) x d.
     moi_s33_ltd t l h x d
     ==> ?j. pl_cell_with_boundary 2 d j /\ pl_sphere 1 j /\
             d SUBSET moi_s33_ww t l h /\
             d INTER frontier (UNIONS x) = j /\
             ~(?a. homotopic_with (\q. T)
                     (subtopology euclidean j, subtopology euclidean (frontier (UNIONS x)))
                     (\y. y) (\y. a)) /\
             compact d /\ connected d /\ ~(d = {}) /\ j SUBSET d /\
             compact j /\ ~(j = {}) /\
             connected (d DIFF j) /\ ~(d DIFF j = {}) /\
             d SUBSET interior (IMAGE h (derived_nbhd t l)) /\
             DISJOINT d (IMAGE h (UNIONS l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_ltd] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `compact (k:real^3->bool) /\ convex k /\ polytope k /\ ~(k = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      DISCH_TAC THEN UNDISCH_TAC `&2 simplex (k:real^3->bool)` THEN
      ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `relative_frontier (k:real^3->bool) SUBSET k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF IMAGE (f:real^3->real^3) (relative_frontier k) =
                IMAGE f (relative_interior k)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN
    UNDISCH_TAC `!x. x IN k ==> (g:real^3->real^3)(f x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 d (IMAGE (f:real^3->real^3) (relative_frontier k))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (f:real^3->real^3) (relative_frontier k))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_sphere] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `d:real^3->bool`] THEN
    ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (d:real^3->bool) /\ connected d /\ ~(d = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; CONNECTED_CONTINUOUS_IMAGE; CONVEX_CONNECTED;
                 IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^3->real^3) (relative_frontier k)) /\
                ~(IMAGE f (relative_frontier k) = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (f:real^3->real^3) (relative_interior k)) /\
                ~(IMAGE f (relative_interior k) = {})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_EQ_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `d SUBSET moi_s33_ww t l h` THEN REWRITE_TAC[moi_s33_ww] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM SET_TAC[]);;

(* The last step of Lemma 9: a loop theorem disk missing the pseudo-cells.  *)

let MOI_S3L9_FINAL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d.
     moi_s33_hd t l h e c /\ moi_s33_noltd t l h c x /\ moi_s33_ltd t l h x d /\
     d INTER moi_s39_pcs l e = {}
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `d:real^3->bool`] MOI_S3L9_CONNECTED_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_s33_noltd t l h c x` THEN REWRITE_TAC[moi_s33_noltd] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `d:real^3->bool`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 3. Topology in the open cell of a pseudo-cell.  A topological       *)
(* circle in the plane bounds the closed disk s UNION inside s              *)
(* (JORDAN_SCHOENFLIES); through the chart of e DIFF j onto the open unit   *)
(* disk every circle jj in e DIFF j bounds a closed disk in e DIFF j, whose *)
(* interior is open there.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_JS_DISK = prove
 (`!s:real^2->bool.
     s homeomorphic sphere(vec 0:real^2,&1)
     ==> ?f g. homeomorphism (cball(vec 0:real^2,&1),s UNION inside s) (f,g) /\
               IMAGE f (sphere(vec 0:real^2,&1)) = s`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_TAC `f1:real^2->real^2`)) THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `circlepath(vec 0:real^2,&1)`;
                 `f0:real^2->real^2`; `f1:real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS;
               REAL_OF_NUM_EQ; ARITH_EQ; INSIDE_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x:real^2. k'((k:real^2->real^2) x) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^2),(:real^2)) (k:real^2->real^2,k')` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k':real^2->real^2`; `k:real^2->real^2`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    REWRITE_TAC[GSYM SPHERE_UNION_BALL] THEN
    UNDISCH_TAC `IMAGE (k:real^2->real^2) s = sphere(vec 0,&1)` THEN
    UNDISCH_TAC `IMAGE (k:real^2->real^2) (inside s) = ball(vec 0,&1)` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM SET_TAC[];
    UNDISCH_TAC `IMAGE (k:real^2->real^2) s = sphere(vec 0,&1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[]]);;

let MOI_S3L9_CELL_CHART = prove
 (`!(e:real^3->bool) j p.
     pseudo_cell e j p
     ==> ?phi:real^3->real^2 psi.
           homeomorphism (e DIFF j,ball(vec 0:real^2,&1)) (phi,psi)`,
  REWRITE_TAC[pseudo_cell; homeomorphic] THEN MESON_TAC[]);;

let MOI_S3L9_CELL_DISK = prove
 (`!(e:real^3->bool) j (phi:real^3->real^2) psi jj.
     homeomorphism (e DIFF j,ball(vec 0:real^2,&1)) (phi,psi) /\
     jj SUBSET e DIFF j /\ jj homeomorphic sphere(vec 0:real^2,&1)
     ==> disk_with_boundary (IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj))) jj /\
         IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj)) SUBSET e DIFF j /\
         jj SUBSET IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj)) /\
         compact (IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj))) /\
         IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj)) DIFF jj =
         IMAGE psi (inside(IMAGE phi jj)) /\
         inside(IMAGE phi jj) SUBSET ball(vec 0,&1) /\
         (!y. y IN e DIFF j
              ==> (y IN IMAGE psi (inside(IMAGE phi jj)) <=>
                   phi y IN inside(IMAGE phi jj))) /\
         open_in (subtopology euclidean (e DIFF j)) (IMAGE psi (inside(IMAGE phi jj)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^2) jj SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (phi:real^3->real^2) (e DIFF j) = ball(vec 0,&1)` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET e DIFF j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^3) (IMAGE phi jj) = jj` ASSUME_TAC THENL
   [UNDISCH_TAC `!x. x IN e DIFF j ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET e DIFF j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^2) jj homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(jj:real^3->bool) homeomorphic IMAGE (phi:real^3->real^2) jj`
    MP_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^2`; `psi:real^2->real^3`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`e DIFF j:real^3->bool`; `ball(vec 0:real^2,&1)`] THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`IMAGE (phi:real^3->real^2) jj`; `jj:real^3->bool`;
                     `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (phi:real^3->real^2) jj)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:real^3->real^2) jj`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside(IMAGE (phi:real^3->real^2) jj) SUBSET ball(vec 0,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (phi:real^3->real^2) jj` MOI_S3L9_JS_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `a = IMAGE (phi:real^3->real^2) jj UNION inside(IMAGE phi jj)` THEN
  SUBGOAL_THEN `a SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (a,IMAGE psi a) (psi:real^2->real^3,phi)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&1)`; `e DIFF j:real^3->bool`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,&1)) = e DIFF j` THEN
    UNDISCH_TAC `a SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(a:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `a:real^2->bool`]
      HOMEOMORPHIC_COMPACTNESS) THEN REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (inside(IMAGE (phi:real^3->real^2) jj))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[disk_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`(psi:real^2->real^3) o (f:real^2->real^2)`;
                          `(g:real^2->real^2) o (phi:real^3->real^2)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `a:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_o]];
    UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,&1)) = e DIFF j` THEN
    UNDISCH_TAC `a SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (psi:real^2->real^3) (IMAGE phi jj) = jj` THEN
    EXPAND_TAC "a" THEN SET_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    EXPAND_TAC "a" THEN
    MP_TAC(ISPEC `IMAGE (phi:real^3->real^2) jj` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `a SUBSET ball(vec 0:real^2,&1)` THEN EXPAND_TAC "a" THEN
    UNDISCH_TAC `!y. y IN ball(vec 0:real^2,&1) ==> (phi:real^3->real^2)(psi y) = y` THEN
    UNDISCH_TAC `IMAGE (psi:real^2->real^3) (IMAGE phi jj) = jj` THEN SET_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `inside(IMAGE (phi:real^3->real^2) jj) SUBSET ball(vec 0,&1)` THEN
    UNDISCH_TAC `(y:real^3) IN e DIFF j` THEN
    UNDISCH_TAC `!y. y IN ball(vec 0:real^2,&1) ==> (phi:real^3->real^2)(psi y) = y` THEN
    UNDISCH_TAC `!x. x IN e DIFF j ==> (psi:real^2->real^3)(phi x) = x` THEN
    SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^2`; `ball(vec 0:real^2,&1)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4. Disks in a pseudo-cell missing the centre are PL disks:          *)
(* compactness in the locally polyhedral open cell gives finitely many      *)
(* polytopes; a common simplicial refinement with the boundary circle; the  *)
(* disk is the union of the simplices meeting its interior; then            *)
(* DISK_RECOG.                                                              *)
(* ------------------------------------------------------------------------- *)

let moi_s3l9i_drec = new_definition
  (mk_eq(mk_var("moi_s3l9i_drec",bool_ty), inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY));;

let MOI_S3L9_PL_SPHERE1_CIRCLE = prove
 (`!s:real^N->bool. pl_sphere 1 s ==> s homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_2;
                REAL_LT_01] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_BOUNDED; AFF_DIM_SIMPLEX]]);;

(* A compact subset of a locally polyhedral set lies in a finite union of   *)
(* polytopes inside the set.                                                 *)

let MOI_S3L9_LP_COVER = prove
 (`!s dd:real^N->bool.
     locally_polyhedral s /\ compact dd /\ dd SUBSET s
     ==> ?c. FINITE c /\ (!k. k IN c ==> polytope k /\ k SUBSET s) /\
             dd SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{u:real^N->bool | open u /\
                      ?c. FINITE c /\ s INTER u SUBSET UNIONS c /\
                          !k. k IN c ==> polytope k /\ k SUBSET s}`) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `u:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "fsub") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?C. !u. u IN f
            ==> FINITE (C u) /\ s INTER u SUBSET UNIONS (C u) /\
                !k:real^N->bool. k IN C u ==> polytope k /\ k SUBSET s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `u:real^N->bool` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "fsub" (MP_TAC o SPEC `u:real^N->bool` o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (IMAGE (C:(real^N->bool)->(real^N->bool)->bool) f)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE];
    REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?u:real^N->bool. u IN f /\ x IN u` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS (C(u:real^N->bool))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]]);;

(* The polyhedrality of a closed region bounded by a polyhedron, inside a   *)
(* locally polyhedral set.                                                    *)

let MOI_S3L9_POLY_REGION = prove
 (`!s dd jj:real^N->bool.
     locally_polyhedral s /\ compact dd /\ dd SUBSET s /\
     pl_polyhedron jj /\ jj SUBSET dd /\
     open_in (subtopology euclidean s) (dd DIFF jj) /\ dd SUBSET closure (dd DIFF jj)
     ==> pl_polyhedron dd`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `dd:real^N->bool`] MOI_S3L9_LP_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cj:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) o
    GEN_REWRITE_RULE I [pl_polyhedron]) THEN
  MP_TAC(ISPEC `c UNION cj:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "refine")))) THEN
  SUBGOAL_THEN `?fj. fj SUBSET t /\ UNIONS fj = jj:real^N->bool` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `{r:real^N->bool | r IN t /\ r SUBSET jj}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^N->bool. k IN cj /\ x IN k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS cj = jj:real^N->bool` THEN UNDISCH_TAC `(x:real^N) IN jj` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "refine" (MP_TAC o SPEC `k:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:real^N->bool. r IN g /\ x IN r` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN k` THEN UNDISCH_TAC `k:real^N->bool = UNIONS g` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(g:(real^N->bool)->bool) SUBSET t` THEN
      UNDISCH_TAC `(r:real^N->bool) IN g` THEN SET_TAC[];
      UNDISCH_TAC `(k:real^N->bool) IN cj` THEN UNDISCH_TAC `k:real^N->bool = UNIONS g` THEN
      UNDISCH_TAC `UNIONS cj = jj:real^N->bool` THEN
      UNDISCH_TAC `(r:real^N->bool) IN g` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (t:(real^N->bool)->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION; UNION_SUBSET] THEN
    REWRITE_TAC[UNIONS_SUBSET] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `(jj:real^N->bool) SUBSET dd` THEN
      UNDISCH_TAC `(dd:real^N->bool) SUBSET s` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN t ==> convex r /\ compact r /\ polytope r`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r q:real^N->bool. r IN t /\ q IN t ==> (r INTER q) face_of r`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (dd:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN t /\ ~(r INTER (dd DIFF jj) = {}) ==> r SUBSET dd`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex (r:real^N->bool) /\ compact r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior r SUBSET (s:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS (t:(real^N->bool)->bool) SUBSET s` THEN
      UNDISCH_TAC `(r:real^N->bool) IN t` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior r INTER (jj:real^N->bool) = {}` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `UNIONS fj = jj:real^N->bool`)) THEN
      REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r INTER q:real^N->bool) face_of r` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(fj:(real^N->bool)->bool) SUBSET t` THEN
        UNDISCH_TAC `(q:real^N->bool) IN fj` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `r INTER q:real^N->bool = r` THENL
       [UNDISCH_TAC `~(r INTER (dd DIFF jj:real^N->bool) = {})` THEN
        UNDISCH_TAC `r INTER q:real^N->bool = r` THEN
        UNDISCH_TAC `UNIONS fj = jj:real^N->bool` THEN
        UNDISCH_TAC `(q:real^N->bool) IN fj` THEN SET_TAC[];
        MP_TAC(ISPECL [`r INTER q:real^N->bool`; `r:real^N->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
        MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_interior r INTER (dd DIFF jj:real^N->bool) = {})`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
        check (fun th -> concl th = `~(r INTER (dd DIFF jj:real^N->bool) = {})`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `open_in (subtopology euclidean s) (dd DIFF jj:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^N) IN closure(relative_interior r)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED;
                     COMPACT_IMP_CLOSED];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN w` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN dd DIFF jj` THEN
        UNDISCH_TAC `dd DIFF jj:real^N->bool = s INTER w` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`w:real^N->bool`; `relative_interior r:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(w INTER closure(relative_interior r:real^N->bool) = {})`
      (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(y:real^N) IN w` THEN
        UNDISCH_TAC `(y:real^N) IN closure(relative_interior r)` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `dd DIFF jj:real^N->bool = s INTER w` THEN
      UNDISCH_TAC `relative_interior r SUBSET (s:real^N->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior r SUBSET (dd DIFF jj:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `(dd DIFF jj) UNION (s DIFF dd):real^N->bool` THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `dd:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(dd:real^N->bool) SUBSET s` THEN SET_TAC[];
        UNDISCH_TAC `relative_interior r INTER (jj:real^N->bool) = {}` THEN
        UNDISCH_TAC `relative_interior r SUBSET (s:real^N->bool)` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r = closure(relative_interior r:real^N->bool)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_interior r SUBSET (dd DIFF jj:real^N->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd DIFF jj SUBSET UNIONS {r:real^N->bool | r IN t /\ r SUBSET dd}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r:real^N->bool. r IN t /\ y IN r` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN UNIONS t` MP_TAC THENL
       [ASM_REWRITE_TAC[UNIONS_UNION] THEN
        UNDISCH_TAC `(y:real^N) IN dd DIFF jj` THEN
        UNDISCH_TAC `(dd:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN dd DIFF jj` THEN UNDISCH_TAC `(y:real^N) IN r` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {r:real^N->bool | r IN t /\ r SUBSET dd})` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd = UNIONS {r:real^N->bool | r IN t /\ r SUBSET dd}` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(dd DIFF jj:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{r:real^N->bool | r IN t /\ r SUBSET dd}` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT]]);;

(* A disk is the closure of its interior part.                               *)

let MOI_S3L9_DISK_DENSE = prove
 (`!d j:real^N->bool.
     disk_with_boundary d j
     ==> compact d /\ j SUBSET d /\ d SUBSET closure (d DIFF j) /\
         connected (d DIFF j) /\ ~(d DIFF j = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `d DIFF j = IMAGE (f:real^2->real^N) (ball(vec 0,&1))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_UNION_BALL) THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] CBALL_DIFF_SPHERE) THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = d` THEN
    UNDISCH_TAC `!x. x IN cball(vec 0:real^2,&1) ==> (g:real^N->real^2)(f x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SPHERE_SUBSET_CBALL];
    EXPAND_TAC "d" THEN
    SUBGOAL_THEN `cball(vec 0:real^2,&1) = closure(ball(vec 0,&1))` SUBST1_TAC THENL
     [SIMP_TAC[CLOSURE_BALL; REAL_LT_01]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
    SIMP_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    SIMP_TAC[CLOSURE_BALL; REAL_LT_01] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[CONNECTED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN REAL_ARITH_TAC]);;

(* The chart disk of a PL circle in the open cell, missing the centre, is a *)
(* PL disk with that boundary.                                              *)

let MOI_S3L9_CELL_PL = prove
 (`!(e:real^3->bool) j p (phi:real^3->real^2) psi jj.
     moi_s3l9i_drec /\ pseudo_cell e j p /\
     homeomorphism (e DIFF j,ball(vec 0:real^2,&1)) (phi,psi) /\
     jj SUBSET e DIFF j /\ pl_sphere 1 jj /\
     ~(p IN IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj)))
     ==> pl_cell_with_boundary 2 (IMAGE psi (IMAGE phi jj UNION inside(IMAGE phi jj))) jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `phi:real^3->real^2`;
                 `psi:real^2->real^3`; `jj:real^3->bool`] MOI_S3L9_CELL_DISK) THEN
  ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE] THEN
  ABBREV_TAC `dd = IMAGE (psi:real^2->real^3)
                   (IMAGE (phi:real^3->real^2) jj UNION inside(IMAGE phi jj))` THEN
  STRIP_TAC THEN
  UNDISCH_TAC `moi_s3l9i_drec` THEN REWRITE_TAC[moi_s3l9i_drec] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `jj:real^3->bool`] MOI_S3L9_DISK_DENSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_S3L9_POLY_REGION THEN
  MAP_EVERY EXISTS_TAC [`(e DIFF j) DELETE (p:real^3)`; `jj:real^3->bool`] THEN
  SUBGOAL_THEN `pl_polyhedron (jj:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral ((e DIFF j) DELETE (p:real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `pseudo_cell (e:real^3->bool) j p` THEN SIMP_TAC[pseudo_cell]; ALL_TAC] THEN
  SUBGOAL_THEN `dd SUBSET (e DIFF j) DELETE (p:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((p:real^3) IN dd)` THEN
    UNDISCH_TAC `dd SUBSET e DIFF (j:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean ((e DIFF j) DELETE (p:real^3))) (dd DIFF jj)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `e DIFF j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 5. PL topology in a PL disk through a planar model: a 2-simplex S  *)
(* in the plane with a PL homeomorphism onto the disk; PL circles in the   *)
(* interior of S bound PL disks (PL Schoenflies); an innermost one among   *)
(* finitely many disjoint circles; a PL cross-cut splits S into two PL     *)
(* disks (MOI_SFR_THETA); PL cells transported into real^3.                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_SIMPLEX_CELL = prove
 (`!S:real^N->bool. &2 simplex S ==> pl_cell_with_boundary 2 S (relative_frontier S)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`S:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{S:real^N->bool}` THEN SIMP_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_S3L9_PLANAR_MODEL = prove
 (`!(d:real^3->bool) j.
     pl_cell_with_boundary 2 d j
     ==> ?(S:real^2->bool) (fs:real^2->real^3) gs.
           &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
           IMAGE fs (relative_frontier S) = j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_FC2_SIMPLEX_RF_R2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `h1:real^2->real^3`
    (X_CHOOSE_THEN `h2:real^3->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier k,IMAGE f (relative_frontier k))
                                 (f:real^3->real^3,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `d:real^3->bool`] THEN
    SUBGOAL_THEN `polytope (k:real^3->bool) /\ compact k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER] THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `S:real^2->bool`; `relative_frontier S:real^2->bool`;
                 `d:real^3->bool`; `IMAGE (f:real^3->real^3) (relative_frontier k)`;
                 `(f:real^3->real^3) o (h1:real^2->real^3)`;
                 `(h2:real^3->real^2) o (g:real^3->real^3)`]
    MOI_CEL_CELL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S3L9_SIMPLEX_CELL] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^3->bool` THEN CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:real^2->real^3` (X_CHOOSE_THEN `gs:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`S:real^2->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (h1:real^2->real^3) (relative_frontier S) = relative_frontier k`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (relative_frontier S,relative_frontier k)
                    (h1:real^2->real^3,h2)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  UNDISCH_TAC `!x. x IN relative_frontier S
                   ==> (fs:real^2->real^3) x = ((f:real^3->real^3) o (h1:real^2->real^3)) x` THEN
  UNDISCH_TAC `IMAGE (h1:real^2->real^3) (relative_frontier S) = relative_frontier k` THEN
  REWRITE_TAC[o_THM] THEN SET_TAC[]);;

(* A 2-simplex in the plane: interior, frontier, inside.                      *)

let MOI_S3L9_PLANE_SIMPLEX = prove
 (`!S:real^2->bool.
     &2 simplex S
     ==> convex S /\ compact S /\ ~(interior S = {}) /\
         relative_frontier S = frontier S /\ relative_interior S = interior S /\
         inside(relative_frontier S) = interior S /\
         S = relative_frontier S UNION interior S /\
         DISJOINT (relative_frontier S) (interior S)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex (S:real^2->bool) /\ compact S` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (S:real^2->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_2] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
               INSIDE_FRONTIER_EQ_INTERIOR; COMPACT_IMP_BOUNDED] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

(* A connected set missing a closed set and meeting its inside lies inside. *)

let MOI_S3L9_CONN_INSIDE = prove
 (`!c s:real^2->bool.
     closed c /\ connected s /\ DISJOINT s c /\ ~(s INTER inside c = {})
     ==> s SUBSET inside c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
  EXISTS_TAC `(:real^2) DIFF c` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `(:real^2) DIFF outside c` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM OPEN_CLOSED] THEN MATCH_MP_TAC OPEN_OUTSIDE THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `c:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
      MP_TAC(ISPEC `c:real^2->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]];
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_SIMP_TAC[OPEN_INSIDE] THEN
    MP_TAC(ISPEC `c:real^2->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[];
    ASM SET_TAC[]]);;

(* PL circles in the interior of a convex set in the plane.                  *)

let MOI_S3L9_PLANE_CIRCLE = prove
 (`!(c:real^2->bool) S.
     pl_sphere 1 c /\ c SUBSET interior S /\ convex S
     ==> pl_cell_with_boundary 2 (c UNION inside c) c /\
         c UNION inside c SUBSET interior S /\
         compact (c UNION inside c) /\ frontier (c UNION inside c) = c /\
         inside c INTER c = {} /\ open (inside c) /\ connected (inside c) /\
         ~(inside c = {}) /\ compact c /\ connected c /\ ~(c = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                                     path_image gam = c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
      HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
    REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `c:real^2->bool`] MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_ball 2 (c UNION inside c:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (c:real^2->bool) /\ connected c /\ ~(c = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (gam:real^1->real^2) = c` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[COMPACT_SIMPLE_PATH_IMAGE; CONNECTED_SIMPLE_PATH_IMAGE;
                 PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SFR_PL_BALL_CELL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_INTERIOR]);;

(* Among finitely many disjoint continua in the plane one is innermost.      *)

let MOI_S3L9_PLANE_INNERMOST = prove
 (`!P:(real^2->bool)->bool.
     FINITE P /\ ~(P = {}) /\
     (!c. c IN P ==> compact c /\ connected c /\ ~(c = {})) /\
     (!c c'. c IN P /\ c' IN P /\ ~(c = c') ==> DISJOINT c c')
     ==> ?c. c IN P /\ !c'. c' IN P /\ ~(c' = c) ==> DISJOINT c' (c UNION inside c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c:real^2->bool. c IN P
        ==> compact c /\ connected c /\ ~(c = {}) /\ inside c INTER c = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[INSIDE_NO_OVERLAP]; ALL_TAC] THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC
   `\n. ?c:real^2->bool. c IN P /\ CARD {c' | c' IN P /\ c' SUBSET inside c} = n` num_WOP)))) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^2->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MAP_EVERY EXISTS_TAC
     [`CARD {c' | c' IN P /\ c' SUBSET inside (c:real^2->bool)}`; `c:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^2->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `c:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c':real^2->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c':real^2->bool) SUBSET inside c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_CONN_INSIDE THEN
    SUBGOAL_THEN `DISJOINT (c':real^2->bool) c` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside(c':real^2->bool) SUBSET inside c` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `CARD {c'' | c'' IN P /\ c'' SUBSET inside (c':real^2->bool)}`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [UNDISCH_TAC `inside(c':real^2->bool) SUBSET inside c` THEN SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `c':real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(inside c' INTER c':real^2->bool = {}) ==> F` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(c':real^2->bool = {})` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SET_TAC[]];
    EXISTS_TAC `c':real^2->bool` THEN ASM_REWRITE_TAC[]]);;

(* PL cells of the planar model, carried into the disk.                     *)

let MOI_S3L9_MODEL_CELL = prove
 (`!(S:real^2->bool) (d:real^3->bool) fs gs u b.
     pl_homeomorphism (S,d) (fs,gs) /\ pl_cell_with_boundary 2 u b /\ u SUBSET S
     ==> pl_cell_with_boundary 2 (IMAGE fs u) (IMAGE fs b) /\
         pl_homeomorphism (u,IMAGE fs u) (fs,gs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (u,IMAGE fs u) (fs:real^2->real^3,gs)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`S:real^2->bool`; `d:real^3->bool`] THEN
    ASM_MESON_TAC[MOI_S4O_CELL_POLY];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_FCL_CELL_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `gs:real^3->real^2`] THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 6. Tools for the swaps: a connected subset of the pseudo-cells     *)
(* lies in one of them; plane topology of Jordan curves (sides, avoidance, *)
(* a disk is its boundary curve with its inside, an open outer collar);    *)
(* the swap of a disk bounded by a circle of the planar model for another  *)
(* disk.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_CONN_PCS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) a.
     moi_s33_hd t l h e c /\ connected a /\ ~(a = {}) /\ a SUBSET moi_s39_pcs l e
     ==> ?u v. ~(u = v) /\ segment[u,v] IN l /\ a SUBSET e(segment[u,v])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PCS_BASIC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_TUBE_BASIC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(a:real^3->bool = {})`)) THEN
  SUBGOAL_THEN `?s. s IN (l:(real^3->bool)->bool) /\ aff_dim s = &1 /\
                    (y:real^3) IN (e:(real^3->bool)->real^3->bool) s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
    REWRITE_TAC[moi_s39_pcs; UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a SUBSET (e:(real^3->bool)->real^3->bool) s` ASSUME_TAC THENL
   [ABBREV_TAC `o1 = UNIONS {(e:(real^3->bool)->real^3->bool) s' |
                              s' IN l /\ aff_dim s' = &1 /\ ~(s' = s)}` THEN
    SUBGOAL_THEN `closed (o1:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "o1" THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `IMAGE (e:(real^3->bool)->real^3->bool) l` THEN
        ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
        ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool) s) o1` ASSUME_TAC THENL
     [EXPAND_TAC "o1" THEN REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS;
                                       FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN
      MATCH_MP_TAC MOI_S3L9_HD_DISJ THEN
      MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                            `h:real^3->real^3`; `c:real^3->real^3->bool`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `a SUBSET (e:(real^3->bool)->real^3->bool) s UNION o1` ASSUME_TAC THENL
     [UNDISCH_TAC `a SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
      EXPAND_TAC "o1" THEN REWRITE_TAC[moi_s39_pcs] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `a SUBSET a DIFF (o1:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
        EXISTS_TAC `(e:(real^3->bool)->real^3->bool) s` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT ((e:(real^3->bool)->real^3->bool) s) o1` THEN
        UNDISCH_TAC `a SUBSET (e:(real^3->bool)->real^3->bool) s UNION o1` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `DISJOINT ((e:(real^3->bool)->real^3->bool) s) o1` THEN
        UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool) s` THEN
        UNDISCH_TAC `(y:real^3) IN a` THEN SET_TAC[]];
      UNDISCH_TAC `a SUBSET (e:(real^3->bool)->real^3->bool) s UNION o1` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `s:real^3->bool`] MOI_S3L9_EDGE_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN
  UNDISCH_TAC `a SUBSET (e:(real^3->bool)->real^3->bool) s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* A connected set missing a closed set lies inside or outside it.           *)

let MOI_S3L9_PLANE_SIDE = prove
 (`!c s:real^2->bool.
     closed c /\ connected s /\ DISJOINT s c
     ==> s SUBSET inside c \/ s SUBSET outside c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s INTER inside c:real^2->bool = {}` THENL
   [DISJ2_TAC THEN MP_TAC(ISPEC `c:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
    ASM SET_TAC[];
    DISJ1_TAC THEN MATCH_MP_TAC MOI_S3L9_CONN_INSIDE THEN ASM_REWRITE_TAC[]]);;

(* Two disjoint Jordan curves g, gam with a point p inside g but not in the *)
(* disk of gam: the disk of gam misses g.                                     *)

let MOI_S3L9_PLANE_AVOID = prove
 (`!g gam (p:real^2).
     compact g /\ connected g /\ compact gam /\ connected gam /\
     DISJOINT g gam /\ p IN inside g /\ ~(p IN gam UNION inside gam)
     ==> DISJOINT g (gam UNION inside gam)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (gam:real^2->bool) g` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->bool`; `gam:real^2->bool`] MOI_S3L9_PLANE_SIDE) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`gam:real^2->bool`; `g:real^2->bool`] INSIDE_INSIDE_COMPACT_CONNECTED) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `g:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `gam:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`gam:real^2->bool`; `g:real^2->bool`] MOI_S3L9_PLANE_SIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`g:real^2->bool`; `gam:real^2->bool`]
        INSIDE_INSIDE_COMPACT_CONNECTED) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `gam:real^2->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]]]);;

(* Images of a disjoint union under an injective map.                        *)

let MOI_S3L9_IMAGE_DIFF_INJ = prove
 (`!(f:A->B) g s t.
     (!x. x IN s UNION t ==> g(f x) = x) /\ DISJOINT s t
     ==> IMAGE f (s UNION t) DIFF IMAGE f s = IMAGE f t`,
  SET_TAC[]);;

let MOI_S3L9_SPHERE_BALL_DISJOINT = prove
 (`!a:real^N r. DISJOINT (sphere(a,r)) (ball(a,r))`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SPHERE; IN_BALL; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

(* A topological disk in the plane is its boundary curve with its inside.   *)

let MOI_S3L9_PLANE_DISK_INSIDE = prove
 (`!d j:real^2->bool.
     disk_with_boundary d j
     ==> d = j UNION inside j /\ frontier d = j /\ interior d = inside j /\
         j homeomorphic sphere(vec 0:real^2,&1) /\ compact d /\ compact j /\
         connected j /\ ~(j = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [disk_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (d:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `d:real^2->bool`] THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (sphere(vec 0,&1)) = j` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (cball(vec 0,&1)) = d` THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (j:real^2->bool) /\ connected j /\ ~(j = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^2) (sphere(vec 0,&1)) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SPHERE_SUBSET_CBALL; COMPACT_SPHERE];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SPHERE_SUBSET_CBALL];
      REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier d = j:real^2->bool` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `d:real^2->bool`; `f:real^2->real^2`;
                   `g:real^2->real^2`] MOI_PL2_HOMEOMORPHISM_FRONTIER) THEN
    ASM_SIMP_TAC[CLOSED_CBALL; COMPACT_IMP_CLOSED; FRONTIER_CBALL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior d = d DIFF j:real^2->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier d = j:real^2->bool` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `d:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (d DIFF j:real^2->bool) /\ ~(d DIFF j = {})` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `d DIFF j = IMAGE (f:real^2->real^2) (ball(vec 0,&1))` SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^2) (sphere(vec 0,&1)) = j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^2) (cball(vec 0,&1)) = d` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM SPHERE_UNION_BALL] THEN
      MATCH_MP_TAC MOI_S3L9_IMAGE_DIFF_INJ THEN EXISTS_TAC `g:real^2->real^2` THEN
      ASM_REWRITE_TAC[SPHERE_UNION_BALL; MOI_S3L9_SPHERE_BALL_DISJOINT];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                                     path_image gam = j` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->bool`; `vec 0:real^2`; `&1`]
      HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
    REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `j:real^2->bool`] MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `d DIFF j SUBSET inside(j:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->bool`; `d DIFF j:real^2->bool`] MOI_S3L9_PLANE_SIDE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `outside j SUBSET d DIFF j:real^2->bool` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `outside j:real^2->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `d:real^2->bool` THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        UNDISCH_TAC `d DIFF j SUBSET outside(j:real^2->bool)` THEN
        UNDISCH_TAC `outside j INTER j:real^2->bool = {}` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `interior d = d DIFF j:real^2->bool` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[OPEN_INTERIOR];
        UNDISCH_TAC `d DIFF j SUBSET outside(j:real^2->bool)` THEN
        UNDISCH_TAC `~(d DIFF j:real^2->bool = {})` THEN SET_TAC[]];
      DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~bounded(outside j:real^2->bool)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `d:real^2->bool` THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside j SUBSET d DIFF j:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
    EXISTS_TAC `inside j:real^2->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `d:real^2->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `d DIFF j SUBSET inside(j:real^2->bool)` THEN
      UNDISCH_TAC `inside j INTER j:real^2->bool = {}` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interior d = d DIFF j:real^2->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[OPEN_INTERIOR];
      UNDISCH_TAC `d DIFF j SUBSET inside(j:real^2->bool)` THEN
      UNDISCH_TAC `~(d DIFF j:real^2->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^2->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^2) (sphere(vec 0,&1)) = j` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (cball(vec 0,&1)) = d` THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = j UNION inside(j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `d DIFF j SUBSET inside(j:real^2->bool)` THEN
    UNDISCH_TAC `inside j SUBSET d DIFF j:real^2->bool` THEN
    UNDISCH_TAC `(j:real^2->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior d = inside(j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `interior d = d DIFF j:real^2->bool` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `d DIFF j SUBSET inside(j:real^2->bool)` THEN
    UNDISCH_TAC `inside j SUBSET d DIFF j:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j = inside(j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `d DIFF j SUBSET inside(j:real^2->bool)` THEN
    UNDISCH_TAC `inside j SUBSET d DIFF j:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* A point of norm at least 1 is at distance norm - 1 from the unit sphere. *)

let MOI_S3L9_SPHERE_RADIAL = prove
 (`!z:real^2. &1 <= norm z
              ==> inv(norm z) % z IN sphere(vec 0,&1) /\
                  dist(inv(norm z) % z,z) = norm z - &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(z:real^2) = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `a % z - z:real^2 = (a - &1) % z`; NORM_MUL] THEN
  SUBGOAL_THEN `abs(inv(norm(z:real^2)) - &1) = &1 - inv(norm z)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> abs(x - &1) = &1 - x`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LINV] THEN REAL_ARITH_TAC);;

(* An open outer collar of a Jordan curve, missing a given compact set.    *)

let MOI_S3L9_OUTER_COLLAR = prove
 (`!(c:real^2->bool) k.
     c homeomorphic sphere(vec 0:real^2,&1) /\ closed k /\ DISJOINT c k
     ==> ?a. open a /\ connected a /\ a SUBSET outside c /\ DISJOINT a k /\
             c SUBSET closure a /\ open (a UNION c UNION inside c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                                     path_image gam = c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
      HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
    REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic] o check (fun th ->
    concl th = `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_TAC `f1:real^2->real^2`)) THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `circlepath(vec 0:real^2,&1)`;
                 `f0:real^2->real^2`; `f1:real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS;
               REAL_OF_NUM_EQ; ARITH_EQ; INSIDE_SPHERE; OUTSIDE_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^2->real^2` (X_CHOOSE_THEN `kk':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNIV] o
    GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      concl th = `homeomorphism ((:real^2),(:real^2)) (kk:real^2->real^2,kk')`)) THEN
  SUBGOAL_THEN
   `?dl. &0 < dl /\
         !z:real^2. &1 < norm z /\ norm z < &1 + dl ==> ~(z IN IMAGE (kk:real^2->real^2) k)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `k:real^2->bool = {}` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `setdist(sphere(vec 0:real^2,&1),IMAGE (kk:real^2->real^2) k)` THEN
    SUBGOAL_THEN `closed (IMAGE (kk:real^2->real^2) k)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`kk:real^2->real^2`; `kk':real^2->real^2`; `(:real^2)`; `(:real^2)`;
                     `k:real^2->bool`] HOMEOMORPHISM_IMP_CLOSED_MAP) THEN
      ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_UNIV; SUBSET_UNIV];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN
      ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_SPHERE] THEN
      REWRITE_TAC[SPHERE_EQ_EMPTY; IMAGE_EQ_EMPTY; DE_MORGAN_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (kk:real^2->real^2) c = sphere(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `DISJOINT (c:real^2->bool) k` THEN
      UNDISCH_TAC `!x:real^2. kk'((kk:real^2->real^2) x) = x` THEN SET_TAC[];
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPEC `z:real^2` MOI_S3L9_SPHERE_RADIAL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `IMAGE (kk:real^2->real^2) k`;
                     `inv(norm(z:real^2)) % z`; `z:real^2`] SETDIST_LE_DIST) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `an = ball(vec 0:real^2,&1 + dl) DIFF cball(vec 0,&1)` THEN
  SUBGOAL_THEN `open (an:real^2->bool) /\ connected an` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "an" THEN SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL] THEN
    SUBGOAL_THEN `ball(vec 0:real^2,&1 + dl) DIFF cball(vec 0,&1) =
                  {x | &1 < norm(x - vec 0) /\ norm(x - vec 0) < &1 + dl}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; IN_ELIM_THM;
                  VECTOR_SUB_RZERO] THEN REAL_ARITH_TAC;
      SIMP_TAC[CONNECTED_ANNULUS; DIMINDEX_2; LE_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (kk':real^2->real^2) an` THEN
  SUBGOAL_THEN `!s:real^2->bool. IMAGE kk' (IMAGE (kk:real^2->real^2) s) = s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^2. kk'((kk:real^2->real^2) x) = x` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean (:real^2)) (IMAGE (kk':real^2->real^2) an)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`kk:real^2->real^2`; `(:real^2)`] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_UNIV; SUBSET_UNIV];
      SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_UNIV; SUBSET_UNIV]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    UNDISCH_TAC `IMAGE (kk:real^2->real^2) (outside c) = (:real^2) DIFF cball(vec 0,&1)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `IMAGE (kk':real^2->real^2)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "an" THEN SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `dl:real`)) (concl th))) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN an` THEN EXPAND_TAC "an" THEN
      REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `c = IMAGE (kk':real^2->real^2) (sphere(vec 0,&1))` SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (kk:real^2->real^2) c = sphere(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (kk':real^2->real^2) (closure an)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
      X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
      EXISTS_TAC `(&1 + min ee dl / &2) % (w:real^2)` THEN
      EXPAND_TAC "an" THEN
      REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_CBALL_0; NORM_MUL; dist;
                  VECTOR_ARITH `a % w - w:real^2 = (a - &1) % w`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
      SIMP_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    SUBGOAL_THEN `IMAGE (kk':real^2->real^2) an UNION c UNION inside c =
                  IMAGE kk' (ball(vec 0,&1 + dl))` SUBST1_TAC THENL
     [SUBGOAL_THEN `ball(vec 0:real^2,&1 + dl) =
                    an UNION sphere(vec 0,&1) UNION ball(vec 0,&1)` SUBST1_TAC THENL
       [EXPAND_TAC "an" THEN
        REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (kk:real^2->real^2) c = sphere(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `IMAGE (kk:real^2->real^2) (inside c) = ball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IMAGE_UNION];
      SUBGOAL_THEN `open_in (subtopology euclidean (:real^2))
                     (IMAGE (kk':real^2->real^2) (ball(vec 0,&1 + dl)))`
      MP_TAC THENL
       [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
        MAP_EVERY EXISTS_TAC [`kk:real^2->real^2`; `(:real^2)`] THEN
        ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_UNIV; OPEN_BALL; SUBSET_UNIV];
        SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_UNIV; SUBSET_UNIV]]]]);;

(* Small facts on polyhedra and closures.                                    *)

let MOI_S3L9_PLPOLY_COMPACT = prove
 (`!s:real^N->bool. pl_polyhedron s ==> compact s`,
  GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[POLYTOPE_IMP_COMPACT]);;

let MOI_S3L9_PLPOLY_UNION = prove
 (`!s t:real^N->bool. pl_polyhedron s /\ pl_polyhedron t ==> pl_polyhedron (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `c2:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `c1 UNION c2:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; UNIONS_UNION] THEN ASM_MESON_TAC[]);;

let MOI_S3L9_CLOSURE_DIFF_CLOSED = prove
 (`!u k:real^N->bool. closed k ==> closure u DIFF k SUBSET closure (u DIFF k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(y:real^N,r) INTER k = {}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N) DIFF k` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN closure u` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_TAC THEN X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min ee r`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
  UNDISCH_TAC `ball(y:real^N,r) INTER k = {}` THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

(* The swap in the planar model: the disk of a circle c0 of the model is    *)
(* replaced by another PL disk e0 with the same boundary meeting the rest  *)
(* only there; the result is a PL disk with the same boundary.             *)

let MOI_S3L9_MODEL_SWAP = prove
 (`!(S:real^2->bool) (d:real^3->bool) fs gs c0 e0.
     &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
     pl_sphere 1 c0 /\ c0 SUBSET interior S /\
     pl_cell_with_boundary 2 e0 (IMAGE fs c0) /\
     e0 INTER IMAGE fs (S DIFF inside c0) = IMAGE fs c0
     ==> pl_cell_with_boundary 2 (IMAGE fs (S DIFF inside c0) UNION e0)
                                 (IMAGE fs (relative_frontier S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `relative_frontier S = frontier (S:real^2->bool)`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `relative_interior S = interior (S:real^2->bool)`)) THEN
  MP_TAC(ISPECL [`c0:real^2->bool`; `S:real^2->bool`] MOI_S3L9_PLANE_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s1 = S DIFF inside(c0:real^2->bool)` THEN
  SUBGOAL_THEN `compact (s1:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN
    ONCE_REWRITE_TAC[SET_RULE `S DIFF t = S INTER ((:real^2) DIFF t)`] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN MATCH_MP_TAC OPEN_INSIDE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 INTER (c0 UNION inside c0) = c0:real^2->bool /\
                s1 UNION (c0 UNION inside c0) = S /\
                relative_frontier S SUBSET s1 /\ c0 SUBSET s1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN
    UNDISCH_TAC `c0 UNION inside c0 SUBSET interior(S:real^2->bool)` THEN
    UNDISCH_TAC `inside c0 INTER c0:real^2->bool = {}` THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (s1:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_POLY_REGION THEN
    MAP_EVERY EXISTS_TAC [`S:real^2->bool`; `c0 UNION relative_frontier S:real^2->bool`] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN REWRITE_TAC[pl_polyhedron] THEN
      EXISTS_TAC `{S:real^2->bool}` THEN SIMP_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      EXPAND_TAC "s1" THEN SET_TAC[];
      MATCH_MP_TAC MOI_S3L9_PLPOLY_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
      SUBGOAL_THEN `s1 DIFF (c0 UNION relative_frontier S) =
                    interior S DIFF (c0 UNION inside(c0:real^2->bool))` SUBST1_TAC THENL
       [EXPAND_TAC "s1" THEN
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
        UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED]];
      SUBGOAL_THEN `s1 DIFF (c0 UNION relative_frontier S) =
                    interior S DIFF (c0 UNION inside(c0:real^2->bool))` SUBST1_TAC THENL
       [EXPAND_TAC "s1" THEN
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
        UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `relative_frontier S SUBSET
                    closure(interior S DIFF (c0 UNION inside(c0:real^2->bool)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure(interior S) DIFF (c0 UNION inside(c0:real^2->bool))` THEN
        ASM_SIMP_TAC[MOI_S3L9_CLOSURE_DIFF_CLOSED; COMPACT_IMP_CLOSED] THEN
        ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
        UNDISCH_TAC `c0 UNION inside c0 SUBSET interior(S:real^2->bool)` THEN
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
        UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `c0 SUBSET closure(interior S DIFF (c0 UNION inside(c0:real^2->bool)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure(interior S INTER outside(c0:real^2->bool))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `interior S INTER closure(outside(c0:real^2->bool))` THEN
          SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET; OPEN_INTERIOR] THEN
          REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
           [UNDISCH_TAC `c0 UNION inside c0 SUBSET interior(S:real^2->bool)` THEN SET_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN `?gam:real^1->real^2. simple_path gam /\
                          pathfinish gam = pathstart gam /\ path_image gam = c0`
          STRIP_ASSUME_TAC THENL
           [MP_TAC(ISPECL [`c0:real^2->bool`; `vec 0:real^2`; `&1`]
              HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
            REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
            ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE];
            ALL_TAC] THEN
          MP_TAC(ISPEC `gam:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier(outside c0:real^2->bool)` THEN
          CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; REWRITE_TAC[frontier] THEN SET_TAC[]];
          MATCH_MP_TAC SUBSET_CLOSURE THEN
          MP_TAC(ISPEC `c0:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
          MP_TAC(ISPEC `c0:real^2->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^2` THEN EXPAND_TAC "s1" THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(y:real^2) IN relative_frontier S` THENL
       [UNDISCH_TAC `(y:real^2) IN relative_frontier S` THEN
        UNDISCH_TAC `relative_frontier S SUBSET
                     closure(interior S DIFF (c0 UNION inside(c0:real^2->bool)))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `(y:real^2) IN c0` THENL
       [UNDISCH_TAC `(y:real^2) IN c0` THEN
        UNDISCH_TAC `c0 SUBSET closure(interior S DIFF (c0 UNION inside(c0:real^2->bool)))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
      UNDISCH_TAC `(y:real^2) IN S` THEN UNDISCH_TAC `~((y:real^2) IN inside c0)` THEN
      UNDISCH_TAC `~((y:real^2) IN relative_frontier S)` THEN
      UNDISCH_TAC `~((y:real^2) IN c0)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (s1,IMAGE fs s1) (fs:real^2->real^3,gs)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`S:real^2->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s1" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (c0,IMAGE fs c0) (fs:real^2->real^3,gs)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`S:real^2->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `c0 UNION inside(c0:real^2->bool)`; `c0:real^2->bool`;
                 `e0:real^3->bool`; `IMAGE (fs:real^2->real^3) c0`;
                 `fs:real^2->real^3`; `gs:real^3->real^2`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^3` (X_CHOOSE_THEN `g2:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact (e0:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_CELL_POLY; MOI_S3L9_PLPOLY_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (fs:real^2->real^3) s1)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN s1 INTER (c0 UNION inside c0)
                    ==> (fs:real^2->real^3) x = f2 x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (s1 INTER (c0 UNION inside c0)) =
                IMAGE fs s1 INTER e0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:real^2->bool`; `c0 UNION inside(c0:real^2->bool)`;
                 `IMAGE (fs:real^2->real^3) s1`; `e0:real^3->bool`;
                 `fs:real^2->real^3`; `gs:real^3->real^2`;
                 `f2:real^2->real^3`; `g2:real^3->real^2`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC));
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `S:real^2->bool`; `relative_frontier S:real^2->bool`;
                 `IMAGE (fs:real^2->real^3) s1 UNION e0`;
                 `\x. if x IN s1 then (fs:real^2->real^3) x else f2 x`;
                 `\y. if y IN IMAGE (fs:real^2->real^3) s1 then (gs:real^3->real^2) y
                      else g2 y`] MOI_FCL_CELL_TRANSFER) THEN
  ASM_SIMP_TAC[MOI_S3L9_SIMPLEX_CELL; DIMINDEX_3; ARITH] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN s1` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `relative_frontier S SUBSET (s1:real^2->bool)` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 7. The circle step.  The antecedents of the main theorem as        *)
(* constants; the chart of a pseudo-cell with its trace (a Jordan curve    *)
(* with the centre inside); an innermost circle of the disk bounds a disk  *)
(* in one piece, so by Lemma 8 its disk in the pseudo-cell misses the      *)
(* centre and the trace; an innermost circle in the pseudo-cell inside     *)
(* that disk; the swap and the push-off remove it and every circle inside  *)
(* its disk.                                                               *)
(* ------------------------------------------------------------------------- *)

let moi_s3l9i_l8 = new_definition
  (mk_eq(mk_var("moi_s3l9i_l8",bool_ty), MOI_S33_L8_BODY));;

let moi_s3l9i_push = new_definition
  (mk_eq(mk_var("moi_s3l9i_push",bool_ty), MOI_S39_PUSH_BODY));;

(* The pieces of X and of its frontier at a pseudo-cell.                     *)

let MOI_S3L9_X_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
     ==> compact (UNIONS x) /\ frontier (UNIONS x) SUBSET UNIONS x /\
         UNIONS x SUBSET interior (IMAGE h (derived_nbhd t l)) /\
         IMAGE h (UNIONS l) SUBSET interior (UNIONS x) /\
         DISJOINT (interior (UNIONS x)) (frontier (UNIONS x)) /\
         DISJOINT (interior (IMAGE h (derived_nbhd t l)))
                  (frontier (IMAGE h (derived_nbhd t l))) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> pl_sphere 1 (e(segment[u,v]) INTER frontier (UNIONS x)) /\
                    disk_with_boundary (e(segment[u,v]) INTER UNIONS x)
                                       (e(segment[u,v]) INTER frontier (UNIONS x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `compact (UNIONS (x:(real^3->bool)->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    SET_TAC[];
    REWRITE_TAC[frontier] THEN SET_TAC[];
    REWRITE_TAC[frontier] THEN SET_TAC[]]);;

(* The chart of an edge pseudo-cell: its trace is a Jordan curve in the     *)
(* chart with the centre inside, and the inside is exactly X.               *)

let MOI_S3L9_EDGE_CHART = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x u v.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ ~(u = v) /\ segment[u,v] IN l
     ==> ?(phi:real^3->real^2) psi.
           homeomorphism (e(segment[u,v]) DIFF moi_s33_rim t l h u v,ball(vec 0,&1))
                         (phi,psi) /\
           e(segment[u,v]) INTER UNIONS x SUBSET
             e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
           compact (IMAGE phi (e(segment[u,v]) INTER frontier (UNIONS x))) /\
           connected (IMAGE phi (e(segment[u,v]) INTER frontier (UNIONS x))) /\
           h(midpoint(u,v)) IN e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
           phi(h(midpoint(u,v))) IN
             inside (IMAGE phi (e(segment[u,v]) INTER frontier (UNIONS x))) /\
           (!y. y IN e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
                ~(y IN frontier (UNIONS x))
                ==> (y IN UNIONS x <=>
                     phi y IN inside (IMAGE phi (e(segment[u,v]) INTER
                                                 frontier (UNIONS x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_HD_PC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] MOI_S3L9_X_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "disk_with_boundary")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ee = (e:(real^3->bool)->real^3->bool)(segment[u,v])` THEN
  ABBREV_TAC `jr = moi_s33_rim t l h u v` THEN
  ABBREV_TAC `pp = (h:real^3->real^3)(midpoint(u,v))` THEN
  ABBREV_TAC `xx = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `np = IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_CELL_CHART o check (fun th ->
    can (term_match [] `pseudo_cell (ee:real^3->bool) jr pp`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_TAC `psi:real^2->real^3`)) THEN
  MAP_EVERY EXISTS_TAC [`phi:real^3->real^2`; `psi:real^2->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (ee DIFF jr,ball(vec 0:real^2,&1))
                           (phi:real^3->real^2,psi)`) (concl th))) THEN
  SUBGOAL_THEN `ee INTER xx SUBSET ee DIFF (jr:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ee INTER frontier np = jr:real^3->bool` THEN
    UNDISCH_TAC `xx SUBSET interior (np:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (interior np) (frontier (np:real^3->bool))` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pp IN ee DIFF (jr:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pseudo_cell (ee:real^3->bool) jr pp` THEN SIMP_TAC[pseudo_cell];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(pp:real^3) IN xx /\ ~(pp IN frontier xx)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ee INTER IMAGE (h:real^3->real^3) (UNIONS l) = {pp}` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior xx` THEN
    UNDISCH_TAC `DISJOINT (interior xx) (frontier (xx:real^3->bool))` THEN
    MP_TAC(ISPEC `xx:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `disk_with_boundary (IMAGE (phi:real^3->real^2) (ee INTER xx))
                                   (IMAGE phi (ee INTER frontier xx))` ASSUME_TAC THENL
   [UNDISCH_TAC `disk_with_boundary (ee INTER xx) (ee INTER frontier (xx:real^3->bool))` THEN
    REWRITE_TAC[disk_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(phi:real^3->real^2) o (f:real^2->real^3)`;
                          `(g:real^3->real^2) o (psi:real^2->real^3)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `ee INTER xx:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`ee DIFF jr:real^3->bool`; `ball(vec 0:real^2,&1)`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee DIFF jr) = ball(vec 0,&1)` THEN
      UNDISCH_TAC `ee INTER xx SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_o]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:real^3->real^2) (ee INTER xx)`;
                 `IMAGE (phi:real^3->real^2) (ee INTER frontier xx)`]
    MOI_S3L9_PLANE_DISK_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier xx SUBSET (xx:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ee DIFF jr /\ ~(y IN frontier xx)
        ==> (y IN xx <=>
             (phi:real^3->real^2) y IN inside (IMAGE phi (ee INTER frontier xx)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!w:real^3. w IN ee DIFF jr /\ (phi:real^3->real^2) w = phi y ==> w = y`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `w:real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((phi:real^3->real^2) y IN IMAGE phi (ee INTER frontier xx))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `w:real^3 = y` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC `ee INTER xx SUBSET ee DIFF (jr:real^3->bool)` THEN
          UNDISCH_TAC `frontier xx SUBSET (xx:real^3->bool)` THEN
          UNDISCH_TAC `(w:real^3) IN ee` THEN UNDISCH_TAC `(w:real^3) IN frontier xx` THEN
          SET_TAC[];
          ASM_REWRITE_TAC[]];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^2) y IN IMAGE phi (ee INTER xx) <=> y IN xx`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `w:real^3 = y` (fun th -> ASM_MESON_TAC[th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC `ee INTER xx SUBSET ee DIFF (jr:real^3->bool)` THEN
          UNDISCH_TAC `(w:real^3) IN ee` THEN UNDISCH_TAC `(w:real^3) IN xx` THEN SET_TAC[];
          ASM_REWRITE_TAC[]];
        DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN ee DIFF jr` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(phi:real^3->real^2) y IN IMAGE phi (ee INTER xx) <=> y IN xx` THEN
    UNDISCH_TAC `~((phi:real^3->real^2) y IN IMAGE phi (ee INTER frontier xx))` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee INTER xx) =
                 IMAGE phi (ee INTER frontier xx) UNION
                 inside (IMAGE phi (ee INTER frontier xx))` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pp:real^3`) THEN ASM_REWRITE_TAC[]);;

(* Members of a general position family.                                    *)

let MOI_S3L9_MEMBER_FACTS = prove
 (`!(l:(real^3->bool)->bool) e (x:(real^3->bool)->bool) d cs a.
     moi_s39_family l e x d cs /\ a IN cs
     ==> a SUBSET d /\ a SUBSET moi_s39_pcs l e /\ compact a /\ connected a /\
         ~(a = {}) /\
         ((pl_sphere 1 a /\ DISJOINT a (frontier (UNIONS x))) \/
          (pl_cell_with_boundary 1 a (a INTER frontier (UNIONS x)) /\
           ~(a INTER frontier (UNIONS x) = {})))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s39_family] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a SUBSET d /\ a SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `d INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = UNIONS cs` THEN
    UNDISCH_TAC `(a:real^3->bool) IN cs` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPEC `a:real^3->bool` MOI_S3L9_PL_SPHERE1_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real^3->bool`; `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      MP_TAC(ISPECL [`a:real^3->bool`; `sphere(vec 0:real^2,&1)`]
        HOMEOMORPHIC_CONNECTEDNESS) THEN
      ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
      DISCH_TAC THEN UNDISCH_TAC `(a:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
      can (term_match [] `pl_cell_with_boundary 1 (a:real^3->bool) b`) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `compact (k:real^3->bool) /\ convex k /\ ~(k = {}) /\
                  ~(relative_frontier k = {})` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        DISCH_TAC THEN UNDISCH_TAC `&1 simplex (k:real^3->bool)` THEN
        ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
        MP_TAC(ISPECL [`k:real^3->bool`; `&1:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_frontier (k:real^3->bool) SUBSET k` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) k = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) k = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[CONVEX_CONNECTED];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) k = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_frontier k) =
                   a INTER frontier (UNIONS (x:(real^3->bool)->bool))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]]]);;

(* An innermost circle of a general position family, in the planar model;   *)
(* every other member (circle or arc) misses its disk in the model.        *)

let MOI_S3L9_CIRCLE_INNER = prove
 (`!(l:(real^3->bool)->bool) e (x:(real^3->bool)->bool) d cs (S:real^2->bool) fs gs.
     moi_s39_family l e x d cs /\ &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
     IMAGE fs (relative_frontier S) = d INTER frontier (UNIONS x) /\
     (?a0. a0 IN cs /\ pl_sphere 1 a0 /\ DISJOINT a0 (frontier (UNIONS x)))
     ==> ?a1. a1 IN cs /\ pl_sphere 1 a1 /\ DISJOINT a1 (frontier (UNIONS x)) /\
              pl_sphere 1 (IMAGE gs a1) /\ IMAGE gs a1 SUBSET interior S /\
              (!a. a IN cs /\ ~(a = a1)
                   ==> DISJOINT (IMAGE gs a) (IMAGE gs a1 UNION inside (IMAGE gs a1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  SUBGOAL_THEN `!a. a IN cs ==> a SUBSET (d:real^3->bool) /\ compact a /\ connected a /\
                    ~(a = {}) /\
                    ((pl_sphere 1 a /\ DISJOINT a bx) \/
                     (pl_cell_with_boundary 1 a (a INTER bx) /\ ~(a INTER bx = {})))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gs:real^3->real^2) (d INTER bx) = relative_frontier S`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) (relative_frontier S) = d INTER bx` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3->bool. a SUBSET d /\ b SUBSET d
                    ==> IMAGE (gs:real^3->real^2) a INTER IMAGE gs b = IMAGE gs (a INTER b) /\
                        (IMAGE gs a = IMAGE gs b ==> a = b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN UNDISCH_TAC `(b:real^3->bool) SUBSET d` THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `IMAGE (fs:real^2->real^3)`) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN `!s:real^3->bool. s SUBSET d
                      ==> IMAGE (\x. (fs:real^2->real^3)((gs:real^3->real^2) x)) s = s`
      (fun th -> ASM_SIMP_TAC[th]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN cs /\ pl_sphere 1 a /\ DISJOINT a bx
        ==> IMAGE (gs:real^3->real^2) a SUBSET interior S /\ pl_sphere 1 (IMAGE gs a) /\
            compact (IMAGE gs a) /\ connected (IMAGE gs a) /\ ~(IMAGE gs a = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (gs:real^3->real^2) a SUBSET S /\
                    IMAGE gs a INTER relative_frontier S = {}` MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (gs:real^3->real^2) d = S` THEN
          UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN SET_TAC[];
          UNDISCH_TAC `IMAGE (gs:real^3->real^2) (d INTER bx) = relative_frontier S` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `d INTER bx:real^3->bool`] o
            check (fun th -> is_forall(concl th) &&
              can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER"))
                (concl th) &&
              can (find_term ((=) `gs:real^3->real^2`)) (concl th))) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
          UNDISCH_TAC `DISJOINT (a:real^3->bool) bx` THEN SET_TAC[]];
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[]];
      MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `S:real^2->bool`; `fs:real^2->real^3`] THEN
      ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
  ABBREV_TAC `pp = {IMAGE (gs:real^3->real^2) a | a | a IN cs /\ pl_sphere 1 a /\
                                                     DISJOINT a bx}` THEN
  MP_TAC(ISPEC `pp:(real^2->bool)->bool` MOI_S3L9_PLANE_INNERMOST) THEN ANTS_TAC THENL
   [EXPAND_TAC "pp" THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family];
        SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `a:real^3->bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `b:real^3->bool` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^3->bool) SUBSET d /\ b SUBSET d` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(a:real^3->bool = b)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(IMAGE (gs:real^3->real^2) a = IMAGE gs b)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (a:real^3->bool) b` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN
        REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `b:real^3->bool`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `gs:real^3->real^2`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      UNDISCH_TAC `DISJOINT (a:real^3->bool) b` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^2->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(c1:real^2->bool) IN pp` THEN EXPAND_TAC "pp" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a1:real^3->bool` THEN
  SUBGOAL_THEN `IMAGE (gs:real^3->real^2) a1 SUBSET interior S /\ pl_sphere 1 (IMAGE gs a1) /\
                compact (IMAGE gs a1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a1:real^3->bool` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "interior")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
        (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `c1 = IMAGE (gs:real^3->real^2) a1`)) THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET d /\ a1 SUBSET d /\ DISJOINT a a1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (gs:real^3->real^2) a) (IMAGE gs a1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `a1:real^3->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gs:real^3->real^2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    UNDISCH_TAC `DISJOINT (a:real^3->bool) a1` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "pp" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(a:real^3->bool = a1)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `a1:real^3->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gs:real^3->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    SUBGOAL_THEN `IMAGE (gs:real^3->real^2) a INTER inside(IMAGE gs a1) = {}` MP_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `DISJOINT (IMAGE (gs:real^3->real^2) a) (IMAGE gs a1)` THEN SET_TAC[]] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (gs:real^3->real^2) a1`; `IMAGE (gs:real^3->real^2) a`]
      MOI_S3L9_CONN_INSIDE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `inside(IMAGE (gs:real^3->real^2) a1) SUBSET interior S` ASSUME_TAC THENL
     [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_SIMP_TAC[CONVEX_INTERIOR]; ALL_TAC] THEN
    SUBGOAL_THEN `~(IMAGE (gs:real^3->real^2) a INTER relative_frontier S = {})` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (gs:real^3->real^2) (d INTER bx) = relative_frontier S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `~(a INTER bx:real^3->bool = {})` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN
      UNDISCH_TAC `inside(IMAGE (gs:real^3->real^2) a1) SUBSET interior S` THEN
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) a SUBSET inside(IMAGE gs a1)` THEN SET_TAC[]]]);;

(* The image under a left inverse.                                           *)

let MOI_S3L9_IMAGE_LEFT_INV = prove
 (`!(f:B->A) (g:A->B) s t.
     (!y. y IN t ==> f(g y) = y) /\ s SUBSET t ==> IMAGE f (IMAGE g s) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `(!x:A. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
  REWRITE_TAC[o_THM] THEN ASM SET_TAC[]);;

(* The disk of the innermost circle in the loop theorem disk: a PL disk     *)
(* meeting the pseudo-cells only in its boundary, inside one piece at an    *)
(* end of the pseudo-cell containing the circle.                            *)

let MOI_S3L9_CIRCLE_PIECE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs
    (S:real^2->bool) fs gs a1.
     moi_s33_hd t l h e c /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\ &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
     a1 IN cs /\ pl_sphere 1 a1 /\ DISJOINT a1 (frontier (UNIONS x)) /\
     pl_sphere 1 (IMAGE gs a1) /\ IMAGE gs a1 SUBSET interior S /\
     (!a. a IN cs /\ ~(a = a1)
          ==> DISJOINT (IMAGE gs a) (IMAGE gs a1 UNION inside (IMAGE gs a1)))
     ==> pl_cell_with_boundary 2 (IMAGE fs (IMAGE gs a1 UNION inside (IMAGE gs a1))) a1 /\
         IMAGE fs (IMAGE gs a1 UNION inside (IMAGE gs a1)) SUBSET d /\
         IMAGE fs (IMAGE gs a1 UNION inside (IMAGE gs a1)) INTER moi_s39_pcs l e = a1 /\
         ?v w. ~(v = w) /\ segment[v,w] IN l /\ {v} IN l /\
               a1 SUBSET e(segment[v,w]) /\
               IMAGE fs (IMAGE gs a1 UNION inside (IMAGE gs a1)) SUBSET c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c1 = IMAGE (gs:real^3->real^2) a1` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a1:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) c1 = a1` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN
    EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `S:real^2->bool`] MOI_S3L9_PLANE_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1 UNION inside c1 SUBSET (S:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `c1 UNION inside c1 SUBSET interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^2->bool`; `d:real^3->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                 `c1 UNION inside c1:real^2->bool`; `c1:real^2->bool`] MOI_S3L9_MODEL_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `dj = IMAGE (fs:real^2->real^3) (c1 UNION inside c1)` THEN
  SUBGOAL_THEN `dj SUBSET (d:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dj" THEN UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
    UNDISCH_TAC `c1 UNION inside c1 SUBSET (S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dj INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = a1` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN d` ASSUME_TAC THENL
       [UNDISCH_TAC `dj SUBSET (d:real^3->bool)` THEN UNDISCH_TAC `(y:real^3) IN dj` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?a. a IN cs /\ (y:real^3) IN a` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN REWRITE_TAC[moi_s39_family] THEN
        STRIP_TAC THEN
        UNDISCH_TAC `d INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = UNIONS cs` THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `a:real^3->bool = a1` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN dj` THEN EXPAND_TAC "dj" THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:real^2) IN S` ASSUME_TAC THENL
       [UNDISCH_TAC `c1 UNION inside c1 SUBSET (S:real^2->bool)` THEN
        UNDISCH_TAC `(z:real^2) IN c1 UNION inside c1` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(gs:real^3->real^2) ((fs:real^2->real^3) z) = z` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "inside")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(gs:real^3->real^2) ((fs:real^2->real^3) z) = z` THEN
      UNDISCH_TAC `((fs:real^2->real^3) z) IN a` THEN
      UNDISCH_TAC `(z:real^2) IN c1 UNION inside c1` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) c1 = a1` THEN
      UNDISCH_TAC `(a1:real^3->bool) SUBSET moi_s39_pcs l e` THEN EXPAND_TAC "dj" THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dj DIFF a1 = IMAGE (fs:real^2->real^3) (inside c1)` ASSUME_TAC THENL
   [EXPAND_TAC "dj" THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) c1 = a1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S3L9_IMAGE_DIFF_INJ THEN EXISTS_TAC `gs:real^3->real^2` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
      UNDISCH_TAC `c1 UNION inside c1 SUBSET (S:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `inside c1 INTER c1:real^2->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (dj DIFF a1:real^3->bool) /\ ~(dj DIFF a1 = {})` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c1 UNION inside c1 SUBSET (S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `dj DIFF a1:real^3->bool`]
    MOI_S3L9_CONNECTED_PIECE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `d SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    UNDISCH_TAC `dj INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = a1` THEN
    UNDISCH_TAC `dj SUBSET (d:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closed ((c:real^3->real^3->bool) v0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v0:real^3`] MOI_S3L9_HD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `dj SUBSET (c:real^3->real^3->bool) v0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a1:real^3->bool) SUBSET closure(dj DIFF a1)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) c1 = a1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (fs:real^2->real^3) (closure(inside c1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        SUBGOAL_THEN `?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                                           path_image gam = c1` STRIP_ASSUME_TAC THENL
         [MP_TAC(ISPECL [`c1:real^2->bool`; `vec 0:real^2`; `&1`]
            HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
          REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
          ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`gam:real^1->real^2`; `c1:real^2->bool`] MOI_SFR_JORDAN_REGION) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
        SIMP_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        UNDISCH_TAC `c1 UNION inside c1 SUBSET (S:real^2->bool)` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `closure(dj DIFF a1) SUBSET (c:real^3->real^3->bool) v0` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `dj DIFF a1 SUBSET (c:real^3->real^3->bool) v0` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET closure(dj DIFF a1)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `a1:real^3->bool`] MOI_S3L9_CONN_PCS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u0:real^3`; `w0:real^3`; `v0:real^3`]
    MOI_S3L9_PIECE_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a1:real^3->bool = {})` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET e(segment[u0:real^3,w0])` THEN
    UNDISCH_TAC `dj SUBSET (c:real^3->real^3->bool) v0` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) c1 = a1` THEN EXPAND_TAC "dj" THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u0:real^3`; `w0:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`w0:real^3`; `u0:real^3`] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Lemma 8 applied to the disk of an innermost circle: the disk bounded by  *)
(* the circle in the pseudo-cell misses the centre.                         *)

let MOI_S3L9_CIRCLE_L8 = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool)
    dj a1 v w (phi:real^3->real^2) psi.
     moi_s3l9i_l8 /\ moi_s33_hd t l h e c /\
     pl_cell_with_boundary 2 dj a1 /\ dj SUBSET moi_s33_ww t l h /\
     dj INTER moi_s39_pcs l e = a1 /\
     ~(v = w) /\ segment[v,w] IN l /\ {v} IN l /\
     a1 SUBSET e(segment[v,w]) /\ dj SUBSET c v /\
     homeomorphism (e(segment[v,w]) DIFF moi_s33_rim t l h v w,ball(vec 0,&1)) (phi,psi) /\
     a1 SUBSET e(segment[v,w]) DIFF moi_s33_rim t l h v w /\ pl_sphere 1 a1
     ==> ~(h(midpoint(v,w)) IN IMAGE psi (IMAGE phi a1 UNION inside(IMAGE phi a1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e(segment[v:real^3,w]):real^3->bool`; `moi_s33_rim t l h v w`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`; `a1:real^3->bool`]
    MOI_S3L9_CELL_DISK) THEN
  ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    can (term_match [] `pl_cell_with_boundary 2 (dj:real^3->bool) a1`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `DISJOINT (dj:real^3->bool) (IMAGE (h:real^3->real^3) (UNIONS l))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `dj SUBSET moi_s33_ww t l h` THEN REWRITE_TAC[moi_s33_ww] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dj:real^3->bool) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `dj SUBSET moi_s33_ww t l h` THEN REWRITE_TAC[moi_s33_ww] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e(segment[v:real^3,w]) SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC(SET_RULE
     `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s3l9i_l8` THEN REWRITE_TAC[moi_s3l9i_l8] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`;
    `dj:real^3->bool`; `k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`]) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[SUBSET_INTER];
    UNDISCH_TAC `a1 = IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `dj INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = a1` THEN
    UNDISCH_TAC `e(segment[v:real^3,w]) SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN SET_TAC[];
    UNDISCH_TAC `a1 = IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `IMAGE (psi:real^2->real^3) (IMAGE (phi:real^3->real^2) a1 UNION
                    inside(IMAGE phi a1))` THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^2->real^3) (IMAGE (phi:real^3->real^2) a1 UNION inside (IMAGE phi a1))
                   SUBSET e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w` THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `DISJOINT (dj:real^3->bool) (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
      UNDISCH_TAC `dj INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = a1` THEN
      UNDISCH_TAC `(h:real^3->real^3)(midpoint(v,w)) IN a1` THEN
      SUBGOAL_THEN `(h:real^3->real^3)(midpoint(v,w)) IN IMAGE h (UNIONS l)` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
        SET_TAC[]]];
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `s:real^3->bool`; `segment[v:real^3,w]`]
      MOI_S3L9_HD_DISJ) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:(real^3->bool)->real^3->bool) s SUBSET moi_s39_pcs l e` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC(SET_RULE
       `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT ((e:(real^3->bool)->real^3->bool) s) (e(segment[v:real^3,w]))` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) s SUBSET moi_s39_pcs l e` THEN
    UNDISCH_TAC `dj INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = a1` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN SET_TAC[];
    UNDISCH_TAC `DISJOINT (dj:real^3->bool) (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
    SET_TAC[]]);;

(* A member of the family meeting a pseudo-cell lies in it.                  *)

let MOI_S3L9_MEMBER_IN_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs a v w.
     moi_s33_hd t l h e c /\ moi_s39_family l e x d cs /\ a IN cs /\
     ~(v = w) /\ segment[v,w] IN l /\ ~(a INTER e(segment[v,w]) = {})
     ==> a SUBSET e(segment[v,w])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `a:real^3->bool`] MOI_S3L9_CONN_PCS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `segment[u':real^3,w'] = segment[v,w]` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `segment[u':real^3,w']`; `segment[v:real^3,w]`]
    MOI_S3L9_HD_DISJ) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  UNDISCH_TAC `~((a:real^3->bool) INTER e(segment[v:real^3,w]) = {})` THEN
  UNDISCH_TAC `(a:real^3->bool) SUBSET e(segment[u':real^3,w'])` THEN SET_TAC[]);;

(* An innermost circle in the pseudo-cell inside the disk of a1 there: its  *)
(* disk meets the loop theorem disk only in the circle, and misses the     *)
(* centre and Bd X.                                                          *)

let MOI_S3L9_CIRCLE_EINNER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs
    a1 v w (phi:real^3->real^2) psi.
     moi_s33_hd t l h e c /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\ a1 IN cs /\ pl_sphere 1 a1 /\
     DISJOINT a1 (frontier (UNIONS x)) /\
     ~(v = w) /\ segment[v,w] IN l /\ a1 SUBSET e(segment[v,w]) /\
     homeomorphism (e(segment[v,w]) DIFF moi_s33_rim t l h v w,ball(vec 0,&1)) (phi,psi) /\
     e(segment[v,w]) INTER UNIONS x SUBSET e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     frontier (UNIONS x) SUBSET UNIONS x /\
     phi(h(midpoint(v,w))) IN inside (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x))) /\
     compact (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x))) /\
     connected (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x))) /\
     h(midpoint(v,w)) IN e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     ~(h(midpoint(v,w)) IN IMAGE psi (IMAGE phi a1 UNION inside(IMAGE phi a1)))
     ==> ?a2. a2 IN cs /\ pl_sphere 1 a2 /\ DISJOINT a2 (frontier (UNIONS x)) /\
              a2 SUBSET e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
              IMAGE psi (IMAGE phi a2 UNION inside(IMAGE phi a2)) INTER d = a2 /\
              ~(h(midpoint(v,w)) IN IMAGE psi (IMAGE phi a2 UNION inside(IMAGE phi a2))) /\
              DISJOINT (IMAGE psi (IMAGE phi a2 UNION inside(IMAGE phi a2)))
                       (frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ee = e(segment[v:real^3,w]):real^3->bool` THEN
  ABBREV_TAC `jr = moi_s33_rim t l h v w` THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `gg = IMAGE (phi:real^3->real^2) (ee INTER bx)` THEN
  ABBREV_TAC `pc = (phi:real^3->real^2)((h:real^3->real^3)(midpoint(v,w)))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (ee DIFF jr,ball(vec 0:real^2,&1))
                           (phi:real^3->real^2,psi)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  SUBGOAL_THEN `d INTER (jr:real^3->bool) = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`] MOI_S3L9_HD_PC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `ee INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) = jr` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `d SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN cs ==> a SUBSET (d:real^3->bool) /\ compact a /\ connected a /\
                    ~(a = {}) /\
                    ((pl_sphere 1 a /\ DISJOINT a bx) \/
                     (pl_cell_with_boundary 1 a (a INTER bx) /\ ~(a INTER bx = {})))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3->bool. a SUBSET ee DIFF jr /\ b SUBSET ee DIFF jr
                    ==> IMAGE (phi:real^3->real^2) a INTER IMAGE phi b = IMAGE phi (a INTER b) /\
                        (IMAGE phi a = IMAGE phi b ==> a = b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET ee DIFF jr` THEN
      UNDISCH_TAC `(b:real^3->bool) SUBSET ee DIFF jr` THEN SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `IMAGE (psi:real^2->real^3)`) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN `!s:real^3->bool. s SUBSET ee DIFF jr
                      ==> IMAGE (\x. (psi:real^2->real^3)((phi:real^3->real^2) x)) s = s`
      (fun th -> ASM_SIMP_TAC[th]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET ee DIFF jr` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `qq = {a:real^3->bool | a IN cs /\ pl_sphere 1 a /\ DISJOINT a bx /\
                                      a SUBSET ee /\
                                      (a = a1 \/ IMAGE (phi:real^3->real^2) a SUBSET
                                                 inside (IMAGE phi a1))}` THEN
  SUBGOAL_THEN `!a. a IN qq ==> a IN cs /\ pl_sphere 1 a /\ DISJOINT a bx /\
                                a SUBSET ee DIFF jr /\
                                compact (IMAGE (phi:real^3->real^2) a) /\
                                connected (IMAGE phi a) /\ ~(IMAGE phi a = {}) /\
                                IMAGE phi a SUBSET IMAGE phi a1 UNION inside (IMAGE phi a1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN EXPAND_TAC "qq" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr` ASSUME_TAC THENL
     [UNDISCH_TAC `d INTER (jr:real^3->bool) = {}` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]) THEN
    TRY(MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]) THEN
    UNDISCH_TAC `a = a1 \/ IMAGE (phi:real^3->real^2) a SUBSET inside (IMAGE phi a1)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (IMAGE (phi:real^3->real^2)) qq` MOI_S3L9_PLANE_INNERMOST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `cs:(real^3->bool)->bool` THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family];
        EXPAND_TAC "qq" THEN SET_TAC[]];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `a1:real^3->bool` THEN
      EXPAND_TAC "qq" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `b:real^3->bool` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr /\ b SUBSET ee DIFF jr /\
                    a IN cs /\ b IN cs` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `b:real^3->bool`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(a:real^3->bool = b)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (a:real^3->bool) b` MP_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN
        REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `IMAGE (phi:real^3->real^2) a INTER IMAGE phi b = IMAGE phi (a INTER b)` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(a2:real^3->bool) IN qq`) o
    check (fun th ->
    is_forall(concl th) && can (find_term ((=) `qq:(real^3->bool)->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact")) (concl th))) THEN
  SUBGOAL_THEN `a2 = a1 \/ IMAGE (phi:real^3->real^2) a2 SUBSET inside (IMAGE phi a1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(a2:real^3->bool) IN qq` THEN EXPAND_TAC "qq" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a1:real^3->bool) IN qq` ASSUME_TAC THENL
   [EXPAND_TAC "qq" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(a1:real^3->bool) IN qq`) o
    check (fun th ->
    is_forall(concl th) && can (find_term ((=) `qq:(real^3->bool)->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact")) (concl th))) THEN
  EXISTS_TAC `a2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(psi:real^2->real^3) pc = (h:real^3->real^3)(midpoint(v,w))` ASSUME_TAC THENL
   [EXPAND_TAC "pc" THEN
    UNDISCH_TAC `(h:real^3->real^3)(midpoint(v,w)) IN ee DIFF jr` THEN
    UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER bx SUBSET (ee DIFF jr:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ee INTER UNIONS x SUBSET (ee DIFF jr:real^3->bool)` THEN
    UNDISCH_TAC `bx SUBSET UNIONS (x:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC(SET_RULE
     `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  ABBREV_TAC `c2 = IMAGE (phi:real^3->real^2) a2` THEN
  ABBREV_TAC `c1 = IMAGE (phi:real^3->real^2) a1` THEN
  (* F0: the centre of the chart is not in the disk of c1 *)
  SUBGOAL_THEN `~(pc IN (c1:real^2->bool) UNION inside c1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((h:real^3->real^3)(midpoint(v,w)) IN
                   IMAGE (psi:real^2->real^3) (c1 UNION inside c1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `pc:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F1, F2: the image of Bd X misses the disk of c1 *)
  SUBGOAL_THEN `DISJOINT gg (c1:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN EXPAND_TAC "c1" THEN REWRITE_TAC[DISJOINT] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`ee INTER bx:real^3->bool`; `a1:real^3->bool`] o
      check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    UNDISCH_TAC `DISJOINT (a1:real^3->bool) bx` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real^2->bool`; `c1:real^2->bool`; `pc:real^2`] MOI_S3L9_PLANE_AVOID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* F5, F3: the disk of c2 lies in the disk of c1 *)
  SUBGOAL_THEN `inside c2 SUBSET inside (c1:real^2->bool)` ASSUME_TAC THENL
   [ASM_CASES_TAC `a2:real^3->bool = a1` THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^2) a2 = c2` THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) a1 = c1` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `c2 SUBSET inside (c1:real^2->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(a2:real^3->bool) = a1 \/ c2 SUBSET inside (c1:real^2->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `c2 UNION inside c2 SUBSET (c1:real^2->bool) UNION inside c1` ASSUME_TAC THENL
   [UNDISCH_TAC `inside c2 SUBSET inside (c1:real^2->bool)` THEN
    UNDISCH_TAC `c2 SUBSET (c1:real^2->bool) UNION inside c1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^2->bool) UNION inside c1 SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c1:real^2->bool) SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
     [EXPAND_TAC "c1" THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee DIFF jr) = ball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_BALL];
    ALL_TAC] THEN
  (* G2: the centre *)
  SUBGOAL_THEN `~((h:real^3->real^3)(midpoint(v,w)) IN
                  IMAGE (psi:real^2->real^3) (c2 UNION inside c2))` ASSUME_TAC THENL
   [UNDISCH_TAC `~((h:real^3->real^3)(midpoint(v,w)) IN
                   IMAGE (psi:real^2->real^3) (c1 UNION inside c1))` THEN
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> (x:real^3) IN IMAGE (f:real^2->real^3) s ==> x IN IMAGE f t`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* points of the chart disk of c2 *)
  SUBGOAL_THEN `!z:real^2. z IN c2 UNION inside c2
                    ==> z IN ball(vec 0,&1) /\ (psi:real^2->real^3) z IN ee DIFF jr /\
                        (phi:real^3->real^2)(psi z) = z /\ ~(z IN gg)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(c1:real^2->bool) UNION inside c1 SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `c2 UNION inside c2 SUBSET (c1:real^2->bool) UNION inside c1` THEN
      UNDISCH_TAC `(z:real^2) IN c2 UNION inside c2` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,&1)) = ee DIFF jr` THEN
      UNDISCH_TAC `(z:real^2) IN ball(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN ball(vec 0,&1)` THEN
      UNDISCH_TAC `!y. y IN ball(vec 0,&1)
                       ==> (phi:real^3->real^2)((psi:real^2->real^3) y) = y` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT gg ((c1:real^2->bool) UNION inside c1)` THEN
    UNDISCH_TAC `c2 UNION inside c2 SUBSET (c1:real^2->bool) UNION inside c1` THEN
    UNDISCH_TAC `(z:real^2) IN c2 UNION inside c2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* G3: Bd X *)
  SUBGOAL_THEN `DISJOINT (IMAGE (psi:real^2->real^3) (c2 UNION inside c2)) bx`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `y:real^3`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `gg:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((z:real^2) IN gg)` THEN REWRITE_TAC[] THEN EXPAND_TAC "gg" THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(psi:real^2->real^3) z` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(psi:real^2->real^3) z IN ee DIFF jr` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* G1: the chart disk of c2 meets d only in a2 *)
  SUBGOAL_THEN `IMAGE (psi:real^2->real^3) c2 = a2` ASSUME_TAC THENL
   [EXPAND_TAC "c2" THEN MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN
    EXISTS_TAC `ee DIFF jr:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^2->real^3) c2 = a2` THEN SET_TAC[];
      FIRST_ASSUM((fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP th
                     (ASSUME `(a2:real^3->bool) IN cs`)))) o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "pl_cell_with_boundary")) (concl th)))]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^2) IN c2 UNION inside c2`) o
    check (fun th ->
    is_forall(concl th) && can (find_term ((=) `gg:real^2->bool`)) (concl th))) THEN
  SUBGOAL_THEN `?a. a IN cs /\ (psi:real^2->real^3) z IN a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s39_family l e x d cs` THEN REWRITE_TAC[moi_s39_family] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `d INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = UNIONS cs` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS] THEN
    DISCH_THEN(MP_TAC o SPEC `(psi:real^2->real^3) z`) THEN
    SUBGOAL_THEN `(psi:real^2->real^3) z IN moi_s39_pcs l e` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `ee SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
      UNDISCH_TAC `(psi:real^2->real^3) z IN ee DIFF jr` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^3->bool = a2` THENL
   [UNDISCH_TAC `(psi:real^2->real^3) z IN a` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> MAP_EVERY ASSUME_TAC
                  (CONJUNCTS (MATCH_MP th (ASSUME `(a:real^3->bool) IN cs`)))) o
    check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET ee` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN MATCH_MP_TAC MOI_S3L9_MEMBER_IN_EDGE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                          `h:real^3->real^3`;
                          `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                          `d:real^3->bool`; `cs:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(psi:real^2->real^3) z IN a` THEN
    UNDISCH_TAC `(psi:real^2->real^3) z IN ee DIFF jr` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr` ASSUME_TAC THENL
   [UNDISCH_TAC `d INTER (jr:real^3->bool) = {}` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (a:real^3->bool) a2` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (phi:real^3->real^2) a) c2` ASSUME_TAC THENL
   [EXPAND_TAC "c2" THEN REWRITE_TAC[DISJOINT] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `a2:real^3->bool`] o
      check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    UNDISCH_TAC `DISJOINT (a:real^3->bool) a2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^3->real^2) a` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(psi:real^2->real^3) z` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^2) a SUBSET inside c2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_CONN_INSIDE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (IMAGE (phi:real^3->real^2) a) c2` THEN
      UNDISCH_TAC `(z:real^2) IN IMAGE (phi:real^3->real^2) a` THEN
      UNDISCH_TAC `(z:real^2) IN c2 UNION inside c2` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `a:real^3->bool`)) (concl th))) THENL
   [(* a is a circle: it would be in qq and inside the innermost c2 *)
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:real^3->bool) IN qq` ASSUME_TAC THENL
     [EXPAND_TAC "qq" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN
      UNDISCH_TAC `inside c2 SUBSET inside (c1:real^2->bool)` THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) a SUBSET inside c2` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(a:real^3->bool) IN qq`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `qq:(real^3->bool)->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "compact")) (concl th)))) THEN
    ANTS_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPEC `c2:real^2->bool` INSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) a SUBSET inside c2` THEN
      UNDISCH_TAC `(z:real^2) IN IMAGE (phi:real^3->real^2) a` THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) a = c2` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^2) IN IMAGE (phi:real^3->real^2) a` THEN
    UNDISCH_TAC `(z:real^2) IN c2 UNION inside c2` THEN SET_TAC[];
    (* a is an arc: it meets Bd X, whose image misses the disk of c1 *)
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `~(IMAGE (phi:real^3->real^2) (a INTER bx) = {}) /\
                  IMAGE (phi:real^3->real^2) (a INTER bx) SUBSET gg /\
                  IMAGE (phi:real^3->real^2) (a INTER bx) SUBSET IMAGE phi a`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
       [EXPAND_TAC "gg" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN SET_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT gg ((c1:real^2->bool) UNION inside c1)` THEN
    UNDISCH_TAC `inside c2 SUBSET inside (c1:real^2->bool)` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^2) a SUBSET inside c2` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^2) (a INTER bx) SUBSET IMAGE phi a` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^2) (a INTER bx) SUBSET gg` THEN
    UNDISCH_TAC `~(IMAGE (phi:real^3->real^2) (a INTER bx) = {})` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8. The swap of the circle step and the circle step itself.           *)
(* ------------------------------------------------------------------------- *)

(* In the planar model, every member of the family other than the circle a2 *)
(* lies inside the model circle of a2 or misses its disk; arcs miss it.    *)

let MOI_S3L9_MODEL_SPLIT = prove
 (`!(l:(real^3->bool)->bool) e (x:(real^3->bool)->bool) d cs (S:real^2->bool) fs gs a2 a.
     moi_s39_family l e x d cs /\ &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
     IMAGE fs (relative_frontier S) = d INTER frontier (UNIONS x) /\
     a2 IN cs /\ IMAGE gs a2 SUBSET interior S /\ pl_sphere 1 (IMAGE gs a2) /\
     a IN cs /\ ~(a = a2)
     ==> IMAGE gs a SUBSET inside (IMAGE gs a2) \/
         DISJOINT (IMAGE gs a) (IMAGE gs a2 UNION inside (IMAGE gs a2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a2:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `c0 = IMAGE (gs:real^3->real^2) a2` THEN
  MP_TAC(ISPECL [`c0:real^2->bool`; `S:real^2->bool`] MOI_S3L9_PLANE_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (a:real^3->bool) a2` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (gs:real^3->real^2) a) c0` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gs:real^3->real^2) a2 = c0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN UNDISCH_TAC `(a2:real^3->bool) SUBSET d` THEN
    UNDISCH_TAC `DISJOINT (a:real^3->bool) a2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (gs:real^3->real^2) a)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `IMAGE (gs:real^3->real^2) a INTER inside c0 = {}` THENL
   [DISJ2_TAC THEN UNDISCH_TAC `IMAGE (gs:real^3->real^2) a INTER inside c0 = {}` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (gs:real^3->real^2) a) c0` THEN SET_TAC[];
    DISJ1_TAC THEN MATCH_MP_TAC MOI_S3L9_CONN_INSIDE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* W is open.                                                                 *)

let MOI_S3L9_WW_OPEN = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool).
     moi_s33_hd t l h e c ==> open (moi_s33_ww t l h) /\ compact (IMAGE h (UNIONS l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S3L9_TUBE_BASIC th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[moi_s33_tube; graph_in_complex] th)) THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (UNIONS l))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simplicial_subcomplex (l:(real^3->bool)->bool) t` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN
      UNDISCH_TAC `simplicial_complex (l:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_COMPACT]];
    ASM_REWRITE_TAC[moi_s33_ww] THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED]]);;

(* Disjoint sets have disjoint images under a map with a left inverse.     *)

let MOI_S3L9_IMAGE_DISJOINT_INJ = prove
 (`!(f:A->B) (g:B->A) s t u.
     (!x. x IN u ==> g(f x) = x) /\ s SUBSET u /\ t SUBSET u /\ DISJOINT s t
     ==> DISJOINT (IMAGE f s) (IMAGE f t)`,
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* The swap and push of the circle step.                                      *)

let MOI_S3L9_CIRCLE_SWAP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs a2 ea v w.
     moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\ a2 IN cs /\ pl_sphere 1 a2 /\
     DISJOINT a2 (frontier (UNIONS x)) /\
     ~(v = w) /\ segment[v,w] IN l /\ a2 SUBSET e(segment[v,w]) /\
     pl_cell_with_boundary 2 ea a2 /\ ea SUBSET e(segment[v,w]) /\
     ea SUBSET moi_s33_ww t l h /\ ea INTER d = a2 /\ DISJOINT ea (frontier (UNIONS x))
     ==> ?d' cs'. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs' /\ cs' PSUBSET cs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `pcs = moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
  ABBREV_TAC `ww = moi_s33_ww t l (h:real^3->real^3)` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_PLANAR_MODEL o check (fun th ->
    (let c,args = strip_comb(concl th) in is_const c && fst(dest_const c) = "pl_cell_with_boundary" &&
     length args = 3 && el 1 args = `d:real^3->bool`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `fs:real^2->real^3`
    (X_CHOOSE_THEN `gs:real^3->real^2` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a2:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `c0 = IMAGE (gs:real^3->real^2) a2` THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) c0 = a2` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN
    UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
    UNDISCH_TAC `(a2:real^3->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gs:real^3->real^2) j = relative_frontier S` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) (relative_frontier S) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 SUBSET interior(S:real^2->bool) /\ pl_sphere 1 c0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `c0 SUBSET (S:real^2->bool) /\ c0 INTER relative_frontier S = {}` MP_TAC THENL
       [EXPAND_TAC "c0" THEN CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (gs:real^3->real^2) d = S` THEN
          UNDISCH_TAC `(a2:real^3->bool) SUBSET d` THEN SET_TAC[];
          UNDISCH_TAC `IMAGE (gs:real^3->real^2) j = relative_frontier S` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
          UNDISCH_TAC `d INTER bx = j:real^3->bool` THEN
          UNDISCH_TAC `DISJOINT (a2:real^3->bool) bx` THEN
          UNDISCH_TAC `(a2:real^3->bool) SUBSET d` THEN SET_TAC[]];
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[]];
      EXPAND_TAC "c0" THEN MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `S:real^2->bool`; `fs:real^2->real^3`] THEN
      ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:real^2->bool`; `S:real^2->bool`] MOI_S3L9_PLANE_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `cs' = {a:real^3->bool | a IN cs /\
                     DISJOINT a (IMAGE (fs:real^2->real^3) (c0 UNION inside c0))}` THEN
  ABBREV_TAC `rr = UNIONS (cs':(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `!a. a IN cs ==> a SUBSET (d:real^3->bool) /\ compact a /\ connected a /\
                    ~(a = {}) /\ a SUBSET pcs /\
                    ((pl_sphere 1 a /\ DISJOINT a bx) \/
                     (pl_cell_with_boundary 1 a (a INTER bx) /\ ~(a INTER bx = {})))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN S ==> (fs:real^2->real^3) z IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c0 UNION inside c0 SUBSET (S:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `c0 UNION inside c0 SUBSET interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN cs /\ ~(a IN cs')
                    ==> a SUBSET IMAGE (fs:real^2->real^3) (c0 UNION inside c0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `a:real^3->bool = a2` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `S:real^2->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                   `a2:real^3->bool`; `a:real^3->bool`] MOI_S3L9_MODEL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET d` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `IMAGE (gs:real^3->real^2) a SUBSET inside c0` THEN
      UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN SET_TAC[];
      UNDISCH_TAC `~((a:real^3->bool) IN cs')` THEN EXPAND_TAC "cs'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (IMAGE (gs:real^3->real^2) a) (c0 UNION inside c0)` THEN
      UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
      UNDISCH_TAC `c0 UNION inside c0 SUBSET (S:real^2->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d INTER pcs = UNIONS (cs:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pcs" THEN UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    SIMP_TAC[moi_s39_family];
    ALL_TAC] THEN
  SUBGOAL_THEN `d INTER pcs SUBSET rr UNION IMAGE (fs:real^2->real^3) (c0 UNION inside c0)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(a:real^3->bool) IN cs'` THENL
     [MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET s ==> a SUBSET s UNION t`) THEN
      EXPAND_TAC "rr" THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET t ==> a SUBSET s UNION t`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* rr: the members kept *)
  SUBGOAL_THEN `FINITE (cs':(real^3->bool)->bool) /\ cs' SUBSET cs` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cs'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family]; SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rr SUBSET (d:real^3->bool) /\ rr SUBSET pcs /\ compact rr /\
                DISJOINT rr (IMAGE (fs:real^2->real^3) (c0 UNION inside c0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[SUBSET];
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[SUBSET];
      EXPAND_TAC "cs'" THEN REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS] THEN
      REWRITE_TAC[IN_ELIM_THM; GSYM DISJOINT] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (rr:real^3->bool) a2` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT rr (IMAGE (fs:real^2->real^3) (c0 UNION inside c0))` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the swapped disk *)
  ABBREV_TAC `ds = IMAGE (fs:real^2->real^3) (S DIFF inside c0) UNION ea` THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (S DIFF inside c0) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ea INTER IMAGE (fs:real^2->real^3) (S DIFF inside c0) = IMAGE fs c0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `ea INTER d = a2:real^3->bool` THEN
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) (S DIFF inside c0) SUBSET d` THEN SET_TAC[];
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ea INTER d = a2:real^3->bool` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `inside c0 INTER c0:real^2->bool = {}` THEN
        UNDISCH_TAC `c0 UNION inside c0 SUBSET (S:real^2->bool)` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^2->bool`; `d:real^3->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                 `c0:real^2->bool`; `ea:real^3->bool`] MOI_S3L9_MODEL_SWAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `ds INTER bx = j:real^3->bool` ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (fs:real^2->real^3) (S DIFF inside c0) SUBSET d` THEN
      UNDISCH_TAC `d INTER bx = j:real^3->bool` THEN
      UNDISCH_TAC `DISJOINT (ea:real^3->bool) bx` THEN SET_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (fs:real^2->real^3) (relative_frontier S) = j`)) THEN
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `s SUBSET t ==> IMAGE (f:real^2->real^3) s SUBSET IMAGE f t UNION u`) THEN
        UNDISCH_TAC `c0 UNION inside c0 SUBSET interior(S:real^2->bool)` THEN
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN
        UNDISCH_TAC `DISJOINT (relative_frontier S) (interior(S:real^2->bool))` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (fs:real^2->real^3) (relative_frontier S) = j` THEN
        UNDISCH_TAC `d INTER bx = j:real^3->bool` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s33_ltd t l h x ds` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_ltd] THEN
    UNDISCH_TAC `pl_cell_with_boundary 2 ds (j:real^3->bool)` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    UNDISCH_TAC `j = IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ds" THEN
    UNDISCH_TAC `ea SUBSET (ww:real^3->bool)` THEN
    UNDISCH_TAC `d SUBSET (ww:real^3->bool)` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) (S DIFF inside c0) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  (* S5: the outer collar aa of c0 in the model, missing the kept members *)
  SUBGOAL_THEN `compact (IMAGE (gs:real^3->real^2) rr)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `d:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT c0 (IMAGE (gs:real^3->real^2) rr)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`gs:real^3->real^2`; `fs:real^2->real^3`; `a2:real^3->bool`;
                   `rr:real^3->bool`; `d:real^3->bool`] MOI_S3L9_IMAGE_DISJOINT_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:real^2->bool`;
                 `IMAGE (gs:real^3->real^2) rr UNION ((:real^2) DIFF interior S)`]
    MOI_S3L9_OUTER_COLLAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE];
      MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR];
      UNDISCH_TAC `DISJOINT c0 (IMAGE (gs:real^3->real^2) rr)` THEN
      UNDISCH_TAC `c0 SUBSET interior(S:real^2->bool)` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `aa:real^2->bool` STRIP_ASSUME_TAC)] THEN
  (* S6: facts about aa and its image in d *)
  SUBGOAL_THEN `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0) /\ ~(aa = {}) /\
                DISJOINT aa (IMAGE (gs:real^3->real^2) rr)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `c0:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
      MP_TAC(ISPEC `c0:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
      MP_TAC(ISPEC `S:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(aa:real^2->bool) SUBSET outside c0` THEN
      UNDISCH_TAC `DISJOINT (aa:real^2->bool)
                     (IMAGE (gs:real^3->real^2) rr UNION ((:real^2) DIFF interior S))` THEN
      SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `c0 SUBSET closure(aa:real^2->bool)` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY];
      UNDISCH_TAC `DISJOINT (aa:real^2->bool)
                     (IMAGE (gs:real^3->real^2) rr UNION ((:real^2) DIFF interior S))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (fs:real^2->real^3) aa) (IMAGE fs (c0 UNION inside c0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_IMAGE_DISJOINT_INJ THEN EXISTS_TAC `gs:real^3->real^2` THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (fs:real^2->real^3) aa) rr` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (aa:real^2->bool) (IMAGE (gs:real^3->real^2) rr)` THEN
    UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
    UNDISCH_TAC `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) aa SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
    UNDISCH_TAC `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (fs:real^2->real^3) aa) pcs` ASSUME_TAC THENL
   [UNDISCH_TAC `d INTER pcs SUBSET rr UNION IMAGE (fs:real^2->real^3) (c0 UNION inside c0)` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) (IMAGE fs (c0 UNION inside c0))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) rr` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (fs:real^2->real^3) aa) /\ ~(IMAGE fs aa = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* S7: the image of aa lies in one piece c v1 *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `IMAGE (fs:real^2->real^3) aa`]
    MOI_S3L9_CONNECTED_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `d SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) pcs` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET d` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `closed ((c:real^3->real^3->bool) v1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v1:real^3`] MOI_S3L9_HD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  (* S8: a2 lies in c v1, so v1 is an end of the edge and ea lies in c v1 *)
  SUBGOAL_THEN `(a2:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (fs:real^2->real^3) (closure aa)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `(aa:real^2->bool) SUBSET S DIFF (c0 UNION inside c0)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ea SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`; `v1:real^3`]
      MOI_S3L9_PIECE_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(a2:real^3->bool = {})` THEN
      UNDISCH_TAC `(a2:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN
      UNDISCH_TAC `(a2:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`] MOI_S3L9_EDGE_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    UNDISCH_TAC `(ea:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN
    UNDISCH_TAC `e(segment[v:real^3,w]) SUBSET (c:real^3->real^3->bool) v` THEN
    UNDISCH_TAC `e(segment[v:real^3,w]) SUBSET (c:real^3->real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  (* S9: the open set u pushed off *)
  SUBGOAL_THEN `DISJOINT (rr:real^3->bool) ea` ASSUME_TAC THENL
   [UNDISCH_TAC `ea INTER d = a2:real^3->bool` THEN
    UNDISCH_TAC `DISJOINT (rr:real^3->bool) a2` THEN
    UNDISCH_TAC `(rr:real^3->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (fs:real^2->real^3) (S DIFF (aa UNION c0 UNION inside c0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `u = (ww:real^3->bool) DIFF
                  (rr UNION IMAGE (fs:real^2->real^3) (S DIFF (aa UNION c0 UNION inside c0)))` THEN
  SUBGOAL_THEN `open (u:real^3->bool) /\ u SUBSET ww /\ DISJOINT u rr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`] MOI_S3L9_WW_OPEN) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ea SUBSET (u:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fs:real^2->real^3`; `gs:real^3->real^2`;
                   `S DIFF (aa UNION c0 UNION inside c0):real^2->bool`; `c0:real^2->bool`;
                   `S:real^2->bool`] MOI_S3L9_IMAGE_DISJOINT_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `c0 UNION inside c0 SUBSET (S:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
    UNDISCH_TAC `ea INTER d = a2:real^3->bool` THEN
    UNDISCH_TAC `DISJOINT (rr:real^3->bool) ea` THEN
    UNDISCH_TAC `ea SUBSET (ww:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER u SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN EXPAND_TAC "u" THEN
    UNDISCH_TAC `ea SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `(a2:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER pcs SUBSET rr UNION (ea:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fs:real^2->real^3`; `gs:real^3->real^2`;
                   `S DIFF (c0 UNION inside c0):real^2->bool`;
                   `c0 UNION inside c0:real^2->bool`;
                   `S:real^2->bool`] MOI_S3L9_IMAGE_DISJOINT_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `c0 UNION inside c0 SUBSET (S:real^2->bool)` THEN SET_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (S DIFF inside c0) SUBSET
                  IMAGE fs (S DIFF (c0 UNION inside c0)) UNION a2` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (S DIFF (c0 UNION inside c0)) SUBSET d`
    ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a2:real^3->bool) SUBSET ea` ASSUME_TAC THENL
     [UNDISCH_TAC `ea INTER d = a2:real^3->bool` THEN SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ds" THEN
    MATCH_MP_TAC(SET_RULE
     `!X Y Z a2 ea d pcs rr:real^3->bool.
        a2 SUBSET ea /\ X SUBSET Y UNION a2 /\ Y SUBSET d /\ DISJOINT Y Z /\
        d INTER pcs SUBSET rr UNION Z
        ==> (X UNION ea) INTER pcs SUBSET rr UNION ea`) THEN
    EXISTS_TAC `IMAGE (fs:real^2->real^3) (S DIFF (c0 UNION inside c0))` THEN
    EXISTS_TAC `IMAGE (fs:real^2->real^3) (c0 UNION inside c0)` THEN
    EXISTS_TAC `a2:real^3->bool` THEN EXISTS_TAC `d:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (ea:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `ea:real^3->bool`; `a2:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER u INTER pcs SUBSET (ea:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ds INTER pcs SUBSET rr UNION (ea:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) rr` THEN SET_TAC[];
    ALL_TAC] THEN
  (* S10: the push *)
  UNDISCH_TAC `moi_s3l9i_push` THEN REWRITE_TAC[moi_s3l9i_push] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `v1:real^3`; `ds:real^3->bool`; `u:real^3->bool`;
    `ea:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->bool` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = pcs`])) THEN
  (* S11: the new family *)
  SUBGOAL_THEN `(ds DIFF u) INTER pcs = rr:real^3->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `ds INTER pcs SUBSET rr UNION (ea:real^3->bool)` THEN
      UNDISCH_TAC `ea SUBSET (u:real^3->bool)` THEN SET_TAC[];
      SUBGOAL_THEN `rr SUBSET IMAGE (fs:real^2->real^3) (S DIFF inside c0)` MP_TAC THENL
       [UNDISCH_TAC `DISJOINT rr (IMAGE (fs:real^2->real^3) (c0 UNION inside c0))` THEN
        UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
        UNDISCH_TAC `(rr:real^3->bool) SUBSET d` THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "ds" THEN
      UNDISCH_TAC `(rr:real^3->bool) SUBSET pcs` THEN
      UNDISCH_TAC `DISJOINT (u:real^3->bool) rr` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a2:real^3->bool) IN cs')` ASSUME_TAC THENL
   [EXPAND_TAC "cs'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) c0 = a2` THEN
    UNDISCH_TAC `~(a2:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s39_family l e x d' cs'` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s39_family l e x d cs` THEN REWRITE_TAC[moi_s39_family] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(cs':(real^3->bool)->bool) SUBSET cs` THEN
      UNDISCH_TAC `(a:real^3->bool) IN cs'` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d':real^3->bool`; `cs':(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[PSUBSET] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((a2:real^3->bool) IN cs')` THEN ASM_REWRITE_TAC[]);;


(* A loop theorem disk misses the rims of the pseudo-cells.                   *)

let MOI_S3L9_LTD_RIM = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d u v.
     moi_s33_hd t l h e c /\ moi_s33_ltd t l h x d /\ ~(u = v) /\ segment[u,v] IN l
     ==> d INTER moi_s33_rim t l h u v = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_HD_PC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `e(segment[u:real^3,v]) INTER frontier (IMAGE (h:real^3->real^3)
                (derived_nbhd t l)) = moi_s33_rim t l h u v` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `d SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

(* Subsets of an open pseudo-cell missing its centre lie in W.               *)

let MOI_S3L9_EDGE_WW = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) u v s.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l /\
     s SUBSET e(segment[u,v]) DIFF moi_s33_rim t l h u v /\ ~(h(midpoint(u,v)) IN s)
     ==> s SUBSET moi_s33_ww t l h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_HD_PC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`] MOI_S3L9_EDGE_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`] MOI_S3L9_PIECE_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_HD_TUBE) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_TUBE_BASIC) THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
                IMAGE h (derived_nbhd t l) DIFF interior (IMAGE h (derived_nbhd t l))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[moi_s33_ww] THEN
  UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
               IMAGE h (derived_nbhd t l) DIFF interior (IMAGE h (derived_nbhd t l))` THEN
  UNDISCH_TAC `e(segment[u:real^3,v]) INTER frontier (IMAGE (h:real^3->real^3)
                (derived_nbhd t l)) = moi_s33_rim t l h u v` THEN
  UNDISCH_TAC `e(segment[u:real^3,v]) INTER IMAGE (h:real^3->real^3) (UNIONS l) =
               {h(midpoint(u,v))}` THEN
  UNDISCH_TAC `e(segment[u:real^3,v]) SUBSET (c:real^3->real^3->bool) u` THEN
  UNDISCH_TAC `(c:real^3->real^3->bool) u SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN
  UNDISCH_TAC `(s:real^3->bool) SUBSET e(segment[u:real^3,v]) DIFF moi_s33_rim t l h u v` THEN
  UNDISCH_TAC `~((h:real^3->real^3)(midpoint(u,v)) IN s)` THEN
  SET_TAC[]);;

(* The circle step: a circle in the family can be removed.                    *)

let MOI_S3L9_CIRCLE_STEP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs.
     moi_s3l9i_l8 /\ moi_s3l9i_drec /\ moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\
     (?a0. a0 IN cs /\ pl_sphere 1 a0 /\ DISJOINT a0 (frontier (UNIONS x)))
     ==> ?d' cs'. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs' /\ cs' PSUBSET cs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_PLANAR_MODEL o check (fun th ->
    (let c,args = strip_comb(concl th) in is_const c && fst(dest_const c) = "pl_cell_with_boundary" &&
     length args = 3 && el 1 args = `d:real^3->bool`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `fs:real^2->real^3`
    (X_CHOOSE_THEN `gs:real^3->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `S:real^2->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`]
    MOI_S3L9_CIRCLE_INNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `a0:real^3->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a1:real^3->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `cs:(real^3->bool)->bool`; `S:real^2->bool`; `fs:real^2->real^3`;
                 `gs:real^3->real^2`; `a1:real^3->bool`] MOI_S3L9_CIRCLE_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `dj = IMAGE (fs:real^2->real^3)
                 (IMAGE (gs:real^3->real^2) a1 UNION inside (IMAGE gs a1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^3` (X_CHOOSE_THEN `w:real^3`
      STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `v:real^3`; `w:real^3`]
    MOI_S3L9_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_THEN `psi:real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`] MOI_S3L9_HD_PC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(a1:real^3->bool) SUBSET e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                   `v:real^3`; `w:real^3`] MOI_S3L9_LTD_RIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a1:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    UNDISCH_TAC `d INTER moi_s33_rim t l h v w = {}` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET d` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `dj:real^3->bool`; `a1:real^3->bool`;
                 `v:real^3`; `w:real^3`; `phi:real^3->real^2`; `psi:real^2->real^3`]
    MOI_S3L9_CIRCLE_L8) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dj SUBSET (d:real^3->bool)` THEN
    UNDISCH_TAC `d SUBSET moi_s33_ww t l h` THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `cs:(real^3->bool)->bool`; `a1:real^3->bool`; `v:real^3`; `w:real^3`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`] MOI_S3L9_CIRCLE_EINNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] MOI_S3L9_X_FACTS) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a2:real^3->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`e(segment[v:real^3,w]):real^3->bool`; `moi_s33_rim t l h v w`;
                 `(h:real^3->real^3)(midpoint(v,w))`; `phi:real^3->real^2`;
                 `psi:real^2->real^3`; `a2:real^3->bool`] MOI_S3L9_CELL_PL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`e(segment[v:real^3,w]):real^3->bool`; `moi_s33_rim t l h v w`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`; `a2:real^3->bool`]
    MOI_S3L9_CELL_DISK) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE]; STRIP_TAC] THEN
  ABBREV_TAC `ea = IMAGE (psi:real^2->real^3)
                 (IMAGE (phi:real^3->real^2) a2 UNION inside (IMAGE phi a2))` THEN
  SUBGOAL_THEN `ea SUBSET moi_s33_ww t l h` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_EDGE_WW THEN
    MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                          `v:real^3`; `w:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3L9_CIRCLE_SWAP THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->real^3->bool`; `d:real^3->bool`; `a2:real^3->bool`;
                        `ea:real^3->bool`; `v:real^3`; `w:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ea SUBSET e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w` THEN
  UNDISCH_TAC `(a2:real^3->bool) SUBSET e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 9. Statement terms of the four pieces of the arc step, proved       *)
(* below: H1 THETA_NULL, H2 MINIMAL_DISK, H3 ARC_COLLAR (uses H2) and H4    *)
(* ARC_IN_CIRCLE.  They use the HOL library and pc_moi_sch3_free.ml,        *)
(* pc_moi_pl2.ml.                                                           *)
(* ------------------------------------------------------------------------- *)


let MOI_S3L9_THETA_NULL_TERM =
 `!(g1:real^1->real^N) g2 g3 (y:real^N->bool).
    arc g1 /\ arc g2 /\ arc g3 /\
    pathstart g2 = pathstart g1 /\ pathfinish g2 = pathfinish g1 /\
    pathstart g3 = pathstart g1 /\ pathfinish g3 = pathfinish g1 /\
    path_image g1 INTER path_image g2 = {pathstart g1,pathfinish g1} /\
    path_image g1 INTER path_image g3 = {pathstart g1,pathfinish g1} /\
    path_image g2 INTER path_image g3 = {pathstart g1,pathfinish g1} /\
    path_image g1 UNION path_image g2 UNION path_image g3 SUBSET y /\
    (?a. homotopic_with (\q. T)
           (subtopology euclidean (path_image g1 UNION path_image g3),
            subtopology euclidean y) (\z. z) (\z. a)) /\
    (?a. homotopic_with (\q. T)
           (subtopology euclidean (path_image g2 UNION path_image g3),
            subtopology euclidean y) (\z. z) (\z. a))
    ==> ?a. homotopic_with (\q. T)
              (subtopology euclidean (path_image g1 UNION path_image g2),
               subtopology euclidean y) (\z. z) (\z. a)`;;

let MOI_S3L9_MINIMAL_DISK_TERM =
 `!(gam:real^2->bool) p (bs:(real^2->bool)->bool).
    gam homeomorphic sphere(vec 0:real^2,&1) /\ gam SUBSET ball(vec 0,&1) /\
    p IN inside gam /\ FINITE bs /\ ~(bs = {}) /\ pairwise DISJOINT bs /\
    (!b. b IN bs
         ==> ?g:real^1->real^2. arc g /\ path_image g = b /\
                                b INTER gam = {pathstart g,pathfinish g}) /\
    (!b. b IN bs ==> b SUBSET ball(vec 0,&1) /\ ~(p IN b)) /\
    ((!b. b IN bs ==> b DIFF gam SUBSET inside gam) \/
     (!b. b IN bs ==> b DIFF gam SUBSET outside gam))
    ==> ?b g:real^1->real^2.
          b IN bs /\ arc g /\ path_image g SUBSET gam /\
          {pathstart g,pathfinish g} = b INTER gam /\
          ~(p IN (b UNION path_image g) UNION inside(b UNION path_image g)) /\
          (b UNION path_image g) UNION inside(b UNION path_image g) SUBSET
            ball(vec 0,&1) /\
          ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam =
            path_image g /\
          (!b'. b' IN bs /\ ~(b' = b)
                ==> DISJOINT b' ((b UNION path_image g) UNION
                                 inside(b UNION path_image g)))`;;

if not (type_of MOI_S3L9_THETA_NULL_TERM = bool_ty && frees MOI_S3L9_THETA_NULL_TERM = [] &&
        type_of MOI_S3L9_MINIMAL_DISK_TERM = bool_ty && frees MOI_S3L9_MINIMAL_DISK_TERM = [])
then failwith "helper terms not closed booleans";;


let MOI_S3L9_ARC_COLLAR_TERM =
 `!(c:real^2->bool) (b:real^1->real^2) (k:real^2->bool).
    c homeomorphic sphere(vec 0:real^2,&1) /\ arc b /\ path_image b SUBSET c /\
    closed k /\ DISJOINT (path_image b) k
    ==> ?a w. connected a /\ a SUBSET (c UNION inside c) DIFF path_image b /\
              DISJOINT a k /\ path_image b SUBSET closure a /\
              open w /\ path_image b SUBSET w /\
              w INTER (c UNION inside c) SUBSET a UNION path_image b`;;

let MOI_S3L9_ARC_IN_CIRCLE_TERM =
 `!(a1:real^1->real^N) a2 g.
    arc a1 /\ arc a2 /\ arc g /\
    pathstart a2 = pathstart a1 /\ pathfinish a2 = pathfinish a1 /\
    path_image a1 INTER path_image a2 = {pathstart a1,pathfinish a1} /\
    path_image g SUBSET path_image a1 UNION path_image a2 /\
    {pathstart g,pathfinish g} = {pathstart a1,pathfinish a1}
    ==> path_image g = path_image a1 \/ path_image g = path_image a2`;;

if not (type_of MOI_S3L9_ARC_COLLAR_TERM = bool_ty && frees MOI_S3L9_ARC_COLLAR_TERM = [] &&
        type_of MOI_S3L9_ARC_IN_CIRCLE_TERM = bool_ty && frees MOI_S3L9_ARC_IN_CIRCLE_TERM = [])
then failwith "helper terms 2 not closed booleans";;


(* ------------------------------------------------------------------------- *)
(* H1: MOI_S3L9_THETA_NULL, the statement MOI_S3L9_THETA_NULL_TERM above;   *)
(* only the HOL Multivariate library is used.  Route through loops: a null  *)
(* circle inclusion makes the loop g1 ++ reversepath g3 null, hence g1 and  *)
(* g3 homotopic as paths (HOMOTOPIC_PATHS_LOOP_PARTS); likewise g2 and g3;  *)
(* so g1 ++ reversepath g2 is a null loop; it is a simple closed path, and  *)
(* the circle map p o (lift o Arg / 2 pi) of                                *)
(* HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS is then a homeomorphism of the  *)
(* unit circle onto its image, which carries the null-homotopy to the       *)
(* inclusion.                                                               *)
(* ------------------------------------------------------------------------- *)

(* A null circle inclusion gives a null loop. *)

let MOI_S3L9TH_LOOP_NULL = prove
 (`!(L:real^1->real^N) y a.
     path L /\ pathfinish L = pathstart L /\
     homotopic_with (\q. T)
       (subtopology euclidean (path_image L),subtopology euclidean y) (\z. z) (\z. a)
     ==> homotopic_loops y L (linepath(a,a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_loops; LINEPATH_REFL] THEN
  MP_TAC(ISPECL [`\f:real^1->real^N. pathfinish f = pathstart f`; `\z:real^N. z`;
                 `\z:real^N. (a:real^N)`; `L:real^1->real^N`;
                 `interval[vec 0:real^1,vec 1]`; `path_image(L:real^1->real^N)`;
                 `y:real^N->bool`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\q:real^N->real^N. T` THEN ASM_REWRITE_TAC[pathstart; pathfinish] THEN
    UNDISCH_TAC `pathfinish (L:real^1->real^N) = pathstart L` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN SIMP_TAC[];
    UNDISCH_TAC `path (L:real^1->real^N)` THEN REWRITE_TAC[path];
    REWRITE_TAC[path_image; SUBSET_REFL]]);;

(* The circle parameter lift(Arg z / 2 pi) lies in [0,1) and determines z  *)
(* on the unit circle.                                                       *)

let MOI_S3L9TH_ARG_PARAM = prove
 (`!z. lift(Arg z / (&2 * pi)) IN interval[vec 0,vec 1] /\
       ~(lift(Arg z / (&2 * pi)) = vec 1)`,
  GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3L9TH_ARG_INJ = prove
 (`!z w. norm z = &1 /\ norm w = &1 /\ Arg z = Arg w ==> z = w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `z:complex` ARG))) THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `w:complex` ARG))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The image of the circle map of a loop is the image of the loop. *)

let MOI_S3L9TH_CIRCLE_IMAGE = prove
 (`!L:real^1->real^N.
     pathfinish L = pathstart L
     ==> IMAGE (\z. L(lift(Arg z / (&2 * pi)))) (sphere(vec 0,&1)) = path_image L`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; path_image; IN_SPHERE_0] THEN
  X_GEN_TAC `p:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `lift(Arg z / (&2 * pi))` THEN
    ASM_REWRITE_TAC[MOI_S3L9TH_ARG_PARAM];
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `t = vec 1:real^1` THENL
     [EXISTS_TAC `Cx(&1)` THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; ARG_NUM; real_div; REAL_MUL_LZERO;
                  LIFT_NUM] THEN
      UNDISCH_TAC `pathfinish (L:real^1->real^N) = pathstart L` THEN
      REWRITE_TAC[pathstart; pathfinish] THEN ASM_MESON_TAC[];
      EXISTS_TAC `cexp(ii * Cx(&2 * pi * drop t))` THEN
      REWRITE_TAC[NORM_CEXP_II] THEN
      SUBGOAL_THEN `&0 <= drop t /\ drop t < &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
        UNDISCH_TAC `~(t = vec 1:real^1)` THEN
        REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `Arg(cexp(ii * Cx(&2 * pi * drop t))) = &2 * pi * drop t`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `ii * Cx(&2 * pi * drop(t:real^1))` ARG_CEXP) THEN
        REWRITE_TAC[IM_MUL_II; RE_CX] THEN DISCH_THEN MATCH_MP_TAC THEN
        MP_TAC PI_POS THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          SUBGOAL_THEN `&0 < pi * (&1 - drop(t:real^1))` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `lift((&2 * pi * drop t) / (&2 * pi)) = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN MP_TAC PI_POS THEN CONV_TAC REAL_FIELD]]);;

(* A null simple closed loop gives a null circle inclusion. *)

let MOI_S3L9TH_CIRCLE_NULL = prove
 (`!(L:real^1->real^N) y a.
     simple_path L /\ pathfinish L = pathstart L /\
     homotopic_loops y L (linepath(a,a))
     ==> homotopic_with (\q. T)
           (subtopology euclidean (path_image L),subtopology euclidean y)
           (\z. z) (\z. a)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
  REWRITE_TAC[LINEPATH_REFL; o_DEF] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  MP_TAC(ISPECL [`sphere(vec 0:complex,&1)`;
                 `\z:complex. (L:real^1->real^N)(lift(Arg z / (&2 * pi)))`;
                 `path_image(L:real^1->real^N)`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_SPHERE; MOI_S3L9TH_CIRCLE_IMAGE] THEN
    REWRITE_TAC[IN_SPHERE_0] THEN
    MAP_EVERY X_GEN_TAC [`z:complex`; `w:complex`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3L9TH_ARG_INJ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simple_path(L:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift(Arg z / (&2 * pi))`; `lift(Arg w / (&2 * pi))`] o
               CONJUNCT2) THEN
    ASM_REWRITE_TAC[MOI_S3L9TH_ARG_PARAM; LIFT_EQ] THEN
    SUBGOAL_THEN `&0 < pi` MP_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->complex` STRIP_ASSUME_TAC o
               REWRITE_RULE[homeomorphism])] THEN
  MP_TAC(ISPECL [`\h:real^N->real^N. T`;
                 `\z:complex. (L:real^1->real^N)(lift(Arg z / (&2 * pi)))`;
                 `\z:complex. (a:real^N)`; `G:real^N->complex`;
                 `path_image(L:real^1->real^N)`; `sphere(vec 0:complex,&1)`;
                 `y:real^N->bool`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`\q:real^N->real^N. T`; `subtopology euclidean (path_image(L:real^1->real^N))`;
    `subtopology euclidean (y:real^N->bool)`;
    `(\z:complex. (L:real^1->real^N)(lift(Arg z / (&2 * pi)))) o (G:real^N->complex)`;
    `(\z:complex. (a:real^N)) o (G:real^N->complex)`;
    `\z:real^N. z`; `\z:real^N. (a:real^N)`] HOMOTOPIC_WITH_EQ) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN ASM_SIMP_TAC[]);;

(* The theta lemma. *)

let MOI_S3L9_THETA_NULL = prove
 (MOI_S3L9_THETA_NULL_TERM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (g1:real^1->real^N) /\ path (g2:real^1->real^N) /\
                path (g3:real^1->real^N)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ARC_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image (g1:real^1->real^N) SUBSET y /\ path_image (g2:real^1->real^N) SUBSET y /\
                path_image (g3:real^1->real^N) SUBSET y`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_paths y (g1:real^1->real^N) g3` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_LOOP_PARTS THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3L9TH_LOOP_NULL THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATH_IMAGE_JOIN;
                 PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_paths y (g2:real^1->real^N) g3` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_LOOP_PARTS THEN EXISTS_TAC `a':real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3L9TH_LOOP_NULL THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; PATH_IMAGE_JOIN;
                 PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_paths y (g1:real^1->real^N) g2` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC `g3:real^1->real^N` THEN
    ASM_MESON_TAC[HOMOTOPIC_PATHS_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths y ((g1:real^1->real^N) ++ reversepath g2)
                      (linepath(pathstart g1,pathstart g1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(g2:real^1->real^N) ++ reversepath g2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                      PATHSTART_REVERSEPATH];
      MP_TAC(ISPECL [`y:real^N->bool`; `g2:real^1->real^N`] HOMOTOPIC_PATHS_RINV) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `pathstart(g1:real^1->real^N)` THEN
  SUBGOAL_THEN
   `path_image (g1:real^1->real^N) UNION path_image g2 =
    path_image (g1 ++ reversepath g2)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_REVERSEPATH; PATH_IMAGE_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3L9TH_CIRCLE_NULL THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 PATH_IMAGE_REVERSEPATH; SUBSET_REFL];
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH;
                    PATHFINISH_LINEPATH]]);;

(* ========================================================================= *)
(* H2 MINIMAL_DISK (Lemma 9, arc step): the statement                        *)
(* MOI_S3L9_MINIMAL_DISK_TERM of Part 9, restated below.                     *)
(*                                                                           *)
(* Route.  For an arc b with ends u, v on gam, split gam at u, v into two    *)
(* arcs (EXISTS_DOUBLE_ARC_EXPLICIT); the theta of b and the two arcs gives  *)
(* a disk D(b,g) = (b UNION g) UNION inside(b UNION g) missing p with        *)
(* D INTER gam = g (SPLIT_INSIDE_SIMPLE_CLOSED_CURVE, THETA_CURVE_INSIDE_    *)
(* CASES).  Take a valid pair (b,g) with the fewest arcs of bs inside D; an  *)
(* arc b' meeting D has its open part in inside or outside of b UNION g, the *)
(* outside option is refuted by the theta decomposition with the            *)
(* complementary arc of gam, so b' lies in D with its ends on g minus b, and *)
(* the sub-arc of g between them bounds a valid disk inside D missing b,    *)
(* with fewer arcs inside: a contradiction.                                  *)
(* Uses only the HOL library and MOI_SFR_JORDAN_REGION, MOI_SFR_ARC_DENSE    *)
(* of pc_moi_sch3_free.ml (in the closure of pc_moi_s33_l9).                 *)
(* ========================================================================= *)

type_invention_error := true;;

let MOI_S3L9_MINIMAL_DISK_TERM =
 `!(gam:real^2->bool) p (bs:(real^2->bool)->bool).
    gam homeomorphic sphere(vec 0:real^2,&1) /\ gam SUBSET ball(vec 0,&1) /\
    p IN inside gam /\ FINITE bs /\ ~(bs = {}) /\ pairwise DISJOINT bs /\
    (!b. b IN bs
         ==> ?g:real^1->real^2. arc g /\ path_image g = b /\
                                b INTER gam = {pathstart g,pathfinish g}) /\
    (!b. b IN bs ==> b SUBSET ball(vec 0,&1) /\ ~(p IN b)) /\
    ((!b. b IN bs ==> b DIFF gam SUBSET inside gam) \/
     (!b. b IN bs ==> b DIFF gam SUBSET outside gam))
    ==> ?b g:real^1->real^2.
          b IN bs /\ arc g /\ path_image g SUBSET gam /\
          {pathstart g,pathfinish g} = b INTER gam /\
          ~(p IN (b UNION path_image g) UNION inside(b UNION path_image g)) /\
          (b UNION path_image g) UNION inside(b UNION path_image g) SUBSET
            ball(vec 0,&1) /\
          ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam =
            path_image g /\
          (!b'. b' IN bs /\ ~(b' = b)
                ==> DISJOINT b' ((b UNION path_image g) UNION
                                 inside(b UNION path_image g)))`;;

(* ------------------------------------------------------------------------- *)
(* MINIMAL_DISK, part 1: Jordan curves from two arcs, splitting gam at two   *)
(* points, the arcs of gam between two points, and the theta cases.         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9MD_LOOP = prove
 (`!g h:real^1->real^2.
     arc g /\ arc h /\ pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
     path_image g INTER path_image h = {pathstart g,pathfinish g}
     ==> simple_path(g ++ reversepath h) /\
         pathfinish(g ++ reversepath h) = pathstart(g ++ reversepath h) /\
         path_image(g ++ reversepath h) = path_image g UNION path_image h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathfinish g = pathstart(reversepath h:real^1->real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_REVERSEPATH]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHFINISH_REVERSEPATH] THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `reversepath h:real^1->real^2`]
                SIMPLE_PATH_JOIN_LOOP_EQ) THEN
  ASM_REWRITE_TAC[PATHFINISH_REVERSEPATH; ARC_REVERSEPATH_EQ; PATH_IMAGE_REVERSEPATH] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; SUBSET_REFL]);;

let MOI_S3L9MD_JORDAN2 = prove
 (`!g h:real^1->real^2.
     arc g /\ arc h /\ {pathstart h,pathfinish h} = {pathstart g,pathfinish g} /\
     path_image g INTER path_image h = {pathstart g,pathfinish g}
     ==> ?c. simple_path c /\ pathfinish c = pathstart c /\
             path_image c = path_image g UNION path_image h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(pathstart h = pathstart g /\ pathfinish h = pathfinish (g:real^1->real^2)) \/
    (pathstart(reversepath h) = pathstart g /\
     pathfinish(reversepath h) = pathfinish (g:real^1->real^2))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MP_TAC(ISPEC `g:real^1->real^2` ARC_DISTINCT_ENDS) THEN
    MP_TAC(ISPEC `h:real^1->real^2` ARC_DISTINCT_ENDS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{pathstart h,pathfinish h} = {pathstart g:real^2,pathfinish g}` THEN
    SET_TAC[];
    EXISTS_TAC `(g:real^1->real^2) ++ reversepath h` THEN
    MATCH_MP_TAC MOI_S3L9MD_LOOP THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `(g:real^1->real^2) ++ reversepath(reversepath h)` THEN
    MP_TAC(ISPECL [`g:real^1->real^2`; `reversepath h:real^1->real^2`] MOI_S3L9MD_LOOP) THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATH_IMAGE_REVERSEPATH]]);;

let MOI_S3L9MD_SPLIT2 = prove
 (`!(gam:real^2->bool) u v.
     gam homeomorphic sphere(vec 0:real^2,&1) /\ u IN gam /\ v IN gam /\ ~(u = v)
     ==> ?g1 g2:real^1->real^2.
           arc g1 /\ arc g2 /\ pathstart g1 = u /\ pathfinish g1 = v /\
           pathstart g2 = u /\ pathfinish g2 = v /\
           path_image g1 INTER path_image g2 = {u,v} /\
           path_image g1 UNION path_image g2 = gam`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`gam:real^2->bool`; `vec 0:real^2`; `&1`]
                HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?a a':real^1. a IN interval[vec 0,vec 1] /\ a' IN interval[vec 0,vec 1] /\
                              (c:real^1->real^2) a = u /\ c a' = v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^2) IN gam` THEN UNDISCH_TAC `(v:real^2) IN gam` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `gam:real^2->bool`)) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop a <= drop a' \/ drop a' <= drop a`) THENL
   [MP_TAC(ISPECL [`c:real^1->real^2`; `a:real^1`; `a':real^1`]
                  EXISTS_DOUBLE_ARC_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` (X_CHOOSE_THEN `d:real^1->real^2`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`g1:real^1->real^2`; `reversepath d:real^1->real^2`] THEN
    REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                PATH_IMAGE_REVERSEPATH] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`c:real^1->real^2`; `a':real^1`; `a:real^1`]
                  EXISTS_DOUBLE_ARC_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` (X_CHOOSE_THEN `d:real^1->real^2`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`reversepath g1:real^1->real^2`; `d:real^1->real^2`] THEN
    REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                PATH_IMAGE_REVERSEPATH] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `path_image g1 INTER path_image d = {v:real^2,u}` THEN SET_TAC[]]);;

let MOI_S3L9MD_CLASSIFY = prove
 (`!g1 g2 g:real^1->real^2 u v.
     arc g1 /\ arc g2 /\ arc g /\
     pathstart g1 = u /\ pathfinish g1 = v /\ pathstart g2 = u /\ pathfinish g2 = v /\
     path_image g1 INTER path_image g2 = {u,v} /\
     path_image g SUBSET path_image g1 UNION path_image g2 /\
     {pathstart g,pathfinish g} = {u,v}
     ==> path_image g = path_image g1 \/ path_image g = path_image g2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `path_image g:real^2->bool`]
                CONNECTED_SUBSET_ARC_PAIR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_ARC_IMAGE] THEN
    MP_TAC(ISPEC `g:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `{pathstart g,pathfinish g} = {u:real^2,v}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC ARC_IMAGE_UNIQUE THEN ASM_SIMP_TAC[ARC_IMP_PATH]);;

(* ------------------------------------------------------------------------- *)
(* MINIMAL_DISK, part 2: the theta cases (three arcs g1, g2, gb from u to v *)
(* meeting only at u and v; gb on the inside or on the outside of the cycle *)
(* of g1 and g2) and the facts of a disk from its frontier pieces.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9MD_THETA_IN = prove
 (`!g1 g2 gb:real^1->real^2 u v.
     arc g1 /\ arc g2 /\ arc gb /\
     pathstart g1 = u /\ pathfinish g1 = v /\ pathstart g2 = u /\ pathfinish g2 = v /\
     pathstart gb = u /\ pathfinish gb = v /\
     path_image g1 INTER path_image g2 = {u,v} /\
     path_image gb INTER path_image g1 = {u,v} /\
     path_image gb INTER path_image g2 = {u,v} /\
     path_image gb DIFF {u,v} SUBSET inside(path_image g1 UNION path_image g2)
     ==> inside(path_image gb UNION path_image g1) INTER
         inside(path_image gb UNION path_image g2) = {} /\
         inside(path_image g1 UNION path_image g2) =
         inside(path_image gb UNION path_image g1) UNION
         inside(path_image gb UNION path_image g2) UNION
         (path_image gb DIFF {u,v})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image g1 INTER path_image gb = {u:real^2,v} /\
    path_image g2 INTER path_image gb = {u:real^2,v} /\
    ~(path_image gb DIFF {u:real^2,v} = {}) /\ ~(u:real^2 = v) /\
    path_image g1 UNION path_image gb = path_image gb UNION path_image g1 /\
    path_image g2 UNION path_image gb = path_image gb UNION path_image g2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image gb INTER path_image g1 = {u:real^2,v}` THEN SET_TAC[];
      UNDISCH_TAC `path_image gb INTER path_image g2 = {u:real^2,v}` THEN SET_TAC[];
      MP_TAC(ISPEC `gb:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      ASM_MESON_TAC[ARC_DISTINCT_ENDS];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                 `u:real^2`; `v:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
    UNDISCH_TAC `path_image gb DIFF {u:real^2,v} SUBSET
                 inside(path_image g1 UNION path_image g2)` THEN
    UNDISCH_TAC `~(path_image gb DIFF {u:real^2,v} = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S3L9MD_THETA_OUT = prove
 (`!g1 g2 gb:real^1->real^2 u v.
     arc g1 /\ arc g2 /\ arc gb /\
     pathstart g1 = u /\ pathfinish g1 = v /\ pathstart g2 = u /\ pathfinish g2 = v /\
     pathstart gb = u /\ pathfinish gb = v /\
     path_image g1 INTER path_image g2 = {u,v} /\
     path_image gb INTER path_image g1 = {u,v} /\
     path_image gb INTER path_image g2 = {u,v} /\
     path_image gb DIFF {u,v} SUBSET outside(path_image g1 UNION path_image g2)
     ==> (path_image g2 DIFF {u,v} SUBSET inside(path_image gb UNION path_image g1) /\
          inside(path_image gb UNION path_image g2) INTER
            inside(path_image g1 UNION path_image g2) = {} /\
          inside(path_image gb UNION path_image g1) =
            inside(path_image gb UNION path_image g2) UNION
            inside(path_image g1 UNION path_image g2) UNION
            (path_image g2 DIFF {u,v})) \/
         (path_image g1 DIFF {u,v} SUBSET inside(path_image gb UNION path_image g2) /\
          inside(path_image gb UNION path_image g1) INTER
            inside(path_image g1 UNION path_image g2) = {} /\
          inside(path_image gb UNION path_image g2) =
            inside(path_image gb UNION path_image g1) UNION
            inside(path_image g1 UNION path_image g2) UNION
            (path_image g1 DIFF {u,v}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image g2 INTER path_image g1 = {u:real^2,v} /\
    path_image g1 INTER path_image gb = {u:real^2,v} /\
    path_image g2 INTER path_image gb = {u:real^2,v} /\
    ~(path_image g1 DIFF {u:real^2,v} = {}) /\
    ~(path_image g2 DIFF {u:real^2,v} = {}) /\
    ~(path_image gb DIFF {u:real^2,v} = {}) /\ ~(u:real^2 = v) /\
    path_image g2 UNION path_image gb = path_image gb UNION path_image g2 /\
    path_image g2 UNION path_image g1 = path_image g1 UNION path_image g2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image g1 INTER path_image g2 = {u:real^2,v}` THEN SET_TAC[];
      UNDISCH_TAC `path_image gb INTER path_image g1 = {u:real^2,v}` THEN SET_TAC[];
      UNDISCH_TAC `path_image gb INTER path_image g2 = {u:real^2,v}` THEN SET_TAC[];
      MP_TAC(ISPEC `g1:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MP_TAC(ISPEC `g2:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MP_TAC(ISPEC `gb:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      ASM_MESON_TAC[ARC_DISTINCT_ENDS];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                 `u:real^2`; `v:real^2`] THETA_CURVE_INSIDE_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [(* the first arc lies inside the cycle of b and the second *)
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`gb:real^1->real^2`; `g2:real^1->real^2`; `g1:real^1->real^2`;
                   `u:real^2`; `v:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
      UNDISCH_TAC `path_image g1 DIFF {u:real^2,v} SUBSET
                   inside(path_image gb UNION path_image g2)` THEN
      UNDISCH_TAC `~(path_image g1 DIFF {u:real^2,v} = {})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image g1 DIFF {u:real^2,v} SUBSET
                 inside(path_image gb UNION path_image g2)` THEN
    SET_TAC[];
    (* the second arc lies inside the cycle of b and the first *)
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`gb:real^1->real^2`; `g1:real^1->real^2`; `g2:real^1->real^2`;
                   `u:real^2`; `v:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
      UNDISCH_TAC `path_image g2 DIFF {u:real^2,v} SUBSET
                   inside(path_image gb UNION path_image g1)` THEN
      UNDISCH_TAC `~(path_image g2 DIFF {u:real^2,v} = {})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `path_image g2 DIFF {u:real^2,v} SUBSET
                 inside(path_image gb UNION path_image g1)` THEN
    SET_TAC[];
    (* b inside the cycle of the two arcs: impossible, it is outside *)
    MP_TAC(ISPEC `path_image g1 UNION path_image (g2:real^1->real^2)` INSIDE_INTER_OUTSIDE) THEN
    UNDISCH_TAC `path_image gb DIFF {u:real^2,v} SUBSET
                 outside(path_image g1 UNION path_image g2)` THEN
    UNDISCH_TAC `path_image gb DIFF {u:real^2,v} SUBSET
                 inside(path_image g1 UNION path_image g2)` THEN
    UNDISCH_TAC `~(path_image gb DIFF {u:real^2,v} = {})` THEN
    SET_TAC[]]);;

let MOI_S3L9MD_VALID_OF = prove
 (`!(gam:real^2->bool) p b (g:real^1->real^2).
     gam SUBSET ball(vec 0,&1) /\ p IN inside gam /\ b SUBSET ball(vec 0,&1) /\ ~(p IN b) /\
     arc g /\ path_image g SUBSET gam /\ {pathstart g,pathfinish g} = b INTER gam /\
     ~(p IN inside(b UNION path_image g)) /\ inside(b UNION path_image g) INTER gam = {}
     ==> arc g /\ path_image g SUBSET gam /\ {pathstart g,pathfinish g} = b INTER gam /\
         ~(p IN (b UNION path_image g) UNION inside(b UNION path_image g)) /\
         (b UNION path_image g) UNION inside(b UNION path_image g) SUBSET ball(vec 0,&1) /\
         ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam =
           path_image g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inside(b UNION path_image g) SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_BALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `gam:real^2->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `g:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
  MP_TAC(ISPEC `g:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MINIMAL_DISK, part 3: every arc b has a disk missing p (EXIST); for such *)
(* a disk, the complementary arc a of gam and the theta decomposition       *)
(* (COMPL).                                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9MD_EXIST = prove
 (`!(gam:real^2->bool) p (gb:real^1->real^2).
     gam homeomorphic sphere(vec 0:real^2,&1) /\ gam SUBSET ball(vec 0,&1) /\
     p IN inside gam /\
     arc gb /\ path_image gb INTER gam = {pathstart gb,pathfinish gb} /\
     path_image gb SUBSET ball(vec 0,&1) /\ ~(p IN path_image gb) /\
     (path_image gb DIFF gam SUBSET inside gam \/
      path_image gb DIFF gam SUBSET outside gam)
     ==> ?g. arc g /\ path_image g SUBSET gam /\
             {pathstart g,pathfinish g} = path_image gb INTER gam /\
             ~(p IN (path_image gb UNION path_image g) UNION
                    inside(path_image gb UNION path_image g)) /\
             (path_image gb UNION path_image g) UNION
               inside(path_image gb UNION path_image g) SUBSET ball(vec 0,&1) /\
             ((path_image gb UNION path_image g) UNION
              inside(path_image gb UNION path_image g)) INTER gam = path_image g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "side")))))))) THEN
  ABBREV_TAC `u = pathstart(gb:real^1->real^2)` THEN
  ABBREV_TAC `v = pathfinish(gb:real^1->real^2)` THEN
  MP_TAC(ISPECL [`gam:real^2->bool`; `u:real^2`; `v:real^2`] MOI_S3L9MD_SPLIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `gb:real^1->real^2` ARC_DISTINCT_ENDS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image gb INTER gam = {u:real^2,v}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` (X_CHOOSE_THEN `g2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `path_image gb INTER path_image g1 = {u:real^2,v} /\
    path_image gb INTER path_image g2 = {u:real^2,v} /\
    path_image gb DIFF {u:real^2,v} = path_image gb DIFF gam`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `g1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g2:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g2:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image gb INTER gam = {u:real^2,v}` THEN
    UNDISCH_TAC `path_image g1 UNION path_image g2 = (gam:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `gam:real^2->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `path_image gb UNION path_image (g1:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `path_image gb UNION path_image (g2:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
  REPEAT DISCH_TAC THEN
  REMOVE_THEN "side" DISJ_CASES_TAC THENL
   [(* b on the inside: p lies in exactly one of the two insides *)
    MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                   `u:real^2`; `v:real^2`] MOI_S3L9MD_THETA_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE
     [ASSUME `path_image g1 UNION path_image g2 = (gam:real^2->bool)`;
      ASSUME `path_image gb DIFF {u:real^2,v} = path_image gb DIFF gam`]) THEN
    SUBGOAL_THEN `(p:real^2) IN inside(path_image gb UNION path_image g1) \/
                  p IN inside(path_image gb UNION path_image g2)` MP_TAC THENL
     [UNDISCH_TAC `(p:real^2) IN inside gam` THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `inside(gam:real^2->bool)`)) THEN
      UNDISCH_TAC `~((p:real^2) IN path_image gb)` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `g2:real^1->real^2`; EXISTS_TAC `g1:real^1->real^2`] THEN
    MATCH_MP_TAC MOI_S3L9MD_VALID_OF THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* b on the outside: the arc not enclosed by the cycle with b *)
    MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                   `u:real^2`; `v:real^2`] MOI_S3L9MD_THETA_OUT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o REWRITE_RULE
     [ASSUME `path_image g1 UNION path_image g2 = (gam:real^2->bool)`]) THENL
     [EXISTS_TAC `g2:real^1->real^2`; EXISTS_TAC `g1:real^1->real^2`] THEN
    MATCH_MP_TAC MOI_S3L9MD_VALID_OF THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_S3L9MD_COMPL_CORE = prove
 (`!(gam:real^2->bool) (gb:real^1->real^2) g1 g2 u v.
     arc g1 /\ arc g2 /\ arc gb /\
     pathstart g1 = u /\ pathfinish g1 = v /\ pathstart g2 = u /\ pathfinish g2 = v /\
     pathstart gb = u /\ pathfinish gb = v /\
     path_image g1 INTER path_image g2 = {u,v} /\ path_image g1 UNION path_image g2 = gam /\
     path_image gb INTER gam = {u,v} /\
     ((path_image gb UNION path_image g1) UNION inside(path_image gb UNION path_image g1))
       INTER gam = path_image g1
     ==> (path_image gb DIFF gam SUBSET inside gam
          ==> inside(path_image gb UNION path_image g1) INTER
              inside(path_image gb UNION path_image g2) = {} /\
              inside gam = inside(path_image gb UNION path_image g1) UNION
                           inside(path_image gb UNION path_image g2) UNION
                           (path_image gb DIFF gam)) /\
         (path_image gb DIFF gam SUBSET outside gam
          ==> path_image g1 DIFF path_image gb SUBSET
                inside(path_image gb UNION path_image g2) /\
              inside(path_image gb UNION path_image g2) =
              inside(path_image gb UNION path_image g1) UNION inside gam UNION
              (path_image g1 DIFF path_image gb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image gb INTER path_image g1 = {u:real^2,v} /\
    path_image gb INTER path_image g2 = {u:real^2,v} /\
    path_image gb DIFF {u:real^2,v} = path_image gb DIFF gam /\
    path_image g1 DIFF {u:real^2,v} = path_image g1 DIFF path_image gb /\
    ~(path_image g2 DIFF {u:real^2,v} = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `g2:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
    MP_TAC(ISPEC `g1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g2:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g2:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
    UNDISCH_TAC `path_image gb INTER gam = {u:real^2,v}` THEN
    UNDISCH_TAC `path_image g1 UNION path_image g2 = (gam:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                   `u:real^2`; `v:real^2`] MOI_S3L9MD_THETA_IN) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `gb:real^1->real^2`;
                   `u:real^2`; `v:real^2`] MOI_S3L9MD_THETA_OUT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [(* the second arc inside the cycle of b and g1: then the disk of g1
         meets gam outside g1 *)
      MP_TAC(ISPEC `path_image gb UNION path_image (g1:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `path_image g2 DIFF {u:real^2,v} SUBSET
                   inside(path_image gb UNION path_image g1)` THEN
      UNDISCH_TAC `((path_image gb UNION path_image g1) UNION
                    inside(path_image gb UNION path_image g1)) INTER gam =
                   path_image (g1:real^1->real^2)` THEN
      UNDISCH_TAC `~(path_image g2 DIFF {u:real^2,v} = {})` THEN
      UNDISCH_TAC `path_image g1 INTER path_image g2 = {u:real^2,v}` THEN
      UNDISCH_TAC `path_image g1 UNION path_image g2 = (gam:real^2->bool)` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[]]]);;

let MOI_S3L9MD_COMPL = prove
 (`!(gam:real^2->bool) (gb:real^1->real^2) (g:real^1->real^2).
     gam homeomorphic sphere(vec 0:real^2,&1) /\
     arc gb /\ path_image gb INTER gam = {pathstart gb,pathfinish gb} /\
     arc g /\ path_image g SUBSET gam /\ {pathstart g,pathfinish g} = path_image gb INTER gam /\
     ((path_image gb UNION path_image g) UNION inside(path_image gb UNION path_image g))
       INTER gam = path_image g
     ==> ?a. compact a /\ path_image g UNION a = gam /\
             path_image g INTER a = path_image gb INTER gam /\
             (path_image gb DIFF gam SUBSET inside gam
              ==> inside(path_image gb UNION path_image g) INTER
                  inside(path_image gb UNION a) = {} /\
                  inside gam = inside(path_image gb UNION path_image g) UNION
                               inside(path_image gb UNION a) UNION (path_image gb DIFF gam)) /\
             (path_image gb DIFF gam SUBSET outside gam
              ==> path_image g DIFF path_image gb SUBSET inside(path_image gb UNION a) /\
                  inside(path_image gb UNION a) =
                  inside(path_image gb UNION path_image g) UNION inside gam UNION
                  (path_image g DIFF path_image gb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = pathstart(gb:real^1->real^2)` THEN
  ABBREV_TAC `v = pathfinish(gb:real^1->real^2)` THEN
  MP_TAC(ISPECL [`gam:real^2->bool`; `u:real^2`; `v:real^2`] MOI_S3L9MD_SPLIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `gb:real^1->real^2` ARC_DISTINCT_ENDS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image gb INTER gam = {u:real^2,v}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` (X_CHOOSE_THEN `g2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `g:real^1->real^2`;
                 `u:real^2`; `v:real^2`] MOI_S3L9MD_CLASSIFY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image g2 INTER path_image g1 = {u:real^2,v} /\
                path_image g2 UNION path_image g1 = (gam:real^2->bool) /\
                path_image gb INTER gam = {u:real^2,v}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `path_image(g2:real^1->real^2)` THEN
    MP_TAC(ISPECL [`gam:real^2->bool`; `gb:real^1->real^2`; `g1:real^1->real^2`;
                   `g2:real^1->real^2`; `u:real^2`; `v:real^2`] MOI_S3L9MD_COMPL_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((path_image gb UNION path_image g) UNION
                    inside(path_image gb UNION path_image g)) INTER gam =
                   path_image (g:real^1->real^2)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[COMPACT_ARC_IMAGE];
    EXISTS_TAC `path_image(g1:real^1->real^2)` THEN
    MP_TAC(ISPECL [`gam:real^2->bool`; `gb:real^1->real^2`; `g2:real^1->real^2`;
                   `g1:real^1->real^2`; `u:real^2`; `v:real^2`] MOI_S3L9MD_COMPL_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((path_image gb UNION path_image g) UNION
                    inside(path_image gb UNION path_image g)) INTER gam =
                   path_image (g:real^1->real^2)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[COMPACT_ARC_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* MINIMAL_DISK, part 4: an arc b' meeting the disk D of (b,g) lies in D     *)
(* with both ends on g minus b (INNER), and then cuts off a smaller disk    *)
(* D' inside D missing b (SUBDISK).                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9MD_CONNECTED_OPEN2 = prove
 (`!s e1 e2:real^N->bool.
     connected s /\ open e1 /\ open e2 /\ e1 INTER e2 = {} /\ s SUBSET e1 UNION e2
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`])
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3L9MD_INNER = prove
 (`!(gam:real^2->bool) b (g:real^1->real^2) a (gb':real^1->real^2).
     compact b /\ compact a /\ arc g /\ path_image g SUBSET gam /\
     path_image g INTER a = b INTER gam /\
     ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam = path_image g /\
     ((path_image gb' DIFF gam SUBSET inside gam /\
       inside(b UNION path_image g) INTER inside(b UNION a) = {} /\
       inside gam = inside(b UNION path_image g) UNION inside(b UNION a) UNION
                    (b DIFF gam)) \/
      (path_image gb' DIFF gam SUBSET outside gam /\
       path_image g DIFF b SUBSET inside(b UNION a) /\
       inside(b UNION a) = inside(b UNION path_image g) UNION inside gam UNION
                           (path_image g DIFF b))) /\
     arc gb' /\ path_image gb' INTER gam = {pathstart gb',pathfinish gb'} /\
     DISJOINT b (path_image gb') /\
     ~DISJOINT (path_image gb') ((b UNION path_image g) UNION inside(b UNION path_image g))
     ==> path_image gb' SUBSET (b UNION path_image g) UNION inside(b UNION path_image g) /\
         path_image gb' INTER gam SUBSET path_image g DIFF b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "case")
    STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN
   `connected(path_image gb' DIFF gam:real^2->bool) /\
    path_image gb' SUBSET closure(path_image gb' DIFF gam) /\
    (path_image gb' DIFF gam) INTER (b UNION path_image (g:real^1->real^2)) = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `path_image gb' DIFF gam =
                  path_image gb' DIFF {pathstart gb',pathfinish (gb':real^1->real^2)}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_SIMPLE_PATH_ENDLESS THEN ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MATCH_MP_TAC MOI_SFR_ARC_DENSE THEN ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(b UNION path_image (g:real^1->real^2)) /\ closed(b UNION a:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNION THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_ARC_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `b UNION path_image (g:real^1->real^2)` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `b UNION path_image (g:real^1->real^2)` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `gam:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `gam:real^2->bool` INSIDE_NO_OVERLAP) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `path_image gb' DIFF gam SUBSET inside(b UNION path_image g) \/
    path_image gb' DIFF gam SUBSET outside(b UNION path_image (g:real^1->real^2))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_S3L9MD_CONNECTED_OPEN2 THEN
    ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE] THEN
    MP_TAC(ISPEC `b UNION path_image (g:real^1->real^2)` INSIDE_UNION_OUTSIDE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [(* inside the cycle: b' lies in the disk *)
    SUBGOAL_THEN `path_image gb' SUBSET
                  (b UNION path_image g) UNION inside(b UNION path_image (g:real^1->real^2))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(path_image gb' DIFF gam:real^2->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(inside(b UNION path_image (g:real^1->real^2)))` THEN
      ASM_SIMP_TAC[SUBSET_CLOSURE; CLOSURE_INSIDE_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* outside the cycle: an end w of b' lies on g minus b *)
  SUBGOAL_THEN `?w:real^2. w IN path_image gb' /\ w IN path_image g /\ ~(w IN b)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "case" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* b' on the inside of gam: its open arc is inside the cycle with a *)
    SUBGOAL_THEN `path_image gb' DIFF gam SUBSET inside(b UNION a:real^2->bool)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2) IN (b UNION a) UNION inside(b UNION a)` MP_TAC THENL
     [SUBGOAL_THEN `path_image gb' SUBSET (b UNION a) UNION inside(b UNION a:real^2->bool)`
      MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure(path_image gb' DIFF gam:real^2->bool)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure(inside(b UNION a:real^2->bool))` THEN
        ASM_SIMP_TAC[SUBSET_CLOSURE; CLOSURE_INSIDE_SUBSET];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM SET_TAC[];
    (* b' on the outside of gam: near w the open arc enters inside(b UNION a) *)
    SUBGOAL_THEN `~(inside(b UNION a) INTER (path_image gb' DIFF gam:real^2->bool) = {})`
    MP_TAC THENL
     [MP_TAC(ISPECL [`inside(b UNION a:real^2->bool)`;
                     `path_image gb' DIFF gam:real^2->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_INSIDE]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM SET_TAC[]]);;

let MOI_S3L9MD_SUBDISK = prove
 (`!(gam:real^2->bool) (gb:real^1->real^2) (g:real^1->real^2) (gb':real^1->real^2).
     arc gb /\ path_image gb INTER gam = {pathstart gb,pathfinish gb} /\
     arc g /\ path_image g SUBSET gam /\
     {pathstart g,pathfinish g} = path_image gb INTER gam /\
     ((path_image gb UNION path_image g) UNION inside(path_image gb UNION path_image g))
       INTER gam = path_image g /\
     arc gb' /\ path_image gb' INTER gam = {pathstart gb',pathfinish gb'} /\
     DISJOINT (path_image gb) (path_image gb') /\
     path_image gb' SUBSET
       (path_image gb UNION path_image g) UNION inside(path_image gb UNION path_image g) /\
     path_image gb' INTER gam SUBSET path_image g DIFF path_image gb
     ==> ?g'. arc g' /\ path_image g' SUBSET gam /\
              {pathstart g',pathfinish g'} = path_image gb' INTER gam /\
              (path_image gb' UNION path_image g') UNION
                inside(path_image gb' UNION path_image g') SUBSET
                (path_image gb UNION path_image g) UNION
                inside(path_image gb UNION path_image g) /\
              ((path_image gb' UNION path_image g') UNION
               inside(path_image gb' UNION path_image g')) INTER gam = path_image g' /\
              DISJOINT (path_image gb)
                ((path_image gb' UNION path_image g') UNION
                 inside(path_image gb' UNION path_image g'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the cycle of b and g *)
  MP_TAC(ISPECL [`gb:real^1->real^2`; `g:real^1->real^2`] MOI_S3L9MD_JORDAN2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `g:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `path_image gb UNION path_image (g:real^1->real^2)`]
                MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the sub-arc of g between the ends of b' *)
  MP_TAC(ISPECL [`g:real^1->real^2`; `pathstart(gb':real^1->real^2)`;
                 `pathfinish(gb':real^1->real^2)`] EXISTS_SUBARC_OF_ARC_NOENDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `gb':real^1->real^2` ARC_DISTINCT_ENDS) THEN
    MP_TAC(ISPEC `gb':real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `gb':real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  (* the cycle of b' and h *)
  MP_TAC(ISPECL [`gb':real^1->real^2`; `h:real^1->real^2`] MOI_S3L9MD_JORDAN2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `h:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c':real^1->real^2`; `path_image gb' UNION path_image (h:real^1->real^2)`]
                MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the new disk is inside the old one *)
  SUBGOAL_THEN `outside(path_image gb UNION path_image g) SUBSET
                outside(path_image gb' UNION path_image (h:real^1->real^2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
    EXISTS_TAC `outside(path_image gb UNION path_image (g:real^1->real^2))` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(path_image gb' UNION path_image h) UNION inside(path_image gb' UNION path_image h)
    SUBSET (path_image gb UNION path_image g) UNION
           inside(path_image gb UNION path_image (g:real^1->real^2))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `inside(path_image gb' UNION path_image h) SUBSET
    inside(path_image gb UNION path_image (g:real^1->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior((path_image gb UNION path_image g) UNION
                         inside(path_image gb UNION path_image (g:real^1->real^2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image h SUBSET (gam:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image h SUBSET
                 path_image g DIFF {pathstart g,pathfinish (g:real^1->real^2)}` THEN
    UNDISCH_TAC `path_image g SUBSET (gam:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((path_image gb' UNION path_image h) UNION inside(path_image gb' UNION path_image h))
    INTER gam = path_image (h:real^1->real^2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `h:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image gb' INTER gam = {pathstart gb',pathfinish (gb':real^1->real^2)}` THEN
    UNDISCH_TAC `path_image h SUBSET (gam:real^2->bool)` THEN
    UNDISCH_TAC `inside(path_image gb' UNION path_image h) SUBSET
                 inside(path_image gb UNION path_image (g:real^1->real^2))` THEN
    UNDISCH_TAC `((path_image gb UNION path_image g) UNION
                  inside(path_image gb UNION path_image g)) INTER gam =
                 path_image (g:real^1->real^2)` THEN
    UNDISCH_TAC `inside(path_image gb UNION path_image g) INTER
                 (path_image gb UNION path_image (g:real^1->real^2)) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (path_image gb)
      ((path_image gb' UNION path_image h) UNION
       inside(path_image gb' UNION path_image (h:real^1->real^2)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (path_image gb) (path_image (gb':real^1->real^2))` THEN
    UNDISCH_TAC `path_image h SUBSET
                 path_image g DIFF {pathstart g,pathfinish (g:real^1->real^2)}` THEN
    UNDISCH_TAC `{pathstart g,pathfinish g} = path_image gb INTER (gam:real^2->bool)` THEN
    UNDISCH_TAC `path_image g SUBSET (gam:real^2->bool)` THEN
    UNDISCH_TAC `inside(path_image gb' UNION path_image h) SUBSET
                 inside(path_image gb UNION path_image (g:real^1->real^2))` THEN
    UNDISCH_TAC `inside(path_image gb UNION path_image g) INTER
                 (path_image gb UNION path_image (g:real^1->real^2)) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `h:real^1->real^2` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MINIMAL_DISK, part 5: the minimal disk.  Among the disks D of valid      *)
(* pairs (b,g), take one with the fewest arcs of bs inside it; an arc b'    *)
(* meeting it would give a valid pair (b',g') with D' inside D and missing  *)
(* b, hence fewer arcs inside.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9MD_CARD_LT = prove
 (`!(s:A->bool) P Q a.
     FINITE s /\ (!x. P x ==> Q x) /\ a IN s /\ Q a /\ ~P a
     ==> CARD {x | x IN s /\ P x} < CARD {x | x IN s /\ Q x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]);;

let MOI_S3L9MD_MAIN_SIDE = prove
 (`!(gam:real^2->bool) p (bs:(real^2->bool)->bool) sd.
     gam homeomorphic sphere(vec 0:real^2,&1) /\ gam SUBSET ball(vec 0,&1) /\
     p IN inside gam /\ FINITE bs /\ ~(bs = {}) /\ pairwise DISJOINT bs /\
     (!b. b IN bs
          ==> ?g:real^1->real^2. arc g /\ path_image g = b /\
                                 b INTER gam = {pathstart g,pathfinish g}) /\
     (!b. b IN bs ==> b SUBSET ball(vec 0,&1) /\ ~(p IN b)) /\
     (sd = inside gam \/ sd = outside gam) /\
     (!b. b IN bs ==> b DIFF gam SUBSET sd)
     ==> ?b g:real^1->real^2.
          b IN bs /\ arc g /\ path_image g SUBSET gam /\
          {pathstart g,pathfinish g} = b INTER gam /\
          ~(p IN (b UNION path_image g) UNION inside(b UNION path_image g)) /\
          (b UNION path_image g) UNION inside(b UNION path_image g) SUBSET
            ball(vec 0,&1) /\
          ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam =
            path_image g /\
          (!b'. b' IN bs /\ ~(b' = b)
                ==> DISJOINT b' ((b UNION path_image g) UNION
                                 inside(b UNION path_image g)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "arcs")
   (CONJUNCTS_THEN2 (LABEL_TAC "ball") (CONJUNCTS_THEN2 (LABEL_TAC "sd")
    (LABEL_TAC "side")))))))))) THEN
  (* valid pairs exist; take one with the fewest arcs in its disk *)
  SUBGOAL_THEN
   `?n b g:real^1->real^2.
      b IN bs /\ arc g /\ path_image g SUBSET gam /\
      {pathstart g,pathfinish g} = b INTER gam /\
      ~(p IN (b UNION path_image g) UNION inside(b UNION path_image g)) /\
      (b UNION path_image g) UNION inside(b UNION path_image g) SUBSET ball(vec 0,&1) /\
      ((b UNION path_image g) UNION inside(b UNION path_image g)) INTER gam =
        path_image g /\
      CARD {b'' | b'' IN bs /\
                  b'' SUBSET (b UNION path_image g) UNION inside(b UNION path_image g)} = n`
  MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `b:real^2->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(bs:(real^2->bool)->bool = {})`)) THEN
    USE_THEN "arcs" (X_CHOOSE_THEN `gb:real^1->real^2` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(b:real^2->bool) IN bs`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `b:real^2->bool`)) THEN
    MP_TAC(ISPECL [`gam:real^2->bool`; `p:real^2`; `gb:real^1->real^2`] MOI_S3L9MD_EXIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `path_image (gb:real^1->real^2) IN bs`)) THEN
      USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `path_image (gb:real^1->real^2) IN bs`)) THEN
      USE_THEN "sd" (DISJ_CASES_THEN SUBST1_TAC) THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`CARD {b'' | b'' IN bs /\
                   b'' SUBSET (path_image gb UNION path_image g) UNION
                              inside(path_image gb UNION path_image (g:real^1->real^2))}`;
      `path_image gb:real^2->bool`; `g:real^1->real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [num_WOP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `b0:real^2->bool` (X_CHOOSE_THEN `g0:real^1->real^2` STRIP_ASSUME_TAC))
    (LABEL_TAC "min"))) THEN
  MAP_EVERY EXISTS_TAC [`b0:real^2->bool`; `g0:real^1->real^2`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b':real^2->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* the arcs of b0 and b' *)
  USE_THEN "arcs" (X_CHOOSE_THEN `gb0:real^1->real^2` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(b0:real^2->bool) IN bs`)) THEN
  USE_THEN "arcs" (X_CHOOSE_THEN `gb':real^1->real^2` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(b':real^2->bool) IN bs`)) THEN
  SUBGOAL_THEN `DISJOINT (b0:real^2->bool) b'` ASSUME_TAC THENL
   [UNDISCH_TAC `pairwise DISJOINT (bs:(real^2->bool)->bool)` THEN REWRITE_TAC[pairwise] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b0 DIFF gam SUBSET (sd:real^2->bool) /\ b' DIFF gam SUBSET sd`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "side" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `b0:real^2->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `b':real^2->bool`)) THEN
  (* the complementary arc of gam and the theta decomposition *)
  MP_TAC(ISPECL [`gam:real^2->bool`; `gb0:real^1->real^2`; `g0:real^1->real^2`]
                MOI_S3L9MD_COMPL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2->bool` STRIP_ASSUME_TAC) THEN
  (* b' lies in the disk with its ends on g0 minus b0 *)
  MP_TAC(ISPECL [`gam:real^2->bool`; `path_image gb0:real^2->bool`; `g0:real^1->real^2`;
                 `a:real^2->bool`; `gb':real^1->real^2`] MOI_S3L9MD_INNER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_ARC_IMAGE] THEN
    USE_THEN "sd" (DISJ_CASES_THEN SUBST_ALL_TAC) THENL [DISJ1_TAC; DISJ2_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  (* the smaller disk *)
  MP_TAC(ISPECL [`gam:real^2->bool`; `gb0:real^1->real^2`; `g0:real^1->real^2`;
                 `gb':real^1->real^2`] MOI_S3L9MD_SUBDISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^2` STRIP_ASSUME_TAC) THEN
  USE_THEN "min" (MP_TAC o SPEC
    `CARD {b'' | b'' IN bs /\
                 b'' SUBSET (path_image gb' UNION path_image g') UNION
                            inside(path_image gb' UNION path_image (g':real^1->real^2))}`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `n:num`)) THEN
    MATCH_MP_TAC MOI_S3L9MD_CARD_LT THEN EXISTS_TAC `path_image gb0:real^2->bool` THEN
    MP_TAC(ISPEC `gb0:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `DISJOINT (path_image gb0)
                   ((path_image gb' UNION path_image g') UNION
                    inside(path_image gb' UNION path_image (g':real^1->real^2)))` THEN
    UNDISCH_TAC `(path_image gb' UNION path_image g') UNION
                 inside(path_image gb' UNION path_image g') SUBSET
                 (path_image gb0 UNION path_image g0) UNION
                 inside(path_image gb0 UNION path_image (g0:real^1->real^2))` THEN
    UNDISCH_TAC `path_image (gb0:real^1->real^2) IN bs` THEN
    UNDISCH_TAC `FINITE (bs:(real^2->bool)->bool)` THEN
    SET_TAC[];
    MAP_EVERY EXISTS_TAC [`path_image gb':real^2->bool`; `g':real^1->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(path_image gb' UNION path_image g') UNION
                 inside(path_image gb' UNION path_image g') SUBSET
                 (path_image gb0 UNION path_image g0) UNION
                 inside(path_image gb0 UNION path_image (g0:real^1->real^2))` THEN
    UNDISCH_TAC `~((p:real^2) IN (path_image gb0 UNION path_image g0) UNION
                       inside(path_image gb0 UNION path_image (g0:real^1->real^2)))` THEN
    UNDISCH_TAC `(path_image gb0 UNION path_image g0) UNION
                 inside(path_image gb0 UNION path_image (g0:real^1->real^2)) SUBSET
                 ball(vec 0:real^2,&1)` THEN
    SET_TAC[]]);;

let MOI_S3L9_MINIMAL_DISK = prove
 (MOI_S3L9_MINIMAL_DISK_TERM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3L9MD_MAIN_SIDE THENL
   [EXISTS_TAC `inside(gam:real^2->bool)`; EXISTS_TAC `outside(gam:real^2->bool)`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* H3 ARC_COLLAR (Lemma 9, arc step): the statement MOI_S3L9_ARC_COLLAR_TERM *)
(* of Part 9, restated below.  It uses MOI_S3L9MD_SPLIT2 and                 *)
(* MOI_S3L9MD_CLASSIFY of H2.                                                *)
(*                                                                           *)
(* Route.  The arc b of the Jordan curve c has a complementary arc b' in c. *)
(* A homeomorphism of c onto the boundary of a triangle with b onto the     *)
(* side [p1,p2] is glued from two arc homeomorphisms (HOMEOMORPHISM_ARC_     *)
(* IMAGES, HOMOEOMORPHISM_PASTE) and extended to the plane by               *)
(* JORDAN_SCHOENFLIES.  In the triangle, the collar is the part of the      *)
(* d-neighbourhood of the side (the sums x + y with x on the side and y in  *)
(* ball(0,d)) lying in the triangle, minus the side: it lies between the    *)
(* convex set of its interior points and their closure, so it is connected. *)
(* Pull back.                                                                *)
(* Uses the HOL library, MOI_PL2_TRIANGLE_POLYGON and                       *)
(* MOI_PL2_TRIANGLE_CLOSED_INSIDE (pc_moi_pl2.ml, in the closure of          *)
(* pc_moi_s33_l9) and the two H2 lemmas above.                               *)
(* ========================================================================= *)

type_invention_error := true;;

let MOI_S3L9_ARC_COLLAR_TERM =
 `!(c:real^2->bool) (b:real^1->real^2) (k:real^2->bool).
    c homeomorphic sphere(vec 0:real^2,&1) /\ arc b /\ path_image b SUBSET c /\
    closed k /\ DISJOINT (path_image b) k
    ==> ?a w. connected a /\ a SUBSET (c UNION inside c) DIFF path_image b /\
              DISJOINT a k /\ path_image b SUBSET closure a /\
              open w /\ path_image b SUBSET w /\
              w INTER (c UNION inside c) SUBSET a UNION path_image b`;;

(* ------------------------------------------------------------------------- *)
(* ARC_COLLAR, part 1: the complementary arc, a collar of a convex boundary *)
(* piece of a convex body, and the triangle model.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9AC_COMPLEMENT = prove
 (`!(c:real^2->bool) (b:real^1->real^2).
     c homeomorphic sphere(vec 0:real^2,&1) /\ arc b /\ path_image b SUBSET c
     ==> ?b'. arc b' /\ pathstart b' = pathstart b /\ pathfinish b' = pathfinish b /\
              path_image b INTER path_image b' = {pathstart b,pathfinish b} /\
              path_image b UNION path_image b' = c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `pathstart(b:real^1->real^2)`;
                 `pathfinish(b:real^1->real^2)`] MOI_S3L9MD_SPLIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `b:real^1->real^2` ARC_DISTINCT_ENDS) THEN
    MP_TAC(ISPEC `b:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `b:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^2` (X_CHOOSE_THEN `g2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g1:real^1->real^2`; `g2:real^1->real^2`; `b:real^1->real^2`;
                 `pathstart(b:real^1->real^2)`; `pathfinish(b:real^1->real^2)`]
                MOI_S3L9MD_CLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `g2:real^1->real^2`; EXISTS_TAC `g1:real^1->real^2`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3L9AC_TRI_COLLAR = prove
 (`!(t:real^2->bool) s kk.
     convex t /\ compact t /\ ~(interior t = {}) /\
     convex s /\ compact s /\ s SUBSET t DIFF interior t /\
     closed kk /\ DISJOINT s kk
     ==> ?a0 w0. connected a0 /\ a0 SUBSET t DIFF s /\ DISJOINT a0 kk /\
                 s SUBSET closure a0 /\ open w0 /\ s SUBSET w0 /\
                 w0 INTER t SUBSET a0 UNION s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `kk:real^2->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `w0 = {x + y:real^2 | x IN s /\ y IN ball(vec 0,d)}` THEN
  SUBGOAL_THEN `open (w0:real^2->bool) /\ convex w0 /\ s SUBSET w0 /\ DISJOINT w0 kk`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_SUMS THEN REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC CONVEX_SUMS THEN ASM_REWRITE_TAC[CONVEX_BALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `vec 0:real^2`] THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `y:real^2`
        STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `z:real^2`]) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^2) IN ball(vec 0,d)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `a0 = (w0 INTER t) DIFF (s:real^2->bool)` THEN
  SUBGOAL_THEN `connected(w0 INTER interior t:real^2->bool) /\
                w0 INTER interior t SUBSET a0 /\
                w0 INTER t SUBSET closure(w0 INTER interior t)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      ASM_SIMP_TAC[CONVEX_INTERIOR];
      EXPAND_TAC "a0" THEN MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `w0 INTER closure(interior t:real^2->bool)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED;
                     SUBSET_REFL];
        ASM_SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a0:real^2->bool`; `w0:real^2->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `w0 INTER interior t:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "a0" THEN ASM SET_TAC[];
    EXPAND_TAC "a0" THEN SET_TAC[];
    EXPAND_TAC "a0" THEN ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(w0 INTER interior t:real^2->bool)` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    EXPAND_TAC "a0" THEN SET_TAC[]]);;

let MOI_S3L9AC_MODEL = prove
 (`!p1 p2 p3:real^2.
     ~collinear{p1,p2,p3}
     ==> ?h s':real^1->real^2.
           simple_path h /\ pathfinish h = pathstart h /\
           path_image h = frontier(convex hull {p1,p2,p3}) /\
           inside(path_image h) = interior(convex hull {p1,p2,p3}) /\
           ~(interior(convex hull {p1,p2,p3}) = {}) /\
           arc s' /\ pathstart s' = p1 /\ pathfinish s' = p2 /\
           segment[p1,p2] INTER path_image s' = {p1,p2} /\
           segment[p1,p2] UNION path_image s' = path_image h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_TRIANGLE_POLYGON) THEN
  SUBGOAL_THEN `~(p1:real^2 = p2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~collinear{p2:real^2,p2,p3}` THEN
    REWRITE_TAC[INSERT_INSERT; COLLINEAR_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`path_image(polygonal_path[p1;p2;p3;p1]):real^2->bool`;
                 `linepath(p1:real^2,p2)`] MOI_S3L9AC_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      MATCH_MP_TAC ARC_LINEPATH THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^1->real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`polygonal_path[p1;p2;p3;p1]:real^1->real^2`; `s':real^1->real^2`] THEN
  ASM_REWRITE_TAC[FRONTIER_OF_TRIANGLE; INSIDE_OF_TRIANGLE] THEN
  REWRITE_TAC[GSYM INSIDE_OF_TRIANGLE] THEN
  MP_TAC(ISPEC `polygonal_path[p1;p2;p3;p1]:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ARC_COLLAR, part 2: pulling the model collar back by a homeomorphism of *)
(* the plane, and the collar of a boundary arc of a Jordan domain.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9AC_PULLBACK = prove
 (`!(k:real^2->real^2) k' d bb kk t s a0 w0.
     homeomorphism ((:real^2),(:real^2)) (k,k') /\
     IMAGE k d = t /\ IMAGE k bb = s /\
     connected a0 /\ a0 SUBSET t DIFF s /\ DISJOINT a0 (IMAGE k kk) /\
     s SUBSET closure a0 /\ open w0 /\ s SUBSET w0 /\ w0 INTER t SUBSET a0 UNION s
     ==> connected (IMAGE k' a0) /\ IMAGE k' a0 SUBSET d DIFF bb /\
         DISJOINT (IMAGE k' a0) kk /\ bb SUBSET closure(IMAGE k' a0) /\
         open {x | k x IN w0} /\ bb SUBSET {x | k x IN w0} /\
         {x | k x IN w0} INTER d SUBSET IMAGE k' a0 UNION bb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV]) THEN
  SUBGOAL_THEN `(!x. x IN IMAGE (k':real^2->real^2) a0 <=> k x IN a0) /\
                (!x. x IN IMAGE (k':real^2->real^2) (closure a0) <=> k x IN closure a0) /\
                (!x. x IN d <=> (k:real^2->real^2) x IN t) /\
                (!x. x IN bb <=> (k:real^2->real^2) x IN s) /\
                (!x. x IN kk <=> (k:real^2->real^2) x IN IMAGE k kk)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun th -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th' ->
                 concl th' = concl th)))
      [ASSUME `IMAGE (k:real^2->real^2) d = t`; ASSUME `IMAGE (k:real^2->real^2) bb = s`] THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k':real^2->real^2) continuous_on (:real^2) /\
                (!x. (k:real^2->real^2) continuous at x)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`k:real^2->real^2`; `(:real^2)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ASM_REWRITE_TAC[SUBSET; IN_DIFF] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (k':real^2->real^2) (closure a0)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET] THEN ASM SET_TAC[];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
      REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN ASM SET_TAC[]]);;

let MOI_S3L9_ARC_COLLAR = prove
 (MOI_S3L9_ARC_COLLAR_TERM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the complementary arc of b in c *)
  MP_TAC(ISPECL [`c:real^2->bool`; `b:real^1->real^2`] MOI_S3L9AC_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b':real^1->real^2` STRIP_ASSUME_TAC) THEN
  (* the triangle model *)
  SUBGOAL_THEN `?p1 p2 p3:real^2. ~collinear{p1,p2,p3}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`vector[&0;&0]:real^2`; `vector[&1;&0]:real^2`;
                          `vector[&0;&1]:real^2`] THEN
    REWRITE_TAC[COLLINEAR_3_2D; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:real^2 = p2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~collinear{p2:real^2,p2,p3}` THEN
    REWRITE_TAC[INSERT_INSERT; COLLINEAR_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p1:real^2`; `p2:real^2`; `p3:real^2`] MOI_S3L9AC_MODEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` (X_CHOOSE_THEN `s':real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* homeomorphisms of b onto the side and of b' onto the rest *)
  MP_TAC(ISPECL [`b:real^1->real^2`; `linepath(p1:real^2,p2)`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_SIMP_TAC[ARC_LINEPATH] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2` (X_CHOOSE_THEN `f1':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`b':real^1->real^2`; `s':real^1->real^2`] HOMEOMORPHISM_ARC_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `f2':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* the glued homeomorphism of c onto the triangle boundary *)
  MP_TAC(ISPECL [`f1:real^2->real^2`; `f1':real^2->real^2`; `f2:real^2->real^2`;
                 `f2':real^2->real^2`; `path_image(b:real^1->real^2)`; `segment[p1:real^2,p2]`;
                 `path_image(b':real^1->real^2)`; `path_image(s':real^1->real^2)`]
                HOMOEOMORPHISM_PASTE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
      ASM_SIMP_TAC[CLOSED_ARC_IMAGE; CLOSED_SEGMENT; SUBSET_UNION] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:real^2->real^2` (X_CHOOSE_THEN `kh:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* Schoenflies *)
  MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
                HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `gc:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`gc:real^1->real^2`; `h:real^1->real^2`; `hh:real^2->real^2`;
                 `kh:real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (path_image b UNION path_image b',
                                segment[p1,p2] UNION path_image s')
                               (hh:real^2->real^2,kh)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real^2->real^2` (X_CHOOSE_THEN `hk':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* the facts about hk *)
  SUBGOAL_THEN `(!x. hk'((hk:real^2->real^2) x) = x) /\ (!y. hk((hk':real^2->real^2) y) = y) /\
                (!x. (hk':real^2->real^2) continuous at x)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      can (term_match [] `homeomorphism ((:real^2),(:real^2)) (hk,hk')`) (concl th))) THEN
    SIMP_TAC[IN_UNIV; CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (hk:real^2->real^2) (path_image b) = segment[p1,p2]` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (hh:real^2->real^2) (path_image b) = segment[p1,p2]` THEN
    UNDISCH_TAC `!x. x IN path_image gc ==> (hk:real^2->real^2) x = hh x` THEN
    UNDISCH_TAC `path_image gc = (c:real^2->bool)` THEN
    UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (hk:real^2->real^2) (c UNION inside c) = convex hull {p1,p2,p3}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN
    UNDISCH_TAC `IMAGE (hk:real^2->real^2) (path_image gc) = path_image h` THEN
    UNDISCH_TAC `IMAGE (hk:real^2->real^2) (inside(path_image gc)) = inside(path_image h)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FRONTIER_OF_TRIANGLE; GSYM INSIDE_OF_TRIANGLE;
                MOI_PL2_TRIANGLE_CLOSED_INSIDE];
    ALL_TAC] THEN
  (* the model collar *)
  MP_TAC(ISPECL [`convex hull {p1:real^2,p2,p3}`; `segment[p1:real^2,p2]`;
                 `IMAGE (hk:real^2->real^2) k`] MOI_S3L9AC_TRI_COLLAR) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY;
             FINITE_IMP_COMPACT; CONVEX_SEGMENT; COMPACT_SEGMENT] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `convex hull {p1:real^2,p2,p3} DIFF interior(convex hull {p1,p2,p3}) =
                    frontier(convex hull {p1,p2,p3})` SUBST1_TAC THENL
       [REWRITE_TAC[frontier] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ALL_TAC] THEN
      UNDISCH_TAC `path_image h = frontier(convex hull {p1:real^2,p2,p3})` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `segment[p1,p2] UNION path_image s' = path_image(h:real^1->real^2)` THEN
      SET_TAC[];
      SUBGOAL_THEN `IMAGE (hk:real^2->real^2) k = {y | hk' y IN k}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `segment[p1:real^2,p2]` &&
        can (find_term (fun t -> t = `hk:real^2->real^2`)) (concl th))) THEN
      UNDISCH_TAC `DISJOINT (path_image b) (k:real^2->bool)` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^2->bool` (X_CHOOSE_THEN `w0:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hk:real^2->real^2`; `hk':real^2->real^2`; `c UNION inside c:real^2->bool`;
                 `path_image(b:real^1->real^2)`; `k:real^2->bool`;
                 `convex hull {p1:real^2,p2,p3}`; `segment[p1:real^2,p2]`;
                 `a0:real^2->bool`; `w0:real^2->bool`] MOI_S3L9AC_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (hk':real^2->real^2) a0`; `{x | (hk:real^2->real^2) x IN w0}`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* H4: MOI_S3L9_ARC_IN_CIRCLE, the statement MOI_S3L9_ARC_IN_CIRCLE_TERM     *)
(* above; library only.  Route: CONNECTED_SUBSET_ARC_PAIR (the connected     *)
(* image of g contains both ends, so it contains one of the two arcs) and    *)
(* ARC_IMAGE_UNIQUE (an arc containing an arc with the same two ends has the *)
(* same image).                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L9_ARC_IN_CIRCLE = prove
 (MOI_S3L9_ARC_IN_CIRCLE_TERM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^1->real^N`; `a2:real^1->real^N`;
                 `path_image(g:real^1->real^N)`] CONNECTED_SUBSET_ARC_PAIR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_ARC_IMAGE] THEN
    MP_TAC(ISPEC `g:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `g:real^1->real^N` PATHFINISH_IN_PATH_IMAGE) THEN
    UNDISCH_TAC
     `{pathstart g,pathfinish g} = {pathstart a1,pathfinish (a1:real^1->real^N)}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARC_IMAGE_UNIQUE THEN
    ASM_SIMP_TAC[ARC_IMP_PATH];
    DISJ2_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARC_IMAGE_UNIQUE THEN
    ASM_SIMP_TAC[ARC_IMP_PATH]]);;

(* ------------------------------------------------------------------------- *)
(* Part 10. The arc step.                                                    *)
(* ------------------------------------------------------------------------- *)

(* A PL 1-cell is the image of a PL arc: MOI_S4L_CELL1_PL_ARC of            *)
(* pc_moi_s34_l910.ml with the same proof, repeated here to keep the load   *)
(* closure small.                                                           *)

let MOI_S3L9_CELL1_PL_ARC = prove
 (`!a aa:real^N->bool.
     pl_cell_with_boundary 1 a aa
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = a /\
             aa = {pathstart h,pathfinish h}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `(f:real^N->real^N) o linepath(x0,x1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `segment[x0:real^N,x1]` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REWRITE_TAC[GSYM path_image; PATH_IMAGE_LINEPATH; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH];
    ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[IMAGE_CLAUSES]]);;

(* Gluing two PL 2-cells in real^3 along a PL arc of both boundaries:       *)
(* MOI_S4OT_DISK_GLUE of pc_moi_s34_touter.ml with the same proof, repeated *)
(* here to keep the load closure small.                                     *)

let MOI_S3L9_DISK_GLUE = prove
 (`!(d1:real^3->bool) j1 d2 j2 b bb.
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     pl_cell_with_boundary 1 b bb /\ d1 INTER d2 = b /\ b SUBSET j1 /\ b SUBSET j2
     ==> pl_cell_with_boundary 2 (d1 UNION d2) ((j1 UNION j2) DIFF (b DIFF bb))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `al:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S3L9_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bb:real^3->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(al:real^1->real^3)`)) THEN
  MATCH_MP_TAC MOI_FSA_GLUE THEN ASM_REWRITE_TAC[]);;

(* The interior of a loop theorem disk lies on one side of Bd X.            *)

let MOI_S3L9_LTD_SIDE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) x d.
     moi_s33_ltd t l h x d
     ==> d DIFF frontier (UNIONS x) SUBSET UNIONS x \/
         DISJOINT (d DIFF frontier (UNIONS x)) (UNIONS x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  SUBGOAL_THEN `d DIFF frontier (UNIONS (x:(real^3->bool)->bool)) = d DIFF j` SUBST1_TAC THENL
   [UNDISCH_TAC `d INTER frontier (UNIONS (x:(real^3->bool)->bool)) = j` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d DIFF j:real^3->bool`; `UNIONS (x:(real^3->bool)->bool)`]
    CONNECTED_INTER_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `d INTER frontier (UNIONS (x:(real^3->bool)->bool)) = j` THEN SET_TAC[]);;

(* An arc carried by a continuous map injective on a set containing it.     *)

let MOI_S3L9_CHART_ARC = prove
 (`!(phi:real^M->real^N) (hh:real^1->real^M) s.
     arc hh /\ path_image hh SUBSET s /\ phi continuous_on s /\
     (!y z. y IN s /\ z IN s /\ phi y = phi z ==> y = z)
     ==> arc (phi o hh) /\ path_image (phi o hh) = IMAGE phi (path_image hh) /\
         pathstart (phi o hh) = phi (pathstart hh) /\
         pathfinish (phi o hh) = phi (pathfinish hh)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]]);;

(* The arcs of the family in a pseudo-cell, in its chart: one of them and   *)
(* an arc of the chart curve bound a disk missing the centre and the other *)
(* arcs (MOI_S3L9_MINIMAL_DISK).                                             *)

let MOI_S3L9_ARC_BS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs a0 v w
    (phi:real^3->real^2) psi.
     moi_s33_hd t l h e c /\ moi_s33_ltd t l h x d /\ moi_s39_family l e x d cs /\
     ~(?a. a IN cs /\ pl_sphere 1 a /\ DISJOINT a (frontier (UNIONS x))) /\
     a0 IN cs /\ ~(v = w) /\ segment[v,w] IN l /\ a0 SUBSET e(segment[v,w]) /\
     homeomorphism (e(segment[v,w]) DIFF moi_s33_rim t l h v w,ball(vec 0,&1)) (phi,psi) /\
     e(segment[v,w]) INTER UNIONS x SUBSET e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     frontier (UNIONS x) SUBSET UNIONS x /\
     pl_sphere 1 (e(segment[v,w]) INTER frontier (UNIONS x)) /\
     phi(h(midpoint(v,w))) IN inside (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x))) /\
     h(midpoint(v,w)) IN e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     (!y. y IN e(segment[v,w]) DIFF moi_s33_rim t l h v w /\ ~(y IN frontier (UNIONS x))
          ==> (y IN UNIONS x <=>
               phi y IN inside (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x)))))
     ==> ?ab g. ab IN cs /\ ab SUBSET e(segment[v,w]) /\ arc g /\
                path_image g SUBSET IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x)) /\
                {pathstart g,pathfinish g} =
                  IMAGE phi ab INTER IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x)) /\
                ~(phi(h(midpoint(v,w))) IN
                  (IMAGE phi ab UNION path_image g) UNION
                  inside(IMAGE phi ab UNION path_image g)) /\
                (IMAGE phi ab UNION path_image g) UNION inside(IMAGE phi ab UNION path_image g)
                  SUBSET ball(vec 0,&1) /\
                ((IMAGE phi ab UNION path_image g) UNION inside(IMAGE phi ab UNION path_image g))
                  INTER IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x)) = path_image g /\
                (!a. a IN cs /\ a SUBSET e(segment[v,w]) /\ ~(a = ab)
                     ==> DISJOINT (IMAGE phi a)
                           ((IMAGE phi ab UNION path_image g) UNION
                            inside(IMAGE phi ab UNION path_image g)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `v:real^3`; `w:real^3`] MOI_S3L9_LTD_RIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `x:(real^3->bool)->bool`; `d:real^3->bool`]
    MOI_S3L9_LTD_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3)(midpoint(v,w)) IN IMAGE h (UNIONS l)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  ABBREV_TAC `ee = e(segment[v:real^3,w]):real^3->bool` THEN
  ABBREV_TAC `jr = moi_s33_rim t l h v w` THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `gg = IMAGE (phi:real^3->real^2) (ee INTER bx)` THEN
  ABBREV_TAC `pc = (phi:real^3->real^2)((h:real^3->real^3)(midpoint(v,w)))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (ee DIFF jr,ball(vec 0:real^2,&1))
                           (phi:real^3->real^2,psi)`) (concl th))) THEN
  (* the members are arcs *)
  SUBGOAL_THEN `!a. a IN cs ==> a SUBSET (d:real^3->bool) /\ compact a /\ connected a /\
                    ~(a = {}) /\ pl_cell_with_boundary 1 a (a INTER bx) /\
                    ~(a INTER bx = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(pl_sphere 1 (a:real^3->bool) /\ DISJOINT a bx)` (fun th -> REWRITE_TAC[th])
    THENL
     [UNDISCH_TAC `~(?a:real^3->bool. a IN cs /\ pl_sphere 1 a /\ DISJOINT a bx)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `a:real^3->bool`) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN cs /\ a SUBSET ee ==> a SUBSET ee DIFF (jr:real^3->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(a:real^3->bool) IN cs`) o
      check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
    UNDISCH_TAC `d INTER (jr:real^3->bool) = {}` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN SET_TAC[];
    ALL_TAC] THEN
  (* injectivity of the chart *)
  SUBGOAL_THEN `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                      (phi:real^3->real^2) y = phi z ==> y = z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3->bool. a SUBSET ee DIFF jr /\ b SUBSET ee DIFF jr
                    ==> IMAGE (phi:real^3->real^2) a INTER IMAGE phi b = IMAGE phi (a INTER b) /\
                        (IMAGE phi a = IMAGE phi b ==> a = b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                         (phi:real^3->real^2) y = phi z ==> y = z` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET ee DIFF jr` THEN
      UNDISCH_TAC `(b:real^3->bool) SUBSET ee DIFF jr` THEN SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `IMAGE (psi:real^2->real^3)`) THEN
      REWRITE_TAC[GSYM IMAGE_o] THEN
      SUBGOAL_THEN `!s:real^3->bool. s SUBSET ee DIFF jr
                      ==> IMAGE ((psi:real^2->real^3) o (phi:real^3->real^2)) s = s`
      (fun th -> ASM_SIMP_TAC[th]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET ee DIFF jr` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER bx SUBSET ee DIFF (jr:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ee INTER UNIONS x SUBSET ee DIFF (jr:real^3->bool)` THEN
    UNDISCH_TAC `bx SUBSET UNIONS (x:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `gg SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee DIFF jr) = ball(vec 0,&1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`gg:real^2->bool`; `ee INTER bx:real^3->bool`;
                         `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^2`; `psi:real^2->real^3`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`ee DIFF jr:real^3->bool`; `ball(vec 0:real^2,&1)`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3L9_PL_SPHERE1_CIRCLE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the hypotheses of MINIMAL_DISK *)
  SUBGOAL_THEN `!a. a IN cs /\ a SUBSET ee
                    ==> ?g:real^1->real^2. arc g /\ path_image g = IMAGE (phi:real^3->real^2) a /\
                                           IMAGE phi a INTER gg = {pathstart g,pathfinish g}`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM((fun th -> MAP_EVERY ASSUME_TAC
                  (CONJUNCTS (MATCH_MP th (ASSUME `(a:real^3->bool) IN cs`)))) o
      check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `jr:real^3->bool`)) (concl th) &&
        not (can (find_term ((=) `phi:real^3->real^2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `hh:real^1->real^3` STRIP_ASSUME_TAC o
      MATCH_MP MOI_S3L9_CELL1_PL_ARC o check (fun th ->
        concl th = `pl_cell_with_boundary 1 (a:real^3->bool) (a INTER bx)`)) THEN
    MP_TAC(ISPECL [`phi:real^3->real^2`; `hh:real^1->real^3`; `ee DIFF jr:real^3->bool`]
      MOI_S3L9_CHART_ARC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXISTS_TAC `(phi:real^3->real^2) o (hh:real^1->real^3)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "gg" THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `ee INTER bx:real^3->bool`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `(a:real^3->bool) INTER (ee INTER bx) = a INTER bx` SUBST1_TAC THENL
     [UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN cs /\ a SUBSET ee
                    ==> IMAGE (phi:real^3->real^2) a SUBSET ball(vec 0,&1) /\
                        ~(pc IN IMAGE phi a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr /\ a SUBSET d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `jr:real^3->bool`)) (concl th) &&
          not (can (find_term ((=) `phi:real^3->real^2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(a:real^3->bool) IN cs`) o
          check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
            fst(dest_const t) = "pl_cell_with_boundary")) (concl th)))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee DIFF jr) = ball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "pc" THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(h:real^3->real^3)(midpoint(v,w)) = y` ASSUME_TAC THENL
       [UNDISCH_TAC `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                           (phi:real^3->real^2) y = phi z ==> y = z` THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(a:real^3->bool) SUBSET ee DIFF jr` THEN
          UNDISCH_TAC `(y:real^3) IN a` THEN SET_TAC[];
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT d (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
      UNDISCH_TAC `(h:real^3->real^3)(midpoint(v,w)) IN IMAGE h (UNIONS l)` THEN
      UNDISCH_TAC `(h:real^3->real^3)(midpoint(v,w)) = y` THEN
      UNDISCH_TAC `(y:real^3) IN a` THEN UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a y. a IN cs /\ a SUBSET ee /\ y IN a /\ ~((phi:real^3->real^2) y IN gg)
                      ==> y IN d DIFF bx /\ (y IN UNIONS x <=> phi y IN inside gg)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr /\ a SUBSET d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `jr:real^3->bool`)) (concl th) &&
          not (can (find_term ((=) `phi:real^3->real^2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(a:real^3->bool) IN cs`) o
          check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
            fst(dest_const t) = "pl_cell_with_boundary")) (concl th)))];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN ee DIFF jr /\ ~(y IN bx)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(a:real^3->bool) SUBSET ee DIFF jr` THEN
        UNDISCH_TAC `(y:real^3) IN a` THEN SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~((phi:real^3->real^2) y IN gg)` THEN
        REWRITE_TAC[] THEN EXPAND_TAC "gg" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(a:real^3->bool) SUBSET ee` THEN UNDISCH_TAC `(y:real^3) IN a` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET d` THEN UNDISCH_TAC `(y:real^3) IN a` THEN
      SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th) &&
        can (find_term ((=) `UNIONS (x:(real^3->bool)->bool)`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a. a IN cs /\ a SUBSET ee ==> IMAGE (phi:real^3->real^2) a DIFF gg SUBSET inside gg) \/
    (!a. a IN cs /\ a SUBSET ee ==> IMAGE (phi:real^3->real^2) a DIFF gg SUBSET outside gg)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `UNIONS (x:(real^3->bool)->bool)`)) (concl th))) THENL
     [DISJ1_TAC THEN X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
      X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `z:real^2`)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `y:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `gg:real^2->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `d DIFF bx SUBSET UNIONS (x:(real^3->bool)->bool)` THEN SET_TAC[];
      DISJ2_TAC THEN X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
      X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `z:real^2`)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `y:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `gg:real^2->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (d DIFF bx) (UNIONS (x:(real^3->bool)->bool))` THEN
      UNDISCH_TAC `~((phi:real^3->real^2) y IN gg)` THEN
      REWRITE_TAC[OUTSIDE_INSIDE] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {IMAGE (phi:real^3->real^2) a | a | a IN cs /\ a SUBSET ee} /\
                ~({IMAGE (phi:real^3->real^2) a | a | a IN cs /\ a SUBSET ee} = {}) /\
                pairwise DISJOINT {IMAGE (phi:real^3->real^2) a | a | a IN cs /\ a SUBSET ee}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family];
        SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (phi:real^3->real^2) a0` THEN EXISTS_TAC `a0:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `a:real^3->bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `b:real^3->bool` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^3->bool) SUBSET ee DIFF jr /\ b SUBSET ee DIFF jr`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `jr:real^3->bool`)) (concl th) &&
          not (can (find_term ((=) `phi:real^3->real^2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(a:real^3->bool = b)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(IMAGE (phi:real^3->real^2) a = IMAGE phi b)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (a:real^3->bool) b` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN
        REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `b:real^3->bool`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      UNDISCH_TAC `DISJOINT (a:real^3->bool) b` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real^2->bool`; `pc:real^2`;
                 `{IMAGE (phi:real^3->real^2) a | a | a IN cs /\ a SUBSET ee}`]
    MOI_S3L9_MINIMAL_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FORALL_IN_GSPEC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^2->bool` (X_CHOOSE_THEN `g:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(b:real^2->bool) IN {IMAGE (phi:real^3->real^2) a | a | a IN cs /\ a SUBSET ee}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ab:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b:real^2->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`ab:real^3->bool`; `g:real^1->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `g:real^1->real^2`)) (concl th))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(a:real^3->bool = ab)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `ab:real^3->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `jr:real^3->bool`)) (concl th) &&
          not (can (find_term ((=) `phi:real^3->real^2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* The chart disk of the arc step in real^3: a PL disk in the pseudo-cell   *)
(* bounded by the arc ab of the family and an arc ht of the trace, meeting  *)
(* d only in ab and Bd X only in ht.                                         *)

let MOI_S3L9_ARC_DISK = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs a0 v w
    (phi:real^3->real^2) psi.
     moi_s3l9i_drec /\
     moi_s33_hd t l h e c /\ moi_s33_ltd t l h x d /\ moi_s39_family l e x d cs /\
     ~(?a. a IN cs /\ pl_sphere 1 a /\ DISJOINT a (frontier (UNIONS x))) /\
     a0 IN cs /\ ~(v = w) /\ segment[v,w] IN l /\ a0 SUBSET e(segment[v,w]) /\
     homeomorphism (e(segment[v,w]) DIFF moi_s33_rim t l h v w,ball(vec 0,&1)) (phi,psi) /\
     e(segment[v,w]) INTER UNIONS x SUBSET e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     frontier (UNIONS x) SUBSET UNIONS x /\
     pl_sphere 1 (e(segment[v,w]) INTER frontier (UNIONS x)) /\
     phi(h(midpoint(v,w))) IN inside (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x))) /\
     h(midpoint(v,w)) IN e(segment[v,w]) DIFF moi_s33_rim t l h v w /\
     (!y. y IN e(segment[v,w]) DIFF moi_s33_rim t l h v w /\ ~(y IN frontier (UNIONS x))
          ==> (y IN UNIONS x <=>
               phi y IN inside (IMAGE phi (e(segment[v,w]) INTER frontier (UNIONS x)))))
     ==> ?ab hab ht dd.
           ab IN cs /\ ab SUBSET e(segment[v,w]) /\
           arc hab /\ pl_map_on (interval[vec 0,vec 1]) hab /\ path_image hab = ab /\
           ab INTER frontier (UNIONS x) = {pathstart hab,pathfinish hab} /\
           arc ht /\ pl_map_on (interval[vec 0,vec 1]) ht /\
           pathstart ht = pathstart hab /\ pathfinish ht = pathfinish hab /\
           path_image ht SUBSET frontier (UNIONS x) /\
           ab INTER path_image ht = {pathstart hab,pathfinish hab} /\
           pl_cell_with_boundary 2 dd (ab UNION path_image ht) /\
           dd SUBSET e(segment[v,w]) /\ dd SUBSET moi_s33_ww t l h /\
           dd INTER d = ab /\ dd INTER frontier (UNIONS x) = path_image ht`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `cs:(real^3->bool)->bool`; `a0:real^3->bool`; `v:real^3`; `w:real^3`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`] MOI_S3L9_ARC_BS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ab:real^3->bool` (X_CHOOSE_THEN `g:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `v:real^3`; `w:real^3`] MOI_S3L9_LTD_RIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`] MOI_S3L9_HD_PC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `ab:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(pl_sphere 1 (ab:real^3->bool) /\ DISJOINT ab (frontier (UNIONS x)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(?a:real^3->bool. a IN cs /\ pl_sphere 1 a /\
                                    DISJOINT a (frontier (UNIONS x)))` THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `ab:real^3->bool`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `ee = e(segment[v:real^3,w]):real^3->bool` THEN
  ABBREV_TAC `jr = moi_s33_rim t l h v w` THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `gg = IMAGE (phi:real^3->real^2) (ee INTER bx)` THEN
  ABBREV_TAC `pc = (phi:real^3->real^2)((h:real^3->real^3)(midpoint(v,w)))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (ee DIFF jr,ball(vec 0:real^2,&1))
                           (phi:real^3->real^2,psi)`) (concl th))) THEN
  SUBGOAL_THEN `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                      (phi:real^3->real^2) y = phi z ==> y = z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x. x IN ee DIFF jr ==> (psi:real^2->real^3)((phi:real^3->real^2) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER bx SUBSET ee DIFF (jr:real^3->bool) /\
                (ab:real^3->bool) SUBSET ee DIFF jr` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ee INTER UNIONS x SUBSET ee DIFF (jr:real^3->bool)` THEN
      UNDISCH_TAC `bx SUBSET UNIONS (x:(real^3->bool)->bool)` THEN SET_TAC[];
      UNDISCH_TAC `d INTER (jr:real^3->bool) = {}` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET ee` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the arc ab *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `hab:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S3L9_CELL1_PL_ARC o check (fun th ->
      concl th = `pl_cell_with_boundary 1 (ab:real^3->bool) (ab INTER bx)`)) THEN
  ABBREV_TAC `p = pathstart(hab:real^1->real^3)` THEN
  ABBREV_TAC `q = pathfinish(hab:real^1->real^3)` THEN
  SUBGOAL_THEN `~(p:real^3 = q) /\ p IN ee INTER bx /\ q IN ee INTER bx` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      MATCH_MP_TAC ARC_DISTINCT_ENDS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET ee` THEN SET_TAC[];
      UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET ee` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the two arcs of the trace between p and q *)
  FIRST_ASSUM(X_CHOOSE_THEN `gam:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP o check (fun th ->
      concl th = `pl_sphere 1 (ee INTER bx:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`gam:real^1->real^3`; `p:real^3`; `q:real^3`] MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^1->real^3` (X_CHOOSE_THEN `t2:real^1->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `path_image t1 SUBSET ee DIFF (jr:real^3->bool) /\
                path_image t2 SUBSET ee DIFF (jr:real^3->bool) /\
                path_image t1 SUBSET ee INTER bx /\ path_image t2 SUBSET ee INTER bx`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image t1 UNION path_image t2 = path_image(gam:real^1->real^3)` THEN
    UNDISCH_TAC `path_image(gam:real^1->real^3) = ee INTER bx` THEN
    UNDISCH_TAC `ee INTER bx SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^2) continuous_on ee DIFF jr` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^2`; `t1:real^1->real^3`; `ee DIFF jr:real^3->bool`]
    MOI_S3L9_CHART_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^2`; `t2:real^1->real^3`; `ee DIFF jr:real^3->bool`]
    MOI_S3L9_CHART_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^2) ab INTER gg = {phi p,phi q} /\
                IMAGE (phi:real^3->real^2) (path_image t1) INTER IMAGE phi (path_image t2) =
                {phi p,phi q} /\
                IMAGE phi (path_image t1) UNION IMAGE phi (path_image t2) = gg`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "gg" THEN
      UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET ee` THEN
      UNDISCH_TAC `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                         (phi:real^3->real^2) y = phi z ==> y = z` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET ee DIFF jr` THEN
      UNDISCH_TAC `ee INTER bx SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `path_image t1 INTER path_image t2 = {p:real^3,q}` THEN
      UNDISCH_TAC `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                         (phi:real^3->real^2) y = phi z ==> y = z` THEN
      UNDISCH_TAC `path_image t1 SUBSET ee DIFF (jr:real^3->bool)` THEN
      UNDISCH_TAC `path_image t2 SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[];
      EXPAND_TAC "gg" THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the chart arc g is the image of one of the two halves *)
  SUBGOAL_THEN `?ht:real^1->real^3. arc ht /\ pl_map_on (interval[vec 0,vec 1]) ht /\
                                    pathstart ht = p /\ pathfinish ht = q /\
                                    path_image ht SUBSET ee INTER bx /\
                                    IMAGE (phi:real^3->real^2) (path_image ht) = path_image g`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(phi:real^3->real^2) o (t1:real^1->real^3)`;
                   `(phi:real^3->real^2) o (t2:real^1->real^3)`; `g:real^1->real^2`]
      MOI_S3L9_ARC_IN_CIRCLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `t1:real^1->real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t2:real^1->real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `tt = path_image(ht:real^1->real^3)` THEN
  ABBREV_TAC `dm = (IMAGE (phi:real^3->real^2) ab UNION path_image g) UNION
                   inside(IMAGE phi ab UNION path_image g)` THEN
  SUBGOAL_THEN `ab INTER tt = {p:real^3,q} /\ tt SUBSET bx /\
                ab UNION tt SUBSET ee DIFF (jr:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ht:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `ht:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN
    UNDISCH_TAC `tt SUBSET ee INTER (bx:real^3->bool)` THEN
    UNDISCH_TAC `(ab:real^3->bool) SUBSET ee DIFF jr` THEN
    UNDISCH_TAC `ee INTER bx SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (ab UNION tt:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hab:real^1->real^3`; `ht:real^1->real^3`] MOI_SLV_ARCS_SPHERE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^2) (ab UNION tt) = IMAGE phi ab UNION path_image g`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
  (* the centre is not in the chart disk *)
  SUBGOAL_THEN `~((h:real^3->real^3)(midpoint(v,w)) IN IMAGE (psi:real^2->real^3) dm)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `pc:real^2 = z` SUBST_ALL_TAC THENL
     [EXPAND_TAC "pc" THEN
      UNDISCH_TAC `(h:real^3->real^3)(midpoint(v,w)) = (psi:real^2->real^3) z` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `!y. y IN ball(vec 0,&1)
                       ==> (phi:real^3->real^2)((psi:real^2->real^3) y) = y` THEN
      UNDISCH_TAC `dm SUBSET ball(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(z:real^2) IN dm` THEN SET_TAC[];
      UNDISCH_TAC `~((z:real^2) IN dm)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ee:real^3->bool`; `jr:real^3->bool`; `(h:real^3->real^3)(midpoint(v,w))`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`; `ab UNION tt:real^3->bool`]
    MOI_S3L9_CELL_PL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`ee:real^3->bool`; `jr:real^3->bool`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`; `ab UNION tt:real^3->bool`]
    MOI_S3L9_CELL_DISK) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_S3L9_PL_SPHERE1_CIRCLE]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `dd = IMAGE (psi:real^2->real^3) dm` THEN
  SUBGOAL_THEN `dd SUBSET moi_s33_ww t l h` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_EDGE_WW THEN
    MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                          `v:real^3`; `w:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* points of the chart disk *)
  SUBGOAL_THEN `!y. y IN dd ==> ?z. z IN dm /\
                                    z IN ball(vec 0,&1) /\ (phi:real^3->real^2) y = z /\
                                    y IN ee DIFF jr`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN EXPAND_TAC "dd" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `dm SUBSET ball(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(z:real^2) IN dm` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN ball(vec 0,&1)` THEN
      UNDISCH_TAC `!y. y IN ball(vec 0,&1)
                       ==> (phi:real^3->real^2)((psi:real^2->real^3) y) = y` THEN
      MESON_TAC[];
      UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,&1)) = ee DIFF jr` THEN
      UNDISCH_TAC `(z:real^2) IN ball(vec 0,&1)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd INTER bx = tt:real^3->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN dd`) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `dd:real^3->bool`)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^2) IN path_image g` MP_TAC THENL
       [UNDISCH_TAC `(dm:real^2->bool) INTER gg = path_image (g:real^1->real^2)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (phi:real^3->real^2) (ee INTER bx) = gg` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(phi:real^3->real^2) y = z` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(y:real^3) IN ee DIFF jr` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^2) tt = path_image g` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `!y z. y IN ee DIFF jr /\ z IN ee DIFF jr /\
                         (phi:real^3->real^2) y = phi z ==> y = z` THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `ab UNION tt SUBSET ee DIFF (jr:real^3->bool)` THEN
        UNDISCH_TAC `(y':real^3) IN tt` THEN SET_TAC[];
        ASM_MESON_TAC[]];
      UNDISCH_TAC `ab UNION tt SUBSET (dd:real^3->bool)` THEN
      UNDISCH_TAC `tt SUBSET (bx:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC(SET_RULE
     `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd INTER d = ab:real^3->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN dd`) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `dd:real^3->bool`)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?a. a IN cs /\ (y:real^3) IN a` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN REWRITE_TAC[moi_s39_family] THEN
        STRIP_TAC THEN
        UNDISCH_TAC `d INTER moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = UNIONS cs` THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(y:real^3) IN moi_s39_pcs l e` MP_TAC THENL
         [UNDISCH_TAC `ee SUBSET moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
          UNDISCH_TAC `(y:real^3) IN ee DIFF jr` THEN SET_TAC[];
          MESON_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC `a:real^3->bool = ab` THENL
       [UNDISCH_TAC `(y:real^3) IN a` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^3->bool) SUBSET ee` ASSUME_TAC THENL
       [EXPAND_TAC "ee" THEN MATCH_MP_TAC MOI_S3L9_MEMBER_IN_EDGE THEN
        MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                              `h:real^3->real^3`;
                              `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                              `d:real^3->bool`; `cs:(real^3->bool)->bool`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN a` THEN
        UNDISCH_TAC `(y:real^3) IN ee DIFF jr` THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `dm:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(phi:real^3->real^2) y = z` THEN
      UNDISCH_TAC `(z:real^2) IN dm` THEN UNDISCH_TAC `(y:real^3) IN a` THEN SET_TAC[];
      UNDISCH_TAC `ab UNION tt SUBSET (dd:real^3->bool)` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ab:real^3->bool`; `hab:real^1->real^3`; `ht:real^1->real^3`;
                        `dd:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `dd SUBSET ee DIFF (jr:real^3->bool)` THEN SET_TAC[]);;


(* One side of the cross-cut: the side disk glued to the chart disk is a   *)
(* loop theorem disk if its boundary is not contractible in Bd X; pushing  *)
(* it off near the chart disk removes ab and the arcs on the other side.   *)

let MOI_S3L9_ARC_SIDE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs
    (S:real^2->bool) fs gs ab hab (ht:real^1->real^3) dd v w (al:real^1->real^2) b u u'.
     moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\
     &2 simplex S /\ pl_homeomorphism (S,d) (fs,gs) /\
     IMAGE fs (relative_frontier S) = d INTER frontier (UNIONS x) /\
     ab IN cs /\ ~(v = w) /\ segment[v,w] IN l /\ ab SUBSET e(segment[v,w]) /\
     arc hab /\ pl_map_on (interval[vec 0,vec 1]) hab /\ path_image hab = ab /\
     ab INTER frontier (UNIONS x) = {pathstart hab,pathfinish hab} /\
     path_image ht SUBSET frontier (UNIONS x) /\
     ab INTER path_image ht = {pathstart hab,pathfinish hab} /\
     pl_cell_with_boundary 2 dd (ab UNION path_image ht) /\
     dd SUBSET e(segment[v,w]) /\ dd SUBSET moi_s33_ww t l h /\
     dd INTER d = ab /\ dd INTER frontier (UNIONS x) = path_image ht /\
     arc al /\ pl_map_on (interval[vec 0,vec 1]) al /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     pathstart b = gs(pathstart hab) /\ pathfinish b = gs(pathfinish hab) /\
     pathstart al = pathstart b /\ pathfinish al = pathfinish b /\
     path_image al INTER path_image b = {pathstart b,pathfinish b} /\
     IMAGE gs ab = path_image b /\
     pl_cell_with_boundary 2 u (path_image al UNION path_image b) /\
     (path_image al UNION path_image b) UNION inside(path_image al UNION path_image b) = u /\
     u SUBSET S /\ u INTER relative_frontier S = path_image al /\
     u UNION u' = S /\ u INTER u' = path_image b /\
     (!s. connected s /\ s SUBSET S /\ s INTER path_image b = {}
          ==> s SUBSET u \/ s SUBSET u') /\
     ~(?a. homotopic_with (\q. T)
             (subtopology euclidean (IMAGE fs (path_image al) UNION path_image ht),
              subtopology euclidean (frontier (UNIONS x))) (\y. y) (\y. a))
     ==> ?d' cs'. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs' /\ cs' PSUBSET cs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `pcs = moi_s39_pcs l (e:(real^3->bool)->real^3->bool)` THEN
  ABBREV_TAC `ww = moi_s33_ww t l (h:real^3->real^3)` THEN
  ABBREV_TAC `p = pathstart(hab:real^1->real^3)` THEN
  ABBREV_TAC `q = pathfinish(hab:real^1->real^3)` THEN
  ABBREV_TAC `tt = path_image(ht:real^1->real^3)` THEN
  ABBREV_TAC `pa = path_image(al:real^1->real^2)` THEN
  ABBREV_TAC `pb = path_image(b:real^1->real^2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `ab:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!a. a IN cs ==> a SUBSET (d:real^3->bool) /\ a SUBSET pcs /\ compact a /\
                    connected a /\ ~(a = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `a:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* basic facts on the cross-cut *)
  SUBGOAL_THEN `(p:real^3) IN ab /\ q IN ab /\ p IN d /\ q IN d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pa SUBSET (S:real^2->bool) /\ pb SUBSET S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(pa UNION pb) UNION inside (pa UNION pb) = (u:real^2->bool)` THEN
      UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) ab = pb` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) d = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) pb = ab` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gs:real^3->real^2) ab = pb` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN EXISTS_TAC `d:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fs:real^2->real^3) ((gs:real^3->real^2) p) = p /\ fs (gs q) = q`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) pa INTER ab = {p,q}` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (fs:real^2->real^3) pa INTER IMAGE fs pb = IMAGE fs (pa INTER pb)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
      UNDISCH_TAC `pa SUBSET (S:real^2->bool)` THEN UNDISCH_TAC `pb SUBSET (S:real^2->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) pb = ab` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN IMAGE fs pa /\ q IN IMAGE (fs:real^2->real^3) pa /\
                p IN tt /\ q IN tt /\ tt SUBSET bx`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) pa INTER ab = {p,q}` THEN
    UNDISCH_TAC `ab INTER tt = {p:real^3,q}` THEN
    UNDISCH_TAC `tt SUBSET (bx:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the side disk d1 and the glued disk ds *)
  MP_TAC(ISPECL [`S:real^2->bool`; `d:real^3->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                 `u:real^2->bool`; `pa UNION pb:real^2->bool`] MOI_S3L9_MODEL_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_UNION] THEN STRIP_TAC THEN
  ABBREV_TAC `d1 = IMAGE (fs:real^2->real^3) u` THEN
  SUBGOAL_THEN `d1 SUBSET (d:real^3->bool) /\ ab SUBSET d1 /\ IMAGE (fs:real^2->real^3) pa SUBSET d1 /\
                d1 INTER bx = IMAGE fs pa`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "d1" THEN UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) pb = ab` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      EXPAND_TAC "d1" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `(pa UNION pb) UNION inside (pa UNION pb) = (u:real^2->bool)` THEN SET_TAC[];
      EXPAND_TAC "d1" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `(pa UNION pb) UNION inside (pa UNION pb) = (u:real^2->bool)` THEN SET_TAC[];
      SUBGOAL_THEN `d1 INTER bx = d1 INTER IMAGE (fs:real^2->real^3) (relative_frontier S)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `IMAGE (fs:real^2->real^3) (relative_frontier S) = d INTER bx` THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `d1 SUBSET (d:real^3->bool)` MP_TAC THENL
         [EXPAND_TAC "d1" THEN UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
          SET_TAC[]];
        ALL_TAC] THEN
      EXPAND_TAC "d1" THEN
      SUBGOAL_THEN `IMAGE (fs:real^2->real^3) u INTER IMAGE fs (relative_frontier S) =
                    IMAGE fs (u INTER relative_frontier S)` SUBST1_TAC THENL
       [UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
        UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN
        UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `IMAGE (fs:real^2->real^3) pa UNION ab`;
                 `dd:real^3->bool`; `ab UNION tt:real^3->bool`; `ab:real^3->bool`;
                 `{p:real^3,q}`] MOI_S3L9_DISK_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `hab:real^1->real^3` MOI_S4O_ARC_CELL) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `dd INTER d = ab:real^3->bool` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d1` THEN
      UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN SET_TAC[];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((IMAGE (fs:real^2->real^3) pa UNION ab) UNION (ab UNION tt)) DIFF
                (ab DIFF {p,q}) = IMAGE fs pa UNION tt` SUBST1_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) pa INTER ab = {p,q}` THEN
    UNDISCH_TAC `ab INTER tt = {p:real^3,q}` THEN
    UNDISCH_TAC `(p:real^3) IN IMAGE (fs:real^2->real^3) pa` THEN
    UNDISCH_TAC `(q:real^3) IN IMAGE (fs:real^2->real^3) pa` THEN SET_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `ds = d1 UNION dd:real^3->bool` THEN
  SUBGOAL_THEN `ds INTER bx = IMAGE (fs:real^2->real^3) pa UNION tt /\ ds SUBSET ww`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN CONJ_TAC THENL
     [UNDISCH_TAC `d1 INTER bx = IMAGE (fs:real^2->real^3) pa` THEN
      UNDISCH_TAC `dd INTER bx = tt:real^3->bool` THEN SET_TAC[];
      UNDISCH_TAC `dd SUBSET (ww:real^3->bool)` THEN UNDISCH_TAC `d SUBSET (ww:real^3->bool)` THEN
      UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s33_ltd t l h x ds` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_ltd] THEN
    UNDISCH_TAC `pl_cell_with_boundary 2 ds (IMAGE (fs:real^2->real^3) pa UNION tt)` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) pa UNION tt = IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the members kept: those on the side of d1 other than ab *)
  ABBREV_TAC `cs' = {a:real^3->bool | a IN cs /\ ~(a = ab) /\ a SUBSET d1}` THEN
  ABBREV_TAC `rr = UNIONS (cs':(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `!a:real^3->bool. a IN cs' <=> a IN cs /\ ~(a = ab) /\ a SUBSET d1`
  ASSUME_TAC THENL
   [EXPAND_TAC "cs'" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (cs':(real^3->bool)->bool) /\ cs' SUBSET cs /\ ~(ab IN cs')`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family];
        ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN cs /\ ~(a = ab) ==> DISJOINT (a:real^3->bool) ab` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    REWRITE_TAC[moi_s39_family; pairwise] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rr SUBSET d1 /\ rr SUBSET pcs /\ compact rr /\ DISJOINT rr (ab:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[];
      REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[DISJOINT]];
    ALL_TAC] THEN
  (* members not kept and other than ab lie on the other side *)
  SUBGOAL_THEN `!a. a IN cs /\ ~(a = ab) /\ ~(a SUBSET d1)
                    ==> DISJOINT (IMAGE (gs:real^3->real^2) a) u`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET d /\ connected a /\ DISJOINT a ab`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `connected (IMAGE (gs:real^3->real^2) a) /\ IMAGE gs a SUBSET S /\
                  IMAGE gs a INTER pb = {}`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        UNDISCH_TAC `IMAGE (gs:real^3->real^2) d = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `IMAGE (gs:real^3->real^2) ab = pb` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MP_TAC(ISPECL [`gs:real^3->real^2`; `fs:real^2->real^3`; `a:real^3->bool`;
                       `ab:real^3->bool`; `d:real^3->bool`] MOI_S3L9_IMAGE_DISJOINT_INJ) THEN
        ASM_REWRITE_TAC[DISJOINT]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (gs:real^3->real^2) a` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `u':real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `~((a:real^3->bool) SUBSET d1)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN EXPAND_TAC "d1" THEN
      SUBGOAL_THEN `(a:real^3->bool) = IMAGE (fs:real^2->real^3) (IMAGE (gs:real^3->real^2) a)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN
        EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `u INTER u' = pb:real^2->bool` THEN
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) a INTER pb = {}` THEN
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) a SUBSET u'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d INTER pcs = UNIONS (cs:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pcs" THEN UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    SIMP_TAC[moi_s39_family];
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 INTER pcs SUBSET rr UNION (ab:real^3->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?a. a IN cs /\ (y:real^3) IN a` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `d INTER pcs = UNIONS (cs:(real^3->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3) IN d` MP_TAC THENL
       [UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN UNDISCH_TAC `(y:real^3) IN d1` THEN
        SET_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `a:real^3->bool = ab` THENL
     [UNDISCH_TAC `(y:real^3) IN a` THEN ASM_REWRITE_TAC[IN_UNION] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(a:real^3->bool) SUBSET d1` THENL
     [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN EXPAND_TAC "rr" THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `u:real^2->bool`)) (concl th) &&
      can (find_term ((=) `d1:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN d1` THEN EXPAND_TAC "d1" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(gs:real^3->real^2) ((fs:real^2->real^3) z) = z` ASSUME_TAC THENL
     [UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
      UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN UNDISCH_TAC `(z:real^2) IN u` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(gs:real^3->real^2) ((fs:real^2->real^3) z) = z` THEN
    UNDISCH_TAC `((fs:real^2->real^3) z) IN a` THEN UNDISCH_TAC `(z:real^2) IN u` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the collar of the cross-cut on the side u (MOI_S3L9_ARC_COLLAR) *)
  SUBGOAL_THEN `compact (IMAGE (gs:real^3->real^2) rr) /\ DISJOINT pb (IMAGE gs rr)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `d:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rr SUBSET (d1:real^3->bool)` THEN UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) ab = pb` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_S3L9_IMAGE_DISJOINT_INJ THEN
      MAP_EVERY EXISTS_TAC [`fs:real^2->real^3`; `d:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT rr (ab:real^3->bool)` THEN
      UNDISCH_TAC `rr SUBSET (d1:real^3->bool)` THEN UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pa UNION pb:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L9_PL_SPHERE1_CIRCLE THEN
    MP_TAC(ISPECL [`al:real^1->real^2`; `b:real^1->real^2`] MOI_SFR_ARCS_SPHERE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pa UNION pb:real^2->bool`; `b:real^1->real^2`;
                 `IMAGE (gs:real^3->real^2) rr`] MOI_S3L9_ARC_COLLAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aa:real^2->bool` (X_CHOOSE_THEN `ww0:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  (* the image of the collar lies in one piece c v1 at an end of the edge *)
  SUBGOAL_THEN `(aa:real^2->bool) SUBSET S /\ ~(aa = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `aa SUBSET u DIFF (pb:real^2->bool)` THEN
      UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `pb SUBSET closure (aa:real^2->bool)` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY] THEN
      EXPAND_TAC "pb" THEN REWRITE_TAC[PATH_IMAGE_NONEMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) aa SUBSET d1 /\ DISJOINT (IMAGE fs aa) ab /\
                DISJOINT (IMAGE fs aa) rr`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "d1" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `aa SUBSET u DIFF (pb:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) pb = ab` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_S3L9_IMAGE_DISJOINT_INJ THEN
      MAP_EVERY EXISTS_TAC [`gs:real^3->real^2`; `S:real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aa SUBSET u DIFF (pb:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (aa:real^2->bool) (IMAGE (gs:real^3->real^2) rr)` THEN
      UNDISCH_TAC `!x. x IN S ==> (gs:real^3->real^2)((fs:real^2->real^3) x) = x` THEN
      UNDISCH_TAC `(aa:real^2->bool) SUBSET S` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (fs:real^2->real^3) aa) pcs /\ connected (IMAGE fs aa) /\
                ~(IMAGE fs aa = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `d1 INTER pcs SUBSET rr UNION (ab:real^3->bool)` THEN
      UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET d1` THEN
      UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) ab` THEN
      UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) rr` THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `IMAGE (fs:real^2->real^3) aa`]
    MOI_S3L9_CONNECTED_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `d SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (fs:real^2->real^3) aa) pcs` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET d1` THEN
    UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `closed ((c:real^3->real^3->bool) v1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v1:real^3`] MOI_S3L9_HD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ab:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) pb = ab` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (fs:real^2->real^3) (closure aa)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`; `v1:real^3`]
      MOI_S3L9_PIECE_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(ab:real^3->bool = {})` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `v:real^3`; `w:real^3`] MOI_S3L9_EDGE_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    UNDISCH_TAC `(dd:real^3->bool) SUBSET e(segment[v:real^3,w])` THEN
    UNDISCH_TAC `e(segment[v:real^3,w]) SUBSET (c:real^3->real^3->bool) v` THEN
    UNDISCH_TAC `e(segment[v:real^3,w]) SUBSET (c:real^3->real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the open set pushed off *)
  SUBGOAL_THEN `compact (u:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `u:real^2->bool`; `pa UNION pb:real^2->bool`] MOI_CEL_CELL_COMPACT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (fs:real^2->real^3) (u DIFF ww0))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `uu = (ww:real^3->bool) DIFF
                   (rr UNION IMAGE (fs:real^2->real^3) (u DIFF ww0))` THEN
  SUBGOAL_THEN `open (uu:real^3->bool) /\ uu SUBSET ww /\ DISJOINT uu rr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "uu" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`] MOI_S3L9_WW_OPEN) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd SUBSET (uu:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fs:real^2->real^3`; `gs:real^3->real^2`; `pb:real^2->bool`;
                   `u DIFF ww0:real^2->bool`; `S:real^2->bool`] MOI_S3L9_IMAGE_DISJOINT_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `pb SUBSET (ww0:real^2->bool)` THEN
      UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (u DIFF ww0) SUBSET d` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (fs:real^2->real^3) S = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN UNDISCH_TAC `(u:real^2->bool) SUBSET S` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "uu" THEN
    UNDISCH_TAC `dd INTER d = ab:real^3->bool` THEN
    UNDISCH_TAC `dd SUBSET (ww:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT rr (ab:real^3->bool)` THEN
    UNDISCH_TAC `rr SUBSET (d1:real^3->bool)` THEN UNDISCH_TAC `d1 SUBSET (d:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER uu SUBSET (c:real^3->real^3->bool) v1` ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN EXPAND_TAC "uu" THEN EXPAND_TAC "d1" THEN
    UNDISCH_TAC `dd SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) aa SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `(ab:real^3->bool) SUBSET (c:real^3->real^3->bool) v1` THEN
    UNDISCH_TAC `IMAGE (fs:real^2->real^3) pb = ab` THEN
    UNDISCH_TAC `ww0 INTER u SUBSET aa UNION (pb:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER pcs SUBSET rr UNION (dd:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ds" THEN
    UNDISCH_TAC `d1 INTER pcs SUBSET rr UNION (ab:real^3->bool)` THEN
    UNDISCH_TAC `dd INTER d = ab:real^3->bool` THEN UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (dd:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `dd:real^3->bool`; `ab UNION tt:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds INTER uu INTER pcs SUBSET (dd:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ds INTER pcs SUBSET rr UNION (dd:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (uu:real^3->bool) rr` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the push *)
  UNDISCH_TAC `moi_s3l9i_push` THEN REWRITE_TAC[moi_s3l9i_push] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `v1:real^3`; `ds:real^3->bool`; `uu:real^3->bool`;
    `dd:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->bool` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `moi_s39_pcs l (e:(real^3->bool)->real^3->bool) = pcs`])) THEN
  SUBGOAL_THEN `(ds DIFF uu) INTER pcs = rr:real^3->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `ds INTER pcs SUBSET rr UNION (dd:real^3->bool)` THEN
      UNDISCH_TAC `dd SUBSET (uu:real^3->bool)` THEN SET_TAC[];
      EXPAND_TAC "ds" THEN
      UNDISCH_TAC `rr SUBSET (d1:real^3->bool)` THEN
      UNDISCH_TAC `rr SUBSET (pcs:real^3->bool)` THEN
      UNDISCH_TAC `DISJOINT (uu:real^3->bool) rr` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s39_family l e x d' cs'` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s39_family l e x d cs` THEN REWRITE_TAC[moi_s39_family] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `a:real^3->bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(cs':(real^3->bool)->bool) SUBSET cs` THEN
      UNDISCH_TAC `(a:real^3->bool) IN cs'` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d':real^3->bool`; `cs':(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[PSUBSET] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((ab:real^3->bool) IN cs')` THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `cs':(real^3->bool)->bool = cs`)) THEN
  ASM_REWRITE_TAC[]);;



(* The arc step: with no circles, an arc of the family can be removed.      *)

let MOI_S3L9_ARC_STEP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs.
     moi_s3l9i_drec /\ moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\ ~(cs = {}) /\
     ~(?a0. a0 IN cs /\ pl_sphere 1 a0 /\ DISJOINT a0 (frontier (UNIONS x)))
     ==> ?d' cs'. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs' /\ cs' PSUBSET cs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a0:real^3->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                 `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                 `a0:real^3->bool`] MOI_S3L9_MEMBER_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `a0:real^3->bool`] MOI_S3L9_CONN_PCS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `v:real^3`; `w:real^3`]
    MOI_S3L9_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_THEN `psi:real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] MOI_S3L9_X_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^3`; `w:real^3`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "disk_with_boundary")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `cs:(real^3->bool)->bool`; `a0:real^3->bool`; `v:real^3`; `w:real^3`;
                 `phi:real^3->real^2`; `psi:real^2->real^3`] MOI_S3L9_ARC_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ab:real^3->bool` (X_CHOOSE_THEN `hab:real^1->real^3`
    (X_CHOOSE_THEN `ht:real^1->real^3` (X_CHOOSE_THEN `dd:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_LTD_BASIC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L9_PLANAR_MODEL o check (fun th ->
    (let c,args = strip_comb(concl th) in is_const c && fst(dest_const c) = "pl_cell_with_boundary" &&
     length args = 3 && el 1 args = `d:real^3->bool`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `fs:real^2->real^3`
    (X_CHOOSE_THEN `gs:real^3->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `bx = frontier (UNIONS (x:(real^3->bool)->bool))` THEN
  ABBREV_TAC `p = pathstart(hab:real^1->real^3)` THEN
  ABBREV_TAC `q = pathfinish(hab:real^1->real^3)` THEN
  ABBREV_TAC `tt = path_image(ht:real^1->real^3)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L9_PLANE_SIMPLEX) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `relative_frontier S = frontier (S:real^2->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (term_match [] `pl_homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (S:real^2->bool,d:real^3->bool) (fs:real^2->real^3,gs)`) (concl th))) THEN
  SUBGOAL_THEN `(ab:real^3->bool) SUBSET d /\ ~(p:real^3 = q) /\ p IN ab /\ q IN ab /\
                p IN j /\ q IN j /\ ab INTER j = {p,q}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(ab:real^3->bool) SUBSET d` ASSUME_TAC THENL
     [UNDISCH_TAC `dd INTER d = ab:real^3->bool` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      MATCH_MP_TAC ARC_DISTINCT_ENDS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ab INTER bx = {p:real^3,q}` THEN UNDISCH_TAC `d INTER bx = j:real^3->bool` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the two arcs of the boundary between p and q *)
  FIRST_ASSUM(X_CHOOSE_THEN `gam:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP o check (fun th -> concl th = `pl_sphere 1 (j:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`gam:real^1->real^3`; `p:real^3`; `q:real^3`] MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^1->real^3` (X_CHOOSE_THEN `k2:real^1->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `path_image k1 SUBSET (j:real^3->bool) /\ path_image k2 SUBSET j /\
                path_image k1 SUBSET (d:real^3->bool) /\ path_image k2 SUBSET d /\
                path_image k1 UNION path_image k2 = j`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image k1 UNION path_image k2 = path_image(gam:real^1->real^3)` THEN
    UNDISCH_TAC `path_image(gam:real^1->real^3) = j` THEN
    UNDISCH_TAC `j SUBSET (d:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y z. y IN d /\ z IN d /\ (gs:real^3->real^2) y = gs z ==> y = z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!y. y IN d ==> (fs:real^2->real^3)((gs:real^3->real^2) y) = y` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* their images in the planar model, and the cross-cut *)
  MP_TAC(ISPECL [`gs:real^3->real^2`; `k1:real^1->real^3`; `d:real^3->bool`]
    MOI_S3L9_CHART_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`gs:real^3->real^2`; `k2:real^1->real^3`; `d:real^3->bool`]
    MOI_S3L9_CHART_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`gs:real^3->real^2`; `hab:real^1->real^3`; `d:real^3->bool`]
    MOI_S3L9_CHART_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_map_on (interval[vec 0,vec 1]) ((gs:real^3->real^2) o (k1:real^1->real^3)) /\
                pl_map_on (interval[vec 0,vec 1]) ((gs:real^3->real^2) o (k2:real^1->real^3)) /\
                pl_map_on (interval[vec 0,vec 1]) ((gs:real^3->real^2) o (hab:real^1->real^3))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[GSYM path_image];
    ALL_TAC] THEN
  ABBREV_TAC `a1 = (gs:real^3->real^2) o (k1:real^1->real^3)` THEN
  ABBREV_TAC `a2 = (gs:real^3->real^2) o (k2:real^1->real^3)` THEN
  ABBREV_TAC `b = (gs:real^3->real^2) o (hab:real^1->real^3)` THEN
  SUBGOAL_THEN `IMAGE (gs:real^3->real^2) j = relative_frontier S` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fs:real^2->real^3) (relative_frontier S) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image a1 INTER path_image a2 = {(gs:real^3->real^2) p,gs q} /\
                path_image a1 UNION path_image a2 = relative_frontier S /\
                path_image b INTER relative_frontier S = {(gs:real^3->real^2) p,gs q} /\
                path_image a1 INTER path_image b = {(gs:real^3->real^2) p,gs q} /\
                path_image a2 INTER path_image b = {(gs:real^3->real^2) p,gs q} /\
                path_image b SUBSET S`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image k1 INTER path_image k2 = {p:real^3,q}` THEN
      UNDISCH_TAC `!y z. y IN d /\ z IN d /\ (gs:real^3->real^2) y = gs z ==> y = z` THEN
      UNDISCH_TAC `path_image k1 SUBSET (d:real^3->bool)` THEN
      UNDISCH_TAC `path_image k2 SUBSET (d:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) j = relative_frontier S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `path_image k1 UNION path_image k2 = j:real^3->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_UNION];
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) j = relative_frontier S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `ab INTER j = {p:real^3,q}` THEN
      UNDISCH_TAC `!y z. y IN d /\ z IN d /\ (gs:real^3->real^2) y = gs z ==> y = z` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN UNDISCH_TAC `j SUBSET (d:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `ab INTER j = {p:real^3,q}` THEN
      UNDISCH_TAC `path_image k1 SUBSET (j:real^3->bool)` THEN
      UNDISCH_TAC `path_image k1 INTER path_image k2 = {p:real^3,q}` THEN
      UNDISCH_TAC `path_image k1 UNION path_image k2 = j:real^3->bool` THEN
      UNDISCH_TAC `!y z. y IN d /\ z IN d /\ (gs:real^3->real^2) y = gs z ==> y = z` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN UNDISCH_TAC `j SUBSET (d:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `ab INTER j = {p:real^3,q}` THEN
      UNDISCH_TAC `path_image k2 SUBSET (j:real^3->bool)` THEN
      UNDISCH_TAC `path_image k1 INTER path_image k2 = {p:real^3,q}` THEN
      UNDISCH_TAC `path_image k1 UNION path_image k2 = j:real^3->bool` THEN
      UNDISCH_TAC `!y z. y IN d /\ z IN d /\ (gs:real^3->real^2) y = gs z ==> y = z` THEN
      UNDISCH_TAC `(ab:real^3->bool) SUBSET d` THEN UNDISCH_TAC `j SUBSET (d:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `IMAGE (gs:real^3->real^2) d = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fs:real^2->real^3) (path_image a1) = path_image k1 /\
                IMAGE (fs:real^2->real^3) (path_image a2) = path_image k2 /\
                IMAGE (gs:real^3->real^2) ab = path_image b`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S3L9_IMAGE_LEFT_INV THEN
    EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `path_image(a1:real^1->real^2)` ||
     lhs(concl th) = `path_image(a2:real^1->real^2)` ||
     lhs(concl th) = `path_image(b:real^1->real^2)`)))) THEN
  (* the cross-cut splits the model (MOI_SFR_THETA) *)
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `relative_frontier S:real^2->bool`;
                 `(path_image a1 UNION path_image b) UNION
                  inside(path_image a1 UNION path_image (b:real^1->real^2))`;
                 `(path_image a2 UNION path_image b) UNION
                  inside(path_image a2 UNION path_image (b:real^1->real^2))`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image b SUBSET (S:real^2->bool)` THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `uu1 = (path_image a1 UNION path_image b) UNION
                    inside(path_image a1 UNION path_image (b:real^1->real^2))` THEN
  ABBREV_TAC `uu2 = (path_image a2 UNION path_image b) UNION
                    inside(path_image a2 UNION path_image (b:real^1->real^2))` THEN
  SUBGOAL_THEN `uu1 UNION uu2 = S:real^2->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart a2 = pathstart (a1:real^1->real^2) /\
                pathfinish a2 = pathfinish (a1:real^1->real^2)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier S UNION inside (relative_frontier S) = S:real^2->bool`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `S = relative_frontier S UNION interior(S:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `uu1:real^2->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. connected s /\ s SUBSET S /\ s INTER path_image b = {}
                    ==> s SUBSET uu2 \/ s SUBSET (uu1:real^2->bool)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `uu1 SUBSET (S:real^2->bool) /\ uu2 SUBSET S /\
                uu2 UNION uu1 = S /\ uu2 INTER uu1 = path_image b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `uu1 UNION uu2 = S:real^2->bool` THEN
    UNDISCH_TAC `uu1 INTER uu2 = path_image (b:real^1->real^2)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image a1 SUBSET (uu1:real^2->bool) /\ path_image a2 SUBSET (uu2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(path_image a1 UNION path_image b) UNION
                 inside(path_image a1 UNION path_image (b:real^1->real^2)) = uu1` THEN
    UNDISCH_TAC `(path_image a2 UNION path_image b) UNION
                 inside(path_image a2 UNION path_image (b:real^1->real^2)) = uu2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `uu1 INTER relative_frontier S = path_image a1 /\
                uu2 INTER relative_frontier S = path_image (a2:real^1->real^2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `a1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `pathstart a2 = pathstart (a1:real^1->real^2)` THEN
    UNDISCH_TAC `pathfinish a2 = pathfinish (a1:real^1->real^2)` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `uu1 INTER path_image a2 =
                 {pathstart a1,pathfinish (a1:real^1->real^2)}` THEN
    UNDISCH_TAC `uu2 INTER path_image a1 =
                 {pathstart a1,pathfinish (a1:real^1->real^2)}` THEN
    UNDISCH_TAC `path_image a1 UNION path_image a2 = relative_frontier (S:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `path_image a1 SUBSET (uu1:real^2->bool)` THEN
    UNDISCH_TAC `path_image a2 SUBSET (uu2:real^2->bool)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  (* one of the two new boundary curves is not contractible (MOI_S3L9_THETA_NULL) *)
  SUBGOAL_THEN `tt SUBSET (dd:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `dd:real^3->bool`; `ab UNION tt:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image k1 INTER tt = {p:real^3,q} /\ path_image k2 INTER tt = {p,q} /\
                path_image k1 UNION path_image k2 UNION tt SUBSET bx`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k1:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `k1:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `k2:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `k2:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image k1 SUBSET (j:real^3->bool)` THEN
    UNDISCH_TAC `path_image k2 SUBSET (j:real^3->bool)` THEN
    UNDISCH_TAC `j SUBSET (d:real^3->bool)` THEN UNDISCH_TAC `d INTER bx = j:real^3->bool` THEN
    UNDISCH_TAC `tt SUBSET (dd:real^3->bool)` THEN UNDISCH_TAC `tt SUBSET (bx:real^3->bool)` THEN
    UNDISCH_TAC `dd INTER d = ab:real^3->bool` THEN UNDISCH_TAC `ab INTER tt = {p:real^3,q}` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?a:real^3. homotopic_with (\q. T)
                   (subtopology euclidean (path_image k1 UNION tt),subtopology euclidean bx)
                   (\z. z) (\z. a)) \/
                ~(?a:real^3. homotopic_with (\q. T)
                   (subtopology euclidean (path_image k2 UNION tt),subtopology euclidean bx)
                   (\z. z) (\z. a))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?a. homotopic_with (\q. T)
                      (subtopology euclidean j,subtopology euclidean bx)
                      (\y:real^3. y) (\y. a))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image k1 UNION path_image k2 = j:real^3->bool` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S3L9_THETA_NULL THEN EXISTS_TAC `ht:real^1->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `S:real^2->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                   `ab:real^3->bool`; `hab:real^1->real^3`; `ht:real^1->real^3`;
                   `dd:real^3->bool`; `v:real^3`; `w:real^3`; `a1:real^1->real^2`;
                   `b:real^1->real^2`; `uu1:real^2->bool`; `uu2:real^2->bool`]
      MOI_S3L9_ARC_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `d:real^3->bool`; `cs:(real^3->bool)->bool`;
                   `S:real^2->bool`; `fs:real^2->real^3`; `gs:real^3->real^2`;
                   `ab:real^3->bool`; `hab:real^1->real^3`; `ht:real^1->real^3`;
                   `dd:real^3->bool`; `v:real^3`; `w:real^3`; `a2:real^1->real^2`;
                   `b:real^1->real^2`; `uu2:real^2->bool`; `uu1:real^2->bool`]
      MOI_S3L9_ARC_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* Part 11. The induction on the size of the family and the headline.      *)
(* ------------------------------------------------------------------------- *)

(* One step: a nonempty family can be made strictly smaller.                  *)

let MOI_S3L9_STEP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x d cs.
     moi_s3l9i_l8 /\ moi_s3l9i_drec /\ moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     moi_s39_family l e x d cs /\ ~(cs = {})
     ==> ?d' cs'. moi_s33_ltd t l h x d' /\ moi_s39_family l e x d' cs' /\ cs' PSUBSET cs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?a0:real^3->bool. a0 IN cs /\ pl_sphere 1 a0 /\
                                  DISJOINT a0 (frontier (UNIONS x))` THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                   `cs:(real^3->bool)->bool`] MOI_S3L9_CIRCLE_STEP);
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                   `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                   `cs:(real^3->bool)->bool`] MOI_S3L9_ARC_STEP)] THEN
  ASM_REWRITE_TAC[]);;

(* No loop theorem disk has a family: induction on the size of the family. *)

let MOI_S3L9_NO_FAMILY = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (c:real^3->real^3->bool) x.
     moi_s3l9i_l8 /\ moi_s3l9i_drec /\ moi_s3l9i_push /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_noltd t l h c x
     ==> !n d cs. moi_s33_ltd t l h x d /\ moi_s39_family l e x d cs /\ CARD cs = n
                  ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:real^3->bool`; `cs:(real^3->bool)->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `cs:(real^3->bool)->bool = {}` THENL
   [MATCH_MP_TAC MOI_S3L9_FINAL THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                          `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                          `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                          `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s39_family l e x d cs` THEN
    ASM_REWRITE_TAC[moi_s39_family; UNIONS_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `d:real^3->bool`;
                 `cs:(real^3->bool)->bool`] MOI_S3L9_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->bool` (X_CHOOSE_THEN `cs':(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(cs':(real^3->bool)->bool)`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `CARD(cs:(real^3->bool)->bool) = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s39_family l e x d cs` THEN SIMP_TAC[moi_s39_family];
    DISCH_THEN(MP_TAC o SPECL [`d':real^3->bool`; `cs':(real^3->bool)->bool`]) THEN
    ASM_REWRITE_TAC[]]);;

(* The headline: Lemma 9 from general position and the push.                *)

let S39_L9_FROM = prove
 (MOI_S39_L9_FROM,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o EQ_MP (SYM moi_s3l9i_push))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o EQ_MP (SYM moi_s3l9i_l8))
    (CONJUNCTS_THEN2 (ASSUME_TAC o EQ_MP (SYM moi_s3l9i_drec)) (K ALL_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `d:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `d:real^3->bool`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "moi_s39_family")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->bool` (X_CHOOSE_THEN `cs:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] MOI_S3L9_NO_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`CARD(cs:(real^3->bool)->bool)`; `d':real^3->bool`;
                             `cs:(real^3->bool)->bool`]) THEN
  ASM_REWRITE_TAC[]);;

