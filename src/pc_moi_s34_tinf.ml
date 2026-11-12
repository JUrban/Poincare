(* ========================================================================= *)
(* pc_moi_s34_tinf: Moise Sec 34 tube and trace infrastructure, loaded by  *)
(* pc_moi_s34_l910 and pc_moi_s34_trace.  Vertex-ball combinatorics of the *)
(* derived neighbourhood (three distinct dual cells have empty             *)
(* intersection), images under the frame map f1, trace facts (compact,     *)
(* finitely many components, each a PL circle), two-sidedness of the trace *)
(* at rim points (invariance of domain), the face torus, and the           *)
(* broken-line lemma MOI_S4L_BROKEN_LINE of Lemma 9 (via carries_h1 and a  *)
(* circle-valued map).                                                     *)
(* ========================================================================= *)

needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_fnd_h1.ml";;

prioritize_real();;
type_invention_error := true;;

(* OCaml helper for assumption selection: does th mention constant c? *)
let moi_s4l_has (c:string) th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = c)) (concl th);;


(* ------------------------------------------------------------------------- *)
(* The tube N'' and its vertex balls: triple intersections are empty.       *)
(* The chain argument follows MOI_FTA_CELLS_DISJOINT (pc_moi_fnd_tubea).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_NBHD_CHAIN_HIT = prove
 (`!(t:(real^N->bool)->bool) l h x.
     graph_in_complex t l /\ x IN derived_nbhd t l /\ moi_bar_chain t h /\
     x IN convex hull (IMAGE simplex_barycentre h)
     ==> ?sg. sg IN l /\ sg IN h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `q = convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(q:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`; `q:real^N->bool`; `x:real^N`]
    MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(g INTER {r:real^N->bool | r face_of q} = {})` MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                   (g INTER {r:real^N->bool | r face_of q}))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM]) THEN
  UNDISCH_TAC `~(g INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r0 = INTERS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t /\ ~(r0 = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision l` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex] o check (fun th ->
        can (find_term ((=) `barycentric_subdivision (l:(real^N->bool)->bool)`))
            (concl th) && is_comb(concl th) &&
        fst(strip_comb(concl th)) = `simplicial_subcomplex:((real^N->bool)->bool)->((real^N->bool)->bool)->bool`)) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain t (f0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f0:(real^N->bool)->bool) SUBSET h` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r0:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `r1:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN f0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = {}) ==> ?x:real^N->bool. x IN s`) THEN
    DISCH_TAC THEN UNDISCH_TAC `~(r0:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `sg:real^N->bool` THEN
  ASM_MESON_TAC[moi_bar_chain; SUBSET]);;

let MOI_S4L_CELLS_TRIPLE = prove
 (`!(t:(real^N->bool)->bool) l u1 u2 u3.
     graph_in_complex t l /\ {u1} IN l /\ {u2} IN l /\ {u3} IN l /\
     ~(u1 = u2) /\ ~(u1 = u3) /\ ~(u2 = u3)
     ==> derived_dual_cell t l u1 INTER derived_dual_cell t l u2 INTER
         derived_dual_cell t l u3 = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{u1:real^N} IN t /\ {u2} IN t /\ {u3} IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `h1:(real^N->bool)->bool` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `h2:(real^N->bool)->bool` STRIP_ASSUME_TAC))
     (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `h3:(real^N->bool)->bool` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                 `u1:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h2:(real^N->bool)->bool`;
                 `u2:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h3:(real^N->bool)->bool`;
                 `u3:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre ((h1 INTER h2) INTER h3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1 INTER h2:(real^N->bool)->bool`;
                   `h3:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `(h1 INTER h2) INTER h3:(real^N->bool)->bool`; `x:real^N`]
    MOI_S4L_NBHD_CHAIN_HIT) THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u1:real^N) IN sg /\ u2 IN sg /\ u3 IN sg` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sg = segment[u1:real^N,u2] /\ sg = segment[u1,u3]` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[] `(a:real^N->bool) = b /\ a = c ==> b = c`)) THEN
  REWRITE_TAC[SEGMENT_EQ] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The tube N'' = N(tt, skeleton 1 kk): vertex balls, splitting disks,      *)
(* edges and triangles of kk.                                               *)
(* ========================================================================= *)

let MOI_S4L_SKEL_VERTEX = prove
 (`!(kk:(real^N->bool)->bool) v. {v} IN skeleton 1 kk <=> {v} IN kk`,
  REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[]);;

let MOI_S4L_SKEL_SEGMENT = prove
 (`!(kk:(real^N->bool)->bool) u v.
     segment[u,v] IN skeleton 1 kk <=> segment[u,v] IN kk`,
  REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let MOI_S4L_PL_CELL_FACTS = prove
 (`!n (s:real^N->bool) b.
     pl_cell_with_boundary n s b
     ==> compact s /\ compact b /\ b SUBSET s /\ connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact(k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[];
    ASM_MESON_TAC[CONNECTED_CONTINUOUS_IMAGE; CONVEX_CONNECTED]]);;

let MOI_S4L_PL_BALL_COMPACT = prove
 (`!n s:real^N->bool. pl_ball n s ==> compact s /\ connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX;
                CONNECTED_CONTINUOUS_IMAGE; CONVEX_CONNECTED]);;

let MOI_S4L_TUBE_TUBE = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> graph_in_complex tt (skeleton 1 kk) /\ lf_simplicial_complex tt /\
         lf_simplicial_complex kk /\ kk SUBSET tt /\
         moi_s34_nb tt kk SUBSET UNIONS tt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ASM_MESON_TAC[simplicial_subcomplex];
    REWRITE_TAC[moi_s34_nb; derived_nbhd] THEN
    SUBGOAL_THEN `UNIONS (barycentric_subdivision (barycentric_subdivision tt)) =
                  UNIONS (tt:(real^N->bool)->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_BS_FACTS]; SET_TAC[]]]);;

let MOI_S4L_GRAPH_TUBE = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> moi_s34_nb tt kk = UNIONS {moi_s34_vb tt kk v | v | {v} IN kk} /\
         moi_s34_bd tt kk SUBSET moi_s34_nb tt kk /\
         (!v. {v} IN kk
              ==> v IN moi_s34_vb tt kk v /\
                  moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk /\
                  pl_cell_with_boundary 3 (moi_s34_vb tt kk v)
                    ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                     UNIONS {moi_s34_vb tt kk v INTER moi_s34_vb tt kk w | w |
                             ~(w = v) /\ segment[v,w] IN kk})) /\
         (!u v. ~(u = v) /\ segment[u,v] IN kk
                ==> pl_cell_with_boundary 2
                      (moi_s34_vb tt kk u INTER moi_s34_vb tt kk v)
                      (moi_s34_vb tt kk u INTER moi_s34_vb tt kk v INTER
                       moi_s34_bd tt kk)) /\
         (!u v. {u} IN kk /\ {v} IN kk /\ ~(u = v) /\ ~(segment[u,v] IN kk)
                ==> moi_s34_vb tt kk u INTER moi_s34_vb tt kk v = {}) /\
         (!u1 u2 u3. {u1} IN kk /\ {u2} IN kk /\ {u3} IN kk /\
                     ~(u1 = u2) /\ ~(u1 = u3) /\ ~(u2 = u3)
                     ==> moi_s34_vb tt kk u1 INTER moi_s34_vb tt kk u2 INTER
                         moi_s34_vb tt kk u3 = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
    GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[MOI_S4L_SKEL_VERTEX; MOI_S4L_SKEL_SEGMENT] THEN
  REWRITE_TAC[GSYM moi_s34_nb; GSYM moi_s34_bd; GSYM moi_s34_vb] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_bd (tt:(real^N->bool)->bool) kk SUBSET moi_s34_nb tt kk`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_bd; moi_s34_nb; SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                   `x:real^N`] MOI_FTA_FRONTIER_IFF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[graph_in_complex]; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[moi_s34_vb] THEN MATCH_MP_TAC MOI_FTA_VERTEX_IN_CELL THEN
      ASM_REWRITE_TAC[MOI_S4L_SKEL_VERTEX];
      REWRITE_TAC[moi_s34_vb; moi_s34_nb; derived_dual_cell] THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[moi_s34_vb] THEN MATCH_MP_TAC MOI_S4L_CELLS_TRIPLE THEN
    ASM_REWRITE_TAC[MOI_S4L_SKEL_VERTEX]]);;

let MOI_S4L_VB_COMPACT = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> compact(moi_s34_vb tt kk v) /\
         compact(moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  SUBGOAL_THEN `compact(moi_s34_vb (tt:(real^N->bool)->bool) kk v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (UNIONS tt))
                  (moi_s34_bd (tt:(real^N->bool)->bool) kk)` MP_TAC THENL
   [REWRITE_TAC[moi_s34_bd; derived_frontier; CLOSED_IN_FRONTIER_OF]; ALL_TAC] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_bd tt kk =
                moi_s34_vb tt kk v INTER c` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET UNIONS tt` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; SET_TAC[]];
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED]]);;

let MOI_S4L_LF_VERTEX_EXTREME = prove
 (`!(c:(real^N->bool)->bool) v s.
     lf_simplicial_complex c /\ {v} IN c /\ s IN c /\ v IN s
     ==> v extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{v:real^N} = {v} INTER s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_S4L_EDGE_VERTS = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> ?u w. ~(u = w) /\ g = segment[u,w] /\ {u} IN kk /\ {w} IN kk /\
               {v | v IN g /\ {v} IN kk} = {u,w} /\
               moi_s34_sd tt kk g = moi_s34_vb tt kk u INTER moi_s34_vb tt kk w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v | v IN segment[u,w] /\ {v} IN kk} = {u:real^N,w}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(v:real^N) extreme_point_of segment[u,w]` MP_TAC THENL
       [MATCH_MP_TAC MOI_S4L_LF_VERTEX_EXTREME THEN
        EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[MOI_S4L_TUBE_TUBE];
        REWRITE_TAC[EXTREME_POINT_OF_SEGMENT]];
      STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4D_SAN_SD_EDGE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S4L_TRI_FORM = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> ?a b c. ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
                 s = convex hull {a,b,c} /\
                 {a} IN kk /\ {b} IN kk /\ {c} IN kk /\
                 segment[a,b] IN kk /\ segment[a,c] IN kk /\ segment[b,c] IN kk /\
                 {v | v IN s /\ {v} IN kk} = {a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(n:int) = &2` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(cc:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(cc:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c:real^N`] THEN
  UNDISCH_TAC `~affine_dependent(cc:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f:real^N->bool. f face_of convex hull {a,b,c} ==> f IN kk`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
    EXISTS_TAC `{a:real^N,b}` THEN SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
    EXISTS_TAC `{a:real^N,c}` THEN SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
    EXISTS_TAC `{b:real^N,c}` THEN SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(v:real^N) extreme_point_of convex hull {a,b,c}` MP_TAC THENL
       [MATCH_MP_TAC MOI_S4L_LF_VERTEX_EXTREME THEN
        EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]]]]);;

(* ========================================================================= *)
(* Images under the tube embedding f1: the sets A_v = f1(C_v INTER         *)
(* Bd N''), the rims, and the traces of the face balls.                      *)
(* ========================================================================= *)

let MOI_S4L_IMAGE_INTER_INJ = prove
 (`!(f:real^N->real^M) n a b.
     (!x y. x IN n /\ y IN n /\ f x = f y ==> x = y) /\ a SUBSET n /\ b SUBSET n
     ==> IMAGE f (a INTER b) = IMAGE f a INTER IMAGE f b`,
  SET_TAC[]);;

let MOI_S4L_FRAME_F1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_frame tt kk h ep f1 car
     ==> f1 continuous_on moi_s34_nb tt kk /\
         (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y
                ==> x = y) /\
         IMAGE f1 (moi_s34_bd tt kk) INTER interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

let MOI_S4L_AV_BASIC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk
     ==> compact(IMAGE f1 (moi_s34_vb tt kk v)) /\
         compact(IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v} /\
         pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4L_VB_COMPACT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET moi_s34_nb tt kk`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
  REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SET_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S4L_SD_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> (!g g'. g IN moi_s34_simp kk (&1) /\ g' IN moi_s34_simp kk (&1) /\ ~(g = g')
                 ==> moi_s34_sd tt kk g INTER moi_s34_sd tt kk g' = {}) /\
         (!g v. g IN moi_s34_simp kk (&1) /\ {v} IN kk /\ ~(v IN g)
                ==> moi_s34_sd tt kk g INTER moi_s34_vb tt kk v = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `g':real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g':real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `w':real^N` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~({u:real^N,w} = {u',w'})` ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_EQ]; ALL_TAC] THEN
    ASM_CASES_TAC `(u':real^N) IN {u,w}` THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`; `u':real^N`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]]] THEN
    ASM_CASES_TAC `(w':real^N) IN {u,w}` THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`; `w':real^N`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]]];
    MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `v:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`; `v:real^N`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((v:real^N) IN g)` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ENDS_IN_SEGMENT];
      SET_TAC[]]]);;

let MOI_S4L_IMAGES = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car
     ==> IMAGE f1 (moi_s34_bd tt kk) =
         UNIONS {IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) | v | {v} IN kk} /\
         (!v w. {v} IN kk /\ {w} IN kk /\ ~(v = w) /\ ~(segment[v,w] IN kk)
                ==> IMAGE f1 (moi_s34_vb tt kk v) INTER IMAGE f1 (moi_s34_vb tt kk w) = {}) /\
         (!a b. a SUBSET moi_s34_nb tt kk /\ b SUBSET moi_s34_nb tt kk
                ==> IMAGE f1 (a INTER b) = IMAGE f1 a INTER IMAGE f1 b) /\
         (!u1 u2 u3. {u1} IN kk /\ {u2} IN kk /\ {u3} IN kk /\
                     ~(u1 = u2) /\ ~(u1 = u3) /\ ~(u2 = u3)
                     ==> IMAGE f1 (moi_s34_vb tt kk u1) INTER
                         IMAGE f1 (moi_s34_vb tt kk u2) INTER
                         IMAGE f1 (moi_s34_vb tt kk u3) = {}) /\
         (!g g'. g IN moi_s34_simp kk (&1) /\ g' IN moi_s34_simp kk (&1) /\ ~(g = g')
                 ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_sd tt kk g') = {}) /\
         (!g v. g IN moi_s34_simp kk (&1) /\ {v} IN kk /\ ~(v IN g)
                ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_vb tt kk v) = {}) /\
         (!g. g IN moi_s34_simp kk (&1) ==> moi_s34_sd tt kk g SUBSET moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_SD_DISJ) THEN
  SUBGOAL_THEN `!a b. a SUBSET moi_s34_nb tt kk /\ b SUBSET moi_s34_nb tt kk
                      ==> IMAGE (f1:real^N->real^3) (a INTER b) = IMAGE f1 a INTER IMAGE f1 b`
  (LABEL_TAC "img") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_IMAGE_INTER_INJ THEN
    EXISTS_TAC `moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. {v} IN kk ==> moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET moi_s34_nb tt kk`
  (LABEL_TAC "vbn") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!g. g IN moi_s34_simp kk (&1)
                    ==> moi_s34_sd (tt:(real^N->bool)->bool) kk g SUBSET moi_s34_nb tt kk`
  (LABEL_TAC "sdn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `moi_s34_sd (tt:(real^N->bool)->bool) kk g =
                 moi_s34_vb tt kk u INTER moi_s34_vb tt kk w` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s34_vb (tt:(real^N->bool)->bool) kk u` THEN
    REWRITE_TAC[INTER_SUBSET] THEN USE_THEN "vbn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (UNIONS {moi_s34_vb tt kk v INTER moi_s34_bd tt kk | v | {v} IN kk})` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s34_bd (tt:(real^N->bool)->bool) kk SUBSET moi_s34_nb tt kk` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        SET_TAC[]];
      REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN SET_TAC[]];
    REPEAT STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`moi_s34_vb (tt:(real^N->bool)->bool) kk v`;
                                   `moi_s34_vb (tt:(real^N->bool)->bool) kk w`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_vb tt kk w = {}`
    (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN ASM_MESON_TAC[];
    USE_THEN "img" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`moi_s34_vb (tt:(real^N->bool)->bool) kk u2`;
                                   `moi_s34_vb (tt:(real^N->bool)->bool) kk u3`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "img" (MP_TAC o SPECL [`moi_s34_vb (tt:(real^N->bool)->bool) kk u1`;
                     `moi_s34_vb (tt:(real^N->bool)->bool) kk u2 INTER moi_s34_vb tt kk u3`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS; INTER_SUBSET]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk u1 INTER moi_s34_vb tt kk u2 INTER
                  moi_s34_vb tt kk u3 = {}`
    (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`moi_s34_sd (tt:(real^N->bool)->bool) kk g`;
                                   `moi_s34_sd (tt:(real^N->bool)->bool) kk g'`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `moi_s34_sd (tt:(real^N->bool)->bool) kk g INTER moi_s34_sd tt kk g' = {}`
    (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`moi_s34_sd (tt:(real^N->bool)->bool) kk g`;
                                   `moi_s34_vb (tt:(real^N->bool)->bool) kk v`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `moi_s34_sd (tt:(real^N->bool)->bool) kk g INTER moi_s34_vb tt kk v = {}`
    (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN ASM_MESON_TAC[];
    USE_THEN "sdn" ACCEPT_TAC]);;

let MOI_S4L_TRACE_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s c a b d.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\ moi_s34_fb1 tt kk h f1 car s c /\
     {v | v IN s /\ {v} IN kk} = {a,b,d}
     ==> moi_s34_trace tt kk f1 c =
         frontier c INTER
         (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_bd tt kk) UNION
          IMAGE f1 (moi_s34_vb tt kk b INTER moi_s34_bd tt kk) UNION
          IMAGE f1 (moi_s34_vb tt kk d INTER moi_s34_bd tt kk)) /\
         compact (moi_s34_trace tt kk f1 c) /\
         compact c /\ frontier c SUBSET c /\
         FINITE (components (moi_s34_trace tt kk f1 c)) /\
         (!j. j IN components (moi_s34_trace tt kk f1 c) ==> pl_sphere 1 j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_fb1]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `compact(c:real^3->bool) /\ frontier c SUBSET c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT; FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN kk /\ {b} IN kk /\ {d} IN kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{v | v IN s /\ {v} IN kk} = {a:real^N,b,d}` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s34_trace tt kk f1 c =
    frontier c INTER
    (IMAGE f1 (moi_s34_vb tt kk a INTER moi_s34_bd tt kk) UNION
     IMAGE f1 (moi_s34_vb tt kk b INTER moi_s34_bd tt kk) UNION
     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk d INTER moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
      check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`)) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^N) IN s` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN {a,b,d}` MP_TAC THENL
     [UNDISCH_TAC `{v | v IN s /\ {v} IN kk} = {a:real^N,b,d}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(moi_s34_trace tt kk (f1:real^N->real^3) c)` ASSUME_TAC THENL
   [SUBGOAL_THEN `!w:real^N. {w} IN kk
                  ==> compact(IMAGE (f1:real^N->real^3)
                                (moi_s34_vb tt kk w INTER moi_s34_bd tt kk))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `w:real^N`] MOI_S4L_AV_BASIC) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_INTER THEN
    ASM_SIMP_TAC[COMPACT_FRONTIER] THEN
    REPEAT(MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`frontier c:real^3->bool`; `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`]
    MOI_S4L_CROSSING_CIRCLES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `compact(moi_s34_trace tt kk (f1:real^N->real^3) c)` THEN
      REWRITE_TAC[moi_s34_trace];
      FIRST_X_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[moi_s34_trace] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `pl_crossing_at`)) (concl th)))];
    REWRITE_TAC[GSYM moi_s34_trace] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_S4L_TRACES_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s s'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\ ~(s = s')
     ==> cb s INTER cb s' INTER IMAGE f1 (moi_s34_bd tt kk) = {} /\
         moi_s34_trace tt kk f1 (cb s) INTER moi_s34_trace tt kk f1 (cb s') = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "fb1") (LABEL_TAC "fb2") o
    GEN_REWRITE_RULE I [moi_s34_fbinv]) THEN
  SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
                interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`
  ASSUME_TAC THENL
   [USE_THEN "fb2" (MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[moi_s34_fb2] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s /\
                frontier(cb s') SUBSET cb s'` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s) /\ pl_ball 3 (cb s')`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "fb1" (MP_TAC o SPEC `s:real^N->bool`);
        USE_THEN "fb1" (MP_TAC o SPEC `s':real^N->bool`)] THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[moi_s34_fb1]]);
      ALL_TAC] THEN
    ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT; FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[moi_s34_trace] THEN ASM SET_TAC[]]);;

let MOI_S4L_IMG_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car
     ==> (!g g'. g IN moi_s34_simp kk (&1) /\ g' IN moi_s34_simp kk (&1) /\ ~(g = g')
                 ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_sd tt kk g') = {}) /\
         (!g v. g IN moi_s34_simp kk (&1) /\ {v} IN kk /\ ~(v IN g)
                ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_vb tt kk v) = {}) /\
         (!u1 u2 u3. {u1} IN kk /\ {u2} IN kk /\ {u3} IN kk /\
                     ~(u1 = u2) /\ ~(u1 = u3) /\ ~(u2 = u3)
                     ==> IMAGE f1 (moi_s34_vb tt kk u1) INTER
                         IMAGE f1 (moi_s34_vb tt kk u2) INTER
                         IMAGE f1 (moi_s34_vb tt kk u3) = {}) /\
         (!v w. {v} IN kk /\ {w} IN kk /\ ~(v = w) /\ ~(segment[v,w] IN kk)
                ==> IMAGE f1 (moi_s34_vb tt kk v) INTER IMAGE f1 (moi_s34_vb tt kk w) = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_IMAGES) THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* Two-sidedness of the rims (invariance of domain on the vertex-ball       *)
(* spheres) and transverse crossings of the trace with a rim.               *)
(* ========================================================================= *)

let MOI_S4L_SPHERE2_HOMEO = prove
 (`!s:real^N->bool. pl_sphere 2 s ==> s homeomorphic sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) = relative_frontier(cball(vec 0,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_3;
                REAL_LT_01] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_BOUNDED; AFF_DIM_SIMPLEX]]);;

let MOI_S4L_BALL_FRONTIER_SPHERE = prove
 (`!u:real^3->bool. pl_ball 3 u ==> pl_sphere 2 (frontier u)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_BALL_BOUNDARY_PLH THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4L_CELL_BOUNDARY_NOT_OPEN = prove
 (`!(sg:real^3->bool) d b x.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 d b /\ d SUBSET sg /\ x IN b
     ==> ~(?u. open_in (subtopology euclidean sg) u /\ x IN u /\ u SUBSET d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4L_SPHERE2_HOMEO) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  REWRITE_TAC[pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact(k:real^3->bool) /\ convex k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `?q:real^3. q IN relative_frontier k /\ (x:real^3) = (f:real^3->real^3) q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN b` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN sg` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `x:real^3`] MOI_SCF_SPHERE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^2`
    (X_CHOOSE_THEN `phi':real^2->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    can (find_term ((=) `phi:real^3->real^2`)) (concl th) &&
    is_comb(concl th) && fst(strip_comb(concl th)) = `homeomorphism:
      (real^3->bool)#(real^2->bool)->(real^3->real^2)#(real^2->real^3)->bool`)) THEN
  ABBREV_TAC `vv = (u:real^3->bool) INTER u'` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (u':real^3->bool)) vv /\
                (x:real^3) IN vv /\ vv SUBSET d`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `sg:real^3->bool` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
        SET_TAC[];
        ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:real^3->real^2) vv)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^2`; `phi':real^2->real^3`; `u':real^3->bool`;
                   `(:real^2)`; `vv:real^3->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[homeomorphism; SUBTOPOLOGY_UNIV; GSYM OPEN_IN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) o (phi':real^2->real^3)`; `(:real^2)`;
                 `affine hull k:real^3->bool`; `IMAGE (phi:real^3->real^2) vv`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFFINE_UNIV; AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL; AFF_DIM_UNIV;
                DIMINDEX_2; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `d:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
        SUBGOAL_THEN `IMAGE ((phi':real^2->real^3) o (phi:real^3->real^2)) vv = vv`
        (fun th -> REWRITE_TAC[th]) THENL
         [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN ASM SET_TAC[];
          ASM_REWRITE_TAC[]]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN MATCH_MP_TAC HULL_INC THEN
      SUBGOAL_THEN `(phi':real^2->real^3)((phi:real^3->real^2) z) = z` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) d = k` THEN ASM SET_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM] THEN
      X_GEN_TAC `z1:real^3` THEN DISCH_TAC THEN X_GEN_TAC `z2:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(phi':real^2->real^3)((phi:real^3->real^2) z1) = z1 /\
                    (phi':real^2->real^3)((phi:real^3->real^2) z2) = z2`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3)((g:real^3->real^3) z1) = z1 /\ f(g z2) = z2`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. (g:real^3->real^3)((phi':real^2->real^3)((phi:real^3->real^2) x))) vv =
                IMAGE g vv` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3) IN relative_interior k` MP_TAC THENL
   [REWRITE_TAC[relative_interior; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) vv` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) d = k` THEN ASM SET_TAC[]];
    UNDISCH_TAC `(q:real^3) IN relative_frontier k` THEN
    REWRITE_TAC[relative_frontier] THEN SET_TAC[]]);;

let MOI_S4L_RIM_SIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w x e.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                    moi_s34_bd tt kk) /\
     &0 < e
     ==> ?y. y IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
             ~(y IN IMAGE f1 (moi_s34_vb tt kk w)) /\ dist(x,y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN moi_s34_simp kk (&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (segment[v,w]) =
                moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_vb tt kk w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4D_SAN_SD_EDGE THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[v:real^N,w]`] MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{u1:real^N,u2} = {v,w}` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[SEGMENT_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w])))
                  (IMAGE f1 (moi_s34_sd tt kk (segment[v,w]) INTER moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `others = UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g') | g' |
                               g' IN moi_s34_simp kk (&1) /\ v IN g' /\ ~(g' = segment[v,w])}` THEN
  SUBGOAL_THEN `closed(others:real^3->bool) /\ ~((x:real^3) IN others)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "others" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN
          EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN
          ASM_MESON_TAC[MOI_S4L_TUBE_TUBE; SUBSET]];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
        REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
        ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g':real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      MP_TAC(CONJUNCT1(UNDISCH_ALL(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] (REWRITE_RULE[IMP_CONJ] MOI_S4L_IMG_FACTS)))) THEN
      DISCH_THEN(MP_TAC o SPECL [`segment[v:real^N,w]`; `g':real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                    moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`others:real^3->bool`; `x:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sepd0"))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "contra" o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1 o check (fun th ->
    is_comb(concl th) && can (find_term ((=) `car:(real^N->bool)->real^3->bool`)) (concl th) &&
    not(is_forall(concl th)))) THEN
  MP_TAC(ISPECL [`frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]) INTER moi_s34_bd tt kk)`;
                 `x:real^3`] MOI_S4L_CELL_BOUNDARY_NOT_OPEN) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4L_BALL_FRONTIER_SPHERE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET a UNION UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[] THEN  REWRITE_TAC[ENDS_IN_SEGMENT];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                    moi_s34_bd tt kk)` THEN SET_TAC[];
    EXISTS_TAC `frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) INTER
                ball(x,min e d0)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))` THEN CONJ_TAC THENL
         [EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[] THEN 
          REWRITE_TAC[ENDS_IN_SEGMENT];
          UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                    moi_s34_bd tt kk)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
        ASM_REAL_ARITH_TAC];
      ALL_TAC]] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_UNION] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
    ASSUME_TAC THENL
     [USE_THEN "contra" (MP_TAC o SPEC `y:real^3`) THEN
      ASM_MESON_TAC[REAL_ARITH `x < min e d ==> ~(e <= x)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `{w:real^N} IN kk` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `segment[v:real^N,w]`] MOI_S4L_EDGE_VERTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `{x | x IN segment[v:real^N,w] /\ {x} IN kk} = {u1,u2}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `{v:real^N,w} = {u1,u2}` MP_TAC THENL
       [ASM_MESON_TAC[SEGMENT_EQ]; SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET moi_s34_nb tt kk /\
                  moi_s34_vb tt kk w SUBSET moi_s34_nb tt kk` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S4L_GRAPH_TUBE]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a:real^N = b` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    UNDISCH_TAC `(y:real^3) IN UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk gg) | gg |
                                       gg IN moi_s34_simp kk (&1) /\ v IN gg}` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `g':real^N->bool = segment[v,w]` THENL
     [UNDISCH_TAC `(y:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN others` MP_TAC THENL
     [EXPAND_TAC "others" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `g':real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN USE_THEN "sepd0" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]]]);;

let MOI_S4L_CONNECTED_TWO_CLOSED = prove
 (`!s p q:real^N->bool.
     connected s /\ s SUBSET p UNION q /\
     closed_in (subtopology euclidean s) (s INTER p) /\
     closed_in (subtopology euclidean s) (s INTER q) /\
     s INTER p INTER q = {}
     ==> s SUBSET p \/ s SUBSET q`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED_IN] o check (fun th ->
    is_comb(concl th) && fst(dest_comb(concl th)) = `connected:(real^N->bool)->bool`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s INTER p:real^N->bool`; `s INTER q:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S4L_CHOICE_SING = prove
 (`!x:A. CHOICE {x} = x`,
  MESON_TAC[CHOICE_DEF; IN_SING; NOT_INSERT_EMPTY]);;

let MOI_S4L_LOCAL_AV_AW = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {v} IN kk /\ {w} IN kk /\ ~(w = v) /\
     x IN IMAGE f1 (moi_s34_vb tt kk v) /\ x IN IMAGE f1 (moi_s34_vb tt kk w)
     ==> ?oo. open oo /\ x IN oo /\
             IMAGE f1 (moi_s34_bd tt kk) INTER oo SUBSET
             IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
             IMAGE f1 (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN car {v:real^N}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u0. open u0 /\ (x:real^3) IN u0 /\
                     FINITE {q:real^N->bool | q IN kk /\ ~(q = {}) /\
                                              ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `car {v:real^N}:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `zs = UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) | u |
                           {u} IN kk /\ ~(u = v) /\ ~(u = w) /\
                           ~((car:(real^N->bool)->real^3->bool) {u} INTER u0 = {})}` THEN
  SUBGOAL_THEN `closed(zs:real^3->bool) /\ ~((x:real^3) IN zs)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `IMAGE (CHOICE:(real^N->bool)->real^N)
                      {q | q IN kk /\ ~(q = {}) /\
                           ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}` THEN
        ASM_SIMP_TAC[FINITE_IMAGE] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `u:real^N` THEN
        STRIP_TAC THEN EXISTS_TAC `{u:real^N}` THEN
        ASM_REWRITE_TAC[MOI_S4L_CHOICE_SING; NOT_INSERT_EMPTY];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_MESON_TAC[MOI_S4L_AV_BASIC]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `w:real^N`; `u:real^N`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
        can (find_term ((=) `(f1:real^N->real^3)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `u0 DIFF (zs:real^3->bool)` THEN
  ASM_SIMP_TAC[OPEN_DIFF; IN_DIFF] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNION] THEN X_GEN_TAC `y:real^3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?u:real^N. {u} IN kk /\
                  (y:real^3) IN IMAGE (f1:real^N->real^3)
                                  (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN UNIONS {IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) | v | {v} IN kk}` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = w` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN zs` (fun th -> ASM_MESON_TAC[th]) THEN
  EXPAND_TAC "zs" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)` THEN CONJ_TAC THENL
   [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ASM SET_TAC[]]);;

let MOI_S4L_CROSS_SIDES = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s c v w x e.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fb1 tt kk h f1 car s c /\
     {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     x IN moi_s34_trace tt kk f1 c /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
     &0 < e
     ==> ?k y. connected k /\ k SUBSET moi_s34_trace tt kk f1 c INTER ball(x,e) /\
               x IN k /\ y IN k /\
               y IN IMAGE f1 (moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
               ~(y IN IMAGE f1 (moi_s34_vb tt kk v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk w INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the edge, its vertices and its splitting disk *)
  SUBGOAL_THEN `segment[v:real^N,w] IN moi_s34_simp kk (&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `segment[v:real^N,w]`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{u1:real^N,u2} = {v,w}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEGMENT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN kk /\
                moi_s34_sd tt kk (segment[v,w]) = moi_s34_vb tt kk v INTER moi_s34_vb tt kk w`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(u1:real^N = v /\ u2 = w) \/ (u1 = w /\ u2 = v)` MP_TAC THENL
     [UNDISCH_TAC `{u1:real^N,u2} = {v,w}` THEN UNDISCH_TAC `~(u1:real^N = u2)` THEN
      SET_TAC[];
      STRIP_TAC THEN ASM_MESON_TAC[INTER_COMM]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_sd tt kk (segment[v:real^N,w])` &&
    can (find_term ((=) `u1:real^N`)) (concl th)))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1 o check (fun th ->
    is_comb(concl th) && not(is_forall(concl th)) &&
    can (find_term ((=) `car:(real^N->bool)->real^3->bool`)) (concl th))) THEN
  SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk w SUBSET moi_s34_nb tt kk /\
                moi_s34_bd tt kk SUBSET moi_s34_nb tt kk` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_GRAPH_TUBE]; ALL_TAC] THEN
  ABBREV_TAC `av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `aw = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `rim = IMAGE (f1:real^N->real^3)
                      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `mm = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `mm:real^3->bool`))) THEN
  SUBGOAL_THEN `(av:real^3->bool) INTER aw = rim /\ av SUBSET mm /\ aw SUBSET mm /\
                rim SUBSET av /\ compact av /\ compact aw /\
                mm INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) = av`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["av"; "aw"; "rim"; "mm"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3)
                    ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                     (moi_s34_vb tt kk w INTER moi_s34_bd tt kk))` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        AP_TERM_TAC THEN SET_TAC[]];
      SET_TAC[];
      SET_TAC[];
      SET_TAC[];
      ASM_MESON_TAC[MOI_S4L_AV_BASIC];
      ASM_MESON_TAC[MOI_S4L_AV_BASIC];
      CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk INTER moi_s34_vb tt kk v)` THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the crossing chart at x *)
  SUBGOAL_THEN `pl_curve_crossing_at mm (moi_s34_trace tt kk (f1:real^N->real^3) c) rim x`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s34_fb1] o
      check (moi_s4l_has "moi_s34_fb1")) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`segment[v:real^N,w]`; `x:real^3`] o
      check (moi_s4l_has "pl_curve_crossing_at")) THEN
    ASM_REWRITE_TAC[INTER_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c` THEN
    REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_curve_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^2`
    (X_CHOOSE_THEN `psi:real^2->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> moi_s4l_has "homeomorphism" th &&
                     can (find_term ((=) `phi:real^3->real^2`)) (concl th))) THEN
  (* Bd N'' near x is A_v UNION A_w *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`; `x:real^3`]
    MOI_S4L_LOCAL_AV_AW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN rim` THEN EXPAND_TAC "rim" THEN
    MAP_EVERY EXPAND_TAC ["av"; "aw"] THEN SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `uu = (u:real^3->bool) INTER oo INTER ball(x,e)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (u:real^3->bool)) uu /\
                (x:real^3) IN uu /\ uu SUBSET u /\ uu SUBSET mm INTER oo INTER ball(x,e)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "uu" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTER_ASSOC] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      SET_TAC[];
      UNDISCH_TAC `open_in (subtopology euclidean mm) (u:real^3->bool)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:real^3->real^2) uu)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^3->real^2) u` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:real^3->real^2`; `psi:real^2->real^3`; `u:real^3->bool`;
                   `IMAGE (phi:real^3->real^2) u`; `uu:real^3->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(vec 0:real^2,r) SUBSET IMAGE (phi:real^3->real^2) uu`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (phi:real^3->real^2) uu)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(phi:real^3->real^2) x = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* psi on the small disk *)
  SUBGOAL_THEN
   `!z. z IN ball(vec 0:real^2,r)
        ==> (psi:real^2->real^3) z IN uu /\ (phi:real^3->real^2)(psi z) = z /\
            z IN IMAGE phi u`
  (LABEL_TAC "psiz") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^3->real^2) uu` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^2->real^3)((phi:real^3->real^2) y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^2->real^3) continuous_on ball(vec 0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (phi:real^3->real^2) u` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(vec 0:real^2,r)
        ==> ((psi:real^2->real^3) z IN av \/ psi z IN aw) /\
            (psi z IN av /\ psi z IN aw <=> z$2 = &0) /\
            psi z IN ball(x,e) /\ psi z IN mm /\
            (z$1 = &0 ==> psi z IN moi_s34_trace tt kk (f1:real^N->real^3) c)`
  (LABEL_TAC "zfacts") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "psiz" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(psi:real^2->real^3) z IN mm INTER oo INTER ball(x,e)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(av:real^3->bool) INTER aw = rim` THEN
      REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^3->real^2) (rim INTER u)` MP_TAC THENL
         [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(psi:real^2->real^3) z` THEN
          ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
        DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^3->real^2) (rim INTER u)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `r1:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(psi:real^2->real^3) z = r1` (fun th -> ASM_REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[]];
      ASM SET_TAC[];
      ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^3->real^2)
                      (moi_s34_trace tt kk (f1:real^N->real^3) c INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `t1:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(psi:real^2->real^3) z = t1` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* each half disk lies on one side *)
  SUBGOAL_THEN
   `!hh:real^2->bool.
      convex hh /\ hh SUBSET ball(vec 0,r) /\ (!z. z IN hh ==> ~(z$2 = &0))
      ==> (!z. z IN hh ==> (psi:real^2->real^3) z IN av) \/
          (!z. z IN hh ==> psi z IN aw)`
  (LABEL_TAC "halves") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`hh:real^2->bool`; `{z:real^2 | (psi:real^2->real^3) z IN av}`;
                   `{z:real^2 | (psi:real^2->real^3) z IN aw}`]
      MOI_S4L_CONNECTED_TWO_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CONNECTED] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
        DISCH_TAC THEN USE_THEN "zfacts" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
        ONCE_REWRITE_TAC[SET_RULE `hh INTER {z:real^2 | P z} = {z | z IN hh /\ P z}`] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; COMPACT_IMP_CLOSED];
        ONCE_REWRITE_TAC[SET_RULE `hh INTER {z:real^2 | P z} = {z | z IN hh /\ P z}`] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; COMPACT_IMP_CLOSED];
        REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
        USE_THEN "zfacts" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `hp = ball(vec 0:real^2,r) INTER {z | z$2 > &0}` THEN
  ABBREV_TAC `hm = ball(vec 0:real^2,r) INTER {z | z$2 < &0}` THEN
  SUBGOAL_THEN `convex(hp:real^2->bool) /\ hp SUBSET ball(vec 0,r) /\
                (!z. z IN hp ==> ~(z$2 = &0)) /\
                convex(hm:real^2->bool) /\ hm SUBSET ball(vec 0,r) /\
                (!z. z IN hm ==> ~(z$2 = &0))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
    SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_GT;
             CONVEX_HALFSPACE_COMPONENT_LT; INTER_SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* not both halves on the side of v *)
  SUBGOAL_THEN `~((!z. z IN hp ==> (psi:real^2->real^3) z IN av) /\
                  (!z. z IN hm ==> psi z IN av))`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `!z. z IN ball(vec 0:real^2,r) ==> (psi:real^2->real^3) z IN av`
    ASSUME_TAC THENL
     [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(z:real^2)$2 = &0` THENL
       [USE_THEN "zfacts" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN ASM_MESON_TAC[];
        SUBGOAL_THEN `(z:real^2) IN hp \/ z IN hm` MP_TAC THENL
         [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean mm)
                    (IMAGE (psi:real^2->real^3) (ball(vec 0,r)))`
    MP_TAC THENL
     [SUBGOAL_THEN `IMAGE (psi:real^2->real^3) (ball(vec 0,r)) =
                    {y | y IN u /\ (phi:real^3->real^2) y IN ball(vec 0,r)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
        EQ_TAC THENL
         [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
          USE_THEN "psiz" (MP_TAC o SPEC `z:real^2`) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          STRIP_TAC THEN EXISTS_TAC `(phi:real^3->real^2) y` THEN ASM_MESON_TAC[]];
        MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^3->bool` THEN
        ASM_SIMP_TAC[CONTINUOUS_OPEN_IN_PREIMAGE; OPEN_BALL]];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) IN g0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN IMAGE (psi:real^2->real^3) (ball(vec 0,r))` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_MESON_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?r0. &0 < r0 /\ ball(x:real^3,r0) SUBSET g0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `w:real^N`; `v:real^N`;
                   `x:real^3`; `r0:real`] MOI_S4L_RIM_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y5:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y5:real^3) IN IMAGE (psi:real^2->real^3) (ball(vec 0,r))` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[IN_BALL]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z5:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((y5:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y5:real^3) IN av` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "av" THEN SET_TAC[];
    ALL_TAC] THEN
  (* a trace point on the side of w *)
  SUBGOAL_THEN
   `!z0. z0 IN ball(vec 0:real^2,r) /\ z0$1 = &0 /\ ~(z0$2 = &0) /\
         (psi:real^2->real^3) z0 IN aw
         ==> ?k y. connected k /\
                   k SUBSET moi_s34_trace tt kk (f1:real^N->real^3) c INTER ball(x,e) /\
                   x IN k /\ y IN k /\ y IN aw /\
                   ~(y IN IMAGE f1 (moi_s34_vb tt kk v))`
  (LABEL_TAC "fin") THENL
   [X_GEN_TAC `z0:real^2` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:real^2->real^3) (segment[vec 0,z0])`;
                          `(psi:real^2->real^3) z0`] THEN
    SUBGOAL_THEN `segment[vec 0:real^2,z0] SUBSET ball(vec 0,r) /\
                  (!z. z IN segment[vec 0,z0] ==> z$1 = &0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_BALL) THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL];
        REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_SEGMENT] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_TAC THEN USE_THEN "zfacts" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(psi:real^2->real^3) z0 IN av` ASSUME_TAC THENL
       [UNDISCH_TAC `mm INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) = av` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
        USE_THEN "zfacts" (MP_TAC o SPEC `z0:real^2`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN ASM_MESON_TAC[];
        USE_THEN "zfacts" (MP_TAC o SPEC `z0:real^2`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. z IN hp ==> (psi:real^2->real^3) z IN aw) \/
                (!z. z IN hm ==> (psi:real^2->real^3) z IN aw)` MP_TAC THENL
   [USE_THEN "halves" (MP_TAC o SPEC `hp:real^2->bool`) THEN
    USE_THEN "halves" (MP_TAC o SPEC `hm:real^2->bool`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ABBREV_TAC `z0 = (r / &2) % basis 2:real^2`;
    ABBREV_TAC `z0 = (--(r / &2)) % basis 2:real^2`] THEN
  USE_THEN "fin" MATCH_MP_TAC THEN EXISTS_TAC `z0:real^2` THEN
  (SUBGOAL_THEN `(z0:real^2)$1 = &0 /\ ~(z0$2 = &0)` STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "z0" THEN
     SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(z0:real^2) IN hp` ASSUME_TAC;
    SUBGOAL_THEN `(z0:real^2) IN hm` ASSUME_TAC] THEN
  TRY(CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]) THEN
  MAP_EVERY EXPAND_TAC ["hp"; "hm"; "z0"] THEN
  SIMP_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;
(* ========================================================================= *)
(* The broken line of Lemma 9 (Moise p.243): for a triangle tau at v,       *)
(* the rims of the two edges of tau at v lie in one connected subset of     *)
(* the trace in A_v together with the two rims.  Otherwise a Urysohn map    *)
(* C_v -> S^1, constant on the trace, would kill H_1 of the face torus.     *)
(* ========================================================================= *)

let MOI_S4L_PL_CELL2_TOPO = prove
 (`!(d:real^N->bool) b.
     pl_cell_with_boundary 2 d b
     ==> connected b /\ ~(b = {}) /\ connected (d DIFF b) /\ ~(d DIFF b = {}) /\
         d SUBSET closure (d DIFF b) /\ path_connected d /\ b SUBSET d /\ compact d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  REWRITE_TAC[pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact(k:real^N->bool) /\ convex k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool) /\
                k DIFF relative_frontier k = relative_interior k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF b = IMAGE (f:real^N->real^N) (relative_interior k)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `relative_interior k:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^N->bool)` THEN
    UNDISCH_TAC `!x. x IN k ==> (g:real^N->real^N)((f:real^N->real^N) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous_on relative_interior k /\
                f continuous_on relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_SPHERE_GEN THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN STRIP_TAC THEN
    UNDISCH_TAC `aff_dim(k:real^N->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `k = closure(relative_interior k:real^N->bool)` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_IMP_PATH_CONNECTED];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_S4L_HOM_INDUCED_CONST = prove
 (`!(top:A topology) (top':B topology) (b:B) c.
     b IN topspace top'
     ==> hom_induced (&1) (top,{}) (top',{}) (\x. b) c =
         group_id(homology_group(&1,top'))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. b:B) = (\y. y) o (\x. b)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:int`; `top:A topology`; `subtopology top' {b:B}`; `top':B topology`;
                 `\x:A. b:B`; `\y:B. y`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_SING] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `hom_induced (&1) (top,{}) (subtopology top' {b},{}) (\x:A. b:B) c =
                group_id(homology_group(&1,subtopology top' {b}))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology top' {b:B}`; `b:B`] HOMOLOGY_DIMENSION_AXIOM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN CONV_TAC INT_REDUCE_CONV THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[trivial_group] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&1:int`; `top:A topology`; `subtopology top' {b:B}`; `\x:A. b:B`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    REWRITE_TAC[group_homomorphism] THEN STRIP_TAC THEN
    ASM_CASES_TAC `c IN group_carrier (homology_group (&1,(top:A topology)))` THENL
     [ASM SET_TAC[];
      MP_TAC(ISPECL [`&1:int`; `top:A topology`; `{}:A->bool`; `subtopology top' {b:B}`;
                     `{}:B->bool`; `\x:A. b:B`; `c:((num->real)->A)frag->bool`]
        HOM_INDUCED_DEFAULT) THEN
      ASM_REWRITE_TAC[GSYM homology_group]];
    MP_TAC(ISPECL [`&1:int`; `subtopology top' {b:B}`; `top':B topology`; `\y:B. y`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism]]);;

let MOI_S4L_FACE_TORUS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s v w1 w2.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {x | x IN s /\ {x} IN kk} = {v,w1,w2} /\
     ~(v = w1) /\ ~(v = w2) /\ ~(w1 = w2) /\
     segment[v,w1] IN kk /\ segment[v,w2] IN kk /\ segment[w1,w2] IN kk
     ==> IMAGE f1 (moi_s34_ft tt kk s) =
         IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w1) UNION
         IMAGE f1 (moi_s34_vb tt kk w2) /\
         IMAGE f1 (moi_s34_vb tt kk v) INTER
         (IMAGE f1 (moi_s34_vb tt kk w1) UNION IMAGE f1 (moi_s34_vb tt kk w2)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) UNION
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) INTER
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) = {} /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) INTER
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1 INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) INTER
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2 INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_bd tt kk) INTER IMAGE f1 (moi_s34_vb tt kk v) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1))
           (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1 INTER moi_s34_bd tt kk)) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2))
           (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2 INTER moi_s34_bd tt kk)) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_vb tt kk w1 INTER moi_s34_vb tt kk w2))
           (IMAGE f1 (moi_s34_vb tt kk w1 INTER moi_s34_vb tt kk w2 INTER moi_s34_bd tt kk)) /\
         pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
         pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk w1)) /\
         pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk w2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN kk /\ {w1} IN kk /\ {w2} IN kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v:real^N,w1,w2}` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE o check (fun th ->
    concl th = `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_FRAME_F1 o
    check (moi_s4l_has "moi_s34_frame")) THEN

  SUBGOAL_THEN `moi_s34_vb (tt:(real^N->bool)->bool) kk v SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk w1 SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk w2 SUBSET moi_s34_nb tt kk`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN moi_s34_simp kk (&1)
        ==> pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))
              (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`
  (LABEL_TAC "cells") THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^N. {a} IN kk /\ {b} IN kk /\ ~(a = b) /\ segment[a,b] IN kk
      ==> moi_s34_sd tt kk (segment[a,b]) = moi_s34_vb tt kk a INTER moi_s34_vb tt kk b /\
          segment[a,b] IN moi_s34_simp kk (&1)`
  (LABEL_TAC "sdab") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[a:real^N,b] IN moi_s34_simp kk (&1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4D_SAN_SD_EDGE THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`] MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^N->bool. a SUBSET moi_s34_nb tt kk /\ b SUBSET moi_s34_nb tt kk
      ==> IMAGE (f1:real^N->real^3) a INTER IMAGE f1 b = IMAGE f1 (a INTER b)`
  (LABEL_TAC "imgs") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S4L_IMAGE_INTER_INJ THEN
    EXISTS_TAC `moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_bd (tt:(real^N->bool)->bool) kk SUBSET moi_s34_nb tt kk`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_ft] THEN
    SUBGOAL_THEN `{moi_s34_vb (tt:(real^N->bool)->bool) kk x | x | x IN s /\ {x} IN kk} =
                  {moi_s34_vb tt kk v, moi_s34_vb tt kk w1, moi_s34_vb tt kk w2}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (moi_s34_vb (tt:(real^N->bool)->bool) kk)
                    {x | x IN s /\ {x} IN kk}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES];
      REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY; IMAGE_UNION]];
    REWRITE_TAC[UNION_OVER_INTER] THEN BINOP_TAC THEN
    USE_THEN "imgs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  ((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) INTER
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2))` THEN
    CONJ_TAC THENL
     [USE_THEN "imgs" MATCH_MP_TAC THEN ASM SET_TAC[];
      SUBGOAL_THEN `(moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_vb tt kk w1) INTER
                    (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) = {}`
      (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN
      MATCH_MP_TAC(SET_RULE `(a:real^N->bool) INTER b INTER c = {}
                             ==> (a INTER b) INTER (a INTER c) = {}`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  ((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) INTER
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))` THEN
    CONJ_TAC THENL
     [USE_THEN "imgs" MATCH_MP_TAC THEN ASM SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  ((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) INTER
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))` THEN
    CONJ_TAC THENL
     [USE_THEN "imgs" MATCH_MP_TAC THEN ASM SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_bd tt kk INTER moi_s34_vb tt kk v)` THEN
    CONJ_TAC THENL
     [USE_THEN "imgs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    USE_THEN "sdab" (MP_TAC o SPECL [`v:real^N`; `w1:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM INTER_ASSOC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `moi_s34_sd tt kk (segment[v:real^N,w1])`)) THEN
    USE_THEN "cells" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "sdab" (MP_TAC o SPECL [`v:real^N`; `w2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM INTER_ASSOC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `moi_s34_sd tt kk (segment[v:real^N,w2])`)) THEN
    USE_THEN "cells" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "sdab" (MP_TAC o SPECL [`w1:real^N`; `w2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM INTER_ASSOC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `moi_s34_sd tt kk (segment[w1:real^N,w2])`)) THEN
    USE_THEN "cells" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[MOI_S4L_AV_BASIC];
    ASM_MESON_TAC[MOI_S4L_AV_BASIC];
    ASM_MESON_TAC[MOI_S4L_AV_BASIC]]);;

let MOI_S4L_CEXP_FACTS = prove
 (`cexp((Cx(&2) * Cx pi * ii) * Cx(&0)) = Cx(&1) /\
   cexp((Cx(&2) * Cx pi * ii) * Cx(&1)) = Cx(&1) /\
   (!r. norm(cexp((Cx(&2) * Cx pi * ii) * Cx r)) = &1)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_RZERO; CEXP_0];
    MP_TAC(SPEC `&1` CEXP_INTEGER_2PI) THEN REWRITE_TAC[INTEGER_CLOSED] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    GEN_TAC THEN REWRITE_TAC[NORM_CEXP] THEN
    REWRITE_TAC[COMPLEX_RING `(a * b * ii) * c = ii * (a * b * c)`; GSYM CX_MUL] THEN
    REWRITE_TAC[RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0]]);;

let MOI_S4L_PL_BALL_PATH_CONNECTED = prove
 (`!n s:real^N->bool. pl_ball n s ==> path_connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(lhs(concl th)) = `k:real^N->bool`)) THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_IMP_PATH_CONNECTED]);;

(* A map to the circle that is constant on j kills every loop class of s *)
(* when j carries H_1 of s.                                               *)
let MOI_S4L_CARRIES_H1_KILL = prove
 (`!(j:real^N->bool) s (phi:real^N->complex) g.
      carries_h1 j s /\ j SUBSET s /\ phi continuous_on s /\
      IMAGE phi s SUBSET sphere(vec 0,&1) /\ (!x. x IN j ==> phi x = Cx(&1)) /\
      path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g
      ==> homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
            (frag_of (path_simplex ((phi o g) o lift))) =
          group_id (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carries_h1; group_image] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_in (subtopology euclidean s) ((g:real^1->real^N) o lift) /\
                (g o lift) (&0) = (g o lift) (&1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^N) = pathstart g` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean s,
                  subtopology euclidean (sphere(vec 0:real^2,&1))) (phi:real^N->complex)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `phi:real^N->complex`; `(g:real^1->real^N) o lift`]
    MOI_FH1_HOM_INDUCED_LOOP) THEN
  ASM_REWRITE_TAC[GSYM o_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `(g:real^1->real^N) o lift`]
    MOI_FH1_LOOP_CLASS_IN_CARRIER) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && moi_s4l_has "hom_induced" th)) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((num->real)->real^N)frag->bool`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
                 `subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `\x:real^N. x`; `phi:real^N->complex`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CONTINUOUS_ON_ID; IMAGE_ID]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:((num->real)->real^N)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`; `{}:real^N->bool`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`; `{}:complex->bool`;
                 `(phi:real^N->complex) o (\x:real^N. x)`; `\x:real^N. Cx(&1)`]
    HOM_INDUCED_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_S4L_HOM_INDUCED_CONST THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM]);;

(* A loop whose image under phi lifts through cexp with lift increment     *)
(* 2 pi i has a nonzero class in H_1 of the circle.                       *)
let MOI_S4L_LIFT_CLASS_NONZERO = prove
 (`!(phi:real^N->complex) (psi:real^N->real^1) (al:real^1->real^N) be cv.
      psi continuous_on (:real^N) /\ path al /\ path be /\ path_image al SUBSET cv /\
      pathfinish al = pathstart be /\ pathfinish be = pathstart al /\
      psi(pathstart al) = vec 0 /\ psi(pathfinish al) = vec 1 /\
      (!z. z IN cv ==> phi z = cexp((Cx(&2) * Cx pi * ii) * Cx(drop(psi z)))) /\
      (!z. z IN path_image be ==> phi z = Cx(&1)) /\
      path (phi o (al ++ be)) /\ path_image (phi o (al ++ be)) SUBSET sphere(vec 0,&1)
      ==> ~(homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
              (frag_of (path_simplex ((phi o (al ++ be)) o lift))) =
            group_id (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "phicv" o check (fun th -> moi_s4l_has "cexp" th)) THEN
  FIRST_X_ASSUM(LABEL_TAC "phibe" o check (fun th ->
    is_forall(concl th) && moi_s4l_has "path_image" th)) THEN
  ABBREV_TAC `ll = ((\z. (Cx(&2) * Cx pi * ii) * Cx(drop((psi:real^N->real^1) z))) o
                    (al:real^1->real^N)) ++ (\t:real^1. (Cx(&2) * Cx pi * ii) * Cx(&1))` THEN
  SUBGOAL_THEN `path(ll:real^1->complex) /\ pathstart ll = (Cx(&2) * Cx pi * ii) * Cx(&0) /\
                pathfinish ll = (Cx(&2) * Cx pi * ii) * Cx(&1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ll" THEN
    SUBGOAL_THEN `pathfinish ((\z. (Cx(&2) * Cx pi * ii) * Cx(drop((psi:real^N->real^1) z))) o
                    (al:real^1->real^N)) = pathstart (\t:real^1. (Cx(&2) * Cx pi * ii) * Cx(&1))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PATHFINISH_COMPOSE; DROP_VEC] THEN REWRITE_TAC[pathstart]; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_COMPOSE] THEN
    ASM_REWRITE_TAC[DROP_VEC; pathfinish; path; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[GSYM path] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                    ==> ((phi:real^N->complex) o (al ++ be)) t = (cexp o ll) t`
  ASSUME_TAC THENL
   [EXPAND_TAC "ll" THEN REWRITE_TAC[joinpaths; o_THM; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [USE_THEN "phicv" MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (al:real^1->real^N) SUBSET cv` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MOI_S4L_CEXP_FACTS] THEN USE_THEN "phibe" MATCH_MP_TAC THEN
      REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `&2 % t - vec 1:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops (sphere(vec 0,&1)) ((phi:real^N->complex) o (al ++ be))
                  (cexp o ll)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  MP_TAC(ISPEC `cexp o (ll:real^1->complex)` MOI_FH1_CIRCLE_CLASS_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CEXP];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC `ll:real^1->complex` WINDING_NUMBER_COMPOSE_CEXP) THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

let MOI_S4L_BROKEN_LINE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s c v w1 w2.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\ moi_s34_fb1 tt kk h f1 car s c /\
     {x | x IN s /\ {x} IN kk} = {v,w1,w2} /\
     ~(v = w1) /\ ~(v = w2) /\ ~(w1 = w2) /\
     segment[v,w1] IN kk /\ segment[v,w2] IN kk /\ segment[w1,w2] IN kk
     ==> ?z. connected z /\
             z SUBSET (moi_s34_trace tt kk f1 c INTER
                       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) UNION
                      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1 INTER
                                moi_s34_bd tt kk) UNION
                      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2 INTER
                                moi_s34_bd tt kk) /\
             ~(z INTER IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1 INTER
                                 moi_s34_bd tt kk) = {}) /\
             ~(z INTER IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2 INTER
                                 moi_s34_bd tt kk) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v:real^N`; `w1:real^N`; `w2:real^N`] MOI_S4L_FACE_TORUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `c:real^3->bool`;
                 `v:real^N`; `w1:real^N`; `w2:real^N`] MOI_S4L_TRACE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `carries_h1 (moi_s34_trace tt kk f1 c INTER IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))
               (IMAGE f1 (moi_s34_ft tt kk s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s c` THEN
    REWRITE_TAC[moi_s34_fb1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) SUBSET
    IMAGE f1 (moi_s34_vb tt kk v) /\
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1) SUBSET
    IMAGE f1 (moi_s34_vb tt kk w1) /\
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) SUBSET
    IMAGE f1 (moi_s34_vb tt kk v) /\
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2) SUBSET
    IMAGE f1 (moi_s34_vb tt kk w2) /\
    IMAGE f1 (moi_s34_vb tt kk w1 INTER moi_s34_vb tt kk w2) SUBSET
    IMAGE f1 (moi_s34_vb tt kk w1) /\
    IMAGE f1 (moi_s34_vb tt kk w1 INTER moi_s34_vb tt kk w2) SUBSET
    IMAGE f1 (moi_s34_vb tt kk w2) /\
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_vb tt kk v) /\
    moi_s34_trace tt kk f1 c SUBSET IMAGE f1 (moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]) THEN
    REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v:real^N,w1,w2}` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `cv = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `cw1 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w1)` THEN
  ABBREV_TAC `cw2 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w2)` THEN
  ABBREV_TAC `d1 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1)` THEN
  ABBREV_TAC `d2 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2)` THEN
  ABBREV_TAC `d3 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w1 INTER moi_s34_vb tt kk w2)` THEN
  ABBREV_TAC `r1 = IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w1 INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `r2 = IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w2 INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `mm = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `tr = moi_s34_trace tt kk (f1:real^N->real^3) c` THEN
  ABBREV_TAC `ff = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  (* basic topology *)
  MP_TAC(ISPECL [`d1:real^3->bool`; `r1:real^3->bool`] MOI_S4L_PL_CELL2_TOPO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `r2:real^3->bool`] MOI_S4L_PL_CELL2_TOPO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(d3:real^3->bool = {})` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      can (find_term ((=) `d3:real^3->bool`)) (concl th))) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(cv:real^3->bool) /\ compact(cw1:real^3->bool) /\
                compact(cw2:real^3->bool) /\ path_connected cv /\
                path_connected(cw1 UNION cw2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`3`; `cv:real^3->bool`] MOI_S4L_PL_BALL_COMPACT) THEN
    MP_TAC(ISPECL [`3`; `cw1:real^3->bool`] MOI_S4L_PL_BALL_COMPACT) THEN
    MP_TAC(ISPECL [`3`; `cw2:real^3->bool`] MOI_S4L_PL_BALL_COMPACT) THEN
    MP_TAC(ISPECL [`3`; `cv:real^3->bool`] MOI_S4L_PL_BALL_PATH_CONNECTED) THEN
    MP_TAC(ISPECL [`3`; `cw1:real^3->bool`] MOI_S4L_PL_BALL_PATH_CONNECTED) THEN
    MP_TAC(ISPECL [`3`; `cw2:real^3->bool`] MOI_S4L_PL_BALL_PATH_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!d:real^3->bool. d SUBSET a /\ d SUBSET b /\ ~(d = {})
      ==> ~(a INTER b = {})`) THEN
    EXISTS_TAC `d3:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "nz" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  (* the compact set Y and the component of rim 1 *)
  SUBGOAL_THEN `compact(r1:real^3->bool) /\ compact(r2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d1:real^3->bool) INTER av = r1` THEN
    UNDISCH_TAC `(d2:real^3->bool) INTER av = r2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_SIMP_TAC[COMPACT_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `yy = (tr INTER av) UNION r1 UNION (r2:real^3->bool)` THEN
  SUBGOAL_THEN `compact(yy:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "yy" THEN ASM_SIMP_TAC[COMPACT_UNION; COMPACT_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) INTER yy SUBSET r1 /\ d2 INTER yy SUBSET r2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "yy" THEN
    UNDISCH_TAC `(d1:real^3->bool) INTER av = r1` THEN
    UNDISCH_TAC `(d2:real^3->bool) INTER av = r2` THEN
    UNDISCH_TAC `(d1:real^3->bool) INTER d2 = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x1:real^3. x1 IN r1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r1:real^3->bool = {})` THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `cc = connected_component (yy:real^3->bool) x1` THEN
  SUBGOAL_THEN `connected(cc:real^3->bool) /\ cc SUBSET yy /\ r1 SUBSET cc /\ closed cc`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "yy" THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_CONNECTED_COMPONENT THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(cc:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `yy:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc INTER (r2:real^3->bool) = {}` ASSUME_TAC THENL
   [USE_THEN "nz" (MP_TAC o SPEC `cc:real^3->bool`) THEN
    REWRITE_TAC[ASSUME `connected(cc:real^3->bool)`; ASSUME `(cc:real^3->bool) SUBSET yy`] THEN
    UNDISCH_TAC `(r1:real^3->bool) SUBSET cc` THEN UNDISCH_TAC `(x1:real^3) IN r1` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* separation of the component from rim 2 *)
  MP_TAC(ISPECL [`subtopology euclidean (yy:real^3->bool)`; `cc:real^3->bool`;
                 `r2:real^3->bool`] SEPARATED_BETWEEN_COMPACT_CONNECTED_COMPONENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_LOCALLY_COMPACT_SPACE THEN
      REWRITE_TAC[compact_space; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN; SUBSET_REFL] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
      REWRITE_TAC[EUCLIDEAN_CONNECTED_COMPONENTS_OF] THEN EXPAND_TAC "cc" THEN
      REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
      EXPAND_TAC "yy" THEN UNDISCH_TAC `(x1:real^3) IN r1` THEN SET_TAC[];
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      EXPAND_TAC "yy" THEN SET_TAC[];
      UNDISCH_TAC `cc INTER (r2:real^3->bool) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^3->bool` (X_CHOOSE_THEN `vv:real^3->bool`
    STRIP_ASSUME_TAC) o REWRITE_RULE[separated_between; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN `closed(uu:real^3->bool) /\ closed(vv:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `yy:real^3->bool` THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THENL
     [SUBGOAL_THEN `uu = (yy:real^3->bool) DIFF vv` SUBST1_TAC;
      SUBGOAL_THEN `vv = (yy:real^3->bool) DIFF uu` SUBST1_TAC] THEN
    TRY(MATCH_MP_TAC CLOSED_IN_DIFF THEN
        ASM_REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
        NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`(uu:real^3->bool) UNION vv = yy`; `DISJOINT (uu:real^3->bool) vv`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* Urysohn *)
  MP_TAC(ISPECL [`d1 UNION uu:real^3->bool`; `d2 UNION vv:real^3->bool`;
                 `vec 0:real^1`; `vec 1:real^1`] URYSOHN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC [`(d1:real^3->bool) INTER d2 = {}`; `(d1:real^3->bool) INTER yy SUBSET r1`;
      `(d2:real^3->bool) INTER yy SUBSET r2`; `(uu:real^3->bool) UNION vv = yy`;
      `DISJOINT (uu:real^3->bool) vv`; `(r1:real^3->bool) SUBSET cc`; `(cc:real^3->bool) SUBSET uu`;
      `(r2:real^3->bool) SUBSET vv`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `psi0:real^3->real^1` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ps0") (LABEL_TAC "ps1")))))] THEN
  (* the circle-valued map phi *)
  SUBGOAL_THEN `?phi:real^3->complex. !z. phi z =
      if z IN cv then cexp((Cx(&2) * Cx pi * ii) * Cx(drop((psi0:real^3->real^1) z)))
      else Cx(&1)`
  (X_CHOOSE_THEN `phi:real^3->complex` (LABEL_TAC "phidef")) THENL
   [EXISTS_TAC `\z:real^3. if z IN cv
      then cexp((Cx(&2) * Cx pi * ii) * Cx(drop((psi0:real^3->real^1) z))) else Cx(&1)` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (psi0:real^3->real^1) z = vec 0 \/ psi0 z = vec 1
                           ==> (phi:real^3->complex) z = Cx(&1)` (LABEL_TAC "phi01") THENL
   [X_GEN_TAC `z:real^3` THEN USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[th; DROP_VEC; MOI_S4L_CEXP_FACTS; COND_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN cw1 UNION cw2 ==> (phi:real^3->complex) z = Cx(&1)`
  (LABEL_TAC "phiw") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(z:real^3) IN cv` THENL
     [USE_THEN "phi01" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN d1 UNION d2` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(z:real^3) IN cw1 UNION cw2`; `(z:real^3) IN cv`;
          `cv INTER (cw1 UNION cw2) = d1 UNION (d2:real^3->bool)`] THEN SET_TAC[];
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
         [DISJ1_TAC THEN USE_THEN "ps0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
          DISJ2_TAC THEN USE_THEN "ps1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]]];
      USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (phi:real^3->complex) z IN sphere(vec 0,&1)` (LABEL_TAC "phis") THENL
   [X_GEN_TAC `z:real^3` THEN USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[IN_SPHERE_0; MOI_S4L_CEXP_FACTS; COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN tr ==> (phi:real^3->complex) z = Cx(&1)` (LABEL_TAC "phitr") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(z:real^3) IN cv` THENL
     [USE_THEN "phi01" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN uu UNION vv` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(z:real^3) IN tr`; `(z:real^3) IN cv`;
          `(tr:real^3->bool) SUBSET mm`; `(mm:real^3->bool) INTER cv = av`;
          `(uu:real^3->bool) UNION vv = yy`;
          `tr INTER av UNION r1 UNION r2 = (yy:real^3->bool)`] THEN SET_TAC[];
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
         [DISJ1_TAC THEN USE_THEN "ps0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
          DISJ2_TAC THEN USE_THEN "ps1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]]];
      USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->complex) continuous_on ff` ASSUME_TAC THENL
   [SUBGOAL_THEN `phi = \z:real^3. if z IN cv
       then cexp((Cx(&2) * Cx pi * ii) * Cx(drop((psi0:real^3->real^1) z))) else Cx(&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN USE_THEN "phidef" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    UNDISCH_TAC `ff = cv UNION cw1 UNION (cw2:real^3->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_UNION; CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^3. cexp((Cx(&2) * Cx pi * ii) * Cx(drop((psi0:real^3->real^1) z)))) =
                    cexp o (\z. (Cx(&2) * Cx pi * ii) * Cx(drop(psi0 z)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TAUT `(p /\ ~p) <=> F`] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "phiw" (MP_TAC o SPEC `z:real^3`) THEN
      USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `(z:real^3) IN cv`; ASSUME `(z:real^3) IN cw1 UNION cw2`]];
    ALL_TAC] THEN
  (* the core loop *)
  SUBGOAL_THEN `?x2:real^3. x2 IN r2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r2:real^3->bool = {})` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^3) IN d1 /\ (x2:real^3) IN d2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(x1:real^3) IN r1`; `(x2:real^3) IN r2`;
      `(r1:real^3->bool) SUBSET d1`; `(r2:real^3->bool) SUBSET d2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?al:real^1->real^3. path al /\ path_image al SUBSET cv /\
                  pathstart al = x1 /\ pathfinish al = x2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_connected(cv:real^3->bool)` THEN REWRITE_TAC[path_connected] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(x1:real^3) IN d1`; `(x2:real^3) IN d2`;
      `(d1:real^3->bool) SUBSET cv`; `(d2:real^3->bool) SUBSET cv`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?be:real^1->real^3. path be /\ path_image be SUBSET cw1 UNION cw2 /\
                  pathstart be = x2 /\ pathfinish be = x1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_connected(cw1 UNION cw2:real^3->bool)` THEN
    REWRITE_TAC[path_connected] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(x1:real^3) IN d1`; `(x2:real^3) IN d2`;
      `(d1:real^3->bool) SUBSET cw1`; `(d2:real^3->bool) SUBSET cw2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path((al:real^1->real^3) ++ be) /\ path_image(al ++ be) SUBSET ff /\
                pathfinish(al ++ be) = pathstart(al ++ be)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    MAP_EVERY UNDISCH_TAC [`path_image (al:real^1->real^3) SUBSET cv`;
      `path_image (be:real^1->real^3) SUBSET cw1 UNION cw2`;
      `ff = cv UNION cw1 UNION (cw2:real^3->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the homology contradiction *)
  MP_TAC(ISPECL [`phi:real^3->complex`; `psi0:real^3->real^1`; `al:real^1->real^3`;
                 `be:real^1->real^3`; `cv:real^3->bool`] MOI_S4L_LIFT_CLASS_NONZERO) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN USE_THEN "ps0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      ASM_REWRITE_TAC[] THEN USE_THEN "ps1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "phidef" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN USE_THEN "phiw" MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(z:real^3) IN path_image be`;
        `path_image (be:real^1->real^3) SUBSET cw1 UNION cw2`] THEN SET_TAC[];
      MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ff:real^3->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[PATH_IMAGE_COMPOSE; SUBSET; FORALL_IN_IMAGE] THEN
      USE_THEN "phis" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
  MATCH_MP_TAC MOI_S4L_CARRIES_H1_KILL THEN
  MAP_EVERY EXISTS_TAC [`tr INTER ff:real^3->bool`; `ff:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN USE_THEN "phis" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "phitr" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

