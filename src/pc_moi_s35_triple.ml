(* ========================================================================= *)
(* pc_moi_s35_triple: the Sec 35 foundation fact TUBE_TRIPLE =               *)
(* MOI_S35_TUBE_TRIPLE (pc_moi_s35_stmt.ml, 7.1): three derived dual cells   *)
(* of distinct vertices of the graph never meet.  A point in all three lies  *)
(* in the hull of barycentres of a chain whose simplices contain the three   *)
(* vertices; the derived neighbourhood reaches it through a simplex of the   *)
(* graph containing them, which is a segment, so two of the vertices         *)
(* coincide.  Adapts MOI_FTA_CELLS_DISJOINT (pc_moi_fnd_tubea).  Moise GTM   *)
(* 47, p.248 (Fig. 35.1).                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* TUBE_TRIPLE.                                                              *)
(* ------------------------------------------------------------------------- *)

let TUBE_TRIPLE = prove
 (MOI_S35_TUBE_TRIPLE,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{u:real^N} IN t /\ {v:real^N} IN t /\ {w:real^N} IN t`
  STRIP_ASSUME_TAC THENL
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
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h2:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h3:(real^N->bool)->bool`;
                 `w:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre (h1 INTER h2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t ((h1 INTER h2):(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre ((h1 INTER h2) INTER h3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `(h1 INTER h2):(real^N->bool)->bool`;
                   `h3:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `h = ((h1 INTER h2) INTER h3):(real^N->bool)->bool` THEN
  SUBGOAL_THEN `moi_bar_chain t (h:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN h ==> u IN s /\ v IN s /\ w IN s`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
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
  SUBGOAL_THEN `(sg:real^N->bool) IN l /\ sg IN h` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `sg = segment[u:real^N,v] /\ sg = segment[u:real^N,w]` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
    `(a:real^N->bool) = b /\ a = c ==> b = c`)) THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  MAP_EVERY UNDISCH_TAC [`~(u:real^N = v)`; `~(v:real^N = w)`] THEN
  SET_TAC[]);;

