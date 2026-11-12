(* ========================================================================= *)
(* pc_moi_fnd_tubea: foundations of the Moise PL core (Moise, Geometric     *)
(* Topology in Dimensions 2 and 3, GTM 47, p.223: the tube N of a graph l   *)
(* in a combinatorial 3-manifold t, its dual cells C_v and the splitting    *)
(* disks C_u INTER C_v).  Main theorems (proving the statement terms of     *)
(* pc_moi_fnd_stmt.ml):                                                      *)
(*   GRAPH_IN_COMPLEX_BARYCENTRIC = MOI_FND_GRAPH_IN_COMPLEX_BARYCENTRIC     *)
(*   GRAPH_TUBE_DUAL_CELLS        = MOI_FND_GRAPH_TUBE                       *)
(* Notation in comments: t1 = barycentric subdivision of t, t2 = that of   *)
(* t1, H(f) = convex hull of the barycentres of a chain f.                  *)
(* The first section: basic facts about chains and their barycentric        *)
(* simplices.                                                                *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 0. Complexes: lf complexes, their subcomplexes and subdivisions.         *)
(* ------------------------------------------------------------------------- *)

let MOI_FTA_LF_BAR = prove
 (`!c:(real^N->bool)->bool. lf_simplicial_complex c ==> moi_bar_complex c`,
  SIMP_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX]);;

let MOI_FTA_BAR_SUB = prove
 (`!(l:(real^N->bool)->bool) c.
        moi_bar_complex c /\ simplicial_subcomplex l c ==> moi_bar_complex l`,
  REWRITE_TAC[moi_bar_complex; simplicial_subcomplex; SUBSET] THEN
  MESON_TAC[]);;

let MOI_FTA_BS_FACTS = prove
 (`!t:(real^N->bool)->bool.
        lf_simplicial_complex t
        ==> moi_bar_complex t /\
            lf_simplicial_complex (barycentric_subdivision t) /\
            moi_bar_complex (barycentric_subdivision t) /\
            UNIONS (barycentric_subdivision t) = UNIONS t /\
            lf_simplicial_complex
              (barycentric_subdivision (barycentric_subdivision t)) /\
            moi_bar_complex
              (barycentric_subdivision (barycentric_subdivision t)) /\
            UNIONS (barycentric_subdivision (barycentric_subdivision t)) =
            UNIONS t`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision
     (barycentric_subdivision (t:(real^N->bool)->bool)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTA_LF_BAR; UNIONS_BARYCENTRIC_SUBDIVISION]);;

let MOI_FTA_SUB_FACTS = prove
 (`!(t:(real^N->bool)->bool) l.
        lf_simplicial_complex t /\ simplicial_subcomplex l t
        ==> moi_bar_complex l /\ lf_simplicial_complex l /\
            simplicial_subcomplex (barycentric_subdivision l)
                                  (barycentric_subdivision t) /\
            UNIONS (barycentric_subdivision l) = UNIONS l /\
            l SUBSET t`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_BAR_SUB THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FTA_LF_BAR];
    ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ASM_MESON_TAC[BARYCENTRIC_SUBDIVISION_SUBCOMPLEX];
    ASM_MESON_TAC[BARYCENTRIC_SUBDIVISION_SUBCOMPLEX];
    ASM_MESON_TAC[simplicial_subcomplex]]);;

(* ------------------------------------------------------------------------- *)
(* 1. Barycentres of points and segments.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FTA_BARY_SING = prove
 (`!a:real^N. simplex_barycentre {a} = a`,
  GEN_TAC THEN
  MP_TAC(ISPEC `{a:real^N}` MOI_BAR_SIMPLEX_BARYCENTRE_HULL) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_1; CONVEX_HULL_SING; BARYCENTRE_1]);;

let MOI_FTA_BARY_SEGMENT = prove
 (`!a b:real^N. simplex_barycentre (segment[a,b]) = midpoint(a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MP_TAC(ISPEC `{a:real^N,b}` MOI_BAR_SIMPLEX_BARYCENTRE_HULL) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_2; BARYCENTRE_2]);;

(* ------------------------------------------------------------------------- *)
(* 2. Chains: least elements, singleton chains, hulls.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_FTA_TOTAL_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f
        ==> ~(f = {}) /\
            (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
            ==> INTERS f IN f`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ch")) THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_1; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `INTERS f IN (f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "ch" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[INTERS_INSERT; IN_INSERT] THEN
  REMOVE_THEN "ch" (MP_TAC o SPECL [`s:real^N->bool`; `INTERS f:real^N->bool`]) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `s SUBSET INTERS f:real^N->bool` THEN
    REWRITE_TAC[SET_RULE `(s:real^N->bool) SUBSET t ==> s INTER t = s`];
    DISJ2_TAC THEN
    SUBGOAL_THEN `s INTER INTERS f:real^N->bool = INTERS f`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `INTERS f SUBSET s:real^N->bool` THEN
    REWRITE_TAC[SET_RULE `(t:real^N->bool) SUBSET s ==> s INTER t = t`]]);;

let MOI_FTA_CHAIN_MIN = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_chain c f /\ ~(f = {})
        ==> INTERS f IN f /\ !s. s IN f ==> INTERS f SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MOI_FTA_TOTAL_INTERS) THEN ASM_REWRITE_TAC[];
    SET_TAC[]]);;

let MOI_FTA_CHAIN_SING = prove
 (`!c s:real^N->bool. s IN c /\ ~(s = {}) ==> moi_bar_chain c {s}`,
  REWRITE_TAC[moi_bar_chain; FINITE_SING; IN_SING; SING_SUBSET] THEN
  MESON_TAC[SUBSET_REFL]);;

let MOI_FTA_CHAIN_INTER = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_chain c f ==> moi_bar_chain c (f INTER g)`,
  MESON_TAC[MOI_BAR_CHAIN_SUBSET; INTER_SUBSET]);;

let MOI_FTA_CHAIN_INSERT = prove
 (`!c f s:real^N->bool.
        moi_bar_chain c f /\ s IN c /\ ~(s = {}) /\
        (!t. t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> moi_bar_chain c (s INSERT f)`,
  REWRITE_TAC[moi_bar_chain; FINITE_INSERT; IN_INSERT; INSERT_SUBSET] THEN
  MESON_TAC[SUBSET_REFL]);;

let MOI_FTA_HULL_EMPTY = prove
 (`!f:(real^N->bool)->bool.
        convex hull (IMAGE simplex_barycentre f) = {} <=> f = {}`,
  REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY]);;

let MOI_FTA_HULL_INJ = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
        convex hull (IMAGE simplex_barycentre f) =
        convex hull (IMAGE simplex_barycentre g)
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_FTA_HULL_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(relative_interior (convex hull (IMAGE simplex_barycentre
        (f:(real^N->bool)->bool))) = {})`
  MP_TAC THENL
   [SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[MOI_FTA_HULL_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_RI_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_FTA_HULL_SUBSET = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
        convex hull (IMAGE simplex_barycentre f) SUBSET
        convex hull (IMAGE simplex_barycentre g)
        ==> f SUBSET g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) = f INTER g`
   (fun th -> ONCE_REWRITE_TAC[th] THEN REWRITE_TAC[INTER_SUBSET]) THEN
  MATCH_MP_TAC MOI_FTA_HULL_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[]);;

let MOI_FTA_BARY_IN_HULL = prove
 (`!c f s:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN c /\ ~(s = {})
        ==> (simplex_barycentre s IN convex hull (IMAGE simplex_barycentre f) <=>
             s IN f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{s:real^N->bool}`;
                   `f:(real^N->bool)->bool`] MOI_FTA_HULL_SUBSET) THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING;
                 SING_SUBSET];
    DISCH_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]);;

let MOI_FTA_BARY_INJ = prove
 (`!c s t:real^N->bool.
        moi_bar_complex c /\ s IN c /\ t IN c /\ ~(s = {}) /\ ~(t = {}) /\
        simplex_barycentre s = simplex_barycentre t
        ==> s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{t:real^N->bool}`;
                 `s:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING]);;

(* A vertex of t lying in a barycentric simplex is a member of its chain,   *)
(* and then lies in every member of the chain.                              *)

let MOI_FTA_VERTEX_IN_HULL = prove
 (`!c f (v:real^N).
        moi_bar_complex c /\ moi_bar_chain c f /\ {v} IN c /\
        v IN convex hull (IMAGE simplex_barycentre f)
        ==> {v} IN f /\ !s. s IN f ==> v IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `{v:real^N}`] MOI_FTA_BARY_IN_HULL) THEN
  ASM_REWRITE_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
  DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o
    last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; SET_TAC[]]);;

(* Points of a barycentric simplex lying in a subcomplex lie in the         *)
(* barycentric simplex of the part of the chain inside the subcomplex.      *)

let MOI_FTA_HULL_SUBCOMPLEX = prove
 (`!c l f (x:real^N).
        moi_bar_complex c /\ simplicial_subcomplex l c /\ moi_bar_chain c f /\
        x IN convex hull (IMAGE simplex_barycentre f) /\ x IN UNIONS l
        ==> x IN convex hull (IMAGE simplex_barycentre (f INTER l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `e:real^N->bool`; `x:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `{u:real^N->bool | u face_of e}` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_BAR_FACES_SUBSET_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:(real^N->bool)->bool) SUBSET l` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {u:real^N->bool | u face_of e} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x IN convex hull (IMAGE simplex_barycentre (f INTER g:(real^N->bool)->bool))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
  MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]);;

(* The barycentre of a simplex lies in a subcomplex only if the simplex     *)
(* does.                                                                     *)

let MOI_FTA_BARY_IN_SUBCOMPLEX = prove
 (`!c l s:real^N->bool.
        moi_bar_complex c /\ simplicial_subcomplex l c /\ s IN c /\
        ~(s = {}) /\ simplex_barycentre s IN UNIONS l
        ==> s IN l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `{s:real^N->bool}`; `simplex_barycentre (s:real^N->bool)`]
    MOI_FTA_HULL_SUBCOMPLEX) THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
  ASM_CASES_TAC `(s:real^N->bool) IN l` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{s:real^N->bool} INTER l = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]]);;

(* Covering of a simplex by the barycentric simplices of chains of faces,   *)
(* intersected with a barycentric simplex.                                  *)

let MOI_FTA_HULL_INTER_SIMPLEX = prove
 (`!c f s (x:real^N).
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN c /\
        x IN convex hull (IMAGE simplex_barycentre f) /\ x IN s
        ==> x IN convex hull (IMAGE simplex_barycentre
                                (f INTER {u | u face_of s}))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FTA_HULL_SUBCOMPLEX THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_BAR_FACES_SUBSET_COMPLEX; SUBSET; IN_ELIM_THM;
                  FACE_OF_TRANS];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]]);;

(* A barycentric simplex inside another one comes from a subchain.          *)

let MOI_FTA_BS_SUBSET_HULL = prove
 (`!c f r:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\
        r IN barycentric_subdivision c /\
        r SUBSET convex hull (IMAGE simplex_barycentre f)
        ==> ?g. g SUBSET f /\ moi_bar_chain c g /\
                r = convex hull (IMAGE simplex_barycentre g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC))) THEN
  EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[]);;

(* Simplices of dimension at most 1 through a vertex.                       *)

let MOI_FTA_SIMPLEX_LE1 = prove
 (`!c s (v:real^N).
        moi_bar_complex c /\ s IN c /\ {v} IN c /\ v IN s /\
        aff_dim s <= &1 /\ ~(s = {v})
        ==> ?w. ~(w = v) /\ s = segment[v,w]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  SUBGOAL_THEN `({v} INTER s:real^N->bool) face_of s` MP_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `{v} INTER s:real^N->bool = {v}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FACE_OF_SING] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s:real^N->bool`)) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(c':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(c':real^N->bool) <= 2` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(convex hull c':real^N->bool) <= &1` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    UNDISCH_TAC `&(CARD(c':real^N->bool)):int = n + &1` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN c' /\ ~(w = v)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `c' = {v:real^N}` THENL
     [UNDISCH_TAC `~(convex hull c':real^N->bool = {v})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_SING];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `{v:real^N,w} SUBSET c'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(GSYM CARD_SUBSET_LE) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
  ASM_ARITH_TAC);;


(* ========================================================================= *)
(* Graphs stay graphs under barycentric subdivision (the theorem             *)
(* GRAPH_IN_COMPLEX_BARYCENTRIC). The vertices of the subdivided graph are   *)
(* the barycentres of its simplices; each lies in the open star of a vertex *)
(* of l in t, whose link is a PL 2-sphere, so its link in the subdivision   *)
(* is one too (INTERIOR_LINK_RETRIANGULATION).                              *)
(* ========================================================================= *)

(* A face of s meeting the relative interior of s is s.                      *)

let MOI_FTA_FACE_RI = prove
 (`!f s (x:real^N).
        f face_of s /\ x IN f /\ x IN relative_interior s ==> f = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->bool`; `s:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Chains in a complex of dimension at most one have at most two members.   *)

let MOI_FTA_CHAIN_CARD_LE2 = prove
 (`!l f:(real^N->bool)->bool.
        moi_bar_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
        moi_bar_chain l f
        ==> CARD f <= 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
  SUBGOAL_THEN `!a b:real^N->bool. a IN f /\ b IN f /\ a SUBSET b /\
                                   aff_dim a = aff_dim b ==> a = b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^N->bool) IN l /\ b IN l` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N->bool) face_of b` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex(b:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[INT_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(IMAGE (aff_dim:(real^N->bool)->int) f) = CARD f`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `s SUBSET t \/ t SUBSET (s:real^N->bool)` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {&0:int,&1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC(INT_ARITH `!x:int. &0 <= x /\ x <= &1 ==> x = &0 \/ x = &1`) THEN
    REWRITE_TAC[AFF_DIM_POS_LE] THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `~({}:real^N->bool IN f)` THEN
      UNDISCH_TAC `(s:real^N->bool) IN f` THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th) &&
      is_forall(concl th) && not(can (find_term ((=) `f:(real^N->bool)->bool`)) (concl th)))) THEN
    ASM SET_TAC[];
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING;
             NOT_IN_EMPTY] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_FTA_BS_DIM1 = prove
 (`!l s:real^N->bool.
        moi_bar_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
        s IN barycentric_subdivision l
        ==> aff_dim s <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_CARD_LE2) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* The barycentre of a nonempty simplex of l lies in the open star (the     *)
(* closed star minus the link) of each of its vertices.                      *)

let MOI_FTA_BARY_OPEN_STAR = prove
 (`!t s (a:real^N).
        lf_simplicial_complex t /\ s IN t /\ ~(s = {}) /\ a IN s
        ==> simplex_barycentre s IN
            UNIONS {r | r IN t /\ a IN r} DIFF UNIONS (simplicial_link t a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^N->bool) IN relative_interior s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r INTER s:real^N->bool = s` MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_FACE_RI THEN
    EXISTS_TAC `simplex_barycentre (s:real^N->bool)` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`;
                   `s:real^N->bool`] MOI_FM3_LF_INTER) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    UNDISCH_TAC `~((a:real^N) IN r)` THEN UNDISCH_TAC `(a:real^N) IN s` THEN
    SET_TAC[]]);;

(* Vertex links in the subdivision of t at the vertices of the subdivided   *)
(* graph.                                                                    *)

let MOI_FTA_BS_LINK = prove
 (`!t l (x:real^N).
        graph_in_complex t l /\ {x} IN barycentric_subdivision l
        ==> pl_sphere 2 (UNIONS (simplicial_link (barycentric_subdivision t) x))`,
  REWRITE_TAC[graph_in_complex] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_VERTICES) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a extreme_point_of s` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN l` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex]) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_LINK_RETRIANGULATION THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `a:real^N`] THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `x:real^N`)) THEN
    MATCH_MP_TAC MOI_FTA_BARY_OPEN_STAR THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[extreme_point_of]]);;

let GRAPH_IN_COMPLEX_BARYCENTRIC = prove
 (`!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> graph_in_complex (barycentric_subdivision t) (barycentric_subdivision l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[graph_in_complex] THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_BS_DIM1 THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_BS_LINK THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Membership in the derived neighbourhood N and the dual cells             *)
(* C_v, and the combinatorial clauses of GRAPH_TUBE_DUAL_CELLS: N is the    *)
(* union of the C_v; C_v lies in the closed star of v in t and contains no  *)
(* other vertex of t; C_v meets the graph in v and the half edges at v;     *)
(* C_u INTER C_v meets the graph in the midpoint of the edge; dual cells of *)
(* non-adjacent vertices are disjoint.                                       *)
(* ========================================================================= *)

(* A vertex of the complex lying in a simplex is an extreme point of it.    *)

let MOI_FTA_VERTEX_EXTREME = prove
 (`!c s (v:real^N).
        moi_bar_complex c /\ s IN c /\ {v} IN c /\ v IN s
        ==> v extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{v:real^N} = {v} INTER s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[MOI_BAR_COMPLEX_INTER]]);;

let MOI_FTA_EXTREME_SEGMENT = prove
 (`!a b x:real^N. x extreme_point_of segment[a,b] ==> x = a \/ x = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  SET_TAC[]);;

(* In a graph, a simplex containing two distinct vertices is their edge.    *)

let MOI_FTA_GRAPH_TWO_VERTICES = prove
 (`!c l s (u:real^N) v.
        moi_bar_complex c /\ simplicial_subcomplex l c /\
        (!s. s IN l ==> aff_dim s <= &1) /\
        s IN l /\ {u} IN c /\ {v} IN c /\ ~(u = v) /\ u IN s /\ v IN s
        ==> s = segment[u,v]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `u:real^N`]
    MOI_FTA_SIMPLEX_LE1) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[u:real^N,w]`; `v:real^N`]
    MOI_FTA_VERTEX_EXTREME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_EXTREME_SEGMENT) THEN
  ASM_MESON_TAC[]);;

(* Membership in the derived neighbourhood: a barycentric simplex of t2     *)
(* given by a chain of t1 that meets the subdivided graph.                   *)

let MOI_FTA_IN_NBHD = prove
 (`!t l (x:real^N).
        lf_simplicial_complex t /\ simplicial_subcomplex l t
        ==> (x IN derived_nbhd t l <=>
             ?g. moi_bar_chain (barycentric_subdivision t) g /\
                 ~(g INTER barycentric_subdivision l = {}) /\
                 x IN convex hull (IMAGE simplex_barycentre g))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)
       ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN
    UNDISCH_TAC `~(s INTER UNIONS l:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `barycentric_subdivision (l:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`; `y:real^N`]
      MOI_FTA_HULL_SUBCOMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `g INTER barycentric_subdivision (l:(real^N->bool)->bool) = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(g INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `simplex_barycentre (r:real^N->bool)` THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                          `g:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* Membership in the closed star of a vertex in t1.                          *)

let MOI_FTA_IN_STAR1 = prove
 (`!t (v:real^N) x.
        lf_simplicial_complex t /\ {v} IN t
        ==> (x IN UNIONS {s | s IN barycentric_subdivision t /\ v IN s} <=>
             ?h. moi_bar_chain t h /\ {v} IN h /\
                 x IN convex hull (IMAGE simplex_barycentre h))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC)
       ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `h:(real^N->bool)->bool` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN UNDISCH_TAC `(v:real^N) IN s` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]]);;

let MOI_FTA_IN_DUAL_CELL = prove
 (`!t l (v:real^N) x.
        lf_simplicial_complex t /\ {v} IN t
        ==> (x IN derived_dual_cell t l v <=>
             x IN derived_nbhd t l /\
             ?h. moi_bar_chain t h /\ {v} IN h /\
                 x IN convex hull (IMAGE simplex_barycentre h))`,
  SIMP_TAC[derived_dual_cell; IN_INTER; MOI_FTA_IN_STAR1]);;

(* The graph lies in the derived neighbourhood.                              *)

let MOI_FTA_GRAPH_IN_NBHD = prove
 (`!t l:(real^N->bool)->bool.
        lf_simplicial_complex t /\ simplicial_subcomplex l t
        ==> UNIONS l SUBSET derived_nbhd t l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `subtopology euclidean (UNIONS t) interior_of
              derived_nbhd (t:(real^N->bool)->bool) l` THEN
  ASM_REWRITE_TAC[INTERIOR_OF_SUBSET]);;

(* Clause (a): N is the union of the dual cells of the vertices of l.        *)

let MOI_FTA_NBHD_UNION_CELLS = prove
 (`!(t:(real^N->bool)->bool) l.
        graph_in_complex t l
        ==> derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v} IN l}`,
  REWRITE_TAC[graph_in_complex] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; derived_dual_cell; INTER_SUBSET]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(g INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS g IN barycentric_subdivision (t:(real^N->bool)->bool)`
  MP_TAC THENL [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision l` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
      lhs(concl th) = `r:real^N->bool`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS g:real^N->bool`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f0:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(r:real^N->bool) IN g` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN
    ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN f0` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(h:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s0 = INTERS (h:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(s0:real^N->bool) IN t /\ ~(s0 = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s0:real^N->bool) IN l` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex]) THEN
    EXISTS_TAC `sg:real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[moi_bar_chain; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. u extreme_point_of s0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN l` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex]) THEN
    EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `derived_dual_cell t l (u:real^N)` THEN
  CONJ_TAC THENL [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL; MOI_FTA_IN_NBHD] THEN CONJ_TAC THENL
   [EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{u:real^N} INSERT h` THEN REWRITE_TAC[IN_INSERT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[SING_SUBSET] THEN
    SUBGOAL_THEN `(s0:real^N->bool) SUBSET s` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(u:real^N) extreme_point_of s0` THEN
    REWRITE_TAC[extreme_point_of] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS g:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;


(* ========================================================================= *)
(* The other combinatorial clauses of GRAPH_TUBE_DUAL_CELLS.                *)
(* ========================================================================= *)

(* Clause (b): C_v lies in the closed star of v in t.                        *)

let MOI_FTA_CELL_IN_STAR = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> derived_dual_cell t l v SUBSET UNIONS {s | s IN t /\ v IN s}`,
  REWRITE_TAC[graph_in_complex] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(h:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `UNIONS h:real^N->bool` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET];
    SUBGOAL_THEN `{v:real^N} SUBSET UNIONS h` MP_TAC THENL
     [ASM_SIMP_TAC[]; SET_TAC[]];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The singleton chain of a vertex.                                          *)

let MOI_FTA_HULL_SING_CHAIN = prove
 (`!s:real^N->bool.
        convex hull (IMAGE simplex_barycentre {s}) = {simplex_barycentre s}`,
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]);;

let MOI_FTA_VERTEX_IN_CELL = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l ==> v IN derived_dual_cell t l v`,
  REWRITE_TAC[graph_in_complex] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FTA_GRAPH_IN_NBHD) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> s SUBSET t ==> x IN t`) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    EXISTS_TAC `{{v:real^N}}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; IN_SING;
                 MOI_FTA_HULL_SING_CHAIN; MOI_FTA_BARY_SING]]);;

(* Clause (c): the only vertex of t in C_v is v.                             *)

let MOI_FTA_CELL_VERTICES = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> {w | {w} IN t /\ w IN derived_dual_cell t l v} = {v}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MOI_FTA_VERTEX_IN_CELL]] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `w:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `{w:real^N}`] o last o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_bar_chain]) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_SING] THEN MESON_TAC[]);;

(* All members of a chain containing a vertex singleton contain the vertex. *)

let MOI_FTA_CHAIN_VERTEX_ALL = prove
 (`!c h (v:real^N).
        moi_bar_chain c h /\ {v} IN h ==> !s. s IN h ==> v IN s`,
  REWRITE_TAC[moi_bar_chain] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`]) THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[]; SET_TAC[]]);;

(* Clause (d): C_v meets the graph in v and the half edges at v.            *)

let MOI_FTA_HALF_EDGE = prove
 (`!(t:(real^N->bool)->bool) l v w.
        graph_in_complex t l /\ {v} IN l /\ ~(w = v) /\ segment[v,w] IN l
        ==> segment[v,midpoint(v,w)] SUBSET derived_dual_cell t l v INTER UNIONS l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t /\ segment[v,w] IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {{v:real^N},segment[v,w]}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; SEGMENT_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[IN_SING; SING_SUBSET] THEN MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[v,midpoint(v:real^N,w)] =
    convex hull (IMAGE simplex_barycentre {{v},segment[v,w]})`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
                SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre {{v},segment[v,w]}) SUBSET
    segment[v:real^N,w]`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_SEGMENT] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] SUBSET UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FTA_GRAPH_IN_NBHD) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    EXISTS_TAC `{{v:real^N},segment[v,w]}` THEN ASM_REWRITE_TAC[IN_INSERT]]);;

let MOI_FTA_CELL_GRAPH = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> derived_dual_cell t l v INTER UNIONS l =
            v INSERT UNIONS {segment[v,midpoint(v,w)] | w |
                             ~(w = v) /\ segment[v,w] IN l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[INSERT_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[MOI_FTA_VERTEX_IN_CELL] THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_HALF_EDGE THEN
      ASM_REWRITE_TAC[]]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTA_HULL_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN
  ASM_CASES_TAC `h INTER l SUBSET {{v:real^N}}` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre {{v}})`
    MP_TAC THENL
     [UNDISCH_TAC `x IN convex hull (IMAGE simplex_barycentre
                     (h INTER l:(real^N->bool)->bool))` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; MOI_FTA_BARY_SING; IN_SING]];
    DISJ2_TAC] THEN
  UNDISCH_TAC `~(h INTER l SUBSET {{v:real^N}})` THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; IN_INTER; IN_SING; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `sg:real^N->bool`; `v:real^N`]
    MOI_FTA_SIMPLEX_LE1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `segment[v:real^N,midpoint(v,w)]` THEN CONJ_TAC THENL
   [EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^N->bool. a IN t /\ b IN t /\ a SUBSET b /\
                  aff_dim a = &1 /\ aff_dim b = &1 ==> a = b`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^N->bool) face_of b` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex(b:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[INT_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `h INTER l SUBSET {{v:real^N},segment[v,w]}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r = {v:real^N}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN t /\ (v:real^N) IN r` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`; `v:real^N`]
      MOI_FTA_SIMPLEX_LE1) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `segment[v:real^N,w] IN t` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(segment[v:real^N,w]) = &1 /\
                  aff_dim(segment[v:real^N,w']) = &1`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~(v:real^N = w) /\ ~(v = w')` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`segment[v:real^N,w]`; `segment[v:real^N,w']`] o
      last o CONJUNCTS o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THENL [CONV_TAC SYM_CONV; ALL_TAC] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre (h INTER l:(real^N->bool)->bool))
    SUBSET convex hull (IMAGE simplex_barycentre {{v},segment[v,w]})`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
              GSYM SEGMENT_CONVEX_HULL] THEN
  ASM SET_TAC[]);;

(* Clause (f), second part: a splitting disk meets the graph in the         *)
(* midpoint of its edge.                                                     *)

let MOI_FTA_DISK_GRAPH = prove
 (`!(t:(real^N->bool)->bool) l u v.
        graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l
        ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
            UNIONS l = {midpoint(u,v)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN l /\ {v:real^N} IN l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex]) THEN
    EXISTS_TAC `segment[u:real^N,v]` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
             AFFINE_INDEPENDENT_2] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN t /\ {v:real^N} IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SING_SUBSET] THEN
    SUBGOAL_THEN `segment[v:real^N,u] IN l /\ ~(v = u)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `u:real^N`; `v:real^N`] MOI_FTA_HALF_EDGE) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`; `u:real^N`] MOI_FTA_HALF_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [`v:real^N`; `u:real^N`] MIDPOINT_SYM) THEN
    MP_TAC(ISPECL [`u:real^N`; `midpoint(u:real^N,v)`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`v:real^N`; `midpoint(u:real^N,v)`] ENDS_IN_SEGMENT) THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN MESON_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC)
     (X_CHOOSE_THEN `h1:(real^N->bool)->bool` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `h2:(real^N->bool)->bool` STRIP_ASSUME_TAC))
     ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h2:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre (h1 INTER h2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h1 INTER h2:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTA_HULL_SUBCOMPLEX) THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h1 INTER h2) INTER l SUBSET {segment[u:real^N,v]}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre ((h1 INTER h2) INTER l))
    SUBSET convex hull (IMAGE simplex_barycentre {segment[u:real^N,v]})`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; MOI_FTA_BARY_SEGMENT] THEN
  ASM SET_TAC[]);;

(* Clause (g): dual cells of distinct vertices not joined by an edge of the *)
(* graph are disjoint.                                                       *)

let MOI_FTA_CELLS_DISJOINT = prove
 (`!(t:(real^N->bool)->bool) l u v.
        graph_in_complex t l /\ {u} IN l /\ {v} IN l /\ ~(u = v) /\
        ~(segment[u,v] IN l)
        ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{u:real^N} IN t /\ {v:real^N} IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `h1:(real^N->bool)->bool` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 (K ALL_TAC)
     (X_CHOOSE_THEN `h2:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h2:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre (h1 INTER h2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `h = (h1 INTER h2):(real^N->bool)->bool` THEN
  SUBGOAL_THEN `moi_bar_chain t (h:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN h ==> u IN s /\ v IN s` ASSUME_TAC THENL
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
  UNDISCH_TAC `~(segment[u:real^N,v] IN l)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN l /\ sg IN h` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `sg = segment[u:real^N,v]` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* The statement term from the two cell clauses (conditional form).         *)
(* MOI_FTA_GRAPH_TUBE_FROM_CELLS: the combinatorial clauses proved above    *)
(* together with the cell clauses as hypotheses give the whole of           *)
(* GRAPH_TUBE_DUAL_CELLS.                                                    *)
(* ========================================================================= *)

let MOI_FTA_GRAPH_TUBE_FROM_CELLS = prove
 (`!(t:(real^N->bool)->bool) l.
     graph_in_complex t l /\
     (!v. {v} IN l
          ==> pl_cell_with_boundary 3 (derived_dual_cell t l v)
                ((derived_dual_cell t l v INTER derived_frontier t l) UNION
                 UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                         w | ~(w = v) /\ segment[v,w] IN l})) /\
     (!u v. ~(u = v) /\ segment[u,v] IN l
            ==> pl_cell_with_boundary 2
                  (derived_dual_cell t l u INTER derived_dual_cell t l v)
                  (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                   derived_frontier t l))
     ==> derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v} IN l} /\
         (!v. {v} IN l
              ==> derived_dual_cell t l v SUBSET UNIONS {s | s IN t /\ v IN s} /\
                  {w | {w} IN t /\ w IN derived_dual_cell t l v} = {v} /\
                  derived_dual_cell t l v INTER UNIONS l =
                  v INSERT UNIONS {segment[v,midpoint(v,w)] | w |
                                   ~(w = v) /\ segment[v,w] IN l} /\
                  pl_cell_with_boundary 3 (derived_dual_cell t l v)
                    ((derived_dual_cell t l v INTER derived_frontier t l) UNION
                     UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                             w | ~(w = v) /\ segment[v,w] IN l})) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> pl_cell_with_boundary 2
                      (derived_dual_cell t l u INTER derived_dual_cell t l v)
                      (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                       derived_frontier t l) /\
                    derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                    UNIONS l = {midpoint(u,v)}) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_NBHD_UNION_CELLS; MOI_FTA_CELL_IN_STAR;
               MOI_FTA_CELL_VERTICES; MOI_FTA_CELL_GRAPH; MOI_FTA_DISK_GRAPH;
               MOI_FTA_CELLS_DISJOINT]);;


(* ========================================================================= *)
(* Derived retriangulations.  For a finite complex c and any                *)
(* choice of points d s in the relative interiors of its simplices, the     *)
(* simplexwise affine map of the barycentric subdivision sending each       *)
(* barycentre b s to d s is a PL homeomorphism of UNIONS c onto itself that *)
(* maps every simplex of c onto itself and every barycentric simplex onto   *)
(* the convex hull of the d-images of its chain.  Proof by induction on the *)
(* dimension: the map is the cone extension, from b s to d s, of its        *)
(* restriction to the relative frontier.                                     *)
(* ========================================================================= *)

let MOI_FTA_DH_EXISTS = prove
 (`!c (d:(real^N->bool)->real^N).
        moi_bar_complex c
        ==> ?h. !f. moi_bar_chain c f
                    ==> ?L y. linear L /\
                              (!s. s IN f ==> L(simplex_barycentre s) + y = d s) /\
                              (!x. x IN convex hull (IMAGE simplex_barycentre f)
                                   ==> h x = L x + y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`simplex_barycentre:(real^N->bool)->real^N`;
                 `d:(real^N->bool)->real^N`;
                 `{f:(real^N->bool)->bool | moi_bar_chain c f /\ ~(f = {})}`]
    MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[abstract_realizes; IN_ELIM_THM; IN_UNIONS] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `f1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `f2:(real^N->bool)->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC)) THEN
      MATCH_MP_TAC MOI_FTA_BARY_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ASM_MESON_TAC[MOI_BAR_CHAIN_HULL_INTER]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^N` THEN
  DISCH_TAC THEN X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^N. vec 0:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[LINEAR_ZERO; NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
    FIRST_X_ASSUM(MP_TAC o SPEC `f:(real^N->bool)->bool`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let MOI_FTA_DH_IMAGE_HULL = prove
 (`!(h:real^N->real^N) (d:(real^N->bool)->real^N) f L y.
        linear L /\ (!s. s IN f ==> L(simplex_barycentre s) + y = d s) /\
        (!x. x IN convex hull (IMAGE simplex_barycentre f) ==> h x = L x + y)
        ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
            convex hull (IMAGE d f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (convex hull (IMAGE simplex_barycentre f)) =
    IMAGE (\x. L x + y) (convex hull (IMAGE simplex_barycentre f))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* The relative frontier of a polytope is the union of its proper faces.    *)

let MOI_FTA_RF_PROPER_FACES = prove
 (`!s:real^N->bool.
        polytope s
        ==> relative_frontier s = UNIONS {f | f face_of s /\ ~(f = s)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN REWRITE_TAC[facet_of] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[INT_ARITH `~(x:int = x - &1)`];
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED] THEN
    MP_TAC(ISPECL [`f:real^N->bool`; `s:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_FTA_IMAGE_ID_ON = prove
 (`!(f:A->A) s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* Bijectivity on the proper faces gives bijectivity on the frontier.       *)

let MOI_FTA_RF_BIJ = prove
 (`!(h:real^N->real^N) s.
        polytope s /\
        (!f. f face_of s /\ ~(f = s)
             ==> IMAGE h f = f /\
                 (!x y. x IN f /\ y IN f /\ h x = h y ==> x = y))
        ==> IMAGE h (relative_frontier s) = relative_frontier s /\
            (!x y. x IN relative_frontier s /\ y IN relative_frontier s /\
                   h x = h y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_RF_PROPER_FACES] THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f1:real^N->bool` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `f2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f1 INTER f2:real^N->bool) face_of s /\ ~(f1 INTER f2 = s)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_INTER] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f1:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) x IN f1 INTER f2` MP_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (f1 INTER f2) = f1 INTER f2`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z:real^N = x /\ z = y` (fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_MESON_TAC[]);;

(* Cone extension from relative interior points is bijective when the map  *)
(* is bijective on the relative frontier.                                    *)

let MOI_FTA_CONE_BIJ = prove
 (`!(h:real^N->real^N) s a a'.
        convex s /\ compact s /\ a IN relative_interior s /\
        a' IN relative_interior s /\ ~(relative_frontier s = {}) /\
        IMAGE h (relative_frontier s) = relative_frontier s /\
        (!y u. y IN relative_frontier s /\ &0 <= u /\ u <= &1
               ==> h((&1 - u) % a + u % y) = (&1 - u) % a' + u % h y)
        ==> (!x y. x IN relative_frontier s /\ y IN relative_frontier s /\
                   h x = h y ==> x = y)
        ==> IMAGE h s = s /\
            (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN(fun inj ->
  SUBGOAL_THEN `closed(s:real^N->bool) /\ bounded s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier s SUBSET (s:real^N->bool) /\
                (!y. y IN relative_frontier s ==> ~(y IN relative_interior s))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior s SUBSET (s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!b x:real^N. b IN relative_interior s /\ x IN s
                 ==> ?y u. y IN relative_frontier s /\ &0 <= u /\ u <= &1 /\
                           x = (&1 - u) % b + u % y`
  (LABEL_TAC "rep") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = b` THENL
     [UNDISCH_TAC `~(relative_frontier s:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `&0`] THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_LE_01] THEN VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`s:real^N->bool`; `b:real^N`; `x:real^N`]
        MOI_BAR_RAY_EXIT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `u:real`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `u:real`] THEN
      ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN relative_frontier s ==> h y IN relative_frontier s`
  ASSUME_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN
      REMOVE_THEN "rep" (MP_TAC o SPECL [`a:real^N`; `x:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `u:real`
        STRIP_ASSUME_TAC)) THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN
      REMOVE_THEN "rep" (MP_TAC o SPECL [`a':real^N`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^N` (X_CHOOSE_THEN `u:real`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `?y:real^N. y IN relative_frontier s /\ h y = (y':real^N)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y':real^N) IN relative_frontier s` THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(&1 - u) % a + u % y:real^N` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
  USE_THEN "rep" (MP_TAC o SPECL [`a:real^N`; `x1:real^N`]) THEN
  REMOVE_THEN "rep" (MP_TAC o SPECL [`a:real^N`; `x2:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:real^N` (X_CHOOSE_THEN `u2:real`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (X_CHOOSE_THEN `u1:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(&1 - u1) % a' + u1 % (h:real^N->real^N) y1 = (&1 - u2) % a' + u2 % h y2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `x1:real^N`)) (concl th) &&
      can (find_term ((=) `x2:real^N`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^N->real^N) y1 = a') /\ ~(h y2 = a')`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^N) y1 IN relative_frontier s /\
                  h y2 IN relative_frontier s` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ASSUME `(a':real^N) IN relative_interior s`) THEN
    UNDISCH_TAC `!y:real^N. y IN relative_frontier s ==> ~(y IN relative_interior s)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u1 = &0` THENL
   [SUBGOAL_THEN `u2 = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC
       `(&1 - u1) % a' + u1 % (h:real^N->real^N) y1 = (&1 - u2) % a' + u2 % h y2` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(&1 - &0) % a' + &0 % b:real^N = (&1 - u) % a' + u % c <=>
        u % (c - a') = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ];
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `u2 = &0` THENL
   [UNDISCH_TAC
     `(&1 - u1) % a' + u1 % (h:real^N->real^N) y1 = (&1 - u2) % a' + u2 % h y2` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a' + u % c:real^N = (&1 - &0) % a' + &0 % b <=>
      u % (c - a') = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a':real^N`; `(h:real^N->real^N) y1`;
                 `(h:real^N->real^N) y2`; `&1 - u1`; `&1 - u2`]
    MOI_BAR_RAY_UNIQUE) THEN
  REWRITE_TAC[MATCH_MP CLOSURE_CLOSED (ASSUME `closed(s:real^N->bool)`)] THEN
  SUBGOAL_THEN `(h:real^N->real^N) y1 IN relative_frontier s /\
                h y2 IN relative_frontier s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `(h:real^N->real^N) y`)) (concl th) &&
      not (can (find_term ((=) `(&1 - u) % a + u % y:real^N`)) (concl th)))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `(h:real^N->real^N) y1 IN relative_frontier s` THEN
      UNDISCH_TAC `relative_frontier s SUBSET (s:real^N->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(h:real^N->real^N) y2 IN relative_frontier s` THEN
      UNDISCH_TAC `relative_frontier s SUBSET (s:real^N->bool)` THEN SET_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_neg(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_neg(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC [`&0 <= u1`; `u1 <= &1`] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(u1 = &0)` THEN UNDISCH_TAC `&0 <= u1` THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`&0 <= u2`; `u2 <= &1`] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(u2 = &0)` THEN UNDISCH_TAC `&0 <= u2` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `&1 - (&1 - u) = u`]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `u1:real = u2 /\ y1:real^N = y2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC inj THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]));;

(* The map along the segment from the barycentre of a simplex.              *)

let MOI_FTA_DH_SEGMENT = prove
 (`!c (d:(real^N->bool)->real^N) (h:real^N->real^N) s y u.
        moi_bar_complex c /\
        (!f. moi_bar_chain c f
             ==> ?L y. linear L /\
                       (!s. s IN f ==> L(simplex_barycentre s) + y = d s) /\
                       (!x. x IN convex hull (IMAGE simplex_barycentre f)
                            ==> h x = L x + y)) /\
        s IN c /\ ~(s = {}) /\ y IN s /\ &0 <= u /\ u <= &1
        ==> h((&1 - u) % simplex_barycentre s + u % y) =
            (&1 - u) % d s + u % h y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `s:real^N->bool`; `y:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c ((s:real^N->bool) INSERT f)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `{t:real^N->bool | t face_of s}` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_BAR_FACES_SUBSET_COMPLEX];
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN
      UNDISCH_TAC `moi_bar_chain {t:real^N->bool | t face_of s} f` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s:real^N->bool) INSERT f`) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y0:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(y:real^N) IN convex hull (IMAGE simplex_barycentre (s INSERT f)) /\
    simplex_barycentre s IN convex hull (IMAGE simplex_barycentre (s INSERT f))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN convex hull (IMAGE simplex_barycentre f)` THEN
      SPEC_TAC(`y:real^N`,`y:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - u) % simplex_barycentre s + u % (y:real^N) IN
    convex hull (IMAGE simplex_barycentre (s INSERT f))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^N->real^N) ((&1 - u) % simplex_barycentre s + u % y) =
    L((&1 - u) % simplex_barycentre s + u % y) + y0 /\
    h y = L y + y0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:(real^N->bool)->real^N) s = L(simplex_barycentre s) + y0`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[ASSUME `linear(L:real^N->real^N)`; LINEAR_ADD; LINEAR_CMUL] THEN
  VECTOR_ARITH_TAC);;

let MOI_FTA_NUM_OF_INT_LT = prove
 (`!a:int b:int. -- &1 <= a /\ a < b ==> num_of_int(a + &1) < num_of_int(b + &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  SUBGOAL_THEN `&0:int <= a + &1 /\ &0:int <= b + &1` STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN ASM_INT_ARITH_TAC]);;

(* Induction on dimension: the map restricts to a bijection of each simplex. *)

let MOI_FTA_DH_FACES = prove
 (`!c (d:(real^N->bool)->real^N) (h:real^N->real^N).
        moi_bar_complex c /\
        (!s. s IN c /\ ~(s = {}) ==> d s IN relative_interior s) /\
        (!f. moi_bar_chain c f
             ==> ?L y. linear L /\
                       (!s. s IN f ==> L(simplex_barycentre s) + y = d s) /\
                       (!x. x IN convex hull (IMAGE simplex_barycentre f)
                            ==> h x = L x + y))
        ==> !s. s IN c
                ==> IMAGE h s = s /\
                    (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  WF_INDUCT_TAC `num_of_int(aff_dim(s:real^N->bool) + &1)` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `polytope (s:real^N->bool) /\ convex s /\ compact s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CONVEX;
                  POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `(d:(real^N->bool)->real^N) {a} = a` ASSUME_TAC THENL
     [SUBGOAL_THEN `(d:(real^N->bool)->real^N) {a} IN relative_interior {a}`
      MP_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `relative_interior:(real^N->bool)->real^N->bool`))
            (concl th))) THEN
        ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
        REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) a = a` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `{{a:real^N}}` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `moi_bar_chain:((real^N->bool)->bool)->((real^N->bool)->bool)->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y0:real^N`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(h:real^N->real^N) a = L a + y0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; MOI_FTA_BARY_SING; IN_SING];
        ALL_TAC] THEN
      SUBGOAL_THEN `(L:real^N->real^N) a + y0 = d {a}` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `{a:real^N}`) THEN
        REWRITE_TAC[IN_SING; MOI_FTA_BARY_SING];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[IMAGE_CLAUSES; IN_SING] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f face_of s /\ ~(f = s)
        ==> IMAGE (h:real^N->real^N) f = f /\
            (!x y. x IN f /\ y IN f /\ h x = h y ==> x = y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^N->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `num_of_int`)) (concl th))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_FTA_NUM_OF_INT_LT THEN REWRITE_TAC[AFF_DIM_GE] THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_BAR_COMPLEX_FACE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `s:real^N->bool`] MOI_FTA_RF_BIJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `s:real^N->bool`;
                 `simplex_barycentre (s:real^N->bool)`;
                 `(d:(real^N->bool)->real^N) s`] MOI_FTA_CONE_BIJ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
      MP_TAC(ISPEC `s:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(aff_dim {a:real^N} = &0)` THEN REWRITE_TAC[AFF_DIM_SING];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_DH_SEGMENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED; SUBSET]];
    SIMP_TAC[]]);;

(* Main lemma of this section: derived retriangulations are PL homeomorphic. *)

let MOI_FTA_DERIVED_HOMEO = prove
 (`!c (d:(real^N->bool)->real^N).
        FINITE c /\ moi_bar_complex c /\
        (!s. s IN c /\ ~(s = {}) ==> d s IN relative_interior s)
        ==> ?h k. pl_homeomorphism (UNIONS c,UNIONS c) (h,k) /\
                  (!f. moi_bar_chain c f
                       ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
                           convex hull (IMAGE d f)) /\
                  (!s. s IN c ==> IMAGE h s = s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d:(real^N->bool)->real^N`]
    MOI_FTA_DH_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (LABEL_TAC "aff")) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d:(real^N->bool)->real^N`;
                 `h:real^N->real^N`] MOI_FTA_DH_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "faces") THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (UNIONS c) = UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN UNIONS c /\ y IN UNIONS c /\ (h:real^N->real^N) x = h y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC)
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(s1 INTER s2:real^N->bool) IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN
      EXISTS_TAC `s1:real^N->bool` THEN ASM_MESON_TAC[MOI_BAR_COMPLEX_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) x IN s1 INTER s2` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `IMAGE (h:real^N->real^N) s1 = s1` (fun th ->
          GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
         [ASM_MESON_TAC[]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
        SUBGOAL_THEN `IMAGE (h:real^N->real^N) s2 = s2` (fun th ->
          GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) (s1 INTER s2) = s1 INTER s2`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^N = x /\ z = y` (fun th -> REWRITE_TAC[GSYM th]) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "faces" (MP_TAC o SPEC `s1:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[];
      REMOVE_THEN "faces" (MP_TAC o SPEC `s2:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (UNIONS c) (h:real^N->real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `barycentric_subdivision (c:(real^N->bool)->bool)` THEN
    EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; OPEN_UNIV; IN_UNIV; INTER_UNIV;
                 MOI_BAR_UNIONS_SUBDIVISION; SUBSET_REFL] THEN
    X_GEN_TAC `k:real^N->bool` THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMAGE THEN
      UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      SIMP_TAC[moi_bar_chain];
      MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_BAR_UNIONS_SUBDIVISION) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "aff" (MP_TAC o C MATCH_MP
        (ASSUME `moi_bar_chain c (f:(real^N->bool)->bool)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y0:real^N`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`L:real^N->real^N`; `y0:real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `h:real^N->real^N`;
                 `UNIONS c:real^N->bool`] HOMEOMORPHISM_COMPACT) THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real^N->real^N`) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[pl_homeomorphism] THEN
    MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN
    EXISTS_TAC `h:real^N->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN
    USE_THEN "aff" (MP_TAC o C MATCH_MP
      (ASSUME `moi_bar_chain c (f:(real^N->bool)->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y0:real^N`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_FTA_DH_IMAGE_HULL THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->real^N`; `y0:real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;


(* ========================================================================= *)
(* Cones over PL spheres, the closed star of a vertex with a PL             *)
(* 2-sphere link (a cone, a PL 3-cell, with a radial PL chart onto a        *)
(* 3-simplex of real^3), recognition of PL 2-spheres in such a star met     *)
(* exactly once by each ray from the vertex (pseudo-radial projection via   *)
(* STAR_SHAPED_PL_SPHERE), and links of vertices of a PL 2-sphere link.     *)
(* ========================================================================= *)

(* A cone over a PL n-sphere with unique cone coordinates is a PL (n+1)-cell *)
(* bounded by the sphere (PL_BALL_CONE with the boundary kept).             *)

let MOI_FTA_CONE_CELL = prove
 (`!n (X:real^N->bool) v.
        pl_sphere n X /\ ~(v IN X) /\
        (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x)
        ==> pl_cell_with_boundary (n + 1) (UNIONS {segment[v,x] | x IN X}) X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
     (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `X:real^N->bool`;
                 `simplex_barycentre (k:real^N->bool)`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k) (v:real^N)
                     (f:real^N->real^N)`;
    `moi_con_conemap (X:real^N->bool) (v:real^N)
                     (simplex_barycentre (k:real^N->bool)) (g:real^N->real^N)`]
  THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (relative_frontier k) = X`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x:real^N. x IN s ==> (f:real^N->real^N) x = g x)
    ==> IMAGE f s = IMAGE g s`) THEN
  ASM_SIMP_TAC[]);;

(* The closed star of a vertex is the cone over its link.                   *)

let MOI_FTA_STAR_EQ_CONE = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        ~(UNIONS (simplicial_link c v) = {})
        ==> UNIONS {s | s IN c /\ v IN s} =
            UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `x:real^N = v` THENL
     [UNDISCH_TAC `~(UNIONS (simplicial_link c (v:real^N)) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `segment[v:real^N,y]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`;
                     `x:real^N`] MOI_CMB_STAR_CONE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `segment[v:real^N,y]` THEN CONJ_TAC THENL
       [EXISTS_TAC `y:real^N` THEN REWRITE_TAC[GSYM IN_UNIONS] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `r:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
      MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]);;

(* A radial PL chart of the closed star of a vertex with a PL 2-sphere link *)
(* onto a 3-simplex of real^3 (copied from MOI_STA_STAR_PLH of pc_moi_star, *)
(* whose hypothesis is weakened to the link of the one vertex, and with the *)
(* radial property of the cone map kept).                                    *)

let MOI_FTA_STAR_CHART = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> ?S:real^3->bool p q.
                &3 simplex S /\
                pl_homeomorphism
                  (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                   S)
                  (p,q) /\
                IMAGE p (UNIONS (simplicial_link c v)) = relative_frontier S /\
                ~(UNIONS (simplicial_link c v) = {}) /\
                (!y r. y IN UNIONS (simplicial_link c v) /\ &0 <= r /\ r <= &1
                       ==> p(v + r % (y - v)) =
                           simplex_barycentre S +
                           r % (p y - simplex_barycentre S)) /\
                3 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_sphere]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `3 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_STA_SIMPLEX_RF_R3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
      ((f0:real^N->real^N) o (f1:real^3->real^N),
       (g1:real^N->real^3) o (g0:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g1:real^N->real^3) o (g0:real^N->real^N))
          (UNIONS (simplicial_link c (v:real^N))) = relative_frontier S /\
    IMAGE ((f0:real^N->real^N) o (f1:real^3->real^N)) (relative_frontier S) =
          UNIONS (simplicial_link c v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
        ((f0:real^N->real^N) o (f1:real^3->real^N),
         (g1:real^N->real^3) o (g0:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `&3:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^N)) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(relative_frontier S:real^3->bool = {})` THEN
    UNDISCH_TAC
     `IMAGE ((f0:real^N->real^N) o (f1:real^3->real^N)) (relative_frontier S) =
      UNIONS (simplicial_link c (v:real^N))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`relative_frontier S:real^3->bool`; `UNIONS (simplicial_link c (v:real^N))`;
    `simplex_barycentre (S:real^3->bool)`; `v:real^N`;
    `(f0:real^N->real^N) o (f1:real^3->real^N)`;
    `(g1:real^N->real^3) o (g0:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `S:real^3->bool` THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^N)
               (simplex_barycentre (S:real^3->bool))
               ((g1:real^N->real^3) o (g0:real^N->real^N))` THEN
  EXISTS_TAC `moi_con_conemap (relative_frontier S)
               (simplex_barycentre (S:real^3->bool)) (v:real^N)
               ((f0:real^N->real^N) o (f1:real^3->real^N))` THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN UNIONS (simplicial_link c v)
               ==> moi_con_conemap (UNIONS (simplicial_link c v)) v
                     (simplex_barycentre (S:real^3->bool))
                     ((g1:real^N->real^3) o (g0:real^N->real^N)) y =
                   (g1 o g0) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^3) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[]]);;

(* The closed star of a vertex with a PL 2-sphere link is a PL 3-cell       *)
(* bounded by the link.                                                      *)

let MOI_FTA_STAR_CELL = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> pl_cell_with_boundary 3 (UNIONS {s | s IN c /\ v IN s})
              (UNIONS (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_STAR_EQ_CONE] THEN
  MP_TAC(ISPECL [`2`; `UNIONS (simplicial_link c (v:real^N))`; `v:real^N`]
    MOI_FTA_CONE_CELL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The closed star complex of a vertex: a finite subcomplex.                *)

let MOI_FTA_CSTAR_COMPLEX = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> FINITE {s | ?r. r IN c /\ v IN r /\ s face_of r} /\
            simplicial_subcomplex {s | ?r. r IN c /\ v IN r /\ s face_of r} c /\
            lf_simplicial_complex {s | ?r. r IN c /\ v IN r /\ s face_of r} /\
            UNIONS {s | ?r. r IN c /\ v IN r /\ s face_of r} =
            UNIONS {s | s IN c /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simplicial_subcomplex {s | ?r. r IN c /\ v IN r /\ s face_of r}
                          (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ASM_MESON_TAC[FACE_OF_TRANS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `{s | ?r. r IN c /\ v IN r /\ s face_of r} =
      UNIONS (IMAGE (\r. {s:real^N->bool | s face_of r})
                    {r | r IN c /\ v IN r})`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `{s:real^N->bool | s face_of r}` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
        EXISTS_TAC `r:real^N->bool` THEN
        UNDISCH_TAC `(s:real^N->bool) IN t` THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{s:real^N->bool | s IN c /\ ~(s INTER u = {})}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_POLYTOPE]];
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]]);;

(* Links of vertices in the link complex of a vertex with a PL 2-sphere     *)
(* link are PL 1-spheres (via the closed star, a PL 3-cell, whose boundary  *)
(* complex is the link: PL_BALL_TRIANGULATION_BOUNDARY and                   *)
(* BOUNDARY_COMPLEX_SURFACE).                                                *)

let MOI_FTA_S2LINK = prove
 (`!c (u:real^N) w.
        lf_simplicial_complex c /\ {u} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c u)) /\
        {w} IN simplicial_link c u
        ==> pl_sphere 1 (UNIONS (simplicial_link (simplicial_link c u) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FTA_CSTAR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = {s | ?r. r IN c /\ (u:real^N) IN r /\ s face_of r}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FTA_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `UNIONS st:real^N->bool`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`st:(real^N->bool)->bool`;
                 `UNIONS (simplicial_link c (u:real^N))`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `st:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
  SUBGOAL_THEN `boundary_complex st = simplicial_link c (u:real^N)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[boundary_complex] THEN EXPAND_TAC "st" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; simplicial_link] THEN
    X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`]
          MOI_STA_LINK_FACTS) THEN
        ASM_REWRITE_TAC[simplicial_link] THEN ASM SET_TAC[];
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[combinatorial_manifold] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Rays from a relative interior point leave a closed convex set after its *)
(* first frontier point.                                                     *)

let MOI_FTA_RAY_BEYOND = prove
 (`!(S:real^M->bool) b u d r.
        convex S /\ closed S /\ b IN relative_interior S /\
        b + d % u IN relative_frontier S /\ &0 < d /\ d < r
        ==> ~(b + r % u IN S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `b:real^M`; `b + r % u:real^M`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `b + d % u:real^M`) THEN
  SUBGOAL_THEN `~(u:real^M = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `b + d % u IN relative_frontier (S:real^M->bool)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; relative_frontier] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `b:real^M = b + r % u <=> r % u = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `d / r` THEN
      SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - t) % b + t % (b + r % u):real^M = b + (t * r) % u`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
    UNDISCH_TAC `b + d % u IN relative_frontier (S:real^M->bool)` THEN
    REWRITE_TAC[relative_frontier] THEN SET_TAC[]]);;

(* The ray count for the radial image of a set met once by each segment.    *)

let MOI_FTA_RAY_COUNT = prove
 (`!(S:real^3->bool) (C:real^N->bool) L X (p:real^N->real^3) q b v.
        convex S /\ compact S /\ b IN relative_interior S /\
        affine hull S = (:real^3) /\
        IMAGE p C = S /\ (!x. x IN C ==> q(p x) = x) /\
        X SUBSET C /\ IMAGE p L = relative_frontier S /\
        (!y r. y IN L /\ &0 <= r /\ r <= &1
               ==> v + r % (y - v) IN C /\
                   p(v + r % (y - v)) = b + r % (p y - b)) /\
        (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X)
        ==> !u. ~(u = vec 0) ==> ?!r. &0 < r /\ b + r % u IN IMAGE p X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `b:real^3`; `u:real^3`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN L /\ (p:real^N->real^3) y = b + dd % u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `b + dd % u IN relative_frontier (S:real^3->bool)` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [SYM (check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `relative_frontier (S:real^3->bool)`) th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->real^3) y - b = dd % u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "rad" o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `C:real^N->bool`)) (concl th) &&
    can (find_term ((=) `b:real^3`)) (concl th))) THEN
  SUBGOAL_THEN
   `!r. &0 < r /\ r <= dd
        ==> v + (r / dd) % (y - v) IN C /\
            b + r % u = (p:real^N->real^3)(v + (r / dd) % (y - v))`
  (LABEL_TAC "mid") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= r / dd /\ r / dd <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "rad" (MP_TAC o SPECL [`y:real^N`; `r / dd`]) THEN
    REWRITE_TAC[ASSUME `(y:real^N) IN L`; ASSUME `&0 <= r / dd`;
                ASSUME `r / dd <= &1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 < r /\ b + r % u IN IMAGE (p:real^N->real^3) X
        ==> r <= dd /\ v + (r / dd) % (y - v) IN X`
  (LABEL_TAC "back") THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `r <= dd` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`S:real^3->bool`; `b:real^3`; `u:real^3`; `dd:real`;
                     `r:real`] MOI_FTA_RAY_BEYOND) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `b + r % u:real^3`)) THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM(check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `S:real^3->bool`) th)]) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
      REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "mid" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `x:real^N = v + (r / dd) % (y - v)` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(x:real^N) IN C` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(q:real^3->real^N) (p (x:real^N)) = x /\
      q (p (v + (r / dd) % (y - v))) = v + (r / dd) % (y - v)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `b + r % u = (p:real^N->real^3) x` THEN
    UNDISCH_TAC `b + r % u = (p:real^N->real^3) (v + r / dd % (y - v))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th) &&
    not (can (find_term ((=) `C:real^N->bool`)) (concl th)))) THEN
  REWRITE_TAC[ASSUME `(y:real^N) IN L`; EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    MP_TAC)) THEN
  DISCH_THEN(fun uniq ->
    REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `s0 * dd:real` THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      USE_THEN "mid" (MP_TAC o SPEC `s0 * dd:real`) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL] THEN
        REWRITE_TAC[REAL_ARITH `s * d <= d <=> &0 <= (&1 - s) * d`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < d ==> (s * d) / d = s`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "back" (MP_TAC o SPEC `r:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(SPEC `r / dd` uniq) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]));;

(* Recognition of PL 2-spheres in the closed star of a vertex with a PL     *)
(* 2-sphere link: a compact polyhedron avoiding the vertex and met exactly *)
(* once by each segment from the vertex to the link.  The radial chart maps *)
(* it to a polyhedron of real^3 met once by every ray from the barycentre   *)
(* of the image simplex (STAR_SHAPED_PL_SPHERE).                             *)

let MOI_FTA_RSS = prove
 (`!c (v:real^N) X.
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v)) /\
        pl_polyhedron X /\ ~(v IN X) /\
        X SUBSET UNIONS {s | s IN c /\ v IN s} /\
        (!y. y IN UNIONS (simplicial_link c v)
             ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X)
        ==> pl_sphere 2 X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `L = UNIONS (simplicial_link c (v:real^N))` THEN
  ABBREV_TAC `C = UNIONS {segment[v,y] | y | (y:real^N) IN L}` THEN
  SUBGOAL_THEN `(X:real^N->bool) SUBSET C` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN C /\
                !y r. y IN L /\ &0 <= r /\ r <= &1 ==> v + r % (y - v) IN C`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(L:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      EXISTS_TAC `segment[v:real^N,y]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
      CONJ_TAC THENL [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `b = simplex_barycentre (S:real^3->bool)` THEN
  FIRST_X_ASSUM(LABEL_TAC "rad" o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `b:real^3`)) (concl th) &&
    can (find_term ((=) `p:real^N->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `(p:real^N->real^3) v = b` ASSUME_TAC THENL
   [UNDISCH_TAC `~(L:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    USE_THEN "rad" (MP_TAC o SPECL [`y:real^N`; `&0`]) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_01; ASSUME `(y:real^N) IN L`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(S:real^3->bool) /\ compact S` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded(S:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(S:real^3->bool) = &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `b IN relative_interior(S:real^3->bool)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `simplex_barycentre (S:real^3->bool) = b`)) THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `&3:int` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(S:real^3->bool) = &3` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull S = (:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (p:real^N->real^3) X`; `b:real^3`]
    STAR_SHAPED_PL_SPHERE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `C:real^N->bool` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
      SUBGOAL_THEN `(q:real^3->real^N) (p (x:real^N)) = x /\ q (p v) = v`
      MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
         [UNDISCH_TAC `(x:real^N) IN X` THEN
          UNDISCH_TAC `(X:real^N->bool) SUBSET C` THEN SET_TAC[];
          FIRST_ASSUM ACCEPT_TAC];
        UNDISCH_TAC `b = (p:real^N->real^3) x` THEN
        UNDISCH_TAC `(p:real^N->real^3) v = b` THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_RAY_COUNT THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `C:real^N->bool`; `L:real^N->bool`;
                          `q:real^3->real^N`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "rad" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:M`] MOI_CMB_PL_SPHERE_TRANSFER) THEN
  EXISTS_TAC `IMAGE (p:real^N->real^3) X` THEN
  EXISTS_TAC `q:real^3->real^N` THEN EXISTS_TAC `p:real^N->real^3` THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (IMAGE (p:real^N->real^3) X,IMAGE q (IMAGE p X)) (q,p)`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `C:real^N->bool`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (q:real^3->real^N) (IMAGE p X) = X`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
  UNDISCH_TAC `(X:real^N->bool) SUBSET C` THEN
  UNDISCH_TAC `!x:real^N. x IN C ==> (q:real^3->real^N) (p x) = x` THEN
  SET_TAC[]);;


(* ========================================================================= *)
(* The dual cell, its part on the frontier of N and the splitting           *)
(* disks as unions of simplices of t2 coming from chains of the closed star *)
(* of v in t1.  Chain classes: gp (the members share an extreme point on   *)
(* the graph), gm (in addition they share one off the graph; these give    *)
(* the frontier of N), gw (members are simplices of the dual block of the  *)
(* edge [v,w] through its midpoint; these give the splitting disk).        *)
(* ========================================================================= *)

let moi_fta_cstar = new_definition
 `moi_fta_cstar (c:(real^N->bool)->bool) (v:real^N) =
    {s | ?r. r IN c /\ v IN r /\ s face_of r}`;;

let moi_fta_gp = new_definition
 `moi_fta_gp (l:(real^N->bool)->bool) (g:(real^N->bool)->bool) <=>
    ~(g = {}) /\ ?a. a IN UNIONS l /\ !r. r IN g ==> a extreme_point_of r`;;

let moi_fta_gm = new_definition
 `moi_fta_gm (l:(real^N->bool)->bool) (g:(real^N->bool)->bool) <=>
    moi_fta_gp l g /\
    ?b. ~(b IN UNIONS l) /\ !r. r IN g ==> b extreme_point_of r`;;

let moi_fta_gw = new_definition
 `moi_fta_gw (t:(real^N->bool)->bool) (v:real^N) w (g:(real^N->bool)->bool) <=>
    ~(g = {}) /\
    !r. r IN g
        ==> ?h. moi_bar_chain t h /\ segment[v,w] IN h /\
                (!s. s IN h ==> segment[v,w] SUBSET s) /\
                r = convex hull (IMAGE simplex_barycentre h)`;;

(* ------------------------------------------------------------------------- *)
(* Generalities.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FTA_IN_INTERIOR_SUB = prove
 (`!u s (x:real^N).
        x IN (subtopology euclidean u) interior_of s <=>
        ?U. open U /\ x IN U /\ x IN u /\ u INTER U SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u INTER U:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Near a point of a locally finite complex, every point lies in a simplex  *)
(* containing the given point.                                               *)

let MOI_FTA_LF_LOCAL_STAR = prove
 (`!c (x:real^N).
        lf_simplicial_complex c /\ x IN UNIONS c
        ==> ?U. open U /\ x IN U /\
                !y. y IN U /\ y IN UNIONS c ==> ?s. s IN c /\ x IN s /\ y IN s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U0 DIFF UNIONS {s:real^N->bool | s IN c /\ ~(s INTER U0 = {}) /\
                                              ~(x IN s)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{s:real^N->bool | s IN c /\ ~(s INTER U0 = {})}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]];
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n"))
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "n" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* A point in the relative interior of one barycentric simplex lying in     *)
(* another one: the first chain is part of the second.                       *)

let MOI_FTA_RI_SUBCHAIN = prove
 (`!c f g (x:real^N).
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre f)) /\
        x IN convex hull (IMAGE simplex_barycentre g)
        ==> f SUBSET g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre (f INTER g:(real^N->bool)->bool)) =
    convex hull (IMAGE simplex_barycentre f)`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_FACE_RI THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f INTER g:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FTA_HULL_INJ) THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN SET_TAC[]]);;

(* The extreme points of a barycentric simplex are the barycentres of its   *)
(* chain.                                                                    *)

let MOI_FTA_BS_EXTREME = prove
 (`!c h (a:real^N).
        moi_bar_complex c /\ moi_bar_chain c h
        ==> (a extreme_point_of convex hull (IMAGE simplex_barycentre h) <=>
             ?s. s IN h /\ a = simplex_barycentre s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* Barycentric subdivisions of subcomplexes are full: a simplex of t1 whose *)
(* extreme points all lie on the graph is a simplex of the subdivided graph. *)

let MOI_FTA_BS_FULL = prove
 (`!t l r:real^N->bool.
        lf_simplicial_complex t /\ simplicial_subcomplex l t /\
        r IN barycentric_subdivision t /\
        (!a. a extreme_point_of r ==> a IN UNIONS l)
        ==> r IN barycentric_subdivision l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision t` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:(real^N->bool)->bool) SUBSET l` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `simplex_barycentre (s:real^N->bool)`] MOI_FTA_BS_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain t (h:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[]);;

(* The closed star complex is a subcomplex; chains of faces of a simplex    *)
(* through v are chains of it.                                               *)

let MOI_FTA_CSTAR_FACTS = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> FINITE (moi_fta_cstar c v) /\
            simplicial_subcomplex (moi_fta_cstar c v) c /\
            moi_fta_cstar c v SUBSET c /\
            lf_simplicial_complex (moi_fta_cstar c v) /\
            moi_bar_complex (moi_fta_cstar c v) /\
            UNIONS (moi_fta_cstar c v) = UNIONS {s | s IN c /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_CSTAR_COMPLEX) THEN
  ASM_REWRITE_TAC[GSYM moi_fta_cstar] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN ASM_MESON_TAC[simplicial_subcomplex]);;

let MOI_FTA_CHAIN_FACES_CSTAR = prove
 (`!c g m (v:real^N).
        lf_simplicial_complex c /\ moi_bar_chain c g /\ m IN c /\ v IN m
        ==> moi_bar_chain (moi_fta_cstar c v) (g INTER {r | r face_of m})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_bar_chain; moi_fta_cstar] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ASM SET_TAC[];
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]);;

(* A shared extreme point on the graph puts a chain's simplex into N.       *)

let MOI_FTA_GP_IN_NBHD = prove
 (`!t l g (x:real^N).
        lf_simplicial_complex t /\ simplicial_subcomplex l t /\
        moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gp l g /\
        x IN convex hull (IMAGE simplex_barycentre g)
        ==> x IN derived_nbhd t l`,
  REWRITE_TAC[moi_fta_gp] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r0:real^N->bool. r0 IN g` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `r0:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain (barycentric_subdivision t) ({a:real^N} INSERT g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[SING_SUBSET] THEN ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({a:real^N} INSERT g))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{a:real^N} INSERT g` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN EXISTS_TAC `{a:real^N}` THEN
    REWRITE_TAC[MOI_FTA_BARY_SING];
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre g)` THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

(* The dual cell as a union of simplices of t2 from gp-chains of the closed *)
(* star of v in t1.                                                          *)

let MOI_FTA_CELL_CHAINS = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> derived_dual_cell t l v =
            UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                    moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g /\
                    moi_fta_gp l g}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; MOI_FTA_HULL_SING_CHAIN;
                 MOI_FTA_BARY_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `v:real^N`]
    MOI_FTA_CSTAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL; MOI_FTA_IN_NBHD] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC `m = convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))` THEN
    SUBGOAL_THEN `(m:real^N->bool) IN barycentric_subdivision t /\ (v:real^N) IN m`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                  (g0 INTER {r:real^N->bool | r face_of m}))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MOI_FTA_HULL_INTER_SIMPLEX THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[]] THEN
    EXISTS_TAC `g0 INTER {r:real^N->bool | r face_of m}` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_FACES_CSTAR THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fta_gp] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `g0:(real^N->bool)->bool`; `m:real^N->bool`; `x:real^N`]
        MOI_FTA_HULL_INTER_SIMPLEX) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    UNDISCH_TAC `~(g0 INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(g0:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g0:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `r0 = INTERS (g0:(real^N->bool)->bool)` THEN
    SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t /\ ~(r0 = {})`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?a:real^N. a extreme_point_of r0` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    EXISTS_TAC `a:real^N` THEN CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `r0:real^N->bool` THEN ASM_MESON_TAC[extreme_point_of];
      ALL_TAC] THEN
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(r0:real^N->bool) face_of s` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ASM_MESON_TAC[EXTREME_POINT_OF_FACE]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `moi_fta_cstar (barycentric_subdivision t) (v:real^N)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[derived_dual_cell; IN_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTA_GP_IN_NBHD THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fta_gp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fta_cstar (barycentric_subdivision t) (v:real^N)`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `UNIONS g IN moi_fta_cstar (barycentric_subdivision t) (v:real^N)`
  MP_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v)
                   (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `m:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`moi_fta_cstar (barycentric_subdivision t) (v:real^N)`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `UNIONS g:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre g)` THEN
  SET_TAC[]);;

(* The frontier of N relative to UNIONS t: points of N not interior to it.  *)

let MOI_FTA_FRONTIER_IFF = prove
 (`!t l (x:real^N).
        lf_simplicial_complex t /\ simplicial_subcomplex l t
        ==> (x IN derived_frontier t l <=>
             x IN derived_nbhd t l /\
             ~(x IN (subtopology euclidean (UNIONS t)) interior_of
                    (derived_nbhd t l)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[derived_frontier; frontier_of; CLOSURE_OF_CLOSED_IN; IN_DIFF]);;

(* Simplices of t2 whose chain shares an extreme point off the graph meet  *)
(* the frontier: their points are limits of points outside N.              *)

let MOI_FTA_GM_NOT_INTERIOR = prove
 (`!t l g (x:real^N).
        lf_simplicial_complex t /\ simplicial_subcomplex l t /\
        moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gm l g /\
        x IN convex hull (IMAGE simplex_barycentre g)
        ==> ~(x IN (subtopology euclidean (UNIONS t)) interior_of
                   (derived_nbhd t l))`,
  REWRITE_TAC[moi_fta_gm; moi_fta_gp] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?r0:real^N->bool. r0 IN g` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{b:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `r0:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  ABBREV_TAC `g' = {b:real^N} INSERT g` THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g':(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "g'" THEN MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[SING_SUBSET] THEN ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  ABBREV_TAC `s' = convex hull (IMAGE simplex_barycentre (g':(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `!y:real^N. y IN relative_interior s' ==> ~(y IN derived_nbhd t l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN EXPAND_TAC "s'" THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `g2:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g':(real^N->bool)->bool`; `g2:(real^N->bool)->bool`;
                   `y:real^N`] MOI_FTA_RI_SUBCHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(g2 INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
    SUBGOAL_THEN `~(g2:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g2:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `r2 = INTERS (g2:(real^N->bool)->bool)` THEN
    SUBGOAL_THEN `(r2:real^N->bool) IN barycentric_subdivision t /\ ~(r2 = {})`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(r2:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `r2 = {b:real^N}` ASSUME_TAC THENL
     [SUBGOAL_THEN `(r2:real^N->bool) SUBSET {b}` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~(b IN UNIONS (l:(real^N->bool)->bool))` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `r2:real^N->bool` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[MOI_FTA_IN_INTERIOR_SUB] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "interior_of"))
        (concl th))) THEN
  SUBGOAL_THEN `(x:real^N) IN closure(relative_interior s')` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(s':real^N->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s'" THEN REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE `!s. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `s':real^N->bool` THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre g)` THEN
    EXPAND_TAC "s'" THEN EXPAND_TAC "g'" THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(U INTER relative_interior s':real^N->bool = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `relative_interior s':real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `UNIONS (t:(real^N->bool)->bool)` &&
      can (find_term ((=) `barycentric_subdivision (barycentric_subdivision
        (t:(real^N->bool)->bool))`)) (concl th))) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s':real^N->bool` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "s'" THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `g':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN derived_nbhd t l` MP_TAC THENL
   [UNDISCH_TAC `UNIONS t INTER U SUBSET derived_nbhd t (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `relative_interior (s':real^N->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* A point of a gp-simplex of t2 that lies in no gm-simplex is interior to *)
(* N: its carrier chain has a least member spanned by graph vertices, which *)
(* belongs to the subdivided graph, so all simplices of t2 around the point *)
(* meet the graph.                                                           *)

let MOI_FTA_NOT_GM_INTERIOR = prove
 (`!t l g (x:real^N).
        lf_simplicial_complex t /\ simplicial_subcomplex l t /\
        moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gp l g /\
        x IN convex hull (IMAGE simplex_barycentre g) /\
        (!g'. moi_bar_chain (barycentric_subdivision t) g' /\ moi_fta_gm l g'
              ==> ~(x IN convex hull (IMAGE simplex_barycentre g')))
        ==> x IN (subtopology euclidean (UNIONS t)) interior_of
                 (derived_nbhd t l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nogm")))))) THEN
  REWRITE_TAC[moi_fta_gp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`; `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (gs:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(gs:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior
                   (convex hull (IMAGE simplex_barycentre gs))` THEN
    ASM_REWRITE_TAC[MOI_BAR_CHAIN_EMPTY_RI];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `gs:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r0 = INTERS (gs:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^N. b extreme_point_of r0 ==> b IN UNIONS l`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "nogm" (MP_TAC o SPEC `gs:(real^N->bool)->bool`) THEN
    REWRITE_TAC[ASSUME `moi_bar_chain (barycentric_subdivision t)
                          (gs:(real^N->bool)->bool)`] THEN
    REWRITE_TAC[moi_fta_gm; moi_fta_gp; ASSUME `~(gs:(real^N->bool)->bool = {})`] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(r0:real^N->bool) face_of r` ASSUME_TAC THENL
         [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
          EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
          ASM_MESON_TAC[EXTREME_POINT_OF_FACE]]];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_BS_FULL THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS (barycentric_subdivision
                  (barycentric_subdivision t))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                    (t:(real^N->bool)->bool))`; `x:real^N`]
    MOI_FTA_LF_LOCAL_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  REWRITE_TAC[MOI_FTA_IN_INTERIOR_SUB] THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS (barycentric_subdivision
                   (barycentric_subdivision t))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  REMOVE_THEN "loc" (MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(s:real^N->bool) IN barycentric_subdivision
                 (barycentric_subdivision t)` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN EXISTS_TAC `g2:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `gs:(real^N->bool)->bool`; `g2:(real^N->bool)->bool`;
                 `x:real^N`] MOI_FTA_RI_SUBCHAIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN DISCH_TAC THEN
  EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Chains of the closed star lie in the faces of one simplex through v.     *)

let MOI_FTA_CSTAR_CHAIN_TOP = prove
 (`!c g (v:real^N).
        lf_simplicial_complex c /\ moi_bar_chain (moi_fta_cstar c v) g /\
        ~(g = {})
        ==> ?m. m IN c /\ v IN m /\ (!r. r IN g ==> r face_of m) /\
                convex hull (IMAGE simplex_barycentre g) SUBSET m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (moi_fta_cstar c (v:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_BAR_SUB THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
    REWRITE_TAC[simplicial_subcomplex; moi_fta_cstar; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ASM_MESON_TAC[FACE_OF_TRANS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fta_cstar c (v:real^N)`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `UNIONS g IN moi_fta_cstar c (v:real^N)` MP_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (moi_fta_cstar c v) (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `UNIONS g:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
    EXISTS_TAC `moi_fta_cstar c (v:real^N)` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`moi_fta_cstar c (v:real^N)`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `UNIONS g:real^N->bool`]
      FACE_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The part of the dual cell on the frontier of N: gm-chains of the star.   *)

let MOI_FTA_CELL_FRONTIER_CHAINS = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> derived_dual_cell t l v INTER derived_frontier t l =
            UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                    moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g /\
                    moi_fta_gm l g}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CELL_CHAINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
    SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; MOI_FTA_HULL_SING_CHAIN;
                 MOI_FTA_BARY_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `v:real^N`]
    MOI_FTA_CSTAR_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `derived_dual_cell t l (v:real^N)`) th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t)
                    (g:(real^N->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `moi_fta_cstar (barycentric_subdivision t) (v:real^N)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?g':(real^N->bool)->bool.
                    moi_bar_chain (barycentric_subdivision t) g' /\
                    moi_fta_gm l g' /\
                    x IN convex hull (IMAGE simplex_barycentre g')`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:(real^N->bool)->bool`; `x:real^N`]
        MOI_FTA_NOT_GM_INTERIOR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(x:real^N) IN derived_frontier t l` THEN
      ASM_SIMP_TAC[MOI_FTA_FRONTIER_IFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_fta_gp]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_CSTAR_CHAIN_TOP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                  (g' INTER {r:real^N->bool | r face_of m}))` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `g' INTER {r:real^N->bool | r face_of m}` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CHAIN_FACES_CSTAR THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_fta_gm l (g':(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fta_gm; moi_fta_gp; IN_INTER] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                       `g':(real^N->bool)->bool`; `m:real^N->bool`; `x:real^N`]
          MOI_FTA_HULL_INTER_SIMPLEX) THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
        ASM SET_TAC[];
        EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[];
        EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC MOI_FTA_HULL_INTER_SIMPLEX THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN derived_dual_cell t l v` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
      [check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `derived_dual_cell t l (v:real^N)`) th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[moi_fta_gm];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_FTA_FRONTIER_IFF] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[derived_dual_cell; IN_INTER]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTA_GM_NOT_INTERIOR THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
  EXISTS_TAC `moi_fta_cstar (barycentric_subdivision t) (v:real^N)` THEN
  ASM_REWRITE_TAC[]);;

(* Helpers for the splitting disks.                                          *)

let MOI_FTA_CHAIN_SUPERSEG = prove
 (`!t h (v:real^N) w.
        moi_bar_complex t /\ moi_bar_chain t h /\
        (!s. s IN h ==> v IN s /\ w IN s)
        ==> !s. s IN h ==> segment[v,w] SUBSET s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
  SUBGOAL_THEN `(s:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ASM_MESON_TAC[]]);;

let MOI_FTA_GRAPH_CHAIN_SEG = prove
 (`!t l f0 h (v:real^N) w.
        moi_bar_complex t /\ simplicial_subcomplex l t /\
        (!s. s IN l ==> aff_dim s <= &1) /\
        {v} IN t /\ {w} IN t /\ ~(v = w) /\
        moi_bar_chain l f0 /\ ~(f0 = {}) /\ f0 SUBSET h /\
        (!s. s IN h ==> v IN s /\ w IN s)
        ==> segment[v,w] IN f0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN f0` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sg = segment[v:real^N,w]` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN h` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `moi_bar_chain l (f0:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_FTA_CHAIN_ELT = prove
 (`!c g r:real^N->bool.
        moi_bar_chain c g /\ r IN g ==> r IN c /\ ~(r = {})`,
  REWRITE_TAC[moi_bar_chain; SUBSET] THEN MESON_TAC[]);;

(* The splitting disk is contained in the union of the gw-simplices.        *)

let MOI_FTA_DISK_SUB = prove
 (`!(t:(real^N->bool)->bool) l v w x.
        graph_in_complex t l /\ ~(w = v) /\ segment[v,w] IN l /\
        {v} IN l /\ {w} IN l /\
        x IN derived_dual_cell t l v /\ x IN derived_dual_cell t l w
        ==> ?g. moi_bar_chain (barycentric_subdivision t) g /\
                moi_fta_gw t v w g /\
                x IN convex hull (IMAGE simplex_barycentre g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN t /\ {w:real^N} IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN derived_nbhd t l /\
    (?h1. moi_bar_chain t h1 /\ {v} IN h1 /\
          x IN convex hull (IMAGE simplex_barycentre h1)) /\
    (?h2. moi_bar_chain t h2 /\ {w} IN h2 /\
          x IN convex hull (IMAGE simplex_barycentre h2))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`; `x:real^N`] MOI_FTA_IN_DUAL_CELL) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `w:real^N`; `x:real^N`] MOI_FTA_IN_DUAL_CELL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h2:(real^N->bool)->bool`;
                 `w:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `h = (h1 INTER h2):(real^N->bool)->bool` THEN
  SUBGOAL_THEN `moi_bar_chain t (h:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN h ==> v IN s /\ w IN s` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[IN_INTER] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre h)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `v:real^N`; `w:real^N`] MOI_FTA_CHAIN_SUPERSEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `q = convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(q:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g0 INTER {r:real^N->bool | r face_of q}` THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                   (g0 INTER {r:real^N->bool | r face_of q}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_HULL_INTER_SIMPLEX THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER; moi_fta_gw] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                   (g0 INTER {r:real^N->bool | r face_of q}))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `~(g0 INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `~(g0:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g0:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `r0 = INTERS (g0:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision t /\ ~(r0 = {})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_ELT THEN EXISTS_TAC `g0:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN barycentric_subdivision l` MP_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain t (f0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f0:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(r0:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_FTA_BS_SUBSET_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT];
      EXPAND_TAC "q" THEN MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f0:(real^N->bool)->bool) SUBSET h'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `r0 = convex hull (IMAGE simplex_barycentre (f0:(real^N->bool)->bool))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `s = convex hull (IMAGE simplex_barycentre (h':(real^N->bool)->bool))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. (x:real^N->bool) IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `f0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_GRAPH_CHAIN_SEG THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                          `h:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* The splitting disk of an edge [v,w] of the graph: gw-chains of t1.        *)

let MOI_FTA_DISK_CHAINS = prove
 (`!(t:(real^N->bool)->bool) l v w.
        graph_in_complex t l /\ ~(w = v) /\ segment[v,w] IN l
        ==> derived_dual_cell t l v INTER derived_dual_cell t l w =
            UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                    moi_bar_chain (barycentric_subdivision t) g /\
                    moi_fta_gw t v w g}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN l /\ {w:real^N} IN l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [simplicial_subcomplex] o check (fun th ->
        can (find_term ((=) `l:(real^N->bool)->bool`)) (concl th) &&
        is_comb(concl th) &&
        fst(strip_comb(concl th)) = `simplicial_subcomplex:((real^N->bool)->bool)->((real^N->bool)->bool)->bool` &&
        not(can (find_term ((=) `barycentric_subdivision (l:(real^N->bool)->bool)`)) (concl th)))) THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
             AFFINE_INDEPENDENT_2] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN t /\ {w:real^N} IN t /\ segment[v,w] IN t`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(v:real^N,w) IN UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`; `w:real^N`; `x:real^N`] MOI_FTA_DISK_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_fta_gp l (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fta_gw t v w (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fta_gw; moi_fta_gp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `midpoint(v:real^N,w)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `midpoint(v:real^N,w)`] MOI_FTA_BS_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN derived_nbhd t l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_GP_IN_NBHD THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fta_gw]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS g` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_fta_gw t v w (g:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_fta_gw] THEN
  DISCH_THEN(MP_TAC o SPEC `UNIONS g:real^N->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u:real^N. (u = v \/ u = w)
               ==> moi_bar_chain t ({u} INSERT h) /\
                   x IN convex hull (IMAGE simplex_barycentre ({u} INSERT h))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
      REWRITE_TAC[SING_SUBSET] THEN
      SUBGOAL_THEN `segment[v:real^N,w] SUBSET s` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`v:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN SET_TAC[];
      UNDISCH_TAC `(x:real^N) IN UNIONS g` THEN ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTA_IN_DUAL_CELL] THEN CONJ_TAC THENL
   [EXISTS_TAC `{v:real^N} INSERT h` THEN ASM_MESON_TAC[IN_INSERT];
    EXISTS_TAC `{w:real^N} INSERT h` THEN ASM_MESON_TAC[IN_INSERT]]);;

(* gw-chains are chains of the closed star of v in t1.                       *)

let MOI_FTA_GW_CSTAR = prove
 (`!(t:(real^N->bool)->bool) v w g.
        lf_simplicial_complex t /\ {v} IN t /\
        moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gw t v w g
        ==> moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fta_gw] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; moi_fta_cstar; IN_ELIM_THM] THEN
  X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `segment[v:real^N,w]`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain t ({v:real^N} INSERT h)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[SING_SUBSET] THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET s` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({v:real^N} INSERT h))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{v:real^N} INSERT h` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
    EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;


(* ========================================================================= *)
(* Level derived points.  For a simplex r whose vertices lie both           *)
(* on and off the graph, moi_fta_lev l r is the midpoint of the barycentres *)
(* of the two vertex groups; otherwise the barycentre.  In a simplex m with *)
(* the affine function f equal to 1 at the graph vertices and 0 at the      *)
(* others, the level points of the mixed faces lie on the level f = 1/2,    *)
(* so the level derived neighbourhood of the graph is the half space        *)
(* f >= 1/2 of m and its frontier the level f = 1/2.                        *)
(* ========================================================================= *)

let moi_fta_lev = new_definition
 `moi_fta_lev (l:(real^N->bool)->bool) (r:real^N->bool) =
    if (?a. a extreme_point_of r /\ a IN UNIONS l) /\
       (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
    then midpoint(barycentre {a | a extreme_point_of r /\ a IN UNIONS l},
                  barycentre {b | b extreme_point_of r /\ ~(b IN UNIONS l)})
    else simplex_barycentre r`;;

(* The midpoint of the barycentres of two complementary vertex groups lies  *)
(* in the relative interior.                                                 *)

let MOI_FTA_MID_BARY_RELINT = prove
 (`!(V:real^N->bool) P.
        ~affine_dependent V /\
        ~({x | x IN V /\ P x} = {}) /\ ~({x | x IN V /\ ~P x} = {})
        ==> midpoint(barycentre {x | x IN V /\ P x},
                     barycentre {x | x IN V /\ ~P x}) IN
            relative_interior(convex hull V)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `A = {x:real^N | x IN V /\ P x}` THEN
  ABBREV_TAC `B = {x:real^N | x IN V /\ ~P x}` THEN
  SUBGOAL_THEN `FINITE(A:real^N->bool) /\ FINITE(B:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(A:real^N->bool) = 0) /\ ~(CARD(B:real^N->bool) = 0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `\x:real^N. if P x then inv(&2 * &(CARD(A:real^N->bool)))
                         else inv(&2 * &(CARD(B:real^N->bool)))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; LT_NZ];
    ASM_SIMP_TAC[SUM_CASES; SUM_CONST] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&(CARD(A:real^N->bool)) * inv(&(CARD A)) = &1 /\
                  &(CARD(B:real^N->bool)) * inv(&(CARD B)) = &1`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
      CONV_TAC REAL_FIELD];
    SUBGOAL_THEN
     `vsum V (\x:real^N. (if P x then inv(&2 * &(CARD(A:real^N->bool)))
                          else inv(&2 * &(CARD(B:real^N->bool)))) % x) =
      vsum V (\x. if P x then inv(&2 * &(CARD A)) % x
                  else inv(&2 * &(CARD B)) % x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VSUM_CASES; barycentre; midpoint] THEN
    REWRITE_TAC[REAL_INV_MUL; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
    VECTOR_ARITH_TAC]);;

let MOI_FTA_LEV_RELINT = prove
 (`!l n (r:real^N->bool).
        n simplex r /\ ~(r = {}) ==> moi_fta_lev l r IN relative_interior r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fta_lev] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`V:real^N->bool`;
    `\x:real^N. x IN UNIONS (l:(real^N->bool)->bool)`] MOI_FTA_MID_BARY_RELINT)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(?a:real^N. a extreme_point_of convex hull V /\ a IN UNIONS l) /\
               (?b. b extreme_point_of convex hull V /\ ~(b IN UNIONS l))` THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN SET_TAC[]);;

(* Affine functions with prescribed 0/1 values at the vertices.              *)

let MOI_FTA_LEVEL_FN = prove
 (`!(V:real^N->bool) (P:real^N->bool).
        ~affine_dependent V
        ==> ?f:real^N->real.
                (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                (!a. a IN V ==> f a = if P a then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`;
                 `\a:real^N. if P a then vec 1:real^1 else vec 0`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^1` (X_CHOOSE_THEN `y0:real^1`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. drop((L:real^N->real^1) x + y0)` THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC]]);;

let MOI_FTA_LEVEL_SET_CONVEX = prove
 (`!(f:real^N->real) c.
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y)
        ==> convex {x | f x = c} /\ convex {x | c <= f x} /\
            convex {x | f x <= c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - u) * (a - c) + u * (b - c)
                             ==> c <= (&1 - u) * a + u * b`) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - u) * (c - a) + u * (c - b)
                             ==> (&1 - u) * a + u * b <= c`) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC]);;

(* Constant on a set gives constant on its convex hull.                       *)

let MOI_FTA_LEVEL_HULL = prove
 (`!(f:real^N->real) c s.
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!x. x IN s ==> f x = c)
        ==> !x. x IN convex hull s ==> f x = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull s SUBSET {x:real^N | (f:real^N->real) x = c}`
   (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[MOI_FTA_LEVEL_SET_CONVEX] THEN ASM SET_TAC[]);;

let MOI_FTA_LEVEL_HULL_GE = prove
 (`!(f:real^N->real) c s.
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!x. x IN s ==> c <= f x)
        ==> !x. x IN convex hull s ==> c <= f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull s SUBSET {x:real^N | c <= f x}`
   (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[MOI_FTA_LEVEL_SET_CONVEX] THEN ASM SET_TAC[]);;

(* The value of the level function at the level point of a face.            *)

let MOI_FTA_LEV_VALUE = prove
 (`!l (f:real^N->real) V W.
        ~affine_dependent V /\
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!a. a IN V ==> f a = if a IN UNIONS l then &1 else &0) /\
        W SUBSET V /\ ~(W = {})
        ==> f (moi_fta_lev l (convex hull W)) =
            if (?a. a IN W /\ a IN UNIONS l) /\ (?b. b IN W /\ ~(b IN UNIONS l))
            then &1 / &2
            else if (?a. a IN W /\ a IN UNIONS l) then &1 else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent(W:real^N->bool) /\ FINITE W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[moi_fta_lev; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               MOI_BAR_SIMPLEX_BARYCENTRE_HULL] THEN
  SUBGOAL_THEN
   `!c (S:real^N->bool). FINITE S /\ ~(S = {}) /\ (!x. x IN S ==> f x = c)
                         ==> (f:real^N->real) (barycentre S) = c`
  (LABEL_TAC "bary") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `c:real`; `S:real^N->bool`]
      MOI_FTA_LEVEL_HULL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC BARYCENTRE_IN_CONVEX_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN W ==> f x = if x IN UNIONS l then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[midpoint; VECTOR_ARITH
     `inv(&2) % (p + q):real^N = (&1 - inv(&2)) % p + inv(&2) % q`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `(&1 - u) * (f:real^N->real) x + u * f y`)) (concl th)) th]) THEN
    SUBGOAL_THEN
     `(f:real^N->real) (barycentre {a | a IN W /\ a IN UNIONS l}) = &1 /\
      f (barycentre {b | b IN W /\ ~(b IN UNIONS l)}) = &0`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN USE_THEN "bary" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN ASM SET_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  USE_THEN "bary" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  ASM SET_TAC[]);;

(* A point of the hull of two level sets lying beyond the first value lies  *)
(* in the hull of the second.                                                *)

let MOI_FTA_HULL_LEVEL = prove
 (`!(f:real^N->real) S1 S2 c1 c2 x.
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!y. y IN S1 ==> f y = c1) /\ (!y. y IN S2 ==> f y = c2) /\
        x IN convex hull (S1 UNION S2) /\
        ((c1 < c2 /\ c2 <= f x) \/ (c2 < c1 /\ f x <= c2))
        ==> x IN convex hull S2 /\ ~(S2 = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  (ASM_CASES_TAC `S2:real^N->bool = {}` THENL
    [UNDISCH_TAC `(x:real^N) IN convex hull (S1 UNION S2)` THEN
     ASM_REWRITE_TAC[UNION_EMPTY] THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`f:real^N->real`; `c1:real`; `S1:real^N->bool`]
       MOI_FTA_LEVEL_HULL) THEN
     ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `S1:real^N->bool = {}` THENL
    [UNDISCH_TAC `(x:real^N) IN convex hull (S1 UNION S2)` THEN
     ASM_REWRITE_TAC[UNION_EMPTY];
     ALL_TAC] THEN
   UNDISCH_TAC `(x:real^N) IN convex hull (S1 UNION S2)` THEN
   ONCE_REWRITE_TAC[HULL_UNION] THEN
   ASM_SIMP_TAC[CONVEX_HULL_UNION_NONEMPTY_EXPLICIT; CONVEX_CONVEX_HULL;
                CONVEX_HULL_EQ_EMPTY; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (X_CHOOSE_THEN `u:real`
     (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `(f:real^N->real) y1 = c1 /\ f y2 = c2` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ISPECL [`f:real^N->real`; `c1:real`; `S1:real^N->bool`]
         MOI_FTA_LEVEL_HULL);
       MP_TAC(ISPECL [`f:real^N->real`; `c2:real`; `S2:real^N->bool`]
         MOI_FTA_LEVEL_HULL)] THEN
     ASM_SIMP_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(&1 - u) * (c2 - c1) = &0` MP_TAC THENL
    [UNDISCH_TAC `((c1:real) < c2 /\ c2 <= f(x:real^N)) \/ (c2 < c1 /\ f x <= c2)` THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
      [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
       REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_ARITH `a * (c2 - c1) <= &0 <=> &0 <= a * (c1 - c2)`] THEN
         MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
         ASM_REAL_ARITH_TAC]];
     ALL_TAC] THEN
   REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL
    [SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
                       VECTOR_MUL_LID]];
     ASM_REAL_ARITH_TAC]));;

(* The face complex of a simplex, and the covering of the simplex by the    *)
(* level-point simplices of its chains of faces (derived retriangulation).  *)

let MOI_FTA_FACE_COMPLEX_BAR = prove
 (`!n m:real^N->bool.
        n simplex m
        ==> FINITE {r | r face_of m} /\ moi_bar_complex {r | r face_of m} /\
            UNIONS {r | r face_of m} = m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:int`; `m:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN SIMP_TAC[]);;

let MOI_FTA_LEV_COVER = prove
 (`!l n m (x:real^N).
        n simplex m /\ x IN m
        ==> ?g. moi_bar_chain {r | r face_of m} g /\
                x IN convex hull (IMAGE (moi_fta_lev l) g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:int`; `m:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `moi_fta_lev l:(real^N->bool)->real^N`]
    MOI_FTA_DERIVED_HOMEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_SIMPLEX THEN
    EXISTS_TAC `{r:real^N->bool | r face_of m}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "fix"))))) THEN
  SUBGOAL_THEN `(x:real^N) IN IMAGE (h:real^N->real^N) m` MP_TAC THENL
   [USE_THEN "fix" (MP_TAC o SPEC `m:real^N->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x':real^N) IN UNIONS (barycentric_subdivision {r | r face_of m})`
  MP_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_UNIONS_SUBDIVISION]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "img" (MP_TAC o C MATCH_MP
    (ASSUME `moi_bar_chain {r:real^N->bool | r face_of m} g`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^N` THEN ASM_MESON_TAC[]);;

(* Level values at faces, in terms of extreme points.                        *)

let MOI_FTA_FACE_LEV_VALUE = prove
 (`!l (f:real^N->real) V r.
        ~affine_dependent V /\
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!a. a IN V ==> f a = if a IN UNIONS l then &1 else &0) /\
        r face_of convex hull V /\ ~(r = {})
        ==> f (moi_fta_lev l r) =
            if (?a. a extreme_point_of r /\ a IN UNIONS l) /\
               (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
            then &1 / &2
            else if (?a. a extreme_point_of r /\ a IN UNIONS l) then &1 else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(r:real^N->bool) face_of convex hull V` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent(W:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  MATCH_MP_TAC MOI_FTA_LEV_VALUE THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(convex hull W:real^N->bool = {})` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY]);;

(* The least member of a chain of faces is a face of every member.          *)

let MOI_FTA_FACE_CHAIN_MIN = prove
 (`!m g:(real^N->bool)->bool.
        moi_bar_chain {r | r face_of m} g /\ ~(g = {})
        ==> INTERS g IN g /\ ~(INTERS g = {}) /\
            (!r. r IN g ==> INTERS g face_of r) /\
            (!r a. r IN g /\ a extreme_point_of INTERS g ==> a extreme_point_of r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `g:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> r face_of m /\ ~(r = {})`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of m} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> INTERS g face_of r` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`INTERS g:real^N->bool`; `m:real^N->bool`; `r:real^N->bool`]
      FACE_OF_FACE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`INTERS g:real^N->bool`; `r:real^N->bool`; `a:real^N`]
    EXTREME_POINT_OF_FACE) THEN
  ASM_SIMP_TAC[]);;

(* Elements of chains of faces of a simplex, with their level points.       *)

let MOI_FTA_FACE_CHAIN_ELT = prove
 (`!l n m g (r:real^N->bool).
        n simplex m /\ moi_bar_chain {r | r face_of m} g /\ r IN g
        ==> r face_of m /\ ~(r = {}) /\ moi_fta_lev l r IN r /\
            moi_fta_lev l r IN m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `g:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FTA_CHAIN_ELT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_fta_lev l (r:real^N->bool) IN r`
   (fun th -> ASM_MESON_TAC[th; FACE_OF_IMP_SUBSET; SUBSET]) THEN
  MATCH_MP_TAC(SET_RULE `!x:real^N r. x IN relative_interior r /\
                           relative_interior r SUBSET r ==> x IN r`) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
  MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:int`; `m:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_BAR_COMPLEX_SIMPLEX THEN
  EXISTS_TAC `{r:real^N->bool | r face_of m}` THEN ASM_REWRITE_TAC[IN_ELIM_THM]);;

let MOI_FTA_IN_UNIONS_HULLS = prove
 (`!(Q:((real^N->bool)->bool)->bool) (d:(real^N->bool)->real^N) x.
        x IN UNIONS {convex hull (IMAGE d g) | g | Q g} <=>
        ?g. Q g /\ x IN convex hull (IMAGE d g)`,
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Chains of faces whose members all have a graph vertex (and a non-graph  *)
(* vertex) are gp (gm) chains, via the least member.                         *)

let MOI_FTA_GP_GM_MIN = prove
 (`!l m g:(real^N->bool)->bool.
        moi_bar_chain {r | r face_of m} g /\ ~(g = {})
        ==> ((!r. r IN g ==> ?a. a extreme_point_of r /\ a IN UNIONS l)
             ==> moi_fta_gp l g) /\
            ((!r. r IN g ==> (?a. a extreme_point_of r /\ a IN UNIONS l) /\
                             (?b. b extreme_point_of r /\ ~(b IN UNIONS l)))
             ==> moi_fta_gm l g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_FACE_CHAIN_MIN) THEN
  REWRITE_TAC[moi_fta_gm; moi_fta_gp] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `INTERS g:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* In a chain of faces, a member with a vertex of P lying above a member    *)
(* without one also has a vertex outside P.                                  *)

let MOI_FTA_CHAIN_EXT_UP = prove
 (`!m g r1 r (P:real^N->bool).
        moi_bar_chain {r | r face_of m} g /\ convex m /\ compact m /\
        r1 IN g /\ r IN g /\
        ~(?a. a extreme_point_of r1 /\ a IN P) /\
        (?a. a extreme_point_of r /\ a IN P)
        ==> ?b. b extreme_point_of r /\ ~(b IN P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `g:(real^N->bool)->bool`;
                 `r1:real^N->bool`] MOI_FTA_CHAIN_ELT) THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `g:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FTA_CHAIN_ELT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r1:real^N->bool) SUBSET r \/ r SUBSET r1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of m} g` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(r1:real^N->bool) face_of r` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `m:real^N->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPEC `r1:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN EXISTS_TAC `b:real^N` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ASM_MESON_TAC[]];
    SUBGOAL_THEN `(r:real^N->bool) face_of r1` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `m:real^N->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    ASM_MESON_TAC[EXTREME_POINT_OF_FACE]]);;

(* The level derived neighbourhood in one simplex: the gp chains of faces  *)
(* give the half space f >= 1/2, the gm chains the level f = 1/2.          *)

let MOI_FTA_SIMPLEX_LEVEL_GE = prove
 (`!l (f:real^N->real) V x.
        ~affine_dependent V /\
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!a. a IN V ==> f a = if a IN UNIONS l then &1 else &0)
        ==> ((?g. moi_bar_chain {r | r face_of convex hull V} g /\
                  moi_fta_gp l g /\
                  x IN convex hull (IMAGE (moi_fta_lev l) g)) <=>
             x IN convex hull V /\ &1 / &2 <= f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r face_of convex hull V /\ ~(r = {})
       ==> f (moi_fta_lev l r) =
           if (?a. a extreme_point_of r /\ a IN UNIONS l) /\
              (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
           then &1 / &2
           else if (?a. a extreme_point_of r /\ a IN UNIONS l) then &1 else &0`
  (LABEL_TAC "val") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_FACE_LEV_VALUE THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. moi_bar_chain {r | r face_of convex hull V} g
        ==> convex hull (IMAGE (moi_fta_lev l) g) SUBSET
            convex hull (V:real^N->bool)`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
      `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
      `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `g:(real^N->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real`; `&1 / &2`;
      `IMAGE (moi_fta_lev l) (g:(real^N->bool)->bool)`] MOI_FTA_LEVEL_HULL_GE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `moi_fta_gp l (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fta_gp] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
    `convex hull V:real^N->bool`; `x:real^N`] MOI_FTA_LEV_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull (IMAGE (moi_fta_lev l) g)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. moi_bar_chain {r | r face_of convex hull V} k /\ ~(k = {}) /\
        (!r. r IN k ==> ?a:real^N. a extreme_point_of r /\ a IN UNIONS l)
        ==> moi_fta_gp l k` (LABEL_TAC "gpmin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `convex hull V:real^N->bool`;
                   `k:(real^N->bool)->bool`] MOI_FTA_GP_GM_MIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?r1:real^N->bool. r1 IN g /\ ~(?a. a extreme_point_of r1 /\ a IN UNIONS l)`
  THENL
   [ALL_TAC;
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "gpmin" MATCH_MP_TAC THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{r:real^N->bool | r IN g /\
                               (?a. a extreme_point_of r /\ a IN UNIONS l)}` THEN
  SUBGOAL_THEN
   `moi_bar_chain {r | r face_of convex hull V}
      {r:real^N->bool | r IN g /\ (?a. a extreme_point_of r /\ a IN UNIONS l)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`;
    `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     ~(?a. a extreme_point_of r /\ a IN UNIONS l)}`;
    `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     (?a. a extreme_point_of r /\ a IN UNIONS l)}`;
    `&0`; `&1 / &2`; `x:real^N`] MOI_FTA_HULL_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r1:real^N->bool`; `r:real^N->bool`; `UNIONS l:real^N->bool`]
        MOI_FTA_CHAIN_EXT_UP) THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
          ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_IMP_COMPACT];
          ASM_MESON_TAC[]];
        DISCH_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     ~(?a. a extreme_point_of r /\ a IN UNIONS l)} UNION
        IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     (?a. a extreme_point_of r /\ a IN UNIONS l)} =
        IMAGE (moi_fta_lev l) g` SUBST1_TAC THENL
       [SET_TAC[]; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gpmin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FTA_SIMPLEX_LEVEL_EQ = prove
 (`!l (f:real^N->real) V x.
        ~affine_dependent V /\
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        (!a. a IN V ==> f a = if a IN UNIONS l then &1 else &0)
        ==> ((?g. moi_bar_chain {r | r face_of convex hull V} g /\
                  moi_fta_gm l g /\
                  x IN convex hull (IMAGE (moi_fta_lev l) g)) <=>
             x IN convex hull V /\ f x = &1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `f:real^N->real`; `V:real^N->bool`;
                 `x:real^N`] MOI_FTA_SIMPLEX_LEVEL_GE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ge")] THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r face_of convex hull V /\ ~(r = {})
       ==> f (moi_fta_lev l r) =
           if (?a. a extreme_point_of r /\ a IN UNIONS l) /\
              (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
           then &1 / &2
           else if (?a. a extreme_point_of r /\ a IN UNIONS l) then &1 else &0`
  (LABEL_TAC "val") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_FACE_LEV_VALUE THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "ge" (MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[moi_fta_gm];
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`f:real^N->real`; `&1 / &2`;
      `IMAGE (moi_fta_lev l) (g:(real^N->bool)->bool)`] MOI_FTA_LEVEL_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `moi_fta_gm l (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fta_gm; moi_fta_gp] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(?a:real^N. a extreme_point_of r /\ a IN UNIONS l) /\
                    (?b:real^N. b extreme_point_of r /\ ~(b IN UNIONS l))`
       (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "ge" (MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fta_gp]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{r:real^N->bool | r IN g /\
                               (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}` THEN
  SUBGOAL_THEN
   `moi_bar_chain {r | r face_of convex hull V}
      {r:real^N->bool | r IN g /\ (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`;
    `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     ~(?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`;
    `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`;
    `&1`; `&1 / &2`; `x:real^N`] MOI_FTA_HULL_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:int`;
        `convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r:real^N->bool`] MOI_FTA_FACE_CHAIN_ELT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `(?a:real^N. a extreme_point_of r /\ a IN UNIONS l) /\
                    (?b:real^N. b extreme_point_of r /\ ~(b IN UNIONS l))`
       (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     ~(?b. b extreme_point_of r /\ ~(b IN UNIONS l))} UNION
        IMAGE (moi_fta_lev l) {r:real^N->bool | r IN g /\
                     (?b. b extreme_point_of r /\ ~(b IN UNIONS l))} =
        IMAGE (moi_fta_lev l) g` SUBST1_TAC THENL
       [SET_TAC[]; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `convex hull V:real^N->bool`;
    `{r:real^N->bool | r IN g /\ (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`]
    MOI_FTA_GP_GM_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* The level retriangulation of the closed star of a graph vertex          *)
(* v in t1 (MOI_FTA_DERIVED_HOMEO with the level points).  In each simplex *)
(* m of t1 containing v it maps C_v onto the half space f >= 1/2 and the    *)
(* frontier part C_v INTER Bd N onto the level f = 1/2.                     *)
(* ========================================================================= *)

(* Standard facts for a graph vertex.                                        *)

let MOI_FTA_SETUP = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> lf_simplicial_complex t /\ simplicial_subcomplex l t /\
            moi_bar_complex t /\ {v} IN t /\
            lf_simplicial_complex (barycentric_subdivision t) /\
            moi_bar_complex (barycentric_subdivision t) /\
            {v} IN barycentric_subdivision t /\
            pl_sphere 2 (UNIONS (simplicial_link (barycentric_subdivision t) v)) /\
            FINITE (moi_fta_cstar (barycentric_subdivision t) v) /\
            moi_bar_complex (moi_fta_cstar (barycentric_subdivision t) v) /\
            moi_fta_cstar (barycentric_subdivision t) v SUBSET
            barycentric_subdivision t /\
            UNIONS (moi_fta_cstar (barycentric_subdivision t) v) =
            UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; MOI_FTA_HULL_SING_CHAIN;
                 MOI_FTA_BARY_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `v:real^N`]
    MOI_FTA_CSTAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTA_BS_LINK THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; MOI_FTA_HULL_SING_CHAIN;
               MOI_FTA_BARY_SING]);;

(* Links are subcomplexes.                                                    *)

let MOI_FTA_LINK_LF = prove
 (`!c (v:real^N).
        lf_simplicial_complex c
        ==> simplicial_subcomplex (simplicial_link c v) c /\
            lf_simplicial_complex (simplicial_link c v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simplicial_subcomplex (simplicial_link c (v:real^N)) c`
   (fun th -> ASM_MESON_TAC[th; MOI_FDN_LF_SUBCOMPLEX]) THEN
  REWRITE_TAC[simplicial_subcomplex; simplicial_link; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    EXISTS_TAC `r:real^N->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS]]);;

(* Transfer of chain unions through the derived homeomorphism, restricted  *)
(* to one simplex m of the complex.                                          *)

let MOI_FTA_TRANSFER = prove
 (`!S (h:real^N->real^N) k d m P x.
        moi_bar_complex S /\
        homeomorphism (UNIONS S,UNIONS S) (h,k) /\
        (!f. moi_bar_chain S f
             ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
                 convex hull (IMAGE d f)) /\
        (!s. s IN S ==> IMAGE h s = s) /\ m IN S /\
        (!g g'. P g /\ g' SUBSET g /\ ~(g' = {}) ==> P g')
        ==> (x IN IMAGE h (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                                  moi_bar_chain S g /\ P g}) /\ x IN m <=>
             ?g. moi_bar_chain {r | r face_of m} g /\ P g /\
                 x IN convex hull (IMAGE d g))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "img") (CONJUNCTS_THEN2 (LABEL_TAC "fix")
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "her")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!r:real^N->bool. r face_of m ==> r IN S` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET UNIONS S` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)
      MP_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `(y:real^N) IN convex hull (IMAGE simplex_barycentre g)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS S` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_bar_chain S (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN m` ASSUME_TAC THENL
     [USE_THEN "fix" (MP_TAC o C MATCH_MP (ASSUME `(m:real^N->bool) IN S`)) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^N->real^N) y IN IMAGE h m` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y:real^N = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `(k:real^N->real^N) (h y) = y /\ k (h y') = y'`
       (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `g INTER {r:real^N->bool | r face_of m}` THEN
    MP_TAC(ISPECL [`S:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
      `m:real^N->bool`; `y:real^N`] MOI_FTA_HULL_INTER_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(g INTER {r:real^N->bool | r face_of m} = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(y:real^N) IN convex hull
        (IMAGE simplex_barycentre (g INTER {u:real^N->bool | u face_of m}))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain S (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_INTER; IN_ELIM_THM] THEN
      SIMP_TAC[FINITE_INTER];
      USE_THEN "her" MATCH_MP_TAC THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      SUBGOAL_THEN `moi_bar_chain S (g INTER {r:real^N->bool | r face_of m})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
        EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
        ALL_TAC] THEN
      USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME
        `moi_bar_chain S (g INTER {r:real^N->bool | r face_of m})`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain S (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of m} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull (IMAGE d (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre g) SUBSET (m:real^N->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of m} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
    MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME
    `moi_bar_chain S (g:(real^N->bool)->bool)`)) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t. x IN IMAGE (h:real^N->real^N) s /\ s SUBSET t
                                 ==> x IN IMAGE h t`) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "fix" (MP_TAC o C MATCH_MP (ASSUME `(m:real^N->bool) IN S`)) THEN
    ASM SET_TAC[]]);;

let MOI_FTA_GP_GM_HER = prove
 (`!l:(real^N->bool)->bool.
        (!g g'. moi_fta_gp l g /\ g' SUBSET g /\ ~(g' = {}) ==> moi_fta_gp l g') /\
        (!g g'. moi_fta_gm l g /\ g' SUBSET g /\ ~(g' = {}) ==> moi_fta_gm l g')`,
  REWRITE_TAC[moi_fta_gp; moi_fta_gm; SUBSET] THEN MESON_TAC[]);;

(* The level retriangulation of the closed star of a graph vertex.          *)

let MOI_FTA_THETA = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> ?h k. pl_homeomorphism
                    (UNIONS {s | s IN barycentric_subdivision t /\ v IN s},
                     UNIONS {s | s IN barycentric_subdivision t /\ v IN s}) (h,k) /\
                  (!s. s IN moi_fta_cstar (barycentric_subdivision t) v
                       ==> IMAGE h s = s) /\
                  (!m. m IN barycentric_subdivision t /\ v IN m
                       ==> ?f. (!x y u. f((&1 - u) % x + u % y) =
                                        (&1 - u) * f x + u * f y) /\
                               (!a. a extreme_point_of m
                                    ==> f a = if a IN UNIONS l then &1 else &0) /\
                               f v = &1 /\
                               (!x. x IN IMAGE h (derived_dual_cell t l v) /\
                                    x IN m <=>
                                    x IN m /\ &1 / &2 <= f x) /\
                               (!x. x IN IMAGE h (derived_dual_cell t l v INTER
                                                  derived_frontier t l) /\
                                    x IN m <=>
                                    x IN m /\ f x = &1 / &2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_SETUP) THEN
  MP_TAC(ISPECL [`moi_fta_cstar (barycentric_subdivision t) (v:real^N)`;
                 `moi_fta_lev (l:(real^N->bool)->bool)`] MOI_FTA_DERIVED_HOMEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_SIMPLEX THEN
    EXISTS_TAC `moi_fta_cstar (barycentric_subdivision t) (v:real^N)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "fix"))))) THEN
  SUBGOAL_THEN
   `homeomorphism (UNIONS (moi_fta_cstar (barycentric_subdivision t) v),
                   UNIONS (moi_fta_cstar (barycentric_subdivision t) (v:real^N)))
                  (h:real^N->real^N,k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism
      (UNIONS (moi_fta_cstar (barycentric_subdivision t) v),
       UNIONS (moi_fta_cstar (barycentric_subdivision t) (v:real^N)))
      (h:real^N->real^N,k)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "fix" ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:real^N->bool) IN moi_fta_cstar (barycentric_subdivision t) v`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of m` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `{v:real^N}`; `m:real^N->bool`] MOI_FM3_LF_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{v:real^N} INTER m = {v}` (fun th -> SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (m:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `V:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `\a:real^N. a IN UNIONS l`]
    MOI_FTA_LEVEL_FN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  EXISTS_TAC `f:real^N->real` THEN
  UNDISCH_TAC `(v:real^N) extreme_point_of convex hull V` THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^N` THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CELL_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`moi_fta_cstar (barycentric_subdivision t) (v:real^N)`;
      `h:real^N->real^N`; `k:real^N->real^N`;
      `moi_fta_lev (l:(real^N->bool)->bool)`; `convex hull V:real^N->bool`;
      `moi_fta_gp (l:(real^N->bool)->bool)`; `x:real^N`] MOI_FTA_TRANSFER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MESON_TAC[MOI_FTA_GP_GM_HER];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOI_FTA_SIMPLEX_LEVEL_GE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CELL_FRONTIER_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`moi_fta_cstar (barycentric_subdivision t) (v:real^N)`;
      `h:real^N->real^N`; `k:real^N->real^N`;
      `moi_fta_lev (l:(real^N->bool)->bool)`; `convex hull V:real^N->bool`;
      `moi_fta_gm (l:(real^N->bool)->bool)`; `x:real^N`] MOI_FTA_TRANSFER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MESON_TAC[MOI_FTA_GP_GM_HER];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOI_FTA_SIMPLEX_LEVEL_EQ THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Combinatorics of the closed star of a graph vertex v in t1:              *)
(* the walls C_v INTER C_w make up the part of C_v on the link of v, and   *)
(* each simplex of t1 at v carries at most one further graph vertex.        *)
(* ========================================================================= *)

let MOI_FTA_SEG_VERTS = prove
 (`!(l:(real^N->bool)->bool) t a b.
        simplicial_subcomplex l t /\ segment[a,b] IN l
        ==> {a} IN l /\ {b} IN l /\ {a} IN t /\ {b} IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN l /\ {b:real^N} IN l` (fun th -> ASM_MESON_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `segment[a:real^N,b]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_FTA_SUBSEG_FACE = prove
 (`!s (v:real^N) w.
        s face_of segment[v,w] /\ ~(s = {}) /\ ~(w IN s) ==> s = {v}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{v:real^N,w}`; `s:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `c = {v:real^N}` (fun th -> REWRITE_TAC[th; CONVEX_HULL_SING]) THEN
  SUBGOAL_THEN `~(c:real^N->bool = {}) /\ ~((w:real^N) IN c)` MP_TAC THENL
   [ASM_MESON_TAC[CONVEX_HULL_EQ_EMPTY; HULL_INC]; ASM SET_TAC[]]);;

(* Closed stars of two distinct vertices of t meet in t1 only on links.     *)

let MOI_FTA_STAR_INTER_LINK = prove
 (`!(t:(real^N->bool)->bool) v w x.
        lf_simplicial_complex t /\ {v} IN t /\ {w} IN t /\ ~(v = w) /\
        x IN UNIONS {s | s IN barycentric_subdivision t /\ v IN s} /\
        x IN UNIONS {s | s IN barycentric_subdivision t /\ w IN s}
        ==> x IN UNIONS (simplicial_link (barycentric_subdivision t) v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `m':real^N->bool` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `m INTER m':real^N->bool` THEN
  ASM_REWRITE_TAC[IN_INTER; simplicial_link; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `m:real^N->bool`; `m':real^N->bool`] MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    STRIP_TAC THEN
    UNDISCH_TAC `(m':real^N->bool) IN barycentric_subdivision t` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `w:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_bar_chain t (h:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `{w:real^N}`] o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* A point of C_v on a simplex q of the link of v in t1 lies in the cell   *)
(* C_w of a graph neighbour w with midpoint(v,w) a vertex of q.             *)

let MOI_FTA_LINK_PART = prove
 (`!(t:(real^N->bool)->bool) l v q x.
        graph_in_complex t l /\ {v} IN l /\
        q IN simplicial_link (barycentric_subdivision t) v /\
        x IN derived_dual_cell t l v /\ x IN q
        ==> ?w. ~(w = v) /\ segment[v,w] IN l /\ midpoint(v,w) IN q /\
                x IN derived_dual_cell t l w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  UNDISCH_TAC `q IN simplicial_link (barycentric_subdivision t) (v:real^N)` THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `?g. moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g /\
        moi_fta_gp l g /\
        (x:real^N) IN convex hull (IMAGE simplex_barycentre g)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CELL_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v)
                   (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
    `g:(real^N->bool)->bool`; `q:real^N->bool`; `x:real^N`]
    MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_bar_chain (barycentric_subdivision t)
      (g INTER {u:real^N->bool | u face_of q}) /\
    ~(g INTER {u:real^N->bool | u face_of q} = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                   (g INTER {u:real^N->bool | u face_of q}))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN g /\ r face_of q /\ (x:real^N) IN r`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `UNIONS (g INTER {u:real^N->bool | u face_of q})` THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
      `g INTER {u:real^N->bool | u face_of q}`] MOI_BAR_CHAIN_MAX) THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
      `g INTER {u:real^N->bool | u face_of q}`] MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fta_gp]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^N) extreme_point_of r` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision t /\ ~(r = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT]; ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN r) /\ (r:real^N->bool) SUBSET m` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision t` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?s1:real^N->bool. s1 IN h /\ a = simplex_barycentre s1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `a:real^N`] MOI_FTA_BS_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN t /\ ~(s1 = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s1` ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision t` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `hm:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hm:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hm:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FTA_BS_SUBSET_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `h:(real^N->bool)->bool = g0` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_INJ THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w extreme_point_of s1 /\ ~(w = v)` STRIP_ASSUME_TAC
  THENL
   [ASM_CASES_TAC `!w:real^N. w extreme_point_of s1 ==> w = v` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `s1 = {v:real^N}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `s1:real^N->bool` KREIN_MILMAN_MINKOWSKI) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `s1 SUBSET {v:real^N}` MP_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM CONVEX_HULL_SING] THEN
        MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      UNDISCH_TAC `(a:real^N) = simplex_barycentre s1` THEN
      ASM_REWRITE_TAC[MOI_FTA_BARY_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN t /\ (w:real^N) IN s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s1:real^N->bool` THEN
      ASM_REWRITE_TAC[FACE_OF_SING];
      ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 = segment[v:real^N,w]` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `midpoint(v:real^N,w) = a` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET; extreme_point_of]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN h ==> w IN s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN t /\ ~(s = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT]; ALL_TAC] THEN
    SUBGOAL_THEN `s SUBSET segment[v:real^N,w] \/ segment[v,w] SUBSET s`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain t (h:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[];
      ALL_TAC;
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N`; `w:real^N`]
      MOI_FTA_SUBSEG_FACE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                     `segment[v:real^N,w]`] MOI_FM3_LF_INTER) THEN
      ASM_SIMP_TAC[SET_RULE `!s t:real^N->bool. s SUBSET t ==> s INTER t = s`] THEN
      ASM_MESON_TAC[MOI_FTA_CHAIN_ELT];
      DISCH_THEN SUBST_ALL_TAC] THEN
    UNDISCH_TAC `~((v:real^N) IN r)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l v` THEN
  REWRITE_TAC[derived_dual_cell; IN_INTER] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({w:real^N} INSERT h))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{w:real^N} INSERT h` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM SET_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{w:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING; IN_INSERT];
    UNDISCH_TAC `(x:real^N) IN r` THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* The graph vertices of a simplex of t1 at v containing the midpoint of a *)
(* graph edge [v,w] are v and that midpoint.                                *)

let MOI_FTA_MID_UNIQUE = prove
 (`!(t:(real^N->bool)->bool) l v w m a.
        graph_in_complex t l /\ {v} IN l /\ ~(w = v) /\ segment[v,w] IN l /\
        m IN barycentric_subdivision t /\ v IN m /\ midpoint(v,w) IN m /\
        a extreme_point_of m /\ a IN UNIONS l
        ==> a = v \/ a = midpoint(v,w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `v:real^N`; `w:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision t` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `hm:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hm:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN hm` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hm:(real^N->bool)->bool`;
                   `segment[v:real^N,w]`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_REWRITE_TAC[MOI_FTA_BARY_SEGMENT] THEN
    ASM_MESON_TAC[ENDS_IN_SEGMENT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hm:(real^N->bool)->bool`;
                 `a:real^N`] MOI_FTA_BS_EXTREME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN t /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN l /\ (v:real^N) IN s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^N) IN s` THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET segment[v,w]` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain t (hm:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `segment[v:real^N,w]`] o
      last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N`; `w:real^N`]
    MOI_FTA_SUBSEG_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                   `segment[v:real^N,w]`] MOI_FM3_LF_INTER) THEN
    ASM_SIMP_TAC[SET_RULE `!s t:real^N->bool. s SUBSET t ==> s INTER t = s`];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]]);;

(* The walls make up the part of C_v on the link of v in t1.                 *)

let MOI_FTA_WALLS_EQ = prove
 (`!(t:(real^N->bool)->bool) l v.
        graph_in_complex t l /\ {v} IN l
        ==> UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                    w | ~(w = v) /\ segment[v,w] IN l} =
            derived_dual_cell t l v INTER
            UNIONS (simplicial_link (barycentric_subdivision t) v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex] o
    CONJUNCT1) THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IN_UNIONS] THEN MATCH_MP_TAC MOI_FTA_STAR_INTER_LINK THEN
    EXISTS_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                   `v:real^N`; `w:real^N`] MOI_FTA_SEG_VERTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[derived_dual_cell; IN_INTER]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `v:real^N`; `q:real^N->bool`; `x:real^N`] MOI_FTA_LINK_PART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^N)` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]]);;

(* A point of the splitting disk lies in a simplex of the link of v in t1  *)
(* containing the midpoint of the edge.                                      *)

let MOI_FTA_DISK_IN_DB = prove
 (`!(t:(real^N->bool)->bool) l u v x.
        graph_in_complex t l /\ ~(u = v) /\ segment[v,u] IN l /\
        x IN derived_dual_cell t l v /\ x IN derived_dual_cell t l u
        ==> ?q. q IN simplicial_link (barycentric_subdivision t) v /\
                midpoint(v,u) IN q /\ x IN q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `v:real^N`; `u:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `v:real^N`; `u:real^N`; `x:real^N`] MOI_FTA_DISK_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fta_gw]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gw")) THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "gw" (MP_TAC o SPEC `UNIONS g:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS g:real^N->bool` THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS g` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN h ==> v IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t ({v:real^N} INSERT h)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `segment[v:real^N,u]` THEN
    ASM_REWRITE_TAC[MOI_FTA_BARY_SEGMENT]] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_CHAIN_ELT];
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,u] SUBSET {v}` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N`) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({v:real^N} INSERT h))` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{v:real^N} INSERT h` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING; IN_INSERT];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]]]);;


(* ========================================================================= *)
(* Rays from the cone point.  Along the ray v + s % (y - v) the            *)
(* level function is (1 - s) + s * f y; the level set f = 1/2 together with *)
(* the part of f >= 1/2 on the base is met exactly once, and the half space *)
(* f >= 1/2 is the initial segment up to that point.                        *)
(* ========================================================================= *)

let MOI_FTA_RAY_REAL = prove
 (`!a. ?r. &0 < r /\ r <= &1 /\
           (!s. &0 < s /\ s <= &1
                ==> ((&1 - s) + s * a = &1 / &2 \/
                     &1 / &2 <= (&1 - s) + s * a /\ s = &1 <=> s = r)) /\
           (!s. &0 <= s /\ s <= &1
                ==> (&1 / &2 <= (&1 - s) + s * a <=> s <= r))`,
  GEN_TAC THEN ASM_CASES_TAC `&1 / &2 <= a` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`s:real`; `&1 - a`; `&1 / &2`] REAL_LE_LMUL) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - a /\ &1 < &2 * (&1 - a)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `inv(&2 * (&1 - a))` THEN
  SUBGOAL_THEN `inv(&2 * (&1 - a)) * (&2 * (&1 - a)) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = inv(&2 * (&1 - a))` THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THEN
  STRIP_TAC THENL
   [EQ_TAC THENL
     [STRIP_TAC THENL
       [SUBGOAL_THEN `(s - r) * (&2 * (&1 - a)) = &0` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&1 / &2 <= (&1 - s) + s * a` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`s:real`; `r:real`; `&1 - a`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_FTA_RAY_DATA = prove
 (`!(v:real^N) y L Y Z m f.
        ~(v IN L) /\
        (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
        y IN L /\ convex m /\ v IN m /\ y IN m /\
        (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        f v = &1 /\
        (!x. x IN m ==> (x IN Y <=> &1 / &2 <= f x)) /\
        (!x. x IN m ==> (x IN Z <=> f x = &1 / &2))
        ==> ?r. &0 < r /\ r <= &1 /\
                (!s. &0 < s /\ s <= &1
                     ==> (v + s % (y - v) IN Z UNION (Y INTER L) <=> s = r)) /\
                (!s. &0 <= s /\ s <= &1 ==> (v + s % (y - v) IN Y <=> s <= r))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rad")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Y") (LABEL_TAC "Z")))))))))) THEN
  MP_TAC(SPEC `(f:real^N->real) y` MOI_FTA_RAY_REAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "r1")
      (LABEL_TAC "r2"))))) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> v + s % (y - v) IN m /\
            (f:real^N->real)(v + s % (y - v)) = (&1 - s) + s * f y`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `v + s % (y - v):real^N = (&1 - s) % v + s % y` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[];
      USE_THEN "aff" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1 ==> ((v:real^N) + s % (y - v) IN L <=> s = &1)`
  (LABEL_TAC "L") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "rad" (MP_TAC o SPECL [`y:real^N`; `v + s % (y - v):real^N`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s:real` THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(v:real^N) + s % (y - v) = y <=> (&1 - s) % (y - v) = vec 0`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_CASES_TAC `y:real^N = v` THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(v:real^N) + &1 % (y - v) = y`]];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
   [USE_THEN "pt" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_INTER] THEN
    USE_THEN "L" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "Y" (MP_TAC o C MATCH_MP
      (ASSUME `(v:real^N) + s % (y - v) IN m`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "Z" (MP_TAC o C MATCH_MP
      (ASSUME `(v:real^N) + s % (y - v) IN m`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "r1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "pt" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Y" (MP_TAC o C MATCH_MP
      (ASSUME `(v:real^N) + s % (y - v) IN m`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "r2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FTA_SEG_RAY = prove
 (`!(v:real^N) y r z.
        z IN segment[v,v + r % (y - v)] <=>
        ?u. &0 <= u /\ u <= &1 /\ z = v + (u * r) % (y - v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(&1 - u) % v + u % (v + r % (y - v)):real^N = v + (u * r) % (y - v)`]);;

(* A set Y in a cone over L whose trace on each ray is cut out by a level   *)
(* function as above is the cone over X = Z UNION (Y INTER L), and X meets  *)
(* each ray exactly once.                                                     *)

let MOI_FTA_CONE_FROM_RAYS = prove
 (`!(v:real^N) L Y Z.
        ~(v IN L) /\ ~(L = {}) /\
        (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
        Y SUBSET UNIONS {segment[v,y] | y | y IN L} /\
        Z SUBSET UNIONS {segment[v,y] | y | y IN L} /\
        (!y. y IN L
             ==> ?m f. convex m /\ v IN m /\ y IN m /\
                       (!x y u. f((&1 - u) % x + u % y) =
                                (&1 - u) * f x + u * f y) /\
                       f v = &1 /\
                       (!x. x IN m ==> (x IN Y <=> &1 / &2 <= f x)) /\
                       (!x. x IN m ==> (x IN Z <=> f x = &1 / &2)))
        ==> (!y. y IN L
                 ==> ?!r. &0 < r /\ r <= &1 /\
                          v + r % (y - v) IN Z UNION (Y INTER L)) /\
            ~(v IN Z UNION (Y INTER L)) /\
            (!x y. x IN Z UNION (Y INTER L) /\ y IN Z UNION (Y INTER L) /\
                   y IN segment[v,x] ==> y = x) /\
            Y = UNIONS {segment[v,x] | x IN Z UNION (Y INTER L)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rad") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "data")))))) THEN
  SUBGOAL_THEN
   `!y. y IN L
        ==> ?r. &0 < r /\ r <= &1 /\
                (!s. &0 < s /\ s <= &1
                     ==> ((v:real^N) + s % (y - v) IN Z UNION (Y INTER L) <=>
                          s = r)) /\
                (!s. &0 <= s /\ s <= &1 ==> (v + s % (y - v) IN Y <=> s <= r))`
  (LABEL_TAC "ray") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_FTA_RAY_DATA THEN
    MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `f:real^N->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN UNIONS {segment[v,y] | y | y IN L}
        ==> ?y s. y IN L /\ &0 <= s /\ s <= &1 /\ z = (v:real^N) + s % (y - v)`
  (LABEL_TAC "cone") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `s:real`] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN Z UNION (Y INTER L))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION; IN_INTER] THEN
    SUBGOAL_THEN `?y0:real^N. y0 IN L` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y0:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "Zm"))))))))) THEN
    USE_THEN "Zm" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN m`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Z UNION (Y INTER L)
        ==> ?y r. y IN L /\ &0 < r /\ r <= &1 /\ x = (v:real^N) + r % (y - v) /\
                  (!s. &0 < s /\ s <= &1
                       ==> (v + s % (y - v) IN Z UNION (Y INTER L) <=> s = r)) /\
                  (!s. &0 <= s /\ s <= &1 ==> (v + s % (y - v) IN Y <=> s <= r))`
  (LABEL_TAC "xpar") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS {segment[v,y] | y | y IN L}` MP_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN Z UNION (Y INTER L)` THEN
      UNDISCH_TAC `(Y:real^N->bool) SUBSET UNIONS {segment[v,y] | y | y IN L}` THEN
      UNDISCH_TAC `(Z:real^N->bool) SUBSET UNIONS {segment[v,y] | y | y IN L}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> USE_THEN "cone" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ray" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "r1")
        (LABEL_TAC "r2"))))) THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LZERO; VECTOR_ADD_RID]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "r1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "ray" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "r1")
        (LABEL_TAC "r2"))))) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `r:real` THEN
    USE_THEN "r1" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "r1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^N`] THEN STRIP_TAC THEN
    USE_THEN "xpar" (MP_TAC o C MATCH_MP
      (ASSUME `(x:real^N) IN Z UNION (Y INTER L)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "r2")))))))) THEN
    UNDISCH_TAC `(z:real^N) IN segment[v,v + r % (y - v)]` THEN
    REWRITE_TAC[MOI_FTA_SEG_RAY] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
    SUBGOAL_THEN `&0 < u * r` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LZERO; VECTOR_ADD_RID]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `u * r = r` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "r1" (MP_TAC o SPEC `u * r`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`u:real`; `&1`; `r:real`] REAL_LE_RMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN UNIONS {segment[v,y] | y | y IN L}` MP_TAC
      THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> USE_THEN "cone" (MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
        STRIP_ASSUME_TAC)) THEN
      USE_THEN "ray" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "r1")
          (LABEL_TAC "r2"))))) THEN
      SUBGOAL_THEN `s <= r` ASSUME_TAC THENL
       [USE_THEN "r2" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[v:real^N,v + r % (y - v)]` THEN CONJ_TAC THENL
       [EXISTS_TAC `(v:real^N) + r % (y - v)` THEN REWRITE_TAC[] THEN
        USE_THEN "r1" (MP_TAC o SPEC `r:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[];
        ASM_REWRITE_TAC[MOI_FTA_SEG_RAY] THEN EXISTS_TAC `s / r` THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                     REAL_MUL_LID; REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "xpar" (MP_TAC o C MATCH_MP
        (ASSUME `(x:real^N) IN Z UNION (Y INTER L)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "r2")))))))) THEN
      UNDISCH_TAC `(z:real^N) IN segment[v,v + r % (y - v)]` THEN
      REWRITE_TAC[MOI_FTA_SEG_RAY] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
      USE_THEN "r2" (MP_TAC o SPEC `u * r`) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MP_TAC(SPECL [`u:real`; `&1`; `r:real`] REAL_LE_RMUL) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
        DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`u:real`; `&1`; `r:real`] REAL_LE_RMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]]);;


(* ========================================================================= *)
(* The dual cell C_v is a PL 3-cell with boundary                           *)
(* (C_v INTER Bd N) UNION (C_v INTER link of v in t1), via the level        *)
(* retriangulation: its image is the cone from v over a PL 2-sphere.        *)
(* ========================================================================= *)

let MOI_FTA_CHAIN_UNIONS_POLY = prove
 (`!(S:(real^N->bool)->bool) P.
        FINITE S
        ==> pl_polyhedron (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                                   moi_bar_chain S g /\ P g})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{convex hull (IMAGE simplex_barycentre g) | g |
               moi_bar_chain S g /\ P g}:(real^N->bool)->bool` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{g:(real^N->bool)->bool | g SUBSET S}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_bar_chain] THEN MESON_TAC[SUBSET];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[polytope] THEN
    EXISTS_TAC `IMAGE simplex_barycentre (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_MESON_TAC[moi_bar_chain]]);;

let MOI_FTA_LINK_POLY = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> simplicial_link c v SUBSET moi_fta_cstar c v /\
            FINITE (simplicial_link c v) /\
            pl_polyhedron (UNIONS (simplicial_link c v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_link c (v:real^N) SUBSET moi_fta_cstar c v`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; simplicial_link; moi_fta_cstar; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_CSTAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (simplicial_link c (v:real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `simplicial_link c (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_POLYTOPE]);;

let MOI_FTA_PLH_IMAGE = prove
 (`!(s:real^N->bool) h k P.
        pl_homeomorphism (s,s) (h,k) /\ P SUBSET s /\ pl_polyhedron P
        ==> pl_polyhedron (IMAGE h P) /\ IMAGE k (IMAGE h P) = P /\
            pl_homeomorphism (IMAGE h P,P) (k,h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s:real^N->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `P:real^N->bool`] MOI_FMB_PLH_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTA_CELL_PLH = prove
 (`!n d j (f:real^N->real^N) g.
        pl_cell_with_boundary n d j /\ pl_homeomorphism (d,IMAGE f d) (f,g)
        ==> pl_cell_with_boundary n (IMAGE f d) (IMAGE f j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
    (X_CHOOSE_THEN `p:real^N->real^N` (X_CHOOSE_THEN `q:real^N->real^N`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`;
    `(f:real^N->real^N) o (p:real^N->real^N)`;
    `(q:real^N->real^N) o (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTA_IMAGE_INTER_INJ = prove
 (`!(h:real^N->real^N) k s A B.
        (!x. x IN s ==> k (h x) = x) /\ A SUBSET s /\ B SUBSET s
        ==> IMAGE h (A INTER B) = IMAGE h A INTER IMAGE h B`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

(* Abstract form: a set C in the closed star of v whose image under a PL   *)
(* self-homeomorphism of the star (fixing its simplices) is cut out by      *)
(* level functions as in MOI_FTA_THETA is a PL 3-cell.                       *)

let MOI_FTA_CELL3_ABS = prove
 (`!c (v:real^N) h k C B.
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v)) /\
        pl_homeomorphism (UNIONS {s | s IN c /\ v IN s},
                          UNIONS {s | s IN c /\ v IN s}) (h,k) /\
        (!s. s IN moi_fta_cstar c v ==> IMAGE h s = s) /\
        C SUBSET UNIONS {s | s IN c /\ v IN s} /\ B SUBSET C /\
        pl_polyhedron C /\ pl_polyhedron B /\
        (!m. m IN c /\ v IN m
             ==> ?f. (!x y u. f((&1 - u) % x + u % y) =
                              (&1 - u) * f x + u * f y) /\
                     f v = &1 /\
                     (!x. x IN IMAGE h C /\ x IN m <=> x IN m /\ &1 / &2 <= f x) /\
                     (!x. x IN IMAGE h B /\ x IN m <=> x IN m /\ f x = &1 / &2))
        ==> pl_cell_with_boundary 3 C
              (B UNION (C INTER UNIONS (simplicial_link c v)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "fix") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lev")))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rad")) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` (ASSUME_TAC o el 3 o CONJUNCTS)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_LINK_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (simplicial_link c (v:real^N)) SUBSET
                UNIONS {s | s IN c /\ v IN s}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN UNIONS {s | s IN c /\ v IN s} ==> (k:real^N->real^N) (h x) = x) /\
    IMAGE (h:real^N->real^N) (UNIONS {s | s IN c /\ v IN s}) =
    UNIONS {s | s IN c /\ (v:real^N) IN s}`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (UNIONS (simplicial_link c v)) =
                UNIONS (simplicial_link c (v:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN X_GEN_TAC `r:real^N->bool` THEN
    DISCH_TAC THEN USE_THEN "fix" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `St = UNIONS {s | s IN c /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link c (v:real^N))` THEN
  MP_TAC(ISPECL [`St:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                 `C:real^N->bool`] MOI_FTA_PLH_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`St:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                 `B UNION (C INTER L):real^N->bool`] MOI_FTA_PLH_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (B UNION (C INTER L)) =
    IMAGE h B UNION (IMAGE h C INTER L)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `St:real^N->bool`;
                   `C:real^N->bool`; `L:real^N->bool`] MOI_FTA_IMAGE_INTER_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `IMAGE (h:real^N->real^N) C`;
                 `IMAGE (h:real^N->real^N) B`] MOI_FTA_CONE_FROM_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      X_GEN_TAC `y:real^N` THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
      USE_THEN "lev" (MP_TAC o SPEC `m:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `f:real^N->real`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `X = IMAGE (h:real^N->real^N) B UNION (IMAGE h C INTER L)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `X:real^N->bool`]
    MOI_FTA_RSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pl_polyhedron (IMAGE (h:real^N->real^N) (B UNION (C INTER L)))` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "X" THEN ASM SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`2`; `X:real^N->bool`; `v:real^N`] MOI_FTA_CONE_CELL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `IMAGE (h:real^N->real^N) C`; `X:real^N->bool`;
                 `k:real^N->real^N`; `h:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) X = B UNION (C INTER L)`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `IMAGE (k:real^N->real^N) (IMAGE h (B UNION (C INTER L))) =
               B UNION (C INTER L)` THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The splitting disk D = C_u INTER C_v is a PL 2-cell with                *)
(* boundary D INTER Bd N.  In the level coordinates of the closed star of  *)
(* u it is the half of the closed star of p = midpoint(u,v) in the link of *)
(* u in t1 next to p, a cone from p over a homothetic copy of the link of   *)
(* p in that link (a PL 1-sphere by MOI_FTA_S2LINK).                        *)
(* ========================================================================= *)

(* A copy of MOI_SCD_PL_SPHERE_NONEMPTY (pc_moi_sch3_stmt.ml), which this    *)
(* file does not load.                                                       *)

let MOI_FTA_PL_SPHERE_NONEMPTY = prove
 (`!n s:real^N->bool. pl_sphere n s ==> ~(s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    REWRITE_RULE[homeomorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded(k:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `&(n + 1) simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN
    MP_TAC(SPEC `n + 1` INT_POS) THEN INT_ARITH_TAC;
    UNDISCH_TAC `&(n + 1) simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    REWRITE_TAC[AFF_DIM_SING; INT_OF_NUM_EQ] THEN ARITH_TAC]);;

let MOI_FTA_BARY_VERTEX = prove
 (`!t s:real^N->bool.
        s IN t /\ ~(s = {})
        ==> {simplex_barycentre s} IN barycentric_subdivision t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  EXISTS_TAC `{s:real^N->bool}` THEN
  ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; MOI_FTA_HULL_SING_CHAIN]);;

let MOI_FTA_IN_CONE = prove
 (`!(v:real^N) L x.
        x IN UNIONS {segment[v,y] | y | y IN L}
        ==> ?y s. y IN L /\ &0 <= s /\ s <= &1 /\ x = v + s % (y - v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* The midpoint p of a graph edge [u,v] is a vertex of the link of u in t1. *)

let MOI_FTA_MID_IN_LINK = prove
 (`!(t:(real^N->bool)->bool) l u v.
        graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l
        ==> {midpoint(u,v)} IN barycentric_subdivision t /\
            {midpoint(u,v)} IN simplicial_link (barycentric_subdivision t) u /\
            midpoint(u,v) IN UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[u:real^N,v] IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{midpoint(u:real^N,v)} IN barycentric_subdivision t`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
    MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN
    ASM_MESON_TAC[ENDS_IN_SEGMENT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[u:real^N,v]` THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
  ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN
  EXISTS_TAC `segment[u:real^N,midpoint(u,v)]` THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  EXISTS_TAC `{{u:real^N},segment[u,v]}` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a:real^N->bool,b} = a INSERT {b}`] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; IN_SING] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT; NOT_IN_EMPTY];
      REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT]];
    REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL]]);;

(* Level data along the rays from p to the link of p in the link of u.     *)

let MOI_FTA_DL_DATA = prove
 (`!(t:(real^N->bool)->bool) l u v (h:real^N->real^N) y.
     graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l /\
     (!m. m IN barycentric_subdivision t /\ u IN m
          ==> ?f. (!x y w. f((&1 - w) % x + w % y) = (&1 - w) * f x + w * f y) /\
                  (!a. a extreme_point_of m
                       ==> f a = if a IN UNIONS l then &1 else &0) /\
                  f u = &1 /\
                  (!x. x IN IMAGE h (derived_dual_cell t l u) /\ x IN m <=>
                       x IN m /\ &1 / &2 <= f x) /\
                  (!x. x IN IMAGE h (derived_dual_cell t l u INTER
                                     derived_frontier t l) /\ x IN m <=>
                       x IN m /\ f x = &1 / &2)) /\
     y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision t) u)
                                  (midpoint(u,v)))
     ==> ?q f. q IN simplicial_link (barycentric_subdivision t) u /\
               midpoint(u,v) IN q /\ y IN q /\
               (!x y w. f((&1 - w) % x + w % y) = (&1 - w) * f x + w * f y) /\
               f (midpoint(u,v)) = &1 /\ f y = &0 /\
               (!x. x IN q ==> (x IN IMAGE h (derived_dual_cell t l u) <=>
                                &1 / &2 <= f x)) /\
               (!x. x IN q ==> (x IN IMAGE h (derived_dual_cell t l u INTER
                                              derived_frontier t l) <=>
                                f x = &1 / &2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lev") MP_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_MID_IN_LINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[IN_UNIONS; IN_ELIM_THM] o
    ONCE_REWRITE_RULE[simplicial_link]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[simplicial_link; IN_ELIM_THM] o check
   (fun th -> concl th =
      `(q:real^N->bool) IN simplicial_link (barycentric_subdivision t) u`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) THEN
  USE_THEN "lev" (MP_TAC o SPEC `m:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ext") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Y") (LABEL_TAC "Z")))))) THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET m /\ (r:real^N->bool) SUBSET q /\
                r face_of m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; FACE_OF_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(u:real^N,v) IN m` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`q:real^N->bool`; `f:real^N->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    USE_THEN "ext" (MP_TAC o SPEC `midpoint(u:real^N,v)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `!a:real^N. a extreme_point_of r ==> f a = &0` ASSUME_TAC THENL
     [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^N) extreme_point_of m /\ a IN r` STRIP_ASSUME_TAC
      THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`r:real^N->bool`; `m:real^N->bool`; `a:real^N`]
            EXTREME_POINT_OF_FACE) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[extreme_point_of];
          ASM_MESON_TAC[extreme_point_of]];
        ALL_TAC] THEN
      USE_THEN "ext" (MP_TAC o C MATCH_MP
        (ASSUME `(a:real^N) extreme_point_of m`)) THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `~((a:real^N) IN UNIONS l)` (fun th -> REWRITE_TAC[th]) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `~(v:real^N = u)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `u:real^N`; `v:real^N`; `m:real^N->bool`; `a:real^N`]
        MOI_FTA_MID_UNIQUE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(r:real^N->bool) SUBSET q` THEN
        UNDISCH_TAC `~((u:real^N) IN q)` THEN
        UNDISCH_TAC `(a:real^N) IN r` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        UNDISCH_TAC `~(midpoint(u:real^N,v) IN r)` THEN
        UNDISCH_TAC `(a:real^N) IN r` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real`; `&0`; `{x:real^N | x extreme_point_of r}`]
      MOI_FTA_LEVEL_HULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `r:real^N->bool` KREIN_MILMAN_MINKOWSKI) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision t` MP_TAC THENL
       [UNDISCH_TAC `(r:real^N->bool) IN
                     simplicial_link (barycentric_subdivision t) u` THEN
        REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
        DISCH_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                     `r:real^N->bool`] MOI_FDN_LF_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "Y" (MP_TAC o SPEC `x:real^N`) THEN
    SUBGOAL_THEN `(x:real^N) IN m` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "Z" (MP_TAC o SPEC `x:real^N`) THEN
    SUBGOAL_THEN `(x:real^N) IN m` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[SUBSET]]);;

let MOI_FTA_MIDPOINT_INJ = prove
 (`!u v w:real^N. midpoint(u,w) = midpoint(u,v) <=> w = v`,
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

(* The level image of the splitting disk.                                    *)

let MOI_FTA_DISK_THETA = prove
 (`!(t:(real^N->bool)->bool) l u v (h:real^N->real^N) k.
     graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l /\
     (!x. x IN UNIONS {s | s IN barycentric_subdivision t /\ u IN s}
          ==> k (h x) = x) /\
     (!s. s IN moi_fta_cstar (barycentric_subdivision t) u ==> IMAGE h s = s)
     ==> IMAGE h (derived_dual_cell t l u INTER derived_dual_cell t l v) =
         IMAGE h (derived_dual_cell t l u) INTER
         UNIONS {q | q IN simplicial_link (barycentric_subdivision t) u /\
                     midpoint(u,v) IN q}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "fix"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `u:real^N`]
    MOI_FTA_LINK_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^N = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`; `u:real^N`; `x:real^N`] MOI_FTA_DISK_IN_DB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fix" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[simplicial_link; IN_ELIM_THM] o check
   (fun th -> concl th =
      `(q:real^N->bool) IN simplicial_link (barycentric_subdivision t) u`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET m` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN q` ASSUME_TAC THENL
   [USE_THEN "fix" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) x IN IMAGE h q` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^N = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(k:real^N->real^N) (h x) = x /\ k (h x') = x'`
     (fun th -> ASM_MESON_TAC[th]) THEN
    CONJ_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l u` THEN
      REWRITE_TAC[derived_dual_cell; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
        `u:real^N`; `x:real^N`] MOI_FTA_STAR_INTER_LINK) THEN
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `u:real^N`; `q:real^N->bool`; `x:real^N`] MOI_FTA_LINK_PART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `w:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `u:real^N`; `w:real^N`] MOI_FTA_MID_IN_LINK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `u:real^N`; `v:real^N`; `m:real^N->bool`; `midpoint(u:real^N,w)`]
    MOI_FTA_MID_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MIDPOINT_EQ_ENDPOINT; MOI_FTA_MIDPOINT_INJ] THEN
  ASM_MESON_TAC[]);;

let MOI_FTA_DISK_POLY = prove
 (`!(t:(real^N->bool)->bool) l u v.
     graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l
     ==> pl_polyhedron (derived_dual_cell t l u INTER derived_dual_cell t l v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_DISK_CHAINS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!g. moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gw t u v g <=>
        moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) u) g /\
        moi_fta_gw t (u:real^N) v g`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC MOI_FTA_GW_CSTAR THEN EXISTS_TAC `v:real^N` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) u)
                     (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET_TRANS]];
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[]]);;

(* Abstract 2-cell recognition: the level image of D is cut out on the     *)
(* closed star of the vertex p of a complex K (with PL 1-sphere link) by   *)
(* level functions equal to 1 at p and 0 on the link of p.                  *)

let MOI_FTA_CELL2_ABS = prove
 (`!K (p:real^N) St h k D E.
        lf_simplicial_complex K /\ {p} IN K /\
        pl_sphere 1 (UNIONS (simplicial_link K p)) /\
        pl_homeomorphism (St,St) (h,k) /\ D SUBSET St /\ E SUBSET D /\
        pl_polyhedron D /\
        IMAGE h D SUBSET UNIONS {q | q IN K /\ p IN q} /\
        (!y. y IN UNIONS (simplicial_link K p)
             ==> ?q f. q IN K /\ p IN q /\ y IN q /\
                       (!x y w. f((&1 - w) % x + w % y) =
                                (&1 - w) * f x + w * f y) /\
                       f p = &1 /\ f y = &0 /\
                       (!x. x IN q ==> (x IN IMAGE h D <=> &1 / &2 <= f x)) /\
                       (!x. x IN q ==> (x IN IMAGE h E <=> f x = &1 / &2)))
        ==> pl_cell_with_boundary 2 D E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "data"))))))))) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rad")) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N`] MOI_FTA_LINK_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FTA_PL_SPHERE_NONEMPTY) THEN
  SUBGOAL_THEN
   `(!x. x IN St ==> (k:real^N->real^N) (h x) = x)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  ABBREV_TAC `L = UNIONS (simplicial_link K (p:real^N))` THEN
  SUBGOAL_THEN `!y. y IN L ==> (p:real^N) + inv(&2) % (y - p) IN IMAGE (h:real^N->real^N) E`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Z")))))))))) THEN
    SUBGOAL_THEN `(p:real^N) + inv(&2) % (y - p) = (&1 - inv(&2)) % p + inv(&2) % y`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - inv(&2)) % p + inv(&2) % y IN (q:real^N->bool)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    USE_THEN "Z" (MP_TAC o C MATCH_MP (ASSUME
      `(&1 - inv(&2)) % p + inv(&2) % y IN (q:real^N->bool)`)) THEN
    DISCH_THEN SUBST1_TAC THEN USE_THEN "aff" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS {q | q IN K /\ (p:real^N) IN q}
        ==> ?y s. y IN L /\ &0 <= s /\ s <= &1 /\ x = p + s % (y - p) /\
                  (x IN IMAGE (h:real^N->real^N) D <=> &1 / &2 <= &1 - s) /\
                  (x IN IMAGE h E <=> &1 - s = &1 / &2)`
  (LABEL_TAC "par") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^N) IN UNIONS {q | q IN K /\ p IN q}` THEN
      REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_IN_CONE) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `s:real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Y") (LABEL_TAC "Z")))))))))) THEN
    SUBGOAL_THEN `(p:real^N) + s % (y - p) = (&1 - s) % p + s % y`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - s) % p + s % y IN (q:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    USE_THEN "Y" (MP_TAC o C MATCH_MP (ASSUME
      `(&1 - s) % p + s % y IN (q:real^N->bool)`)) THEN
    USE_THEN "Z" (MP_TAC o C MATCH_MP (ASSUME
      `(&1 - s) % p + s % y IN (q:real^N->bool)`)) THEN
    USE_THEN "aff" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) E = IMAGE (\y. p + inv(&2) % (y - p)) L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      USE_THEN "par" (MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s = inv(&2)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE (h:real^N->real^N) E <=> &1 - s = &1 / &2` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) D INTER L = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term ((=) `&1 / &2 <= (f:real^N->real) x`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^N`; `L:real^N->bool`; `IMAGE (h:real^N->real^N) D`;
                 `IMAGE (h:real^N->real^N) E`] MOI_FTA_CONE_FROM_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM SET_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      USE_THEN "data" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN L`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`q:real^N->bool`; `f:real^N->real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPECL [`L:real^N->bool`; `p:real^N`; `inv(&2)`]
    MOI_CMB_SCALE_PL_HOMEOMORPHISM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (h:real^N->real^N) E)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`;
      `\y:real^N. p + inv(&2) % (y - p)`;
      `\z:real^N. p + inv(inv(&2)) % (z - p)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `IMAGE (h:real^N->real^N) E`; `p:real^N`]
    MOI_FTA_CONE_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`St:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                 `D:real^N->bool`] MOI_FTA_PLH_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `IMAGE (h:real^N->real^N) D`; `IMAGE (h:real^N->real^N) E`;
                 `k:real^N->real^N`; `h:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) (IMAGE h E) = E`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The cell clauses and the theorem GRAPH_TUBE_DUAL_CELLS.                  *)
(* ========================================================================= *)

let MOI_FTA_CELL3 = prove
 (`!(t:(real^N->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l
     ==> pl_cell_with_boundary 3 (derived_dual_cell t l v)
           ((derived_dual_cell t l v INTER derived_frontier t l) UNION
            UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                    w | ~(w = v) /\ segment[v,w] IN l})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_FTA_WALLS_EQ th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_SETUP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTA_THETA) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "lev"))))) THEN
  MATCH_MP_TAC MOI_FTA_CELL3_ABS THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[derived_dual_cell; INTER_SUBSET];
    REWRITE_TAC[INTER_SUBSET];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CELL_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CELL_FRONTIER_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "lev" (MP_TAC o SPEC `m:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[]]);;

let MOI_FTA_CELL2 = prove
 (`!(t:(real^N->bool)->bool) l u v.
     graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l
     ==> pl_cell_with_boundary 2
           (derived_dual_cell t l u INTER derived_dual_cell t l v)
           (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
            derived_frontier t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`; `v:real^N`] MOI_FTA_MID_IN_LINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `u:real^N`] MOI_FTA_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fix")
      (LABEL_TAC "lev"))))) THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s}
        ==> (k:real^N->real^N) (h x) = x`
  (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `u:real^N`; `v:real^N`; `h:real^N->real^N`; `k:real^N->real^N`]
    MOI_FTA_DISK_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N)
      (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
       derived_frontier t l) =
    IMAGE h (derived_dual_cell t l u INTER derived_dual_cell t l v) INTER
    IMAGE h (derived_dual_cell t l u INTER derived_frontier t l)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `derived_dual_cell t l u INTER derived_dual_cell t l v INTER
      derived_frontier t l =
      (derived_dual_cell t l u INTER derived_dual_cell t l v) INTER
      (derived_dual_cell t l u INTER derived_frontier t (l:(real^N->bool)->bool))`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
    EXISTS_TAC `k:real^N->real^N` THEN
    EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[derived_dual_cell] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTA_CELL2_ABS THEN
  MAP_EVERY EXISTS_TAC
   [`simplicial_link (barycentric_subdivision t) (u:real^N)`;
    `midpoint(u:real^N,v)`;
    `UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s}`;
    `h:real^N->real^N`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `u:real^N`]
      MOI_FTA_LINK_LF) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[derived_dual_cell] THEN SET_TAC[];
    SET_TAC[];
    MATCH_MP_TAC MOI_FTA_DISK_POLY THEN ASM_REWRITE_TAC[];
    SET_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `u:real^N`; `v:real^N`; `h:real^N->real^N`; `y:real^N`]
      MOI_FTA_DL_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Y") (LABEL_TAC "Z")))))))))) THEN
    MAP_EVERY EXISTS_TAC [`q:real^N->bool`; `f:real^N->real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THENL
     [USE_THEN "Y" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN q`)) THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS {q | q IN simplicial_link
                      (barycentric_subdivision t) u /\ midpoint(u,v) IN q}`
       (fun th -> REWRITE_TAC[IN_INTER; th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `q:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "Y" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN q`)) THEN
      USE_THEN "Z" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN q`)) THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS {q | q IN simplicial_link
                      (barycentric_subdivision t) u /\ midpoint(u,v) IN q}`
       (fun th -> REWRITE_TAC[IN_INTER; th]) THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `q:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]]]);;

let GRAPH_TUBE_DUAL_CELLS = prove
 (`!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v} IN l} /\
         (!v. {v} IN l
              ==> derived_dual_cell t l v SUBSET UNIONS {s | s IN t /\ v IN s} /\
                  {w | {w} IN t /\ w IN derived_dual_cell t l v} = {v} /\
                  derived_dual_cell t l v INTER UNIONS l =
                  v INSERT UNIONS {segment[v,midpoint(v,w)] | w |
                                   ~(w = v) /\ segment[v,w] IN l} /\
                  pl_cell_with_boundary 3 (derived_dual_cell t l v)
                    ((derived_dual_cell t l v INTER derived_frontier t l) UNION
                     UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                             w | ~(w = v) /\ segment[v,w] IN l})) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> pl_cell_with_boundary 2
                      (derived_dual_cell t l u INTER derived_dual_cell t l v)
                      (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                       derived_frontier t l) /\
                    derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                    UNIONS l = {midpoint(u,v)}) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FTA_GRAPH_TUBE_FROM_CELLS THEN
  ASM_SIMP_TAC[MOI_FTA_CELL3; MOI_FTA_CELL2]);;

