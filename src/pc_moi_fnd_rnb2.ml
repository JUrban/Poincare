(* ========================================================================= *)
(* pc_moi_fnd_rnb2: the derived neighbourhood of a PL ball of dimension at  *)
(* most 2 or of a tree, all of whose vertices have 2-sphere links, is a PL  *)
(* 3-cell bounded by its frontier (MOI_FND_DERIVED_NBHD_BALL_2 of           *)
(* pc_moi_fnd_stmt4.ml, Moise GTM 47 p.169, 23.11-23.12):                   *)
(*   DERIVED_NBHD_BALL_2 : |- MOI_FND_DERIVED_NBHD_BALL_2                    *)
(* (2D invariance for the disk case from pc_moi_s28_trib, SURF_INVARIANT).  *)
(* Route: collapsibility.  The neighbourhood is the union of the closed     *)
(* stars in the second derived of the barycentres of the simplices of l     *)
(* (pc_moi_fnd_rnsc for one simplex); an elementary collapse (an edge with  *)
(* a free vertex, or a triangle with a free edge) changes it by two stars   *)
(* attached along PL 2-cells (dual 2-cells and fans of them), so it stays a *)
(* 3-cell.  Trees collapse to a vertex by removing leaves (handshake and    *)
(* chi = 1); a triangulated 2-disk collapses because every subcomplex with *)
(* a triangle has a free edge (dual connectivity of the disk and a boundary *)
(* edge).                                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_rnsc.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_stmt4.ml";;
needs "src/pc_moi_s28_trib.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Closed stars over a subcomplex l of t whose vertices have                *)
(* 2-sphere links: each star is a PL 3-cell, the derived neighbourhood is  *)
(* their union, and the gluing step of pc_moi_fnd_rnsc for index sets of   *)
(* simplices of l.  The attaching set of a new star is the union of the    *)
(* dual 2-cells of the edges joining it to the comparable old simplices.   *)
(* ========================================================================= *)

let MOI_FRB_SUB_FACE = prove
 (`!(t:(real^N->bool)->bool) p q.
     lf_simplicial_complex t /\ p IN t /\ q IN t /\ p SUBSET q ==> p face_of q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p = (p:real^N->bool) INTER q` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]]);;

let MOI_FRB_LINK_OK = prove
 (`!(t:(real^N->bool)->bool) l p.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\ p IN l
     ==> p IN t /\
         (!w. {w} IN t /\ w IN p ==> pl_sphere 2 (UNIONS (simplicial_link t w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `{w:real^N} face_of p` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ASM_MESON_TAC[simplicial_subcomplex]]);;

let MOI_FRB_STAR_CELL = prove
 (`!(t:(real^N->bool)->bool) l p.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     p IN l /\ ~(p = {})
     ==> {simplex_barycentre p} IN barycentric_subdivision t /\
         pl_cell_with_boundary 3
           (moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p})
           (moi_fcl_ldual (barycentric_subdivision t) {simplex_barycentre p})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `p:real^N->bool`]
    MOI_FRB_LINK_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRS_STAR_CELL THEN EXISTS_TAC `p:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
  ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]);;

let MOI_FRB_EDGE_CELL = prove
 (`!(t:(real^N->bool)->bool) l p1 p2.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     p1 IN l /\ p2 IN l /\ ~(p1 = {}) /\ p1 SUBSET p2 /\ ~(p1 = p2)
     ==> pl_cell_with_boundary 2
           (moi_fcl_dual (barycentric_subdivision t)
              (segment[simplex_barycentre p1,simplex_barycentre p2]))
           (moi_fcl_ldual (barycentric_subdivision t)
              (segment[simplex_barycentre p1,simplex_barycentre p2]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `p2:real^N->bool`]
    MOI_FRB_LINK_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p1:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRS_EDGE_CELL THEN EXISTS_TAC `p2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]);;

let MOI_FRB_STAR_MINT_T = prove
 (`!(t:(real^N->bool)->bool) l p x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     p IN l /\ ~(p = {}) /\
     x IN moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p}
     ==> moi_fmb_mint (UNIONS t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `p:real^N->bool`]
    MOI_FRB_LINK_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRS_STAR_MINT_T THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->bool`; `p:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
  ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]);;

(* The derived neighbourhood of a subcomplex is the union of the closed     *)
(* stars of the barycentres of its nonempty simplices (generalising         *)
(* MOI_FRS_NBHD_STARS from the faces of one simplex).                       *)

let MOI_FRB_NBHD_STARS = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> derived_nbhd t l =
         UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p IN l /\ ~(p = {})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `(l:(real^N->bool)->bool)`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FTA_BS_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N->bool. p IN l /\ ~(p = {})
                ==> {simplex_barycentre p} IN barycentric_subdivision t /\
                    {simplex_barycentre p} IN
                    barycentric_subdivision (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET t` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; MOI_FCL_IN_DUAL] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `INTERS g IN barycentric_subdivision (l:(real^N->bool)->bool)`
    MP_TAC THENL
     [SUBGOAL_THEN `INTERS g = (INTERS g) INTER (r:real^N->bool)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(INTERS g INTER r) face_of (r:real^N->bool)` ASSUME_TAC THENL
       [MP_TAC(ASSUME `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`) THEN
        REWRITE_TAC[moi_bar_complex] THEN
        DISCH_THEN(MP_TAC o SPECL [`INTERS g:real^N->bool`; `r:real^N->bool`] o
          CONJUNCT2 o CONJUNCT2) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        MP_TAC(ASSUME `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)`) THEN
        MP_TAC(ASSUME `simplicial_subcomplex
          (barycentric_subdivision (l:(real^N->bool)->bool))
          (barycentric_subdivision t)`) THEN
        REWRITE_TAC[moi_bar_chain; simplicial_subcomplex] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ASSUME `simplicial_subcomplex
        (barycentric_subdivision (l:(real^N->bool)->bool))
        (barycentric_subdivision t)`) THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[barycentric_subdivision; IN_ELIM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(f0:(real^N->bool)->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `INTERS g IN (g:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN
      MP_TAC(ASSUME `moi_bar_chain (barycentric_subdivision t)
                       (g:(real^N->bool)->bool)`) THEN
      SIMP_TAC[moi_bar_chain];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:real^N->bool` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `p:real^N->bool` THEN
    SUBGOAL_THEN `(p:real^N->bool) IN l /\ ~(p = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `f0 SUBSET (l:(real^N->bool)->bool)` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `simplex_barycentre (p:real^N->bool) IN INTERS g` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `{simplex_barycentre (p:real^N->bool)} INSERT g` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_SIMP_TAC[NOT_INSERT_EMPTY] THEN
      X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
      REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[];
      REWRITE_TAC[NOT_INSERT_EMPTY];
      REWRITE_TAC[FORALL_IN_INSERT; SUBSET_REFL] THEN
      REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[];
      UNDISCH_TAC `x IN convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `{simplex_barycentre (p:real^N->bool)} INSERT g` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_SIMP_TAC[NOT_INSERT_EMPTY];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `{simplex_barycentre (p:real^N->bool)}` THEN
      ASM_SIMP_TAC[IN_INSERT];
      UNDISCH_TAC `x IN convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]]);;

(* Gluing steps indexed by simplices of l.                                 *)

let MOI_FRB_FACE_STEP = prove
 (`!(t:(real^N->bool)->bool) l P q A jA.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     FINITE P /\ (!p. p IN P ==> p IN l /\ ~(p = {})) /\
     q IN l /\ ~(q = {}) /\ ~(q IN P) /\
     pl_cell_with_boundary 3
       (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                p | p IN P})
       ((subtopology euclidean (UNIONS t)) frontier_of
        (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p IN P})) /\
     UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
             p | p IN P} INTER
     moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre q} = A /\
     pl_cell_with_boundary 2 A jA
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN q INSERT P})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN q INSERT P}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p:real^N->bool. p IN l ==> p IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MOI_FRS_FACE_UNIONS; IMAGE_CLAUSES] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `IMAGE simplex_barycentre (P:(real^N->bool)->bool)`;
                 `simplex_barycentre (q:real^N->bool)`;
                 `A:real^N->bool`; `jA:real^N->bool`] MOI_FRS_GLUE_STEP) THEN
  ASM_REWRITE_TAC[MOI_FRS_FACE_UNIONS] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool`
      STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`; `p:real^N->bool`]
      MOI_FTA_BARY_INJ) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_INSERT; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_FRB_STAR_MINT_T THEN
      MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `q:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_FRB_STAR_MINT_T THEN
      MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `p:real^N->bool`] THEN
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRB_STAR_CELL) THEN
    ASM_SIMP_TAC[]]);;

let MOI_FRB_FACE_BASE = prove
 (`!(t:(real^N->bool)->bool) l q.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     q IN l /\ ~(q = {})
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN {q}})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN {q}}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `q:real^N->bool`]
    MOI_FRB_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `simplex_barycentre (q:real^N->bool)`] MOI_FRS_GLUE_BASE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRB_STAR_MINT_T THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES]);;

(* The attaching set of a new star: the dual 2-cells of the edges of the   *)
(* first derived joining its barycentre to the comparable old ones.         *)

let MOI_FRB_ATTACH = prove
 (`!(t:(real^N->bool)->bool) P q.
     lf_simplicial_complex t /\ (!p. p IN P ==> p IN t /\ ~(p = {})) /\
     q IN t /\ ~(q = {})
     ==> UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p IN P} INTER
         moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre q} =
         UNIONS {moi_fcl_dual (barycentric_subdivision t)
                   (segment[simplex_barycentre p,simplex_barycentre q]) |
                 p | p IN P /\ (p SUBSET q \/ q SUBSET p)}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; EXISTS_IN_GSPEC] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `p:real^N->bool` THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p:real^N->bool`; `q:real^N->bool`]
      MOI_FRS_PAIR_INTER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p:real^N->bool`; `q:real^N->bool`]
      MOI_FRS_PAIR_INTER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONJ_TAC THENL [EXISTS_TAC `p:real^N->bool` THEN ASM SET_TAC[]; ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Fans of dual 2-cells.  Five 2-cells in a row glue to a 2-cell;          *)
(* the fan at an edge of a triangle (three cells) and the fan at a triangle *)
(* (five cells) of a 3-manifold part are PL 2-cells.                        *)
(* ========================================================================= *)

let MOI_FRB_GLUE_SETS = prove
 (`(!x1 x2 x3 a:real^N->bool.
      x1 INTER x3 = {} /\ x2 INTER x3 = a ==> (x1 UNION x2) INTER x3 = a) /\
   (!x1 x2 x3 x4 a:real^N->bool.
      x1 INTER x4 = {} /\ x2 INTER x4 = {} /\ x3 INTER x4 = a
      ==> ((x1 UNION x2) UNION x3) INTER x4 = a) /\
   (!x1 x2 x3 x4 x5 a:real^N->bool.
      x1 INTER x5 = {} /\ x2 INTER x5 = {} /\ x3 INTER x5 = {} /\ x4 INTER x5 = a
      ==> (((x1 UNION x2) UNION x3) UNION x4) INTER x5 = a) /\
   (!a1 a2 j1 j2 e:real^N->bool.
      a2 SUBSET j2 /\ a1 INTER a2 = {} ==> a2 SUBSET (j1 UNION j2) DIFF (a1 DIFF e))`,
  REPEAT CONJ_TAC THEN SET_TAC[]);;

(* Gluing five PL 2-cells in a row along two-segment arcs (repeated         *)
(* MOI_FRS_GLUE2): consecutive cells meet in the arcs, the others are       *)
(* disjoint, consecutive arcs are disjoint.                                 *)

let MOI_FRB_GLUE5 = prove
 (`!(x1:real^N->bool) j1 x2 j2 x3 j3 x4 j4 x5 j5
    p1 q1 r1 p2 q2 r2 p3 q3 r3 p4 q4 r4.
     2 <= dimindex(:N) /\
     pl_cell_with_boundary 2 x1 j1 /\ pl_cell_with_boundary 2 x2 j2 /\
     pl_cell_with_boundary 2 x3 j3 /\ pl_cell_with_boundary 2 x4 j4 /\
     pl_cell_with_boundary 2 x5 j5 /\
     ~(p1 = q1) /\ ~(q1 = r1) /\ segment[p1,q1] INTER segment[q1,r1] = {q1} /\
     ~(p2 = q2) /\ ~(q2 = r2) /\ segment[p2,q2] INTER segment[q2,r2] = {q2} /\
     ~(p3 = q3) /\ ~(q3 = r3) /\ segment[p3,q3] INTER segment[q3,r3] = {q3} /\
     ~(p4 = q4) /\ ~(q4 = r4) /\ segment[p4,q4] INTER segment[q4,r4] = {q4} /\
     x1 INTER x2 = segment[p1,q1] UNION segment[q1,r1] /\
     x2 INTER x3 = segment[p2,q2] UNION segment[q2,r2] /\
     x3 INTER x4 = segment[p3,q3] UNION segment[q3,r3] /\
     x4 INTER x5 = segment[p4,q4] UNION segment[q4,r4] /\
     x1 INTER x3 = {} /\ x1 INTER x4 = {} /\ x1 INTER x5 = {} /\
     x2 INTER x4 = {} /\ x2 INTER x5 = {} /\ x3 INTER x5 = {} /\
     (segment[p1,q1] UNION segment[q1,r1]) INTER
     (segment[p2,q2] UNION segment[q2,r2]) = {} /\
     (segment[p2,q2] UNION segment[q2,r2]) INTER
     (segment[p3,q3] UNION segment[q3,r3]) = {} /\
     (segment[p3,q3] UNION segment[q3,r3]) INTER
     (segment[p4,q4] UNION segment[q4,r4]) = {} /\
     segment[p1,q1] UNION segment[q1,r1] SUBSET j1 /\
     segment[p1,q1] UNION segment[q1,r1] SUBSET j2 /\
     segment[p2,q2] UNION segment[q2,r2] SUBSET j2 /\
     segment[p2,q2] UNION segment[q2,r2] SUBSET j3 /\
     segment[p3,q3] UNION segment[q3,r3] SUBSET j3 /\
     segment[p3,q3] UNION segment[q3,r3] SUBSET j4 /\
     segment[p4,q4] UNION segment[q4,r4] SUBSET j4 /\
     segment[p4,q4] UNION segment[q4,r4] SUBSET j5
     ==> ?j. pl_cell_with_boundary 2 (x1 UNION x2 UNION x3 UNION x4 UNION x5) j`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`x1:real^N->bool`; `j1:real^N->bool`; `x2:real^N->bool`;
                 `j2:real^N->bool`; `p1:real^N`; `q1:real^N`; `r1:real^N`]
    MOI_FRS_GLUE2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`x1 UNION x2:real^N->bool`;
                 `(j1 UNION j2) DIFF
                  ((segment[p1,q1] UNION segment[q1,r1]) DIFF {p1,r1:real^N})`;
                 `x3:real^N->bool`; `j3:real^N->bool`;
                 `p2:real^N`; `q2:real^N`; `r2:real^N`] MOI_FRS_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST [MATCH_MP_TAC(el 0 (CONJUNCTS MOI_FRB_GLUE_SETS));
           MATCH_MP_TAC(el 3 (CONJUNCTS MOI_FRB_GLUE_SETS))] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(x1 UNION x2) UNION x3:real^N->bool`;
                 `((j1 UNION j2) DIFF
                   ((segment[p1,q1] UNION segment[q1,r1]) DIFF {p1,r1:real^N}) UNION
                   j3) DIFF
                  ((segment[p2,q2] UNION segment[q2,r2]) DIFF {p2,r2:real^N})`;
                 `x4:real^N->bool`; `j4:real^N->bool`;
                 `p3:real^N`; `q3:real^N`; `r3:real^N`] MOI_FRS_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST [MATCH_MP_TAC(el 1 (CONJUNCTS MOI_FRB_GLUE_SETS));
           MATCH_MP_TAC(el 3 (CONJUNCTS MOI_FRB_GLUE_SETS))] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`((x1 UNION x2) UNION x3) UNION x4:real^N->bool`;
                 `(((j1 UNION j2) DIFF
                    ((segment[p1,q1] UNION segment[q1,r1]) DIFF {p1,r1:real^N}) UNION
                    j3) DIFF
                   ((segment[p2,q2] UNION segment[q2,r2]) DIFF {p2,r2:real^N}) UNION
                   j4) DIFF
                  ((segment[p3,q3] UNION segment[q3,r3]) DIFF {p3,r3:real^N})`;
                 `x5:real^N->bool`; `j5:real^N->bool`;
                 `p4:real^N`; `q4:real^N`; `r4:real^N`] MOI_FRS_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST [MATCH_MP_TAC(el 2 (CONJUNCTS MOI_FRB_GLUE_SETS));
           MATCH_MP_TAC(el 3 (CONJUNCTS MOI_FRB_GLUE_SETS))] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_ASSOC] THEN MESON_TAC[]);;

(* The fan at an edge e of a triangle tr, with vertices u0, u1: the dual    *)
(* cells of the edges of the first derived at b(e) towards b(u0), b(tr),   *)
(* b(u1) form a PL 2-cell (three cells in a row, MOI_FRS_GLUE3).          *)

let MOI_FRB_EDGE_FAN = prove
 (`!(t:(real^N->bool)->bool) u0 u1 e tr X1 X2.
     lf_simplicial_complex t /\
     (!w. {w} IN t /\ w IN tr ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     u0 IN t /\ u1 IN t /\ e IN t /\ tr IN t /\
     aff_dim u0 = &0 /\ aff_dim u1 = &0 /\ aff_dim e = &1 /\ aff_dim tr = &2 /\
     u0 SUBSET e /\ u1 SUBSET e /\ e SUBSET tr /\
     ~(u0 SUBSET u1) /\ ~(u1 SUBSET u0) /\
     ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\ aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
     tr SUBSET X1 /\ tr SUBSET X2 /\
     (!X. X IN t /\ tr SUBSET X /\ ~(X = tr) ==> X = X1 \/ X = X2)
     ==> ?j. pl_cell_with_boundary 2
               (moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre u0,simplex_barycentre e]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre e,simplex_barycentre tr]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre u1,simplex_barycentre e])) j`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(u0:real^N->bool = {}) /\ ~(u1:real^N->bool = {}) /\
                ~(e:real^N->bool = {}) /\ ~(tr:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_POS_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u0:real^N->bool = e) /\ ~(u1:real^N->bool = e) /\
                ~(e:real^N->bool = tr) /\ ~(u0:real^N->bool = tr) /\
                ~(u1:real^N->bool = tr) /\ ~(u0:real^N->bool = u1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET_REFL]) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u0:real^N->bool) SUBSET tr /\ (u1:real^N->bool) SUBSET tr`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN t /\ u SUBSET tr ==> u face_of tr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRB_SUB_FACE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?w:real^N. {w} IN t /\ w IN tr` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `aff_dim(u0:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THEN
      EXISTS_TAC `w:real^N` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `3 <= n ==> 2 <= n`) THEN
    MATCH_MP_TAC MOI_FRS_SPHERE2_DIM THEN
    EXISTS_TAC `UNIONS (simplicial_link t (w:real^N))` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the three 2-cells *)
  SUBGOAL_THEN
   `!p q:real^N->bool.
      p IN t /\ q IN t /\ q SUBSET tr /\ p SUBSET q /\ ~(p = {}) /\ ~(p = q)
      ==> pl_cell_with_boundary 2
            (moi_fcl_dual (barycentric_subdivision t)
               (segment[simplex_barycentre p,simplex_barycentre q]))
            (moi_fcl_ldual (barycentric_subdivision t)
               (segment[simplex_barycentre p,simplex_barycentre q]))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRS_EDGE_CELL THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "face_of"
                                with Failure _ -> false)) (concl th))) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  (* the two arcs *)
  SUBGOAL_THEN `moi_bar_chain t {u0,e,tr:real^N->bool} /\
                moi_bar_chain t {u1,e,tr:real^N->bool}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FRS_CHAIN3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {u0,e:real^N->bool} /\
                moi_bar_chain t {e,tr:real^N->bool} /\
                moi_bar_chain t {u1,e:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THENL
     [EXISTS_TAC `{u0,e,tr:real^N->bool}`;
      EXISTS_TAC `{u0,e,tr:real^N->bool}`;
      EXISTS_TAC `{u1,e,tr:real^N->bool}`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u0:real^N->bool`; `e:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u1:real^N->bool`; `e:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* intersections of the three cells *)
  SUBGOAL_THEN `~moi_bar_chain t {u0,u1,e:real^N->bool} /\
                ~moi_bar_chain t {u0,u1,e,tr:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; IN_INSERT; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN DISCH_THEN(MP_TAC o SPECL [`u0:real^N->bool`; `u1:real^N->bool`] o
      last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{u0,e:real^N->bool}`;
                 `{e,tr:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{e,tr:real^N->bool}`;
                 `{u1,e:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{u0,e:real^N->bool}`;
                 `{u1,e:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{u0,e,tr:real^N->bool}`;
                 `{u1,e,tr:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; MOI_FRS_HULL_PAIR] THEN
  SUBGOAL_THEN `{u0,e} UNION {e,tr} = {u0,e,tr:real^N->bool} /\
                {e,tr} UNION {u1,e} = {u1,e,tr:real^N->bool} /\
                {u0,e} UNION {u1,e} = {u0,u1,e:real^N->bool} /\
                {u0,e,tr} UNION {u1,e,tr} = {u0,u1,e,tr:real^N->bool}`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u0,e,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u0,simplex_barycentre e]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u0,e,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre e,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u1,e,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre e,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u1,e,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u1,simplex_barycentre e])`
  MP_TAC THENL
   [REWRITE_TAC[GSYM MOI_FRS_HULL_PAIR] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_FRS_CHAIN_RIM THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    FIRST [MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,b,c})`);
           MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,c,b})`);
           MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {c,a,b})`)] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRS_GLUE3 THEN
  MAP_EVERY EXISTS_TAC
   [`moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre u0,simplex_barycentre (e:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre e,simplex_barycentre (tr:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre u1,simplex_barycentre (e:real^N->bool)])`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,e,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,e,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,e,tr,X2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,e,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,e,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,e,tr,X2:real^N->bool}))`] THEN
  ASM_SIMP_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `{}:real^N->bool` &&
    can (find_term ((=) `tr:real^N->bool`)) (lhs(concl th)) &&
    can (find_term ((=) `u1:real^N->bool`)) (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FRB_NONCHAIN_TAC x y =
  REWRITE_TAC[moi_bar_chain; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPECL [x; y] o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];;

let MOI_FRB_DCI_TAC f g ueq =
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; f; g] MOI_FRS_DUAL_CHAIN_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN ueq (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FRS_HULL_PAIR] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* The fan at a triangle tr with vertices u0, u2, u1 and edges f0 (from u0 *)
(* to u2) and f1 (from u2 to u1): the dual cells of the edges of the first *)
(* derived at b(tr) towards b(u0), b(f0), b(u2), b(f1), b(u1) form a PL    *)
(* 2-cell (five cells in a row, MOI_FRB_GLUE5).                            *)

let MOI_FRB_TRI_FAN = prove
 (`!(t:(real^N->bool)->bool) u0 f0 u2 f1 u1 tr X1 X2.
     lf_simplicial_complex t /\
     (!w. {w} IN t /\ w IN tr ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     u0 IN t /\ f0 IN t /\ u2 IN t /\ f1 IN t /\ u1 IN t /\ tr IN t /\
     aff_dim u0 = &0 /\ aff_dim u2 = &0 /\ aff_dim u1 = &0 /\
     aff_dim f0 = &1 /\ aff_dim f1 = &1 /\ aff_dim tr = &2 /\
     u0 SUBSET f0 /\ u2 SUBSET f0 /\ u2 SUBSET f1 /\ u1 SUBSET f1 /\
     f0 SUBSET tr /\ f1 SUBSET tr /\
     ~(u0 SUBSET u2) /\ ~(u2 SUBSET u0) /\ ~(u0 SUBSET u1) /\ ~(u1 SUBSET u0) /\
     ~(u2 SUBSET u1) /\ ~(u1 SUBSET u2) /\
     ~(u0 SUBSET f1) /\ ~(f1 SUBSET u0) /\ ~(u1 SUBSET f0) /\ ~(f0 SUBSET u1) /\
     ~(f0 SUBSET f1) /\ ~(f1 SUBSET f0) /\
     ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\ aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
     tr SUBSET X1 /\ tr SUBSET X2 /\
     (!X. X IN t /\ tr SUBSET X /\ ~(X = tr) ==> X = X1 \/ X = X2)
     ==> ?j. pl_cell_with_boundary 2
               (moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre u0,simplex_barycentre tr]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre f0,simplex_barycentre tr]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre u2,simplex_barycentre tr]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre f1,simplex_barycentre tr]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre u1,simplex_barycentre tr])) j`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(u0:real^N->bool = {}) /\ ~(f0:real^N->bool = {}) /\
                ~(u2:real^N->bool = {}) /\ ~(f1:real^N->bool = {}) /\
                ~(u1:real^N->bool = {}) /\ ~(tr:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_POS_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u0:real^N->bool = tr) /\ ~(f0:real^N->bool = tr) /\
                ~(u2:real^N->bool = tr) /\ ~(f1:real^N->bool = tr) /\
                ~(u1:real^N->bool = tr) /\ ~(u0:real^N->bool = f0) /\
                ~(u2:real^N->bool = f0) /\ ~(u2:real^N->bool = f1) /\
                ~(u1:real^N->bool = f1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u0:real^N->bool) SUBSET tr /\ (u2:real^N->bool) SUBSET tr /\
                (u1:real^N->bool) SUBSET tr`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN t /\ u SUBSET tr ==> u face_of tr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRB_SUB_FACE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?w:real^N. {w} IN t /\ w IN tr` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `aff_dim(u0:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THEN
      EXISTS_TAC `w:real^N` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `3 <= n ==> 2 <= n`) THEN
    MATCH_MP_TAC MOI_FRS_SPHERE2_DIM THEN
    EXISTS_TAC `UNIONS (simplicial_link t (w:real^N))` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N->bool.
      p IN t /\ p SUBSET tr /\ ~(p = {}) /\ ~(p = tr)
      ==> pl_cell_with_boundary 2
            (moi_fcl_dual (barycentric_subdivision t)
               (segment[simplex_barycentre p,simplex_barycentre tr]))
            (moi_fcl_ldual (barycentric_subdivision t)
               (segment[simplex_barycentre p,simplex_barycentre tr]))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRS_EDGE_CELL THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "face_of"
                                with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {u0,f0,tr:real^N->bool} /\
                moi_bar_chain t {u2,f0,tr:real^N->bool} /\
                moi_bar_chain t {u2,f1,tr:real^N->bool} /\
                moi_bar_chain t {u1,f1,tr:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FRS_CHAIN3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {u0,tr:real^N->bool} /\
                moi_bar_chain t {f0,tr:real^N->bool} /\
                moi_bar_chain t {u2,tr:real^N->bool} /\
                moi_bar_chain t {f1,tr:real^N->bool} /\
                moi_bar_chain t {u1,tr:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THENL
     [EXISTS_TAC `{u0,f0,tr:real^N->bool}`;
      EXISTS_TAC `{u0,f0,tr:real^N->bool}`;
      EXISTS_TAC `{u2,f0,tr:real^N->bool}`;
      EXISTS_TAC `{u2,f1,tr:real^N->bool}`;
      EXISTS_TAC `{u1,f1,tr:real^N->bool}`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u0:real^N->bool`; `f0:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u2:real^N->bool`; `f0:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u2:real^N->bool`; `f1:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `u1:real^N->bool`; `f1:real^N->bool`;
                 `tr:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~moi_bar_chain t {u0,u2,tr:real^N->bool} /\
    ~moi_bar_chain t {u0,f1,tr:real^N->bool} /\
    ~moi_bar_chain t {u0,u1,tr:real^N->bool} /\
    ~moi_bar_chain t {f0,f1,tr:real^N->bool} /\
    ~moi_bar_chain t {f0,u1,tr:real^N->bool} /\
    ~moi_bar_chain t {u2,u1,tr:real^N->bool} /\
    ~moi_bar_chain t {u0,u2,f0,tr:real^N->bool} /\
    ~moi_bar_chain t {u2,f0,f1,tr:real^N->bool} /\
    ~moi_bar_chain t {u2,u1,f1,tr:real^N->bool}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MOI_FRB_NONCHAIN_TAC `u0:real^N->bool` `u2:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `u0:real^N->bool` `f1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `u0:real^N->bool` `u1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `f0:real^N->bool` `f1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `f0:real^N->bool` `u1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `u2:real^N->bool` `u1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `u0:real^N->bool` `u2:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `f0:real^N->bool` `f1:real^N->bool`;
      MOI_FRB_NONCHAIN_TAC `u2:real^N->bool` `u1:real^N->bool`];
    ALL_TAC] THEN

  (* intersections of the five cells and of the four arcs *)
  MOI_FRB_DCI_TAC `{u0,tr:real^N->bool}` `{f0,tr:real^N->bool}`
    `{u0,tr} UNION {f0,tr} = {u0,f0,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{f0,tr:real^N->bool}` `{u2,tr:real^N->bool}`
    `{f0,tr} UNION {u2,tr} = {u2,f0,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u2,tr:real^N->bool}` `{f1,tr:real^N->bool}`
    `{u2,tr} UNION {f1,tr} = {u2,f1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{f1,tr:real^N->bool}` `{u1,tr:real^N->bool}`
    `{f1,tr} UNION {u1,tr} = {u1,f1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u0,tr:real^N->bool}` `{u2,tr:real^N->bool}`
    `{u0,tr} UNION {u2,tr} = {u0,u2,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u0,tr:real^N->bool}` `{f1,tr:real^N->bool}`
    `{u0,tr} UNION {f1,tr} = {u0,f1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u0,tr:real^N->bool}` `{u1,tr:real^N->bool}`
    `{u0,tr} UNION {u1,tr} = {u0,u1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{f0,tr:real^N->bool}` `{f1,tr:real^N->bool}`
    `{f0,tr} UNION {f1,tr} = {f0,f1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{f0,tr:real^N->bool}` `{u1,tr:real^N->bool}`
    `{f0,tr} UNION {u1,tr} = {f0,u1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u2,tr:real^N->bool}` `{u1,tr:real^N->bool}`
    `{u2,tr} UNION {u1,tr} = {u2,u1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u0,f0,tr:real^N->bool}` `{u2,f0,tr:real^N->bool}`
    `{u0,f0,tr} UNION {u2,f0,tr} = {u0,u2,f0,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u2,f0,tr:real^N->bool}` `{u2,f1,tr:real^N->bool}`
    `{u2,f0,tr} UNION {u2,f1,tr} = {u2,f0,f1,tr:real^N->bool}` THEN
  MOI_FRB_DCI_TAC `{u2,f1,tr:real^N->bool}` `{u1,f1,tr:real^N->bool}`
    `{u2,f1,tr} UNION {u1,f1,tr} = {u2,u1,f1,tr:real^N->bool}` THEN
  (* the arcs lie in the boundaries of the cells *)
  SUBGOAL_THEN
   `moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u0,f0,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u0,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u0,f0,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre f0,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u2,f0,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre f0,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u2,f0,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u2,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u2,f1,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u2,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u2,f1,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre f1,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u1,f1,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre f1,simplex_barycentre tr]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {u1,f1,tr:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre u1,simplex_barycentre tr])`
  MP_TAC THENL
   [REWRITE_TAC[GSYM MOI_FRS_HULL_PAIR] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_FRS_CHAIN_RIM THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    FIRST [MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,b,c})`);
           MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,c,b})`);
           MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {c,a,b})`)] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRB_GLUE5 THEN
  MAP_EVERY EXISTS_TAC
   [`moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre u0,simplex_barycentre (tr:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre f0,simplex_barycentre (tr:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre u2,simplex_barycentre (tr:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre f1,simplex_barycentre (tr:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre u1,simplex_barycentre (tr:real^N->bool)])`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,f0,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,f0,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u0,f0,tr,X2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f0,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f0,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f0,tr,X2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f1,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f1,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u2,f1,tr,X2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,f1,tr,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,f1,tr:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {u1,f1,tr,X2:real^N->bool}))`] THEN
  ASM_SIMP_TAC[SUBSET_REFL]);;

(* ========================================================================= *)
(* The two elementary collapses, read as expansions.  Adding an              *)
(* edge with a free vertex, or a triangle with a free edge, to the index    *)
(* set of stars keeps the union a PL 3-cell bounded by its frontier.        *)
(* ========================================================================= *)

let MOI_FRB_GSPEC_SING = prove
 (`!(f:A->B) a. {f p | p | p = a} = {f a}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[]);;

(* An elementary collapse of an edge [v,w] from its free vertex v, read     *)
(* backwards: the star of b[v,w] attaches along the dual 2-cell of the     *)
(* edge of the first derived from w, then the star of v along the dual     *)
(* 2-cell of the edge from b[v,w].                                          *)

let MOI_FRB_COLLAPSE1 = prove
 (`!(t:(real^N->bool)->bool) l P v w.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!x. {x} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t x))) /\
     FINITE P /\ (!p. p IN P ==> p IN l /\ ~(p = {})) /\
     segment[v,w] IN l /\ ~(v = w) /\ {w} IN P /\
     (!p. p IN P ==> ~(v IN p)) /\
     pl_cell_with_boundary 3
       (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                p | p IN P})
       ((subtopology euclidean (UNIONS t)) frontier_of
        (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p IN P}))
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN {v} INSERT segment[v,w] INSERT P})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN {v} INSERT segment[v,w] INSERT P}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!p:real^N->bool. p IN l ==> p IN t) /\ segment[v:real^N,w] IN t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} face_of segment[v,w] /\ {w:real^N} face_of segment[v,w]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN l /\ {w:real^N} IN l` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[v:real^N,w] = {}) /\ ~({v:real^N} = segment[v,w]) /\
                ~({w:real^N} = segment[v,w]) /\ {v} SUBSET segment[v:real^N,w] /\
                {w} SUBSET segment[v:real^N,w] /\ (v:real^N) IN segment[v,w]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT] THEN
    ASM_MESON_TAC[ENDS_IN_SEGMENT; IN_SING; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[v:real^N,w] IN P) /\ ~({v:real^N} IN P)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  (* the star of b[v,w] *)
  SUBGOAL_THEN
   `!p:real^N->bool. p IN P /\ (p SUBSET segment[v,w] \/ segment[v,w] SUBSET p) <=>
                     p = {w}`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [SUBGOAL_THEN `(p:real^N->bool) IN {{v},{w},segment[v,w]}` MP_TAC THENL
         [REWRITE_TAC[GSYM MOI_FRS_SEG_FACE_LIST; IN_ELIM_THM] THEN CONJ_TAC THENL
           [MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
            ASM_SIMP_TAC[];
            ASM_MESON_TAC[]];
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
          ASM_MESON_TAC[IN_SING]];
        ASM_MESON_TAC[SUBSET]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `P:(real^N->bool)->bool`;
                 `segment[v:real^N,w]`] MOI_FRB_ATTACH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_FRB_GSPEC_SING; UNIONS_1] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `P:(real^N->bool)->bool`; `segment[v:real^N,w]`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {w:real^N},
                             simplex_barycentre (segment[v:real^N,w])])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre {w:real^N},
                             simplex_barycentre (segment[v:real^N,w])])`]
    MOI_FRB_FACE_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRB_EDGE_CELL THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    DISCH_TAC] THEN
  (* the star of v *)
  SUBGOAL_THEN
   `!p:real^N->bool. p IN segment[v,w] INSERT P /\ (p SUBSET {v} \/ {v} SUBSET p) <=>
                     p = segment[v,w]`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^N->bool` THEN REWRITE_TAC[IN_INSERT] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (SUBGOAL_THEN `~((p:real^N->bool) = {})` ASSUME_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC]) THEN
      ASM_MESON_TAC[SUBSET; IN_SING; MEMBER_NOT_EMPTY];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `segment[v:real^N,w] INSERT P`;
                 `{v:real^N}`] MOI_FRB_ATTACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_INSERT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_FRB_GSPEC_SING; UNIONS_1] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `segment[v:real^N,w] INSERT P`; `{v:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[v:real^N,w]),
                             simplex_barycentre {v:real^N}])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[v:real^N,w]),
                             simplex_barycentre {v:real^N}])`]
    MOI_FRB_FACE_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; IN_INSERT; NOT_INSERT_EMPTY] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN MATCH_MP_TAC MOI_FRB_EDGE_CELL THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    REWRITE_TAC[]]);;

(* An elementary collapse of the triangle hull{a,b,c} from its free edge   *)
(* [a,b], read backwards: the star of the barycentre of the triangle        *)
(* attaches along the five-cell fan at it (MOI_FRB_TRI_FAN), then the star  *)
(* of b[a,b] along the three-cell fan at it (MOI_FRB_EDGE_FAN).             *)

let MOI_FRB_COLLAPSE2 = prove
 (`!(t:(real^N->bool)->bool) l P a b c.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!x. {x} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t x))) /\
     FINITE P /\ (!p. p IN P ==> p IN l /\ ~(p = {})) /\
     convex hull {a,b,c} IN l /\ ~affine_dependent {a,b,c} /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     {a} IN P /\ {b} IN P /\ {c} IN P /\ segment[b,c] IN P /\ segment[c,a] IN P /\
     (!p. p IN P ==> ~(segment[a,b] SUBSET p)) /\
     pl_cell_with_boundary 3
       (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                p | p IN P})
       ((subtopology euclidean (UNIONS t)) frontier_of
        (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p IN P}))
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN segment[a,b] INSERT convex hull {a,b,c} INSERT P})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN segment[a,b] INSERT convex hull {a,b,c} INSERT P}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `convex hull {a:real^N,b,c}`] MOI_FRB_LINK_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tr = convex hull {a:real^N,b,c}` THEN
  SUBGOAL_THEN `(!p:real^N->bool. p IN l ==> p IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] face_of tr` ASSUME_TAC THENL
   [EXPAND_TAC "tr" THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
    EXISTS_TAC `{a:real^N,b}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN t /\ {b:real^N} IN t /\ {c:real^N} IN t /\
                segment[b:real^N,c] IN t /\ segment[c:real^N,a] IN t /\
                segment[a:real^N,b] IN t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(tr:real^N->bool = {}) /\ ~(segment[a:real^N,b] = tr) /\
                ~(segment[a:real^N,b] = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN CONJ_TAC THENL
     [EXPAND_TAC "tr" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ASM_MESON_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim {a:real^N} = &0 /\ aff_dim {b:real^N} = &0 /\
                aff_dim {c:real^N} = &0 /\
                aff_dim (segment[a:real^N,b]) = &1 /\ aff_dim (segment[b:real^N,c]) = &1 /\
                aff_dim (segment[c:real^N,a]) = &1 /\ aff_dim (tr:real^N->bool) = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_SEGMENT] THEN
    EXPAND_TAC "tr" THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{a,b,c:real^N}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_CARD3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  (* the two tetrahedra on tr *)
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link t (a:real^N)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "pl_sphere"
                                with Failure _ -> false)) (concl th) &&
      can (find_term (fun tm -> tm = `tr:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
    MOI_FRS_TWO_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X1:real^N->bool` (X_CHOOSE_THEN `X2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  (* faces of tr and of [a,b] *)
  SUBGOAL_THEN
   `!p:real^N->bool. p IN t /\ p SUBSET tr /\ ~(p = {})
      ==> p IN {{a},{b},{c},segment[a,b],segment[b,c],segment[c,a],tr}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACE_LIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p IN t /\ p SUBSET segment[a,b] /\ ~(p = {})
      ==> p IN {{a},{b},segment[a,b]}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MOI_FRS_SEG_FACE_LIST; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[a:real^N,b] IN P) /\ ~(tr IN P)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  (* the star of b(tr) *)
  SUBGOAL_THEN
   `!p:real^N->bool. p IN P /\ (p SUBSET tr \/ tr SUBSET p) <=>
                     p IN {{a},segment[c,a],{c},segment[b,c],{b}}`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [SUBGOAL_THEN `(p:real^N->bool) IN
                      {{a},{b},{c},segment[a,b],segment[b,c],segment[c,a],tr}`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_REFL];
        ASM_MESON_TAC[SUBSET_TRANS]];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
            p | p IN P} INTER
    moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre tr} =
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre {a:real^N},simplex_barycentre tr]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre (segment[c:real^N,a]),simplex_barycentre tr]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre {c:real^N},simplex_barycentre tr]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre (segment[b:real^N,c]),simplex_barycentre tr]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre {b:real^N},simplex_barycentre tr])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `P:(real^N->bool)->bool`;
                   `tr:real^N->bool`] MOI_FRB_ATTACH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{a:real^N}`; `segment[c:real^N,a]`;
                 `{c:real^N}`; `segment[b:real^N,c]`; `{b:real^N}`; `tr:real^N->bool`;
                 `X1:real^N->bool`; `X2:real^N->bool`] MOI_FRB_TRI_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `j1:real^N->bool`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `P:(real^N->bool)->bool`; `tr:real^N->bool`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},simplex_barycentre tr]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[c:real^N,a]),
                             simplex_barycentre tr]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {c:real^N},simplex_barycentre tr]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[b:real^N,c]),
                             simplex_barycentre tr]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},simplex_barycentre tr])`;
                 `j1:real^N->bool`] MOI_FRB_FACE_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  (* the star of b[a,b] *)
  SUBGOAL_THEN
   `!p:real^N->bool. p IN tr INSERT P /\ (p SUBSET segment[a,b] \/ segment[a,b] SUBSET p) <=>
                     p IN {{a},tr,{b}}`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^N->bool` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(p:real^N->bool) IN {{a},{b},segment[a,b]}` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
            p | p IN tr INSERT P} INTER
    moi_fcl_dual (barycentric_subdivision t)
      {simplex_barycentre (segment[a:real^N,b])} =
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre {a:real^N},
               simplex_barycentre (segment[a:real^N,b])]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre tr,simplex_barycentre (segment[a:real^N,b])]) UNION
    moi_fcl_dual (barycentric_subdivision t)
      (segment[simplex_barycentre {b:real^N},
               simplex_barycentre (segment[a:real^N,b])])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `tr INSERT P:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`] MOI_FRB_ATTACH) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{a:real^N}`; `{b:real^N}`;
                 `segment[a:real^N,b]`; `tr:real^N->bool`;
                 `X1:real^N->bool`; `X2:real^N->bool`] MOI_FRB_EDGE_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ISPECL [`simplex_barycentre (segment[a:real^N,b])`;
                      `simplex_barycentre (tr:real^N->bool)`]
                (CONJUNCT1 SEGMENT_SYM)] THEN
  DISCH_THEN(X_CHOOSE_TAC `j2:real^N->bool`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `tr INSERT P:(real^N->bool)->bool`; `segment[a:real^N,b]`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},
                             simplex_barycentre (segment[a:real^N,b])]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre tr,
                             simplex_barycentre (segment[a:real^N,b])]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},
                             simplex_barycentre (segment[a:real^N,b])])`;
                 `j2:real^N->bool`] MOI_FRB_FACE_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; IN_INSERT] THEN ASM_MESON_TAC[];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Bookkeeping for the collapses.  Cut-connectivity of the                  *)
(* 1-skeleton (moi_frb_conn) follows from connectedness of the polyhedron  *)
(* and survives both kinds of elementary collapse; so do chi and being a   *)
(* subcomplex.  A connected graph with chi = 1 and an edge has a leaf.      *)
(* ========================================================================= *)

let moi_frb_conn = new_definition
 `moi_frb_conn (l:(real^N->bool)->bool) <=>
    !a. a SUBSET {v | {v} IN l} /\ ~(a = {}) /\ ~(a = {v | {v} IN l})
        ==> ?x y. x IN a /\ {y} IN l /\ ~(y IN a) /\ segment[x,y] IN l`;;

(* Two vertices of a simplex of a complex span an edge of it.               *)

let MOI_FRB_VERTEX_EDGE = prove
 (`!(l:(real^N->bool)->bool) s u w.
     simplicial_complex l /\ s IN l /\ {u} IN l /\ {w} IN l /\ u IN s /\ w IN s
     ==> segment[u,w] IN l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `V:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^N) IN V /\ (w:real^N) IN V` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x:real^N. {x} IN l /\ x IN s ==> x IN V` (fun th ->
      ASM_MESON_TAC[th]) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^N} face_of s` MP_TAC THENL
     [SUBGOAL_THEN `{x:real^N} = {x} INTER s` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^N,w] face_of s` MP_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
    EXISTS_TAC `{u:real^N,w}` THEN ASM SET_TAC[];
    ASM_MESON_TAC[simplicial_complex]]);;

(* Connectedness of the polyhedron gives cut-connectivity.                  *)

let MOI_FRB_CONN_OF_CONNECTED = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ connected (UNIONS l) ==> moi_frb_conn l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_frb_conn] THEN
  X_GEN_TAC `a:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\
                (!s:real^N->bool. s IN l ==> compact s /\ convex s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FRN_SA_SC_FACTS]; ALL_TAC] THEN
  (* every nonempty simplex has its vertices on one side *)
  SUBGOAL_THEN
   `!s. s IN l /\ ~(s = {})
        ==> (!v:real^N. {v} IN l /\ v IN s ==> v IN a) \/
            (!v:real^N. {v} IN l /\ v IN s ==> ~(v IN a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `~(~p /\ ~q) ==> p \/ q`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `u:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRB_VERTEX_EDGE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (UNIONS (l:(real^N->bool)->bool))` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {s:real^N->bool | s IN l /\ ~(s = {}) /\
                              !v. {v} IN l /\ v IN s ==> v IN a}`;
    `UNIONS {s:real^N->bool | s IN l /\ ~(s = {}) /\
                              !v. {v} IN l /\ v IN s ==> ~(v IN a)}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `a:real^N->bool`)) (concl th) &&
      not (can (find_term (fun tm -> try fst(dest_const tm) = "segment"
                                     with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s1 INTER s2:real^N->bool`]
      MOI_SCF_SC_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(s1 INTER s2:real^N->bool) face_of s1` MP_TAC THENL
         [ASM_MESON_TAC[simplicial_complex]; ASM_MESON_TAC[simplicial_complex]];
        ASM SET_TAC[]];
      REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]];
    UNDISCH_TAC `~(a:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `u:real^N`) THEN
    EXISTS_TAC `u:real^N` THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    SUBGOAL_THEN `{u:real^N} IN l` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[IN_SING]];
    SUBGOAL_THEN `?w:real^N. {w} IN l /\ ~(w IN a)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `w:real^N` THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]]]);;

(* Cut-connectivity survives the collapse of a triangle from a free edge    *)
(* [a,b] (the path a, c, b remains) and of an edge from a free vertex.       *)

let MOI_FRB_CONN_COLLAPSE2 = prove
 (`!(l:(real^N->bool)->bool) a b c.
     moi_frb_conn l /\ ~(a = b) /\ aff_dim(convex hull {a,b,c}) = &2 /\ {c} IN l /\
     segment[b,c] IN l /\ segment[c,a] IN l /\
     ~(segment[b,c] = segment[a,b]) /\ ~(segment[c,a] = segment[a,b])
     ==> moi_frb_conn (l DIFF {convex hull {a,b,c}, segment[a,b]})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y:real^N. ~(segment[x,y] = convex hull {a,b,c})` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. ~({v} = convex hull {a,b,c}) /\ ~({v} = segment[a,b])`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SEGMENT_REFL]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N) IN {v} /\ (b:real^N) IN {v}` MP_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN l DIFF {convex hull {a,b,c}, segment[a,b]} <=>
                           {v} IN l`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_frb_conn] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a0:real^N->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frb_conn (l:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_frb_conn] THEN DISCH_THEN(MP_TAC o SPEC `a0:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `segment[x:real^N,y] = segment[a,b]` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(x:real^N = a /\ y = b) \/ (x = b /\ y = a)` MP_TAC THENL
   [UNDISCH_TAC `segment[x:real^N,y] = segment[a,b]` THEN
    REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `(c:real^N) IN a0` THENL
   [MAP_EVERY EXISTS_TAC [`c:real^N`; `b:real^N`] THEN
    SUBST1_TAC(ISPECL [`c:real^N`; `b:real^N`] (CONJUNCT1 SEGMENT_SYM)) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `c:real^N`] THEN
    SUBST1_TAC(ISPECL [`a:real^N`; `c:real^N`] (CONJUNCT1 SEGMENT_SYM)) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`c:real^N`; `a:real^N`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`] THEN ASM_REWRITE_TAC[]]);;

let MOI_FRB_CONN_COLLAPSE1 = prove
 (`!(l:(real^N->bool)->bool) v w.
     moi_frb_conn l /\ ~(v = w) /\ segment[v,w] IN l /\ {v} IN l /\
     (!s. s IN l /\ v IN s ==> s = {v} \/ s = segment[v,w])
     ==> moi_frb_conn (l DIFF {segment[v,w], {v}})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N. ~({u} = segment[v,w])` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN {u} /\ (w:real^N) IN {u}` MP_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. {u} IN l DIFF {segment[v,w], {v}} <=> {u} IN l /\ ~(u = v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. segment[x:real^N,y] IN l /\ ~(x = y) /\ (x = v \/ y = v)
                      ==> segment[x,y] = segment[v,w]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^N) IN segment[x,y]` ASSUME_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(segment[x:real^N,y] = {v})` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN {v} /\ (y:real^N) IN {v}` MP_TAC THENL
       [UNDISCH_TAC `segment[x:real^N,y] = {v}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[ENDS_IN_SEGMENT];
        REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. segment[x:real^N,y] IN l /\ ~(x = v) /\ ~(y = v)
          ==> segment[x,y] IN l DIFF {segment[v,w], {v}}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(v:real^N) IN {x,y}` MP_TAC THENL
       [UNDISCH_TAC `segment[x:real^N,y] = segment[v,w]` THEN
        REWRITE_TAC[SEGMENT_EQ] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(x:real^N) IN {v}` MP_TAC THENL
       [UNDISCH_TAC `segment[x:real^N,y] = {v}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[ENDS_IN_SEGMENT];
        REWRITE_TAC[IN_SING] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_frb_conn] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a0:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((v:real^N) IN a0) /\ a0 SUBSET {u:real^N | {u} IN l}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_frb_conn (l:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_frb_conn] THEN DISCH_THEN(LABEL_TAC "conn") THEN
  USE_THEN "conn" (MP_TAC o SPEC `a0:real^N->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(x:real^N = v) /\ ~(x = y)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `y:real^N = v` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `x:real^N = w` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `segment[x:real^N,v] = segment[v,w]` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "\\/"
                                  with Failure _ -> false)) (concl th) &&
        can (find_term ((=) `segment[v:real^N,w]`)) (concl th) &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "DIFF"
                                       with Failure _ -> false)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_EQ] THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "conn" (MP_TAC o SPEC `(v:real^N) INSERT a0`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~(a0 = {u:real^N | {u} IN l /\ ~(u = v)})` THEN
      REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` (X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(y':real^N = v) /\ ~(y' IN a0)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x':real^N = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,y'] = segment[v,w]` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "\\/"
                                  with Failure _ -> false)) (concl th) &&
        can (find_term ((=) `segment[v:real^N,w]`)) (concl th) &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "DIFF"
                                       with Failure _ -> false)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x':real^N`; `y':real^N`] THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

(* chi is unchanged by removing two simplices of consecutive dimensions.    *)

let MOI_FRB_EULER_DELETE2 = prove
 (`!(l:(real^N->bool)->bool) s r.
     FINITE l /\ s IN l /\ r IN l /\ ~(r = {}) /\ aff_dim s = aff_dim r + &1
     ==> complex_euler (l DIFF {s,r}) = complex_euler l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real^N->bool = r) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    TRY(UNDISCH_TAC `aff_dim(r:real^N->bool) = aff_dim r + &1` THEN INT_ARITH_TAC) THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_GE) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. aff_dim(r:real^N->bool) = &m` (X_CHOOSE_TAC `m:num`) THENL
   [REWRITE_TAC[INT_OF_NUM_EXISTS; AFF_DIM_POS_LE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM_ALT; FINITE_DIFF] THEN
  SUBGOAL_THEN `l DIFF {s,r:real^N->bool} = (l DELETE s) DELETE r` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_DELETE; FINITE_DELETE; IN_DELETE] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_ADD; NUM_OF_INT_OF_NUM; REAL_POW_ADD; REAL_POW_1] THEN
  REAL_ARITH_TAC);;

(* A finite set with at most one element containing a is {a}.            *)

let MOI_FRB_CARD_LE1_SING = prove
 (`!s (a:A). FINITE s /\ CARD s <= 1 /\ a IN s ==> s = {a}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `b:A` THEN
  REWRITE_TAC[IN_SING] THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{a:A,b}`; `s:A->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_ARITH_TAC);;

(* A connected graph with chi = 1 and an edge has a vertex in exactly one   *)
(* edge (handshake).                                                         *)

let MOI_FRB_LEAF = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
     complex_euler l = &1 /\ moi_frb_conn l /\
     (?e. e IN l /\ aff_dim e = &1)
     ==> ?v w. segment[v,w] IN l /\ ~(v = w) /\ {v} IN l /\ {w} IN l /\
               !s. s IN l /\ v IN s ==> s = {v} \/ s = segment[v,w]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN l}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FGB_CHI_DIM1) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 = a - b <=> a = b + &1`; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRN_SA_LK_HANDSHAKE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* some vertex has degree at most one *)
  SUBGOAL_THEN `?u:real^N. {u} IN l /\
                  CARD {e | e IN l /\ aff_dim e = &1 /\ u IN e} <= 1`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_LE]) THEN
    SUBGOAL_THEN
     `nsum {u:real^N | {u} IN l} (\u. 2) <=
      nsum {u | {u} IN l} (\u. CARD {e | e IN l /\ aff_dim e = &1 /\ u IN e})`
    MP_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC];
    ALL_TAC] THEN
  (* it has an edge, by connectivity *)
  SUBGOAL_THEN `?w:real^N. {w} IN l /\ ~(w = u)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FRN_SA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
      STRIP_ASSUME_TAC)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_frb_conn (l:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_frb_conn] THEN DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim(segment[u:real^N,y]) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    SUBGOAL_THEN `~(u:real^N = y)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{e | e IN l /\ aff_dim e = &1 /\ (u:real^N) IN e} = {segment[u,y]}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRB_CARD_LE1_SING THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ENDS_IN_SEGMENT] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &0 \/ aff_dim s = &1` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `u:real^N` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(u:real^N) IN {z}` THEN REWRITE_TAC[IN_SING] THEN MESON_TAC[];
    DISJ2_TAC THEN
    UNDISCH_TAC `{e | e IN l /\ aff_dim e = &1 /\ (u:real^N) IN e} = {segment[u,y]}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[]]);;

(* Removing a free pair keeps a subcomplex.                                 *)

let MOI_FRB_SUBCX_DEL2 = prove
 (`!(l:(real^N->bool)->bool) l0 e tr.
     simplicial_subcomplex l l0 /\ e IN l /\ tr IN l /\ e SUBSET tr /\ ~(e = tr) /\
     (!r. r IN l /\ e SUBSET r /\ ~(r = e) ==> r = tr)
     ==> simplicial_subcomplex (l DIFF {tr,e}) l0`,
  REWRITE_TAC[simplicial_subcomplex] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(s:real^N->bool) IN l DIFF {tr,e}` THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN l /\ f SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `(s:real^N->bool) = tr` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    SUBGOAL_THEN `(s:real^N->bool) = tr` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FRB_SUBCX_DEL1 = prove
 (`!(l:(real^N->bool)->bool) l0 v e.
     simplicial_subcomplex l l0 /\ v IN e /\
     (!s. s IN l /\ v IN s ==> s = {v} \/ s = e)
     ==> simplicial_subcomplex (l DIFF {e,{v}}) l0`,
  REWRITE_TAC[simplicial_subcomplex] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(s:real^N->bool) IN l DIFF {e,{v}}` THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN l /\ f SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((v:real^N) IN s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Free edges.  Dual connectivity of a connected finite                     *)
(* combinatorial 2-manifold with boundary (the closed-surface proofs of     *)
(* pc_moi_fnd_rn with arc links added), hence: every subcomplex of a        *)
(* connected 2-manifold with nonempty boundary that contains a triangle     *)
(* has an edge lying in exactly one of its simplices besides itself.        *)
(* ========================================================================= *)

let MOI_FRB_ARC_EDGES_CONN = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g U.
        simplicial_complex L /\ &1 simplex k /\
        homeomorphism (k,UNIONS L) (f,g) /\
        U SUBSET {e | e IN L /\ aff_dim e = &1} /\ ~(U = {}) /\
        (!e e'. e IN U /\ e' IN L /\ aff_dim e' = &1 /\ ~(e INTER e' = {})
                ==> e' IN U)
        ==> U = {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool) /\
                (!s:real^N->bool. s IN L ==> compact s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_SA_SC_FACTS]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `e1:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FGB_ARC_CUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS U:real^N->bool`;
    `UNIONS {e:real^N->bool | e IN L /\ aff_dim e = &1 /\ ~(e IN U)}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      SET_TAC[];
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(t:real^N->bool) IN U` THEN SET_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?e:real^N->bool. e IN L /\ aff_dim e = &1 /\ y IN e`
    MP_TAC THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                     `f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
        MOI_FGB_ARC_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
      SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_ARITH `&0 <= x:int /\ x <= &1 <=> x = &0 \/ x = &1`;
                  IMP_IMP] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN
        REWRITE_TAC[AFF_DIM_EQ_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(y:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC MOI_FGB_ARC_DEG_GE1 THEN
        MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                              `g:real^N->real^N`] THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(e:real^N->bool) IN U` THENL
       [DISJ1_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC)
         ASSUME_TAC)) THEN
    UNDISCH_TAC `~((e':real^N->bool) IN U)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    UNDISCH_TAC `~(U:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `e0:real^N->bool`) THEN
    SUBGOAL_THEN `(e0:real^N->bool) IN L /\ aff_dim e0 = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(e0:real^N->bool) IN U` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(e0:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
    CONJ_TAC THEN EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `~(e1:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `e1:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The edges of the link of a vertex of a finite combinatorial 2-manifold  *)
(* with boundary (a PL circle or arc) are connected through common points. *)

let MOI_FRB_CMB2_LINK_EDGES = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c
     ==> simplicial_complex (simplicial_link c v) /\
         (?e. e IN simplicial_link c v /\ aff_dim e = &1) /\
         !U. U SUBSET {e | e IN simplicial_link c v /\ aff_dim e = &1} /\
             ~(U = {}) /\
             (!e e'. e IN U /\ e' IN simplicial_link c v /\ aff_dim e' = &1 /\
                     ~(e INTER e' = {}) ==> e' IN U)
             ==> U = {e | e IN simplicial_link c v /\ aff_dim e = &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_CMB2_LINK) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC)))) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `?s:real^N->bool. s IN L /\ ~(s = {})` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `k:real^N->bool` MOI_FRN_SA_RF_TWO_POINTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
          STRIP_ASSUME_TAC)) THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
        SUBGOAL_THEN `(f:real^N->real^N) a IN UNIONS L` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[NOT_IN_EMPTY];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                     `g:real^N->real^N`; `w:real^N`] MOI_FRN_SA_LK_EDGE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_LK_EDGES_CONN THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                            `g:real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `homeomorphism (k,UNIONS L) (f:real^N->real^N,g)` ASSUME_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `?s:real^N->bool. s IN L /\ ~(s = {})` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `~(k:real^N->bool = {})` MP_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&1:int = -- &1)`]; ALL_TAC] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
        SUBGOAL_THEN `(f:real^N->real^N) a IN UNIONS L` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[NOT_IN_EMPTY];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                     `g:real^N->real^N`; `w:real^N`] MOI_FGB_ARC_DEG_GE1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRB_ARC_EDGES_CONN THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                            `g:real^N->real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

(* Every vertex lies in a triangle.                                         *)

let MOI_FRB_CMB2_VTRI = prove
 (`!c v:real^N.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c
        ==> ?t. t IN c /\ aff_dim t = &2 /\ v IN t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRB_CMB2_LINK_EDGES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT e)` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MOI_FRB_CMB2_PURE = prove
 (`!(c:(real^N->bool)->bool) q.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ q IN c /\ ~(q = {})
     ==> ?t. t IN c /\ aff_dim t = &2 /\ q SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aff_dim(q:real^N->bool) = &0 \/ aff_dim q = &1 \/ aff_dim q = &2`
  MP_TAC THENL
   [MP_TAC(ISPEC `q:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `q:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FGB_CMB2_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(q:real^N->bool) = &0` THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FRB_CMB2_VTRI) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[SING_SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FGB_CMB2_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
     `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ q SUBSET t} = {}` THENL
     [ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MESON_TAC[]];
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FRB_CMB2_LCONN = prove
 (`!c (v:real^N) Y.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
        Y SUBSET {t | t IN c /\ aff_dim t = &2 /\ v IN t} /\ ~(Y = {}) /\
        (!t t' u. t IN Y /\ t' IN c /\ aff_dim t' = &2 /\ v IN t' /\
                  ~(u = v) /\ {u} IN c /\ u IN t /\ u IN t'
                  ==> t' IN Y)
        ==> Y = {t | t IN c /\ aff_dim t = &2 /\ v IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRB_CMB2_LINK_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (LABEL_TAC "lke"))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  USE_THEN "lke" (MP_TAC o SPEC
                 `{s:real^N->bool | s IN L /\ aff_dim s = &1 /\
                                    convex hull (v INSERT s) IN Y}`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(Y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool`) THEN
      SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2 /\ v IN t`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        UNDISCH_TAC `(t:real^N->bool) IN Y` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?u:real^N. {u} IN L /\ u IN s1 /\ u IN s2` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s1 INTER s2:real^N->bool`]
          MOI_SCF_SC_VERTEX) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(s1 INTER s2:real^N->bool) face_of s1` MP_TAC THENL
           [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
          ASM_MESON_TAC[simplicial_complex];
          REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `~(u:real^N = v) /\ {u} IN c /\ u IN convex hull (v INSERT s1) /\
        u IN convex hull (v INSERT s2) /\
        aff_dim(convex hull ((v:real^N) INSERT s2)) = &2`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
          UNDISCH_TAC `{u:real^N} IN L` THEN EXPAND_TAC "L" THEN
          SIMP_TAC[simplicial_link; IN_ELIM_THM];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s2:real^N->bool` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT s1)`; `u:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN
                {s | s IN L /\ aff_dim s = &1 /\ convex hull (v INSERT s) IN Y}`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_FRB_CMB2_DCONN = prove
 (`!(c:(real^N->bool)->bool) Z.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c) /\
     Z SUBSET {t | t IN c /\ aff_dim t = &2} /\ ~(Z = {}) /\
     (!t t'. t IN Z /\ t' IN c /\ aff_dim t' = &2 /\ aff_dim(t INTER t') = &1
             ==> t' IN Z)
     ==> Z = {t | t IN c /\ aff_dim t = &2}`,
  REPEAT STRIP_TAC THEN POP_ASSUM(LABEL_TAC "ZC") THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ moi_bar_complex c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_TOUCH_CLOSED THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_SC_CLOSED];
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    SUBGOAL_THEN `UNIONS {t:real^N->bool | t IN c /\ aff_dim t = &2} =
                  UNIONS c` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRB_CMB2_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER t':real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t INTER t':real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`;
                 `{u:real^N->bool | u IN Z /\ w IN u}`] MOI_FRB_CMB2_LCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `a':real^N->bool`; `u:real^N`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^N->bool) IN c /\ aff_dim a = &2`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N->bool`;
                     `a':real^N->bool`; `u:real^N`; `w:real^N`]
        MOI_FRN_TRI_SHARE2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(a:real^N->bool) IN Z` THEN ASM_REWRITE_TAC[];
        USE_THEN "ZC" MATCH_MP_TAC THEN EXISTS_TAC `a:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;
(* A finite set with at most two elements containing a and b (distinct) is *)
(* {a,b}.                                                                    *)

let MOI_FRB_CARD_LE2_PAIR = prove
 (`!s (a:A) b. FINITE s /\ CARD s <= 2 /\ a IN s /\ b IN s /\ ~(a = b)
               ==> s = {a,b}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `c:A` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `CARD {a:A,b,c} = 3` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{a:A,b,c}`; `s:A->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_ARITH_TAC);;

(* Free edges: every subcomplex l of a connected finite combinatorial       *)
(* 2-manifold l0 with nonempty boundary that contains a triangle has an    *)
(* edge lying in exactly one other simplex of l, a triangle.  If the        *)
(* triangles of l are closed under adjacency in l0 they are all triangles   *)
(* of l0 (dual connectivity) and a boundary edge of l0 is free in l;        *)
(* otherwise an edge of l between a triangle of l and one of l0 outside l   *)
(* lies in no other triangle of l0.                                          *)

let MOI_FRB_FREE_EDGE = prove
 (`!(l0:(real^N->bool)->bool) l.
     FINITE l0 /\ combinatorial_manifold_with_boundary 2 l0 /\
     connected (UNIONS l0) /\ ~(surface_boundary l0 = {}) /\
     simplicial_subcomplex l l0 /\ (?tr. tr IN l /\ aff_dim tr = &2)
     ==> ?e tr. e IN l /\ aff_dim e = &1 /\ tr IN l /\ aff_dim tr = &2 /\
                e SUBSET tr /\ !r. r IN l /\ e SUBSET r /\ ~(r = e) ==> r = tr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (l0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l0 ==> aff_dim s <= &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FGB_CMB2_DIM]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET l0 /\
                (!s f. s IN l /\ f face_of s ==> f IN l)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e r:real^N->bool. e IN l0 /\ aff_dim e = &1 /\ r IN l0 /\ e SUBSET r /\ ~(r = e)
                       ==> aff_dim r = &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `r:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
        MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `l0:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!t t':real^N->bool. t IN l /\ aff_dim t = &2 /\ t' IN l0 /\ aff_dim t' = &2 /\
                        aff_dim(t INTER t') = &1 ==> t' IN l`
  THENL
   [MP_TAC(ISPECL [`l0:(real^N->bool)->bool`;
                   `{t:real^N->bool | t IN l /\ aff_dim t = &2}`]
      MOI_FRB_CMB2_DCONN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]];
      DISCH_THEN(LABEL_TAC "allt")] THEN
    UNDISCH_TAC `~(surface_boundary (l0:(real^N->bool)->bool) = {})` THEN
    REWRITE_TAC[surface_boundary; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `e0:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FCL_CARD_1_NONEMPTY) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `{r:real^N->bool | r IN l0 /\ aff_dim r = &2 /\ e0 SUBSET r} = {t0}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRB_CARD_LE1_SING THEN ASM_REWRITE_TAC[IN_ELIM_THM; LE_REFL] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l0:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t0:real^N->bool) IN l` ASSUME_TAC THENL
     [USE_THEN "allt" (MP_TAC o SPEC `t0:real^N->bool` o
        GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e0:real^N->bool`; `t0:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "face_of"
                                  with Failure _ -> false)) (concl th))) THEN
      EXISTS_TAC `t0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FRB_SUB_FACE THEN EXISTS_TAC `l0:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) IN
                    {r | r IN l0 /\ aff_dim r = &2 /\ e0 SUBSET r}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `&2:int`)) (concl th) &&
          can (find_term (fun tm -> try fst(dest_const tm) = "SUBSET"
                                    with Failure _ -> false)) (concl th))) THEN
        EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_SING]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `e = t INTER (t':real^N->bool)` THEN
  SUBGOAL_THEN `(t:real^N->bool) IN l0 /\ e face_of t /\ e face_of t'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN EXPAND_TAC "e" THEN
    UNDISCH_TAC `lf_simplicial_complex (l0:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o
      CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN l /\ e IN l0 /\ e SUBSET t /\ e SUBSET t'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM SET_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{r:real^N->bool | r IN l0 /\ aff_dim r = &2 /\ e SUBSET r} = {t,t'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRB_CARD_LE2_PAIR THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l0:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FGB_CMB2_EDGE) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN {r | r IN l0 /\ aff_dim r = &2 /\ e SUBSET r}`
  MP_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2:int`)) (concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "SUBSET"
                                with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Collapsing to a vertex.  For an ambient finite subcomplex l0 of          *)
(* dimension at most 2 with the free-edge property, every subcomplex l of  *)
(* l0 with chi = 1, cut-connected 1-skeleton and a vertex has derived      *)
(* neighbourhood a PL 3-cell bounded by its frontier: induction on CARD l, *)
(* removing a triangle with a free edge, else a leaf edge, down to a       *)
(* vertex.                                                                   *)
(* ========================================================================= *)

(* The vertices of a triangle with a given edge.                            *)

let MOI_FRB_TRI_EDGE_VERTS = prove
 (`!(c:(real^N->bool)->bool) tr e.
     simplicial_complex c /\ tr IN c /\ aff_dim tr = &2 /\ e IN c /\
     aff_dim e = &1 /\ e SUBSET tr
     ==> ?a b d. ~affine_dependent {a,b,d} /\ ~(a = b) /\ ~(a = d) /\ ~(b = d) /\
                 tr = convex hull {a,b,d} /\ e = segment[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FRN_SA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN tr /\ (q:real^N) IN tr` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`; `p:real^N`]
    MOI_FRN_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^N) IN {p,x,y}` MP_TAC THENL
   [SUBGOAL_THEN `(q:real^N) extreme_point_of convex hull {p,x,y}` MP_TAC THENL
     [REWRITE_TAC[GSYM FACE_OF_SING] THEN
      SUBGOAL_THEN `{q:real^N} = {q} INTER tr` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `tr = convex hull {p:real^N,x,y}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[moi_bar_complex];
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(p:real^N = q)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `y:real^N`] THEN
    UNDISCH_TAC `(q:real^N) = x` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `x:real^N`] THEN
    UNDISCH_TAC `(q:real^N) = y` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `{p,y,x} = {p:real^N,x,y}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* The proper faces of a triangle of a face-closed family lie in it.         *)

let MOI_FRB_TRI_FACES_IN = prove
 (`!(l:(real^N->bool)->bool) a b c.
     (!s f. s IN l /\ f face_of s ==> f IN l) /\ convex hull {a,b,c} IN l /\
     ~affine_dependent {a,b,c}
     ==> {a} IN l /\ {b} IN l /\ {c} IN l /\ segment[a,b] IN l /\
         segment[b,c] IN l /\ segment[c,a] IN l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACE_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun tm -> try fst(dest_const tm) = "face_of"
                              with Failure _ -> false)) (concl th) &&
    not (can (find_term (fun tm -> try fst(dest_const tm) = "convex"
                                   with Failure _ -> false)) (concl th)))) THEN
  EXISTS_TAC `convex hull {a:real^N,b,c}` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_FRB_COLLAPSE_IND = prove
 (`!(t:(real^N->bool)->bool) l0.
     lf_simplicial_complex t /\ simplicial_subcomplex l0 t /\ FINITE l0 /\
     (!x. {x} IN l0 ==> pl_sphere 2 (UNIONS (simplicial_link t x))) /\
     (!s. s IN l0 ==> aff_dim s <= &2) /\
     (!l. simplicial_subcomplex l l0 /\ (?tr. tr IN l /\ aff_dim tr = &2)
          ==> ?e tr. e IN l /\ aff_dim e = &1 /\ tr IN l /\ aff_dim tr = &2 /\
                     e SUBSET tr /\ !r. r IN l /\ e SUBSET r /\ ~(r = e) ==> r = tr)
     ==> !l. simplicial_subcomplex l l0 /\ complex_euler l = &1 /\
             moi_frb_conn l /\ (?v. {v} IN l)
             ==> pl_cell_with_boundary 3
                   (UNIONS {moi_fcl_dual (barycentric_subdivision t)
                              {simplex_barycentre p} | p | p IN l /\ ~(p = {})})
                   ((subtopology euclidean (UNIONS t)) frontier_of
                    (UNIONS {moi_fcl_dual (barycentric_subdivision t)
                               {simplex_barycentre p} | p | p IN l /\ ~(p = {})}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fe")))))) THEN
  SUBGOAL_THEN `(l0:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND; MEASURE]
    (ISPEC `CARD:((real^N->bool)->bool)->num` WF_MEASURE)) THEN
  X_GEN_TAC `l:(real^N->bool)->bool` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\ l SUBSET l0 /\
                (!s f. s IN l /\ f face_of s ==> f IN l)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (l:(real^N->bool)->bool) t` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex] THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ALL_TAC] THEN
  ASM_CASES_TAC `?tr:real^N->bool. tr IN l /\ aff_dim tr = &2` THENL
   [(* a triangle with a free edge *)
    USE_THEN "fe" (MP_TAC o SPEC `l:(real^N->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `tr:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `tr:real^N->bool`; `e:real^N->bool`]
      MOI_FRB_TRI_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `c:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
            SUBST_ALL_TAC)))))))) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
      MOI_FRB_TRI_FACES_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~({a:real^N} = convex hull {a,b,c}) /\ ~({b:real^N} = convex hull {a,b,c}) /\
      ~({c:real^N} = convex hull {a,b,c}) /\
      ~(segment[b:real^N,c] = convex hull {a,b,c}) /\
      ~(segment[c:real^N,a] = convex hull {a,b,c}) /\
      ~(segment[a:real^N,b] = convex hull {a,b,c}) /\
      ~({a:real^N} = segment[a,b]) /\ ~({b:real^N} = segment[a,b]) /\
      ~({c:real^N} = segment[a,b]) /\ ~(segment[b:real^N,c] = segment[a,b]) /\
      ~(segment[c:real^N,a] = segment[a,b])`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE `(s:real^N->bool) = t ==> t SUBSET s`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `l' = l DIFF {convex hull {a:real^N,b,c}, segment[a,b]}` THEN
    SUBGOAL_THEN
     `!p:real^N->bool. p IN l /\ ~(p = {}) <=>
                       p IN segment[a,b] INSERT convex hull {a,b,c} INSERT
                            {q | q IN l' /\ ~(q = {})}`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `p:real^N->bool` THEN EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM; IN_DIFF; NOT_IN_EMPTY] THEN
      SUBGOAL_THEN `~(segment[a:real^N,b] = {}) /\ ~(convex hull {a:real^N,b,c} = {})`
      MP_TAC THENL
       [REWRITE_TAC[SEGMENT_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
        UNDISCH_TAC `segment[a:real^N,b] IN l` THEN
        UNDISCH_TAC `convex hull {a:real^N,b,c} IN l` THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRB_COLLAPSE2 THEN
    EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!q:real^N->bool. q IN l /\ ~(q = convex hull {a,b,c}) /\ ~(q = segment[a,b]) /\
                       ~(q = {})
                       ==> q IN {q | q IN l' /\ ~(q = {})}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "l'" THEN SET_TAC[];
      EXPAND_TAC "l'" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET l0` THEN SET_TAC[];
      UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET l0` THEN
      UNDISCH_TAC `convex hull {a:real^N,b,c} IN l` THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY];
      EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `p = convex hull {a:real^N,b,c}`
        (fun th -> UNDISCH_TAC `~(p = convex hull {a:real^N,b,c})` THEN
                   REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `segment[a:real^N,b]`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "SUBSET"
                                  with Failure _ -> false)) (concl th) &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "DIFF"
                                       with Failure _ -> false)) (concl th)) &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "GSPEC"
                                       with Failure _ -> false)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "IH" (MP_TAC o SPEC `l':(real^N->bool)->bool`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
        EXPAND_TAC "l'" THEN UNDISCH_TAC `convex hull {a:real^N,b,c} IN l` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [EXPAND_TAC "l'" THEN MATCH_MP_TAC MOI_FRB_SUBCX_DEL2 THEN
          ASM_REWRITE_TAC[];
          EXPAND_TAC "l'" THEN
          MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `convex hull {a:real^N,b,c}`;
                         `segment[a:real^N,b]`] MOI_FRB_EULER_DELETE2) THEN
          ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN ANTS_TAC THENL
           [CONV_TAC INT_REDUCE_CONV; SIMP_TAC[]];
          EXPAND_TAC "l'" THEN MATCH_MP_TAC MOI_FRB_CONN_COLLAPSE2 THEN
          ASM_REWRITE_TAC[];
          EXISTS_TAC `a:real^N` THEN EXPAND_TAC "l'" THEN
          REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  (* no triangle *)
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2 /\ ~(aff_dim s = &2)` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET]; INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `?e:real^N->bool. e IN l /\ aff_dim e = &1` THENL
   [(* a leaf *)
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_LEAF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC `l' = l DIFF {segment[u1:real^N,u2], {u1}}` THEN
    SUBGOAL_THEN
     `!p:real^N->bool. p IN l /\ ~(p = {}) <=>
                       p IN {u1} INSERT segment[u1,u2] INSERT {q | q IN l' /\ ~(q = {})}`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `p:real^N->bool` THEN EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM; IN_DIFF; NOT_IN_EMPTY] THEN
      SUBGOAL_THEN `~(segment[u1:real^N,u2] = {}) /\ ~({u1:real^N} = {})` MP_TAC THENL
       [REWRITE_TAC[SEGMENT_EQ_EMPTY; NOT_INSERT_EMPTY]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRB_COLLAPSE1 THEN
    EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~({u2:real^N} = segment[u1,u2]) /\ ~({u2:real^N} = {u1})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `(u1:real^N) IN {u2}` MP_TAC THENL
         [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]];
        UNDISCH_TAC `{u2:real^N} = {u1}` THEN REWRITE_TAC[SET_RULE
          `{a:A} = {b} <=> a = b`] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "l'" THEN SET_TAC[];
      EXPAND_TAC "l'" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET l0` THEN SET_TAC[];
      UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET l0` THEN
      UNDISCH_TAC `segment[u1:real^N,u2] IN l` THEN SET_TAC[];
      EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY] THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "l'" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `segment[u1:real^N,u2]`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "\\/"
                                  with Failure _ -> false)) (concl th) &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "GSPEC"
                                       with Failure _ -> false)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "IH" (MP_TAC o SPEC `l':(real^N->bool)->bool`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
        EXPAND_TAC "l'" THEN UNDISCH_TAC `segment[u1:real^N,u2] IN l` THEN SET_TAC[];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [EXPAND_TAC "l'" THEN MATCH_MP_TAC MOI_FRB_SUBCX_DEL1 THEN
          ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
          EXPAND_TAC "l'" THEN
          MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `segment[u1:real^N,u2]`;
                         `{u1:real^N}`] MOI_FRB_EULER_DELETE2) THEN
          ASM_REWRITE_TAC[NOT_INSERT_EMPTY; AFF_DIM_SING; AFF_DIM_SEGMENT] THEN
          ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; SIMP_TAC[]];
          EXPAND_TAC "l'" THEN MATCH_MP_TAC MOI_FRB_CONN_COLLAPSE1 THEN
          ASM_REWRITE_TAC[];
          EXISTS_TAC `u2:real^N` THEN EXPAND_TAC "l'" THEN
          REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  (* a single vertex *)
  SUBGOAL_THEN `!p:real^N->bool. p IN l /\ ~(p = {}) <=> p IN {{v}}`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `p:real^N->bool` THEN REWRITE_TAC[IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `aff_dim(p:real^N->bool) = &0` MP_TAC THENL
       [SUBGOAL_THEN `aff_dim(p:real^N->bool) <= &1 /\ ~(aff_dim p = &1)` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `p:real^N->bool` AFF_DIM_GE) THEN
        UNDISCH_TAC `~(p:real^N->bool = {})` THEN REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
        INT_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` SUBST_ALL_TAC) THEN
      REWRITE_TAC[SET_RULE `{x:real^N} = {y} <=> x = y`] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `moi_frb_conn (l:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_frb_conn] THEN DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM SET_TAC[]; SET_TAC[];
          DISCH_TAC THEN
          SUBGOAL_THEN `(v:real^N) IN {u | {u} IN l}` MP_TAC THENL
           [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_SING] THEN
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_SING; NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(?e:real^N->bool. e IN l /\ aff_dim e = &1)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `segment[x:real^N,y]` THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRB_FACE_BASE THEN
  EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* The main theorem DERIVED_NBHD_BALL_2.  A finite subcomplex l that is     *)
(* a PL ball of dimension at most 2 or a tree has dimension at most 2,      *)
(* chi = 1, a connected nonempty polyhedron, and the free-edge property of  *)
(* MOI_FRB_COLLAPSE_IND for all its subcomplexes: vacuous in dimension at   *)
(* most 1 (points, arcs by MOI_FGB_ARC_DIM, trees); for a disk by 2D        *)
(* invariance (SURF_INVARIANT of pc_moi_s28_trib applied to the faces of a  *)
(* 2-simplex: l is a combinatorial 2-manifold with nonempty boundary) and   *)
(* MOI_FRB_FREE_EDGE.  Then MOI_FRB_COLLAPSE_IND applies with l0 = l.       *)
(* ========================================================================= *)

(* 2D invariance (pc_moi_s28_tria/trib) at M = N.                           *)

let MOI_FRB_SURF_INVARIANT = prove
 (inst [`:N`,`:M`] MOI_S28_SURF_INVARIANT_BODY,
  ACCEPT_TAC(INST_TYPE [`:N`,`:M`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))));;

(* The faces of a 2-simplex: a combinatorial 2-manifold with boundary whose *)
(* boundary is nonempty.                                                    *)

let MOI_FRB_FACE_COMPLEX_CMWB2 = prove
 (`!k:real^N->bool.
        &2 simplex k ==> combinatorial_manifold_with_boundary 2 {f | f face_of k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING] THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_LINK] THEN DISJ2_TAC THEN
  MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN
  UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &2 + &1` THEN
  SUBGOAL_THEN `1 <= CARD(V:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC);;

let MOI_FRB_FACE_COMPLEX_SB = prove
 (`!k:real^N->bool. &2 simplex k ==> ~(surface_boundary {f | f face_of k} = {})`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `aff_dim(convex hull {a:real^N,b,c}) = &2 /\
                convex(convex hull {a:real^N,b,c})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_CONVEX_HULL; AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{a:real^N,b,c}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `a:real^N` THEN EXISTS_TAC `segment[a:real^N,b]` THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  SUBGOAL_THEN `segment[a:real^N,b] face_of convex hull {a,b,c}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{a:real^N,b,c}`; `segment[a:real^N,b]`]
      FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `{a:real^N,b}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  SUBGOAL_THEN `{r:real^N->bool | r face_of convex hull {a,b,c} /\ aff_dim r = &2 /\
                                  segment[a,b] SUBSET r} =
                {convex hull {a,b,c}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `convex hull {a:real^N,b,c}`]
        FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_REFL THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]];
    REWRITE_TAC[CARD_SING]]);;

(* A nonempty finite complex has a vertex.                                   *)

let MOI_FRB_HAS_VERTEX = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ ~(UNIONS l = {}) ==> ?v. {v} IN l`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; MESON_TAC[]]);;

(* Complexes of dimension at most 1: dimension at most 2, and the free-edge *)
(* hypothesis of MOI_FRB_COLLAPSE_IND holds vacuously (no triangles).       *)

let MOI_FRB_DIM1_FACTS = prove
 (`!l:(real^N->bool)->bool.
     (!s. s IN l ==> aff_dim s <= &1)
     ==> (!s. s IN l ==> aff_dim s <= &2) /\
         (!l'. simplicial_subcomplex l' l /\ (?tr. tr IN l' /\ aff_dim tr = &2)
               ==> ?e tr. e IN l' /\ aff_dim e = &1 /\ tr IN l' /\ aff_dim tr = &2 /\
                          e SUBSET tr /\ !r. r IN l' /\ e SUBSET r /\ ~(r = e) ==> r = tr)`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH `x:int <= &1 ==> x <= &2`) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (tr:real^N->bool) <= &1` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&1:int`)) (concl th))) THEN ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP (INT_ARITH `x:int <= &1 ==> ~(x = &2)`)) THEN
      ASM_REWRITE_TAC[]]]);;

(* A PL ball is connected and nonempty.                                      *)

let MOI_FRB_BALL_CONN = prove
 (`!(l:(real^N->bool)->bool) n.
     pl_ball n (UNIONS l) ==> connected (UNIONS l) /\ ~(UNIONS l = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN
    EXISTS_TAC `&n:int` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&n simplex ({}:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC]);;

(* A triangulated point: one vertex, no edges, chi = 1.                      *)

let MOI_FRB_BALL0_FACTS = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ pl_ball 0 (UNIONS l)
     ==> (!s. s IN l ==> aff_dim s <= &1) /\ complex_euler l = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?b:real^N. UNIONS l = {b}` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
    REWRITE_TAC[SIMPLEX_ZERO; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `(f:real^N->real^N) a` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `{b:real^N}`] AFF_DIM_SUBSET) THEN
    REWRITE_TAC[AFF_DIM_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) IN l` THEN
    UNDISCH_TAC `UNIONS l = {b:real^N}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH `x:int <= &0 ==> x <= &1`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FGB_CHI_DIM1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{u:real^N | {u} IN l} = {b} /\
                {e:real^N->bool | e IN l /\ aff_dim e = &1} = {}`
  (fun th -> REWRITE_TAC[th; CARD_SING; CARD_CLAUSES]) THENL
   [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(u:real^N) IN UNIONS l` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[IN_SING]];
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_HAS_VERTEX) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
      SUBGOAL_THEN `v:real^N = b` (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[]) THEN
      SUBGOAL_THEN `(v:real^N) IN UNIONS l` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[IN_SING]]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (e:real^N->bool) <= &0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* A triangulated arc: dimension at most 1 (MOI_FGB_ARC_DIM), chi = 1.       *)

let MOI_FRB_BALL1_FACTS = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ pl_ball 1 (UNIONS l)
     ==> (!s. s IN l ==> aff_dim s <= &1) /\ complex_euler l = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &1` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
    REWRITE_TAC[pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_ARC_DIM THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= &1 ==> x <= &2`) THEN ASM_SIMP_TAC[];
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

(* A triangulated disk: by 2D invariance (SURF_INVARIANT of pc_moi_s28_trib *)
(* on the faces of a 2-simplex) a combinatorial 2-manifold with nonempty   *)
(* boundary, so MOI_FRB_FREE_EDGE gives the free edges; chi = 1.            *)

let MOI_FRB_BALL2_FACTS = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ pl_ball 2 (UNIONS l)
     ==> (!s. s IN l ==> aff_dim s <= &2) /\
         (!l'. simplicial_subcomplex l' l /\ (?tr. tr IN l' /\ aff_dim tr = &2)
               ==> ?e tr. e IN l' /\ aff_dim e = &1 /\ tr IN l' /\ aff_dim tr = &2 /\
                          e SUBSET tr /\ !r. r IN l' /\ e SUBSET r /\ ~(r = e) ==> r = tr) /\
         complex_euler l = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
  REWRITE_TAC[pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE {q:real^N->bool | q face_of k}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
    EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (l:(real^N->bool)->bool)` THEN
    SIMP_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{q:real^N->bool | q face_of k}`; `l:(real^N->bool)->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRB_SURF_INVARIANT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FRB_FACE_COMPLEX_CMWB2]; STRIP_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_CMB2_DIM THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(surface_boundary (l:(real^N->bool)->bool) = {})` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `surface_boundary (l:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN MATCH_MP_TAC MOI_FRB_FACE_COMPLEX_SB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS (l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `2`] MOI_FRB_BALL_CONN) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRB_FREE_EDGE THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `l:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* The three ball cases together.                                            *)

let MOI_FRB_BALL_FACTS = prove
 (`!(l:(real^N->bool)->bool) n.
     simplicial_complex l /\ n <= 2 /\ pl_ball n (UNIONS l)
     ==> (!s. s IN l ==> aff_dim s <= &2) /\
         (!l'. simplicial_subcomplex l' l /\ (?tr. tr IN l' /\ aff_dim tr = &2)
               ==> ?e tr. e IN l' /\ aff_dim e = &1 /\ tr IN l' /\ aff_dim tr = &2 /\
                          e SUBSET tr /\ !r. r IN l' /\ e SUBSET r /\ ~(r = e) ==> r = tr) /\
         complex_euler l = &1 /\ connected (UNIONS l) /\ ~(UNIONS l = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:num`] MOI_FRB_BALL_CONN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n = 0 \/ n = 1 \/ n = 2` MP_TAC THENL
   [UNDISCH_TAC `n <= 2` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_BALL0_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_DIM1_FACTS) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_BALL1_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_DIM1_FACTS) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_BALL2_FACTS) THEN
    ASM_REWRITE_TAC[]]);;

(* A tree: chi = V - E = 1.                                                  *)

let MOI_FRB_TREE_FACTS = prove
 (`!l:(real^N->bool)->bool.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
     CARD {v | {v} IN l} = CARD {e | e IN l /\ aff_dim e = &1} + 1
     ==> complex_euler l = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FGB_CHI_DIM1) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) - x = &1`]);;

(* The reduction to the collapsing induction (l0 = l).                       *)

let MOI_FRB_NBHD_OF_FACTS = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     (!s. s IN l ==> aff_dim s <= &2) /\
     (!l'. simplicial_subcomplex l' l /\ (?tr. tr IN l' /\ aff_dim tr = &2)
           ==> ?e tr. e IN l' /\ aff_dim e = &1 /\ tr IN l' /\ aff_dim tr = &2 /\
                      e SUBSET tr /\ !r. r IN l' /\ e SUBSET r /\ ~(r = e) ==> r = tr) /\
     complex_euler l = &1 /\ connected (UNIONS l) /\ ~(UNIONS l = {})
     ==> pl_cell_with_boundary 3 (derived_nbhd t l) (derived_frontier t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[derived_frontier] THEN ASM_SIMP_TAC[MOI_FRB_NBHD_STARS] THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (l:(real^N->bool)->bool) l` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frb_conn (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRB_CONN_OF_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN l` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRB_HAS_VERTEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRB_COLLAPSE_IND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let DERIVED_NBHD_BALL_2 = prove
 (MOI_FND_DERIVED_NBHD_BALL_2,
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_FRB_NBHD_OF_FACTS THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `n:num`] MOI_FRB_BALL_FACTS) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_DIM1_FACTS) THEN
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FRB_TREE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

