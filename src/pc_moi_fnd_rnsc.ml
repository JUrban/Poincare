(* ========================================================================= *)
(* pc_moi_fnd_rnsc: second-derived neighbourhoods of simplices (Moise        *)
(* GTM 47, p.169, 23.11-23.12): the second-derived neighbourhood of a        *)
(* simplex of dimension at most 2 whose vertices are interior (links PL      *)
(* 2-spheres) is a PL 3-cell bounded by its frontier, and small PL 3-cells   *)
(* around such a simplex exist inside any relatively open set. Main theorems *)
(* (proving the statement terms of pc_moi_fnd_stmt2.ml):                     *)
(*   DERIVED_NBHD_SIMPLEX = MOI_FND_DERIVED_NBHD_SIMPLEX                     *)
(*   SIMPLEX_SMALL_CELL   = MOI_FND_SIMPLEX_SMALL_CELL                       *)
(* Notation in comments: K = barycentric subdivision of t, K' that of K,   *)
(* b(p) = simplex_barycentre p, D(r) = moi_fcl_dual K r, Dd(r) =            *)
(* moi_fcl_ldual K r (pc_moi_fnd_collar).  Route: the neighbourhood is the  *)
(* union of the closed stars D({b(p)}) in K' of the barycentres of the      *)
(* faces p of s, glued one at a time along dual 2-cells (MOI_S5V_CELL_UNION *)
(* of pc_moi_s35_cells); the frontier by invariance of domain; small cells  *)
(* by moving the derived points towards s (MOI_FTA_DERIVED_HOMEO).          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_stmt2.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_s35_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The derived neighbourhood of a simplex is the union of the               *)
(* closed stars in the second derived of the barycentres of its faces, and  *)
(* each of these stars is a PL 3-cell bounded by its link.                  *)
(* ========================================================================= *)

let MOI_FRS_NBHD_STARS = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ s IN t
     ==> derived_nbhd t {f | f face_of s} =
         UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                 p | p face_of s /\ ~(p = {})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{f:real^N->bool | f face_of s}`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FTA_BS_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N->bool. p face_of s /\ ~(p = {})
                ==> {simplex_barycentre p} IN barycentric_subdivision t /\
                    {simplex_barycentre p} IN
                    barycentric_subdivision {f:real^N->bool | f face_of s}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `{f:real^N->bool | f face_of s} SUBSET t` THEN
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
    SUBGOAL_THEN `INTERS g IN barycentric_subdivision {f:real^N->bool | f face_of s}`
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
          (barycentric_subdivision {f:real^N->bool | f face_of s})
          (barycentric_subdivision t)`) THEN
        REWRITE_TAC[moi_bar_chain; simplicial_subcomplex] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ASSUME `simplicial_subcomplex
        (barycentric_subdivision {f:real^N->bool | f face_of s})
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
    SUBGOAL_THEN `p face_of (s:real^N->bool) /\ ~(p = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `f0 SUBSET {f:real^N->bool | f face_of s}` THEN
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

let MOI_FRS_CSTAR_UNIONS = prove
 (`!(c:(real^N->bool)->bool) v.
     moi_bar_complex c
     ==> UNIONS (moi_fm3_cstar c v) = UNIONS {r | r IN c /\ v IN r}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fm3_cstar] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]]);;

let MOI_FRS_STAR_CELL = prove
 (`!(t:(real^N->bool)->bool) s p.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     p face_of s /\ ~(p = {})
     ==> {simplex_barycentre p} IN barycentric_subdivision t /\
         pl_cell_with_boundary 3
           (moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p})
           (moi_fcl_ldual (barycentric_subdivision t) {simplex_barycentre p})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `{simplex_barycentre (p:real^N->bool)} IN barycentric_subdivision t`
  ASSUME_TAC THENL [MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = simplex_barycentre (p:real^N->bool)` THEN
  SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision (barycentric_subdivision t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `{w:real^N}`]
      MOI_FTA_BARY_VERTEX) THEN
    ASM_REWRITE_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a extreme_point_of p` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN t /\ a IN s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{a:real^N} face_of p` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FACE_OF_SING]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex];
      ASM_MESON_TAC[extreme_point_of; FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 2 (UNIONS (simplicial_link
      (barycentric_subdivision (barycentric_subdivision t)) (w:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTERIOR_LINK_RETRIANGULATION THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `a:real^N`] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "w" THEN
    MATCH_MP_TAC MOI_FTA_BARY_OPEN_STAR THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`;
                 `w:real^N`] MOI_FTA_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `w:real^N`]
    MOI_FCL_LINK_BARY) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `w:real^N`]
    MOI_FCL_CSTAR_BARY) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`;
                 `w:real^N`] MOI_FRS_CSTAR_UNIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* Links in the boundary of a closed star.  For an edge e of a              *)
(* complex c at a vertex u (no faces of e strictly between {u} and e), the  *)
(* link of the barycentre of e in the boundary part of the closed star of u *)
(* in the barycentric subdivision is the link dual cell Dd(e).              *)
(* ========================================================================= *)

let MOI_FRS_EDGE_LINK = prove
 (`!(c:(real^N->bool)->bool) u e.
     moi_bar_complex c /\ {u} IN c /\ e IN c /\ u IN e /\ ~(e = {u}) /\
     (!t. t IN c /\ t SUBSET e /\ u IN t ==> t = {u} \/ t = e)
     ==> UNIONS (simplicial_link
                  {s | s IN moi_fm3_cstar (barycentric_subdivision c) u /\
                       s SUBSET moi_fcl_ldual c {u}}
                  (simplex_barycentre e)) =
         moi_fcl_ldual c e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_CSTAR_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{u:real^N}`] MOI_FCL_LDUAL_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FTA_BARY_SING] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(r:real^N->bool) IN moi_fm3_cstar (barycentric_subdivision c) u` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(q:real^N->bool) IN moi_fm3_cstar (barycentric_subdivision c) u` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^N->bool) IN g` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                     `e:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET g` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((e:real^N->bool) IN f)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(simplex_barycentre (e:real^N->bool) IN r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~({u:real^N} IN f)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((u:real^N) IN moi_fcl_ldual c {u})` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `!t:real^N->bool. t IN f ==> e SUBSET t /\ ~(t = e)`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET e \/ e SUBSET t` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `{u:real^N}`)) (concl th) &&
          can (find_term ((=) `e:real^N->bool`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ASM_MESON_TAC[]];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(f:(real^N->bool)->bool) = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c ((e:real^N->bool) INSERT f)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN e INSERT f ==> u IN t /\ {u} SUBSET t /\ ~(t = {u})`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT] THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET t /\ ~(t = e)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_INSERT];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_INSERT];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `e:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                 ((e:real^N->bool) INSERT f))` THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(e:real^N->bool) INSERT f` THEN ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `(e:real^N->bool) INSERT f` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* Two comparable distinct faces of s give an edge of the first derived.     *)

let MOI_FRS_BARY_EDGE = prove
 (`!(t:(real^N->bool)->bool) p1 p2.
     lf_simplicial_complex t /\ p1 IN t /\ p2 IN t /\ ~(p1 = {}) /\
     p1 SUBSET p2 /\ ~(p1 = p2)
     ==> segment[simplex_barycentre p1,simplex_barycentre p2] =
         convex hull (IMAGE simplex_barycentre {p1,p2}) /\
         moi_bar_chain t {p1,p2} /\
         segment[simplex_barycentre p1,simplex_barycentre p2] IN
           barycentric_subdivision t /\
         ~(simplex_barycentre p1 = simplex_barycentre p2) /\
         (!r. r IN barycentric_subdivision t /\
              r SUBSET segment[simplex_barycentre p1,simplex_barycentre p2] /\
              simplex_barycentre p1 IN r
              ==> r = {simplex_barycentre p1} \/
                  r = segment[simplex_barycentre p1,simplex_barycentre p2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[simplex_barycentre p1,simplex_barycentre p2] =
                convex hull (IMAGE simplex_barycentre {p1,p2:real^N->bool})`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; IMAGE_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {p1,p2:real^N->bool}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[barycentric_subdivision; IN_ELIM_THM] THEN
    EXISTS_TAC `{p1,p2:real^N->bool}` THEN
    ASM_MESON_TAC[moi_bar_chain];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p1:real^N->bool`; `p2:real^N->bool`]
      MOI_FTA_BARY_INJ) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[barycentric_subdivision; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain t (f:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_bar_chain]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET {p1,p2}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p1:real^N->bool) IN f` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `p1:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(p2:real^N->bool) IN f` THENL
     [DISJ2_TAC THEN
      SUBGOAL_THEN `f = {p1,p2:real^N->bool}` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM SET_TAC[];
      DISJ1_TAC THEN
      SUBGOAL_THEN `f = {p1:real^N->bool}` SUBST_ALL_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]]]);;

(* The barycentre of a simplex e at a vertex u is a vertex of the boundary  *)
(* part of the closed star of u in the barycentric subdivision.             *)

let MOI_FRS_BARY_IN_CSTAR = prove
 (`!(c:(real^N->bool)->bool) u e.
     moi_bar_complex c /\ {u} IN c /\ e IN c /\ u IN e /\ ~(e = {u})
     ==> {simplex_barycentre e} IN moi_fm3_cstar (barycentric_subdivision c) u /\
         simplex_barycentre e IN moi_fcl_ldual c {u}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c {e:real^N->bool}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_CSTAR_BARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    EXISTS_TAC `{e:real^N->bool}` THEN
    ASM_REWRITE_TAC[IN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{e:real^N->bool}` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; IN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[SING_SUBSET]]);;

(* The dual cell of such an edge is a PL 2-cell bounded by its link part.  *)

let MOI_FRS_EDGE_CELL = prove
 (`!(t:(real^N->bool)->bool) s p1 p2.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     p1 face_of s /\ p2 face_of s /\ ~(p1 = {}) /\ p1 SUBSET p2 /\ ~(p1 = p2)
     ==> pl_cell_with_boundary 2
           (moi_fcl_dual (barycentric_subdivision t)
              (segment[simplex_barycentre p1,simplex_barycentre p2]))
           (moi_fcl_ldual (barycentric_subdivision t)
              (segment[simplex_barycentre p1,simplex_barycentre p2]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p1:real^N->bool) IN t /\ p2 IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p1:real^N->bool`; `p2:real^N->bool`]
    MOI_FRS_BARY_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `p1:real^N->bool`]
    MOI_FRS_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w1 = simplex_barycentre (p1:real^N->bool)` THEN
  ABBREV_TAC `w2 = simplex_barycentre (p2:real^N->bool)` THEN
  ABBREV_TAC `K = barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  ABBREV_TAC `e:real^N->bool = segment[w1,w2]` THEN
  SUBGOAL_THEN `{w1:real^N} IN barycentric_subdivision K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `{w1:real^N}`] MOI_FTA_BARY_VERTEX) THEN
    ASM_REWRITE_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w1:real^N) IN e /\ ~(e = {w1})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N->bool. (w2:real^N) IN x`) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the link of b(e) in the boundary complex of the closed star of w1 *)
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w1:real^N`; `e:real^N->bool`]
    MOI_FRS_EDGE_LINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real^N->bool`)) (concl th) &&
      can (find_term ((=) `{w1:real^N}`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `C1 = moi_fm3_cstar (barycentric_subdivision K) (w1:real^N)` THEN
  SUBGOAL_THEN `FINITE (C1:(real^N->bool)->bool) /\ lf_simplicial_complex C1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision K:(real^N->bool)->bool`; `w1:real^N`]
      MOI_FTA_CSTAR_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C1" THEN REWRITE_TAC[moi_fm3_cstar] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (C1:(real^N->bool)->bool) = moi_fcl_dual K {w1}`
  ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w1:real^N`] MOI_FCL_CSTAR_BARY) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C1:(real^N->bool)->bool`; `moi_fcl_ldual K {w1:real^N}`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `C1:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (moi_fcl_ldual K (e:real^N->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 2 (boundary_complex C1:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre (e:real^N->bool)` o CONJUNCT2) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `boundary_complex C1 =
                  {s | s IN C1 /\ s SUBSET moi_fcl_ldual K {w1:real^N}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[boundary_complex] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w1:real^N`; `e:real^N->bool`]
      MOI_FRS_BARY_IN_CSTAR) THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fcl_ldual K (e:real^N->bool) = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `moi_fcl_ldual K (e:real^N->bool)`;
                 `simplex_barycentre (e:real^N->bool)`] MOI_FTA_CONE_CELL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Dual cells of chains of t meet in the dual cell of the union             *)
(* chain; the closed stars of the barycentres of faces of p lie in the open *)
(* star of each vertex of p; points there are interior manifold points.     *)
(* ========================================================================= *)

(* Members of the barycentric subdivision are hulls of barycentres of chains. *)

let MOI_FRS_IN_BSD = prove
 (`!(c:(real^N->bool)->bool) r.
     r IN barycentric_subdivision c <=>
     ?f. moi_bar_chain c f /\ r = convex hull (IMAGE simplex_barycentre f)`,
  REWRITE_TAC[barycentric_subdivision; IN_ELIM_THM; moi_bar_chain] THEN
  MESON_TAC[]);;

(* Dual cells (in the first derived of t) of simplices of chains of t: two  *)
(* of them meet in the dual cell of the union chain, or not at all.        *)

let MOI_FRS_DUAL_CHAIN_INTER = prove
 (`!(t:(real^N->bool)->bool) f g.
     moi_bar_complex t /\ moi_bar_chain t f /\ moi_bar_chain t g /\
     ~(f = {}) /\ ~(g = {})
     ==> moi_fcl_dual (barycentric_subdivision t)
           (convex hull (IMAGE simplex_barycentre f)) INTER
         moi_fcl_dual (barycentric_subdivision t)
           (convex hull (IMAGE simplex_barycentre g)) =
         if moi_bar_chain t (f UNION g)
         then moi_fcl_dual (barycentric_subdivision t)
                (convex hull (IMAGE simplex_barycentre (f UNION g)))
         else {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_COMPLEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FCL_DUAL_INTER] THEN
  SUBGOAL_THEN
   `!u. u IN barycentric_subdivision t /\
        convex hull (IMAGE simplex_barycentre f) SUBSET u /\
        convex hull (IMAGE simplex_barycentre g) SUBSET u
        ==> ?h. moi_bar_chain t h /\ f UNION g SUBSET h /\
                u = convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN REWRITE_TAC[MOI_FRS_IN_BSD] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      MATCH_MP_TAC(CONJUNCT1(SPEC_ALL MOI_FCL_DUAL_MONO)) THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                   ((f:(real^N->bool)->bool) UNION g))` THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_FRS_IN_BSD] THEN ASM_MESON_TAC[];
        REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN ASM SET_TAC[];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]];
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~moi_bar_chain t ((f:(real^N->bool)->bool) UNION g)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* The closed star of b(p) in the second derived lies in the open star of  *)
(* every vertex a of p in t: each of its points is in the relative interior *)
(* of a simplex of t containing p.                                          *)

let MOI_FRS_DUAL_OPEN_STAR = prove
 (`!(t:(real^N->bool)->bool) p a.
     lf_simplicial_complex t /\ p IN t /\ ~(p = {}) /\ a IN p
     ==> moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} SUBSET
         UNIONS {r | r IN t /\ a IN r} DIFF UNIONS (simplicial_link t a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `f:(real^N->bool)->bool`; `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool) /\
                ~(g = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`; `x:real^N`] MOI_BAR_CHAIN_RI_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tau:real^N->bool = UNIONS g` THEN
  SUBGOAL_THEN `simplex_barycentre (p:real^N->bool) IN tau /\
                tau IN barycentric_subdivision t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `{simplex_barycentre (p:real^N->bool)} SUBSET tau` MP_TAC THENL
       [UNDISCH_TAC `!t:real^N->bool. t IN f ==> {simplex_barycentre p} SUBSET t` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
        SET_TAC[]];
      ASM_MESON_TAC[moi_bar_chain; SUBSET]];
    ALL_TAC] THEN
  UNDISCH_TAC `tau IN barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_FRS_IN_BSD] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^N->bool) IN h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                   `p:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(h:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_RI_MAX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `M:real^N->bool = UNIONS h` THEN
  SUBGOAL_THEN `(M:real^N->bool) IN t /\ (a:real^N) IN M /\ x IN M`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ASM_MESON_TAC[SUBSET];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `M:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `rho:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(rho INTER M:real^N->bool) face_of M` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `rho INTER M:real^N->bool = M` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rho INTER M:real^N->bool`; `M:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* moi_fmb_mint is local: a subset containing a relatively open            *)
(* neighbourhood of the point.                                               *)

let MOI_FRS_MINT_LOCAL = prove
 (`!(X:real^N->bool) Y O x.
     Y SUBSET X /\ moi_fmb_mint Y x /\
     open_in (subtopology euclidean X) O /\ x IN O /\ O SUBSET Y
     ==> moi_fmb_mint X x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `V:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^N->real^3`
          (X_CHOOSE_TAC `k:real^3->real^N`))))))) STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U INTER O:real^N->bool`;
                        `IMAGE (h:real^N->real^3) (U INTER O)`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U) (U INTER O:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_OPEN_IN_SUBSET_INTER THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean Y) (U:real^N->bool)` THEN
    UNDISCH_TAC `open_in (subtopology euclidean X) (O:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g1 INTER g2:real^N->bool` THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^N->real^3`; `k:real^3->real^N`; `U:real^N->bool`;
                   `V:real^3->bool`; `U INTER O:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `k:real^3->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `V:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (U:real^N->bool,V:real^3->bool) (h,k)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

(* Points of the open star of a vertex with a PL 2-sphere link have a      *)
(* neighbourhood in UNIONS t homeomorphic to an open subset of real^3.     *)

let MOI_FRS_OPEN_STAR_MINT = prove
 (`!(t:(real^N->bool)->bool) a x.
     lf_simplicial_complex t /\ {a} IN t /\
     pl_sphere 2 (UNIONS (simplicial_link t a)) /\
     x IN UNIONS {r | r IN t /\ a IN r} DIFF UNIONS (simplicial_link t a)
     ==> moi_fmb_mint (UNIONS t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `a:real^N`] MOI_FTA_CSTAR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = {s | ?r. r IN t /\ (a:real^N) IN r /\ s face_of r}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `a:real^N`] MOI_FTA_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `UNIONS st:real^N->bool`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`st:(real^N->bool)->bool`;
                 `UNIONS (simplicial_link t (a:real^N))`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS st /\ ~(x IN UNIONS (simplicial_link t a))`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_MINT_CB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FTA_LF_LOCAL_STAR) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_FRS_MINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`UNIONS st:real^N->bool`; `UNIONS t INTER U:real^N->bool`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex st (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^N) IN r` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `?rho:real^N->bool. rho IN t /\ a IN rho /\ x IN rho`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((x:real^N) IN UNIONS (simplicial_link t a))` THEN
    REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    EXISTS_TAC `r INTER rho:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex];
      EXISTS_TAC `rho:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[lf_simplicial_complex]];
    ALL_TAC] THEN
  EXPAND_TAC "st" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]);;

(* ========================================================================= *)
(* Invariance of domain tools.  moi_fmb_mint restricts to open              *)
(* neighbourhoods; a PL 3-cell triangulated inside the manifold part of     *)
(* UNIONS t has its frontier relative to UNIONS t as boundary.              *)
(* ========================================================================= *)

(* moi_fmb_mint passes to relatively open neighbourhoods.                   *)

let MOI_FRS_MINT_RESTRICT = prove
 (`!(X:real^N->bool) U x.
     moi_fmb_mint X x /\ open_in (subtopology euclidean X) U /\ x IN U
     ==> moi_fmb_mint U x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U1:real^N->bool` (X_CHOOSE_THEN `V:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^N->real^3`
          (X_CHOOSE_TAC `k:real^3->real^N`))))))) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`U1 INTER U:real^N->bool`;
                        `IMAGE (h:real^N->real^3) (U1 INTER U)`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U1) (U1 INTER U:real^N->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean X) (U:real^N->bool)` THEN
    UNDISCH_TAC `open_in (subtopology euclidean X) (U1:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean X) (U:real^N->bool)` THEN
    UNDISCH_TAC `open_in (subtopology euclidean X) (U1:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^N->real^3`; `k:real^3->real^N`; `U1:real^N->bool`;
                   `V:real^3->bool`; `U1 INTER U:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `k:real^3->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U1:real^N->bool`; `V:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (U1:real^N->bool,V:real^3->bool) (h,k)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

(* A PL 3-cell triangulated inside the manifold part of UNIONS t: its       *)
(* boundary is its frontier relative to UNIONS t (invariance of domain).   *)

let MOI_FRS_CELL_FRONTIER = prove
 (`!(t:(real^N->bool)->bool) c B.
     FINITE c /\ lf_simplicial_complex c /\ UNIONS c SUBSET UNIONS t /\
     pl_cell_with_boundary 3 (UNIONS c) B /\
     (!x. x IN UNIONS c ==> moi_fmb_mint (UNIONS t) x)
     ==> (subtopology euclidean (UNIONS t)) frontier_of (UNIONS c) = B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `B:real^N->bool`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_UNIONS_CLOSED_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(subtopology euclidean (UNIONS t)) closure_of (UNIONS c) =
                UNIONS c:real^N->bool` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    SUBGOAL_THEN `UNIONS t INTER UNIONS c = UNIONS c:real^N->bool` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_CB_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[frontier_of] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_DIFF] THEN
  ASM_CASES_TAC `(x:real^N) IN UNIONS c` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS t) (x:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN (subtopology euclidean (UNIONS t)) interior_of
                                 (UNIONS c))` THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`UNIONS t:real^N->bool`; `UNIONS c:real^N->bool`; `x:real^N`]
      MOI_FCL_MINT_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_MINT_CB) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MESON_TAC[]];
    DISCH_TAC THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:real^N->bool`; `x:real^N`]
      MOI_FCL_MINT_NOT_CB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRS_MINT_RESTRICT THEN
      EXISTS_TAC `UNIONS t:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Gluing closed stars. Unions of closed stars of vertices of K in K' are    *)
(* triangulated; adding one star along a 2-cell keeps a 3-cell whose         *)
(* boundary is its frontier (MOI_S5V_CELL_UNION and the frontier lemma       *)
(* above); the first star.                                                   *)
(* ========================================================================= *)

(* Unions of closed stars of vertices of K in the barycentric subdivision   *)
(* of K are triangulated by finite subcomplexes of it.                      *)

let MOI_FRS_STARS_COMPLEX = prove
 (`!(K:(real^N->bool)->bool) W.
     lf_simplicial_complex K /\ FINITE W /\ (!v. v IN W ==> {v} IN K)
     ==> FINITE (UNIONS {moi_fm3_cstar (barycentric_subdivision K) v | v | v IN W}) /\
         lf_simplicial_complex
           (UNIONS {moi_fm3_cstar (barycentric_subdivision K) v | v | v IN W}) /\
         UNIONS (UNIONS {moi_fm3_cstar (barycentric_subdivision K) v | v | v IN W}) =
         UNIONS {moi_fcl_dual K {v} | v | v IN W} /\
         UNIONS {moi_fcl_dual K {v} | v | v IN W} SUBSET UNIONS K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `K:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN W
                ==> FINITE (moi_fm3_cstar (barycentric_subdivision K) v) /\
                    simplicial_subcomplex (moi_fm3_cstar (barycentric_subdivision K) v)
                                          (barycentric_subdivision K) /\
                    UNIONS (moi_fm3_cstar (barycentric_subdivision K) v) =
                    moi_fcl_dual K {v}`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision K` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `{v:real^N}`] MOI_FTA_BARY_VERTEX) THEN
      ASM_SIMP_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision K:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_CSTAR_COMPLEX) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_CSTAR_BARY) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_fm3_cstar] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE];
    MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN
    EXISTS_TAC `barycentric_subdivision K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      ASM_MESON_TAC[simplicial_subcomplex]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^N) IN moi_fcl_dual K {v}` THEN
        REWRITE_TAC[GSYM th; IN_UNIONS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(last(CONJUNCTS th))] THEN
      MP_TAC(el 1 (CONJUNCTS th))) THEN
    REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[]]);;

(* Distinct closed stars of vertices of K in K' meet inside the link part   *)
(* of each.                                                                   *)

let MOI_FRS_STAR_INTER_LDUAL = prove
 (`!(K:(real^N->bool)->bool) v w.
     moi_bar_complex K /\ ~(v = w)
     ==> moi_fcl_dual K {v} INTER moi_fcl_dual K {w} SUBSET moi_fcl_ldual K {w}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FCL_DUAL_INTER; MOI_FCL_LDUAL_EQ] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* One gluing step: adding the closed star of a new vertex along a 2-cell. *)

let MOI_FRS_GLUE_STEP = prove
 (`!(K:(real^N->bool)->bool) W w A jA.
     lf_simplicial_complex K /\ FINITE W /\ (!v. v IN W ==> {v} IN K) /\
     {w} IN K /\ ~(w IN W) /\
     (!x. x IN UNIONS {moi_fcl_dual K {v} | v | v IN w INSERT W}
          ==> moi_fmb_mint (UNIONS K) x) /\
     pl_cell_with_boundary 3 (UNIONS {moi_fcl_dual K {v} | v | v IN W})
       ((subtopology euclidean (UNIONS K)) frontier_of
        (UNIONS {moi_fcl_dual K {v} | v | v IN W})) /\
     pl_cell_with_boundary 3 (moi_fcl_dual K {w}) (moi_fcl_ldual K {w}) /\
     UNIONS {moi_fcl_dual K {v} | v | v IN W} INTER moi_fcl_dual K {w} = A /\
     pl_cell_with_boundary 2 A jA
     ==> pl_cell_with_boundary 3 (UNIONS {moi_fcl_dual K {v} | v | v IN w INSERT W})
           ((subtopology euclidean (UNIONS K)) frontier_of
            (UNIONS {moi_fcl_dual K {v} | v | v IN w INSERT W}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS {moi_fcl_dual K {v} | v | (v:real^N) IN W}` THEN
  SUBGOAL_THEN `UNIONS {moi_fcl_dual K {v} | v | (v:real^N) IN w INSERT W} =
                U UNION moi_fcl_dual K {w}` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun tm -> is_const tm &&
                              fst(dest_const tm) = "moi_fmb_mint")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* A lies in the link part of the new star *)
  SUBGOAL_THEN `(A:real^N->bool) SUBSET moi_fcl_ldual K {w}` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "U" THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
      MOI_FRS_STAR_INTER_LDUAL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `{w:real^N}`] MOI_FCL_LDUAL_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FTA_BARY_SING] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fcl_dual K {w:real^N} SUBSET UNIONS K /\
                (U:real^N->bool) SUBSET UNIONS K` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(w:real^N) INSERT W`]
      MOI_FRS_STARS_COMPLEX) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* A lies in the frontier of U *)
  SUBGOAL_THEN `(A:real^N->bool) SUBSET
                (subtopology euclidean (UNIONS K)) frontier_of U`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN U /\ z IN moi_fcl_ldual K {w} /\ ~(z = w)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[w:real^N,z] SUBSET moi_fcl_dual K {w}` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `{w:real^N}`] MOI_FCL_DUAL_CONE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FTA_BARY_SING] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[frontier_of; IN_DIFF] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (UNIONS K:real^N->bool)`; `U:real^N->bool`]
        CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_FTA_IN_INTERIOR_SUB] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`G:real^N->bool`; `segment(w:real^N,z)`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[CLOSURE_SEGMENT] THEN
    SUBGOAL_THEN `~(w:real^N = z)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> ~(p <=> q)`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN segment[w,z]` ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN moi_fcl_ldual K {w}` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN U` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
        MOI_FRS_STAR_INTER_LDUAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^N = z` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^N) IN segment(w,z)` THEN REWRITE_TAC[ENDS_NOT_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `(subtopology euclidean (UNIONS K)) frontier_of (U:real^N->bool)`;
                 `moi_fcl_dual K {w:real^N}`; `moi_fcl_ldual K {w:real^N}`;
                 `A:real^N->bool`; `jA:real^N->bool`] MOI_S5V_CELL_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(w:real^N) INSERT W`]
    MOI_FRS_STARS_COMPLEX) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                 `UNIONS {moi_fm3_cstar (barycentric_subdivision K) v |
                          v | (v:real^N) IN w INSERT W}`;
                 `((subtopology euclidean (UNIONS K)) frontier_of (U:real^N->bool) UNION
                   moi_fcl_ldual K {w}) DIFF (A DIFF jA)`] MOI_FRS_CELL_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* The first star: a closed star which is a 3-cell bounded by its link part *)
(* has its frontier as boundary.                                             *)

let MOI_FRS_GLUE_BASE = prove
 (`!(K:(real^N->bool)->bool) w.
     lf_simplicial_complex K /\ {w} IN K /\
     (!x. x IN moi_fcl_dual K {w} ==> moi_fmb_mint (UNIONS K) x) /\
     pl_cell_with_boundary 3 (moi_fcl_dual K {w}) (moi_fcl_ldual K {w})
     ==> pl_cell_with_boundary 3 (UNIONS {moi_fcl_dual K {v} | v | v IN {w}})
           ((subtopology euclidean (UNIONS K)) frontier_of
            (UNIONS {moi_fcl_dual K {v} | v | v IN {w}}))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {moi_fcl_dual K {v} | v | (v:real^N) IN {w}} =
                moi_fcl_dual K {w}` SUBST1_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_1]; ALL_TAC] THEN
  MP_TAC(ISPEC `K:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `{w:real^N}`] MOI_FTA_BARY_VERTEX) THEN
    ASM_SIMP_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision K:(real^N->bool)->bool`; `w:real^N`]
    MOI_FTA_CSTAR_COMPLEX) THEN
  ASM_REWRITE_TAC[GSYM moi_fm3_cstar] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`] MOI_FCL_CSTAR_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                 `moi_fm3_cstar (barycentric_subdivision K) (w:real^N)`;
                 `moi_fcl_ldual K {w:real^N}`] MOI_FRS_CELL_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `UNIONS {s | s IN barycentric_subdivision K /\ (w:real^N) IN s} =
                 moi_fcl_dual K {w}` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision K) = UNIONS (K:(real^N->bool)->bool)` THEN
    SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Full flags of a triangle.  A triangle at an interior vertex              *)
(* lies in exactly two tetrahedra; the simplices of the first derived       *)
(* properly containing the simplex of a full flag {v} < e < s are the two  *)
(* simplices of the chains with one of these tetrahedra added.              *)
(* ========================================================================= *)

(* Cardinalities of small sets of distinct points.                          *)

let MOI_FRS_CARD3 = prove
 (`!a b c:real^N. ~(a = b) /\ ~(a = c) /\ ~(b = c) ==> CARD {a,b,c} = 3`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_FRS_CARD4 = prove
 (`!a b c d:real^N.
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> CARD {a,b,c,d} = 4`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* A triangle at a vertex whose link is a PL 2-sphere lies in exactly two  *)
(* tetrahedra of t, and in no other simplex of t but itself.               *)

let MOI_FRS_TWO_TETS = prove
 (`!(t:(real^N->bool)->bool) v0 v1 v2.
     lf_simplicial_complex t /\ convex hull {v0,v1,v2} IN t /\
     ~affine_dependent {v0,v1,v2} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\ {v0} IN t /\
     pl_sphere 2 (UNIONS (simplicial_link t v0))
     ==> ?X1 X2. ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\
                 aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
                 convex hull {v0,v1,v2} SUBSET X1 /\
                 convex hull {v0,v1,v2} SUBSET X2 /\
                 (!X. X IN t /\ convex hull {v0,v1,v2} SUBSET X /\
                      ~(X = convex hull {v0,v1,v2})
                      ==> X = X1 \/ X = X2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v0:real^N`] MOI_FTA_CSTAR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `C = {s | ?r. r IN t /\ (v0:real^N) IN r /\ s face_of r}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v0:real^N`] MOI_FTA_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `UNIONS C:real^N->bool`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:(real^N->bool)->bool`;
                 `UNIONS (simplicial_link t (v0:real^N))`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s:real^N->bool = convex hull {v0,v1,v2}` THEN
  SUBGOAL_THEN `(s:real^N->bool) IN C /\ (v0:real^N) IN s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v0:real^N) IN s` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:(real^N->bool)->bool`; `v0:real^N`; `v1:real^N`; `v2:real^N`]
    MOI_FRN_TRIANGLE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(C:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (convex hull {v0,v1,v2,u1:real^N}) = &3 /\
                aff_dim (convex hull {v0,v1,v2,u2:real^N}) = &3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{v0,v1,v2,u1:real^N}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `{v0,v1,v2,u2:real^N}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`] MOI_FRS_CARD4) THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`] MOI_FRS_CARD4) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (s:real^N->bool) = &2` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{v0,v1,v2:real^N}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`] MOI_FRS_CARD3) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0,v1,v2,u1:real^N} IN t /\
                convex hull {v0,v1,v2,u2:real^N} IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`convex hull {v0,v1,v2,u1:real^N}`;
                        `convex hull {v0,v1,v2,u2:real^N}`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET convex hull {v0,v1,v2,u1} /\
                s SUBSET convex hull {v0,v1,v2,u2}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(v0:real^N) IN complex_boundary C` MP_TAC THENL
     [REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{r | r IN C /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r} =
                    {convex hull {v0,v1,v2,u1}}`
      (fun th -> REWRITE_TAC[th; CARD_SING]) THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
       [STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun tm -> try fst(dest_const tm) = "aff_dim"
                                    with Failure _ -> false)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
      MESON_TAC[]];
    X_GEN_TAC `X:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(X:real^N->bool) IN C` ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `X:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "aff_dim"
                                with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH `!x:int. x <= &3 /\ &2 < x ==> x = &3`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CM_WB_DIM];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `aff_dim(s:real^N->bool)`)) THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      SUBGOAL_THEN `s = s INTER (X:real^N->bool)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[lf_simplicial_complex]]]);;

(* Two segments from q to points p, r of a set met once by each ray from q *)
(* meet only in q.                                                           *)

let MOI_FRS_SEG_SEG = prove
 (`!(q:real^N) p r X.
     p IN X /\ r IN X /\ ~(q IN X) /\ ~(p = r) /\
     (!x y. x IN X /\ y IN X /\ y IN segment[q,x] ==> y = x)
     ==> segment[p,q] INTER segment[q,r] = {q}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SING_SUBSET; IN_INTER; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `u = &1` THENL
   [UNDISCH_TAC `y:real^N = (&1 - u) % p + u % q` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `w = &0` THENL
   [UNDISCH_TAC `y:real^N = (&1 - w) % q + w % r` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) % (p - q:real^N) = w % (r - q)` ASSUME_TAC THENL
   [UNDISCH_TAC `y:real^N = (&1 - u) % p + u % q` THEN
    UNDISCH_TAC `y:real^N = (&1 - w) % q + w % r` THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = &1 - u` THEN
  SUBGOAL_THEN `&0 < v /\ &0 < w` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `v <= w \/ w <= v`) THENL
   [SUBGOAL_THEN `(r:real^N) = p` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
      EXISTS_TAC `v / w` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      SUBGOAL_THEN `r:real^N = q + inv w % (w % (r - q))` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `w % (r - q:real^N)`)) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN
      REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC;
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `(p:real^N) = r` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
      EXISTS_TAC `w / v` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      SUBGOAL_THEN `p:real^N = q + inv v % (v % (p - q))` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN
      REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

(* In a complex, a simplex comparable with every member of a flag          *)
(* p0 < p1 < p2 of dimensions 0, 1, 2 and not in the flag contains p2      *)
(* properly.                                                                 *)

let MOI_FRS_FLAG_EXTRA = prove
 (`!(t:(real^N->bool)->bool) p0 p1 p2 X.
     lf_simplicial_complex t /\ p0 IN t /\ p1 IN t /\ p2 IN t /\ X IN t /\
     aff_dim p0 = &0 /\ aff_dim p1 = &1 /\ aff_dim p2 = &2 /\
     p0 SUBSET p1 /\ p1 SUBSET p2 /\ ~(X = {}) /\
     (X SUBSET p0 \/ p0 SUBSET X) /\ (X SUBSET p1 \/ p1 SUBSET X) /\
     (X SUBSET p2 \/ p2 SUBSET X) /\
     ~(X = p0) /\ ~(X = p1) /\ ~(X = p2)
     ==> p2 SUBSET X`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!Y Z:real^N->bool. Y IN t /\ Z IN t /\ Y SUBSET Z /\ ~(Y = Z)
                ==> aff_dim Y < aff_dim Z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    SUBGOAL_THEN `Y = Y INTER (Z:real^N->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= aff_dim (X:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_POS_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `p2:real^N->bool`)) (concl th))) THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `aff_dim (X:real^N->bool) < &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `p1:real^N->bool`)) (concl th))) THENL
   [SUBGOAL_THEN `aff_dim (X:real^N->bool) < &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (X:real^N->bool) = &0` MP_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `aff_dim (p0:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` SUBST_ALL_TAC) THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `aff_dim (p1:real^N->bool) < aff_dim (X:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_INT_ARITH_TAC]]);;

(* In a complex, a simplex properly inside another has smaller dimension. *)

let MOI_FRS_PROPER_DIM = prove
 (`!(t:(real^N->bool)->bool) Y Z.
     lf_simplicial_complex t /\ Y IN t /\ Z IN t /\ Y SUBSET Z /\ ~(Y = Z)
     ==> aff_dim Y < aff_dim Z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `Y = Y INTER (Z:real^N->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]]);;

(* The simplices of the first derived properly containing the simplex T of *)
(* a full flag p0 < p1 < p2 of a triangle on exactly two tetrahedra X1, X2: *)
(* the two simplices of the chains with X1 or X2 added.                     *)

let MOI_FRS_FLAG_COFACES = prove
 (`!(t:(real^N->bool)->bool) p0 p1 p2 X1 X2 u.
     lf_simplicial_complex t /\ moi_bar_chain t {p0,p1,p2} /\
     aff_dim p0 = &0 /\ aff_dim p1 = &1 /\ aff_dim p2 = &2 /\
     p0 SUBSET p1 /\ p1 SUBSET p2 /\
     ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\ aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
     p2 SUBSET X1 /\ p2 SUBSET X2 /\
     (!X. X IN t /\ p2 SUBSET X /\ ~(X = p2) ==> X = X1 \/ X = X2) /\
     u IN barycentric_subdivision t /\
     convex hull (IMAGE simplex_barycentre {p0,p1,p2}) SUBSET u /\
     ~(u = convex hull (IMAGE simplex_barycentre {p0,p1,p2}))
     ==> u = convex hull (IMAGE simplex_barycentre {p0,p1,p2,X1}) \/
         u = convex hull (IMAGE simplex_barycentre {p0,p1,p2,X2})`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `u IN barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_FRS_IN_BSD] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{p0,p1,p2:real^N->bool} SUBSET G` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^N->bool. X IN G /\ ~(X IN {p0,p1,p2}) ==> X = X1 \/ X = X2`
  ASSUME_TAC THENL
   [X_GEN_TAC `X:real^N->bool` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `X1:real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `G:(real^N->bool)->bool`)) (concl th)))) THEN
    MP_TAC(ASSUME `moi_bar_chain t (G:(real^N->bool)->bool)`) THEN
    MP_TAC(ASSUME `moi_bar_chain t {p0,p1,p2:real^N->bool}`) THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chG")))) THEN
    SUBGOAL_THEN `(X:real^N->bool) IN t /\ ~(X = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p0:real^N->bool) IN G /\ p1 IN G /\ p2 IN G` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{p0,p1,p2:real^N->bool} SUBSET G` THEN
      REWRITE_TAC[INSERT_SUBSET] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRS_FLAG_EXTRA THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `p0:real^N->bool`;
                          `p1:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    USE_THEN "chG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(X1 SUBSET X2:real^N->bool) /\ ~(X2 SUBSET X1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
        MOI_FRS_PROPER_DIM);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `X2:real^N->bool`; `X1:real^N->bool`]
        MOI_FRS_PROPER_DIM)] THEN
    ASM_REWRITE_TAC[INT_LT_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(G = {p0,p1,p2:real^N->bool})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?X:real^N->bool. X IN G /\ ~(X IN {p0,p1,p2})` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `G = (X:real^N->bool) INSERT {p0,p1,p2}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `Y:real^N->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(Y:real^N->bool) IN {p0,p1,p2}` THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INSERT] THEN DISJ1_TAC THEN
      SUBGOAL_THEN `((Y:real^N->bool) = X1 \/ Y = X2) /\ (X = X1 \/ X = X2)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ASSUME `moi_bar_chain t (G:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[moi_bar_chain] THEN
      DISCH_THEN(MP_TAC o SPECL [`X:real^N->bool`; `Y:real^N->bool`] o
        last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N->bool. Z INSERT {p0,p1,p2} = {p0,p1,p2,Z}`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^N->bool) = X1 \/ X = X2` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* A nonempty set of members of {a,b} not containing both is {a} or {b}.   *)

let MOI_FRS_PAIR_CASES = prove
 (`!(ff:A->bool) a b.
     ~(ff = {}) /\ (!u. u IN ff ==> u = a \/ u = b) /\ ~(a IN ff /\ b IN ff)
     ==> ff = {a} \/ ff = {b}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:A) IN ff` THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_SING] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

(* The dual cell of the simplex T of a full flag of a triangle on exactly  *)
(* two tetrahedra is an arc: two segments from b(T) to the barycentres of  *)
(* the two simplices of the first derived containing T.                    *)

let MOI_FRS_FLAG_ARC = prove
 (`!(t:(real^N->bool)->bool) p0 p1 p2 X1 X2.
     lf_simplicial_complex t /\ moi_bar_chain t {p0,p1,p2} /\
     aff_dim p0 = &0 /\ aff_dim p1 = &1 /\ aff_dim p2 = &2 /\
     p0 SUBSET p1 /\ p1 SUBSET p2 /\
     ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\ aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
     p2 SUBSET X1 /\ p2 SUBSET X2 /\
     (!X. X IN t /\ p2 SUBSET X /\ ~(X = p2) ==> X = X1 \/ X = X2)
     ==> moi_fcl_dual (barycentric_subdivision t)
           (convex hull (IMAGE simplex_barycentre {p0,p1,p2})) =
         segment[simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X1})),
                 simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2}))] UNION
         segment[simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2})),
                 simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X2}))] /\
         ~(simplex_barycentre (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X1})) =
           simplex_barycentre (convex hull (IMAGE simplex_barycentre {p0,p1,p2}))) /\
         ~(simplex_barycentre (convex hull (IMAGE simplex_barycentre {p0,p1,p2})) =
           simplex_barycentre (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X2}))) /\
         segment[simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X1})),
                 simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2}))] INTER
         segment[simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2})),
                 simplex_barycentre
                   (convex hull (IMAGE simplex_barycentre {p0,p1,p2,X2}))] =
         {simplex_barycentre (convex hull (IMAGE simplex_barycentre {p0,p1,p2}))}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MAP_EVERY ASSUME_TAC (CONJUNCTS th) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `K = barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  ABBREV_TAC `tf = convex hull (IMAGE simplex_barycentre {p0,p1,p2:real^N->bool})` THEN
  ABBREV_TAC `tau1 = convex hull (IMAGE simplex_barycentre {p0,p1,p2,X1:real^N->bool})` THEN
  ABBREV_TAC `tau2 = convex hull (IMAGE simplex_barycentre {p0,p1,p2,X2:real^N->bool})` THEN
  (* the chains *)
  SUBGOAL_THEN `!X:real^N->bool. X IN t /\ aff_dim X = &3 /\ p2 SUBSET X
                ==> moi_bar_chain t {p0,p1,p2,X} /\ ~(X IN {p0,p1,p2})`
  ASSUME_TAC THENL
   [X_GEN_TAC `X:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ASSUME `moi_bar_chain t {p0,p1,p2:real^N->bool}`) THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(X:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(X:real^N->bool = p0) /\ ~(X = p1) /\ ~(X = p2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {p0,p1,p2,X1:real^N->bool} /\
                ~(X1 IN {p0,p1,p2}) /\
                moi_bar_chain t {p0,p1,p2,X2:real^N->bool} /\
                ~(X2 IN {p0,p1,p2})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tf IN K /\ tau1 IN K /\ (tau2:real^N->bool) IN K` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "tf"; "tau1"; "tau2"] THEN
    REWRITE_TAC[MOI_FRS_IN_BSD] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tf:real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "tf" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tau1:real^N->bool = {}) /\ ~(tau2:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tau1"; "tau2"] THEN
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  (* containments between the three simplices *)
  SUBGOAL_THEN `tf SUBSET tau1 /\ ~(tf = tau1) /\ tf SUBSET tau2 /\ ~(tf = tau2) /\
                ~(tau1 SUBSET tau2) /\ ~(tau2 SUBSET (tau1:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tf"; "tau1"; "tau2"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1,p2:real^N->bool}`;
                     `{p0,p1,p2,X1:real^N->bool}`] MOI_FTA_HULL_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1,p2:real^N->bool}`;
                     `{p0,p1,p2,X2:real^N->bool}`] MOI_FTA_HULL_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1,p2,X1:real^N->bool}`;
                     `{p0,p1,p2,X2:real^N->bool}`] MOI_FTA_HULL_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1,p2,X2:real^N->bool}`;
                     `{p0,p1,p2,X1:real^N->bool}`] MOI_FTA_HULL_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the link part of the dual cell of tf *)
  SUBGOAL_THEN `moi_fcl_ldual K tf =
                {simplex_barycentre tau1, simplex_barycentre (tau2:real^N->bool)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `ff:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `!u:real^N->bool. u IN ff ==> u = tau1 \/ u = tau2`
      ASSUME_TAC THENL
       [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
        MAP_EVERY EXPAND_TAC ["tau1"; "tau2"] THEN
        MATCH_MP_TAC MOI_FRS_FLAG_COFACES THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MP_TAC(ASSUME `moi_bar_chain K (ff:(real^N->bool)->bool)`) THEN
          REWRITE_TAC[moi_bar_chain; SUBSET] THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `ff:(real^N->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `ff = {tau1:real^N->bool} \/ ff = {tau2}` MP_TAC THENL
       [MP_TAC(ASSUME `moi_bar_chain K (ff:(real^N->bool)->bool)`) THEN
        REWRITE_TAC[moi_bar_chain] THEN
        DISCH_THEN(MP_TAC o SPECL [`tau1:real^N->bool`; `tau2:real^N->bool`] o
          last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MATCH_MP_TAC MOI_FRS_PAIR_CASES THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING]) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THENL
       [EXISTS_TAC `{tau1:real^N->bool}`; EXISTS_TAC `{tau2:real^N->bool}`] THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; IN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING;
                      FORALL_UNWIND_THM2] THEN
      MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `tf:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `tf:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(simplex_barycentre tau1 = simplex_barycentre (tau2:real^N->bool))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `tau1:real^N->bool`;
                   `tau2:real^N->bool`] MOI_FTA_BARY_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(tau2 SUBSET (tau2:real^N->bool))` THEN REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2; UNION_EMPTY] THEN
    REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    UNDISCH_TAC `~(simplex_barycentre (tf:real^N->bool) IN
                   {simplex_barycentre tau1, simplex_barycentre tau2})` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    UNDISCH_TAC `~(simplex_barycentre (tf:real^N->bool) IN
                   {simplex_barycentre tau1, simplex_barycentre tau2})` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    MATCH_MP_TAC MOI_FRS_SEG_SEG THEN
    EXISTS_TAC `{simplex_barycentre tau1, simplex_barycentre (tau2:real^N->bool)}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(simplex_barycentre (tf:real^N->bool) IN
                   {simplex_barycentre tau1, simplex_barycentre tau2})` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Gluing PL 2-cells along arcs made of two segments (fans of two           *)
(* and three cells), via MOI_FSA_GLUE.                                      *)
(* ========================================================================= *)

(* Gluing two PL 2-cells along a common boundary arc made of two segments. *)

let MOI_FRS_GLUE2 = prove
 (`!(x1:real^N->bool) j1 x2 j2 p q r.
     2 <= dimindex(:N) /\
     pl_cell_with_boundary 2 x1 j1 /\ pl_cell_with_boundary 2 x2 j2 /\
     ~(p = q) /\ ~(q = r) /\ segment[p,q] INTER segment[q,r] = {q} /\
     x1 INTER x2 = segment[p,q] UNION segment[q,r] /\
     segment[p,q] UNION segment[q,r] SUBSET j1 /\
     segment[p,q] UNION segment[q,r] SUBSET j2
     ==> pl_cell_with_boundary 2 (x1 UNION x2)
           ((j1 UNION j2) DIFF ((segment[p,q] UNION segment[q,r]) DIFF {p,r}))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x1:real^N->bool`; `j1:real^N->bool`; `x2:real^N->bool`;
                 `j2:real^N->bool`; `linepath(p:real^N,q) ++ linepath(q,r)`]
    MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_JOIN;
               PATHFINISH_JOIN] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[ARC_JOIN_EQ_ALT; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                 PATH_IMAGE_LINEPATH; ARC_LINEPATH];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
    REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]]);;

(* Gluing three PL 2-cells in a row: consecutive ones along two-segment    *)
(* arcs, the outer ones disjoint, the two arcs disjoint.                    *)

let MOI_FRS_GLUE3 = prove
 (`!(x1:real^N->bool) j1 x2 j2 x3 j3 p q r p' q' r'.
     2 <= dimindex(:N) /\
     pl_cell_with_boundary 2 x1 j1 /\ pl_cell_with_boundary 2 x2 j2 /\
     pl_cell_with_boundary 2 x3 j3 /\
     ~(p = q) /\ ~(q = r) /\ segment[p,q] INTER segment[q,r] = {q} /\
     ~(p' = q') /\ ~(q' = r') /\ segment[p',q'] INTER segment[q',r'] = {q'} /\
     x1 INTER x2 = segment[p,q] UNION segment[q,r] /\
     x2 INTER x3 = segment[p',q'] UNION segment[q',r'] /\
     x1 INTER x3 = {} /\
     (segment[p,q] UNION segment[q,r]) INTER (segment[p',q'] UNION segment[q',r']) = {} /\
     segment[p,q] UNION segment[q,r] SUBSET j1 /\
     segment[p,q] UNION segment[q,r] SUBSET j2 /\
     segment[p',q'] UNION segment[q',r'] SUBSET j2 /\
     segment[p',q'] UNION segment[q',r'] SUBSET j3
     ==> ?j. pl_cell_with_boundary 2 (x1 UNION x2 UNION x3) j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x1:real^N->bool`; `j1:real^N->bool`; `x2:real^N->bool`;
                 `j2:real^N->bool`; `p:real^N`; `q:real^N`; `r:real^N`]
    MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x1 UNION x2:real^N->bool`;
                 `(j1 UNION j2) DIFF ((segment[p,q] UNION segment[q,r]) DIFF {p,r:real^N})`;
                 `x3:real^N->bool`; `j3:real^N->bool`;
                 `p':real^N`; `q':real^N`; `r':real^N`] MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[UNION_ASSOC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    MESON_TAC[]]);;

(* Closed stars in K' of barycentres of two simplices of t: they meet in   *)
(* the dual cell of the edge joining the barycentres if the simplices are  *)
(* comparable, and not at all otherwise.                                    *)

let MOI_FRS_PAIR_INTER = prove
 (`!(t:(real^N->bool)->bool) p q.
     lf_simplicial_complex t /\ p IN t /\ q IN t /\ ~(p = {}) /\ ~(q = {})
     ==> moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} INTER
         moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre q} =
         if p SUBSET q \/ q SUBSET p
         then moi_fcl_dual (barycentric_subdivision t)
                (segment[simplex_barycentre p,simplex_barycentre q])
         else {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p:real^N->bool}`; `{q:real^N->bool}`]
    MOI_FRS_DUAL_CHAIN_INTER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR; MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `moi_bar_chain t ({p,q:real^N->bool}) <=> p SUBSET q \/ q SUBSET p`
  (fun th -> REWRITE_TAC[SET_RULE `{a:A} UNION {b} = {a,b}`; th]) THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~({} = p:real^N->bool) /\ ~({} = q:real^N->bool)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL; IMAGE_CLAUSES]);;

(* A dual cell of a proper coface lies in the link part.                    *)

let MOI_FRS_DUAL_IN_LDUAL = prove
 (`!(K:(real^N->bool)->bool) e u.
     u IN K /\ ~(u = {}) /\ e SUBSET u /\ ~(u = e)
     ==> moi_fcl_dual K u SUBSET moi_fcl_ldual K e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
  MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* Three nested nonempty simplices form a chain.                           *)

let MOI_FRS_CHAIN3 = prove
 (`!(t:(real^N->bool)->bool) p0 p1 p2.
     p0 IN t /\ p1 IN t /\ p2 IN t /\ ~(p0 = {}) /\ ~(p1 = {}) /\ ~(p2 = {}) /\
     p0 SUBSET p1 /\ p1 SUBSET p2
     ==> moi_bar_chain t {p0,p1,p2}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
              FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN `(p0:real^N->bool) SUBSET p2` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* Proper subchains give proper faces of the chain simplices, and the dual  *)
(* cell of the bigger simplex lies in the link part of the smaller one.     *)

let MOI_FRS_CHAIN_HULL_PROPER = prove
 (`!(t:(real^N->bool)->bool) f g.
     moi_bar_complex t /\ moi_bar_chain t f /\ moi_bar_chain t g /\
     f SUBSET g /\ ~(f = g)
     ==> convex hull (IMAGE simplex_barycentre f) SUBSET
         convex hull (IMAGE simplex_barycentre g) /\
         ~(convex hull (IMAGE simplex_barycentre g) =
           convex hull (IMAGE simplex_barycentre f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FTA_HULL_INJ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_FRS_CHAIN_RIM = prove
 (`!(t:(real^N->bool)->bool) e f.
     moi_bar_complex t /\ moi_bar_chain t e /\ moi_bar_chain t f /\
     ~(e = {}) /\ e SUBSET f /\ ~(e = f)
     ==> moi_fcl_dual (barycentric_subdivision t)
           (convex hull (IMAGE simplex_barycentre f)) SUBSET
         moi_fcl_ldual (barycentric_subdivision t)
           (convex hull (IMAGE simplex_barycentre e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `e:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`] MOI_FRS_CHAIN_HULL_PROPER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRS_DUAL_IN_LDUAL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_FRS_IN_BSD; CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

(* A PL 2-sphere in real^N forces dimindex(:N) >= 3.                        *)

let MOI_FRS_SPHERE2_DIM = prove
 (`!X:real^N->bool. pl_sphere 2 X ==> 3 <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE]);;

(* Hulls of barycentres of chains of two faces are segments.               *)

let MOI_FRS_HULL_PAIR = prove
 (`!p q:real^N->bool.
     convex hull (IMAGE simplex_barycentre {p,q}) =
     segment[simplex_barycentre p,simplex_barycentre q]`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; IMAGE_CLAUSES]);;

(* The fan at a corner p0 of the triangle p2 with edges p1, q1: the union  *)
(* of the dual cells of the three edges of the first derived at b(p0)       *)
(* inside p2 is a PL 2-cell.                                                 *)

let MOI_FRS_CORNER_FAN = prove
 (`!(t:(real^N->bool)->bool) p0 p1 q1 p2 X1 X2.
     lf_simplicial_complex t /\
     (!w. {w} IN t /\ w IN p2 ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     p0 IN t /\ p1 IN t /\ q1 IN t /\ p2 IN t /\
     aff_dim p0 = &0 /\ aff_dim p1 = &1 /\ aff_dim q1 = &1 /\ aff_dim p2 = &2 /\
     p0 SUBSET p1 /\ p1 SUBSET p2 /\ p0 SUBSET q1 /\ q1 SUBSET p2 /\
     ~(p1 SUBSET q1) /\ ~(q1 SUBSET p1) /\
     ~(X1 = X2) /\ X1 IN t /\ X2 IN t /\ aff_dim X1 = &3 /\ aff_dim X2 = &3 /\
     p2 SUBSET X1 /\ p2 SUBSET X2 /\
     (!X. X IN t /\ p2 SUBSET X /\ ~(X = p2) ==> X = X1 \/ X = X2)
     ==> ?j. pl_cell_with_boundary 2
               (moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre p0,simplex_barycentre p1]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre p0,simplex_barycentre p2]) UNION
                moi_fcl_dual (barycentric_subdivision t)
                  (segment[simplex_barycentre p0,simplex_barycentre q1])) j`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* basic facts on the faces *)
  SUBGOAL_THEN `~(p0:real^N->bool = {}) /\ ~(p1:real^N->bool = {}) /\
                ~(q1:real^N->bool = {}) /\ ~(p2:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_POS_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p0:real^N->bool = p1) /\ ~(p0:real^N->bool = q1) /\
                ~(p0:real^N->bool = p2) /\ ~(p1:real^N->bool = p2) /\
                ~(q1:real^N->bool = p2) /\ ~(p1:real^N->bool = q1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET_REFL]) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p0:real^N->bool) SUBSET p2` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN t /\ u SUBSET p2 ==> u face_of p2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `u = u INTER (p2:real^N->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?w:real^N. {w} IN t /\ w IN p2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `aff_dim(p0:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THEN
      EXISTS_TAC `w:real^N` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `3 <= n ==> 2 <= n`) THEN
    MATCH_MP_TAC MOI_FRS_SPHERE2_DIM THEN
    EXISTS_TAC `UNIONS (simplicial_link t (w:real^N))` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the three 2-cells *)
  SUBGOAL_THEN
   `!q:real^N->bool. q IN t /\ q SUBSET p2 /\ p0 SUBSET q /\ ~(p0 = q)
      ==> pl_cell_with_boundary 2
            (moi_fcl_dual (barycentric_subdivision t)
               (segment[simplex_barycentre p0,simplex_barycentre q]))
            (moi_fcl_ldual (barycentric_subdivision t)
               (segment[simplex_barycentre p0,simplex_barycentre q]))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRS_EDGE_CELL THEN
    EXISTS_TAC `p2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "face_of"
                                with Failure _ -> false)) (concl th))) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  (* the two arcs *)
  SUBGOAL_THEN `moi_bar_chain t {p0,p1,p2:real^N->bool} /\
                moi_bar_chain t {p0,q1,p2:real^N->bool}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FRS_CHAIN3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {p0,p1:real^N->bool} /\
                moi_bar_chain t {p0,p2:real^N->bool} /\
                moi_bar_chain t {p0,q1:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THENL
     [EXISTS_TAC `{p0,p1,p2:real^N->bool}`;
      EXISTS_TAC `{p0,p1,p2:real^N->bool}`;
      EXISTS_TAC `{p0,q1,p2:real^N->bool}`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p0:real^N->bool`; `p1:real^N->bool`;
                 `p2:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p0:real^N->bool`; `q1:real^N->bool`;
                 `p2:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_FLAG_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* intersections of the three cells *)
  SUBGOAL_THEN `~moi_bar_chain t {p0,p1,q1:real^N->bool} /\
                ~moi_bar_chain t {p0,p1,p2,q1:real^N->bool}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; IN_INSERT; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN DISCH_THEN(MP_TAC o SPECL [`p1:real^N->bool`; `q1:real^N->bool`] o
      last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1:real^N->bool}`;
                 `{p0,p2:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p2:real^N->bool}`;
                 `{p0,q1:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1:real^N->bool}`;
                 `{p0,q1:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{p0,p1,p2:real^N->bool}`;
                 `{p0,q1,p2:real^N->bool}`] MOI_FRS_DUAL_CHAIN_INTER) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; MOI_FRS_HULL_PAIR] THEN
  SUBGOAL_THEN `{p0,p1} UNION {p0,p2} = {p0,p1,p2:real^N->bool} /\
                {p0,p2} UNION {p0,q1} = {p0,q1,p2:real^N->bool} /\
                {p0,p1} UNION {p0,q1} = {p0,p1,q1:real^N->bool} /\
                {p0,p1,p2} UNION {p0,q1,p2} = {p0,p1,p2,q1:real^N->bool}`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {p0,p1,p2:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre p0,simplex_barycentre p1]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {p0,p1,p2:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre p0,simplex_barycentre p2]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {p0,q1,p2:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre p0,simplex_barycentre p2]) /\
    moi_fcl_dual (barycentric_subdivision t)
      (convex hull (IMAGE simplex_barycentre {p0,q1,p2:real^N->bool})) SUBSET
    moi_fcl_ldual (barycentric_subdivision t)
      (segment[simplex_barycentre p0,simplex_barycentre q1])`
  MP_TAC THENL
   [REWRITE_TAC[GSYM MOI_FRS_HULL_PAIR] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_FRS_CHAIN_RIM THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    FIRST [MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,b,c})`);
           MATCH_MP_TAC(SET_RULE `~((c:A) IN {a,b}) ==> ~({a,b} = {a,c,b})`)] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRS_GLUE3 THEN
  MAP_EVERY EXISTS_TAC
   [`moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre p0,simplex_barycentre (p1:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre p0,simplex_barycentre (p2:real^N->bool)])`;
    `moi_fcl_ldual (barycentric_subdivision t)
       (segment[simplex_barycentre p0,simplex_barycentre (q1:real^N->bool)])`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,p1,p2,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,p1,p2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,p1,p2,X2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,q1,p2,X1:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,q1,p2:real^N->bool}))`;
    `simplex_barycentre (convex hull (IMAGE simplex_barycentre
       {p0,q1,p2,X2:real^N->bool}))`] THEN
  ASM_SIMP_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `{}:real^N->bool` &&
    can (find_term ((=) `p2:real^N->bool`)) (lhs(concl th)) &&
    can (find_term ((=) `q1:real^N->bool`)) (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[]);;

(* Points of the closed star in K' of the barycentre of a face of s are     *)
(* interior manifold points of UNIONS K.                                     *)

let MOI_FRS_STAR_MINT = prove
 (`!(t:(real^N->bool)->bool) s p x.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     p face_of s /\ ~(p = {}) /\
     x IN moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p}
     ==> moi_fmb_mint (UNIONS (barycentric_subdivision t)) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a extreme_point_of p` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN t /\ a IN s /\ a IN p` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{a:real^N} face_of p` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FACE_OF_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN p` ASSUME_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FRS_OPEN_STAR_MINT THEN EXISTS_TAC `a:real^N` THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p:real^N->bool`; `a:real^N`]
    MOI_FRS_DUAL_OPEN_STAR) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The nonempty faces of a triangle.                                         *)

let MOI_FRS_TRI_FACE_LIST = prove
 (`!a b c:real^N.
     ~affine_dependent {a,b,c}
     ==> {p | p face_of convex hull {a,b,c} /\ ~(p = {})} =
         {{a},{b},{c},segment[a,b],segment[b,c],segment[c,a],convex hull {a,b,c}}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `p:real^N->bool` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_CONVEX_HULL] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC `(a:real^N) IN d` THEN ASM_CASES_TAC `(b:real^N) IN d` THEN
    ASM_CASES_TAC `(c:real^N) IN d` THENL
     [SUBGOAL_THEN `d = {a,b,c:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {a,b:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {c,a:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {a:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {b,c:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {b:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {c:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d:real^N->bool = {}` SUBST_ALL_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `~(convex hull {}:real^N->bool = {})` THEN
        REWRITE_TAC[CONVEX_HULL_EMPTY]]] THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THENL
     [EXISTS_TAC `{a:real^N}`; EXISTS_TAC `{b:real^N}`; EXISTS_TAC `{c:real^N}`;
      EXISTS_TAC `{a,b:real^N}`; EXISTS_TAC `{b,c:real^N}`; EXISTS_TAC `{c,a:real^N}`;
      EXISTS_TAC `{a,b,c:real^N}`] THEN
    REWRITE_TAC[CONVEX_HULL_SING; NOT_INSERT_EMPTY; CONVEX_HULL_EQ_EMPTY] THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The derived neighbourhood of a triangle.  The seven closed               *)
(* stars of the barycentres of its faces are glued in the order b(s), the  *)
(* edge barycentres (each along one dual 2-cell), the vertices (each along *)
(* a fan of three dual 2-cells, MOI_FRS_CORNER_FAN).                        *)
(* ========================================================================= *)

(* Inclusions between the faces of a triangle.                              *)

let MOI_FRS_TRI_FACTS = prove
 (`!a b c:real^N.
     ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> ~(a IN segment[b,c]) /\ ~(b IN segment[c,a]) /\ ~(c IN segment[a,b]) /\
         {a} SUBSET segment[a,b] /\ {a} SUBSET segment[c,a] /\
         {b} SUBSET segment[a,b] /\ {b} SUBSET segment[b,c] /\
         {c} SUBSET segment[b,c] /\ {c} SUBSET segment[c,a] /\
         segment[a,b] SUBSET convex hull {a,b,c} /\
         segment[b,c] SUBSET convex hull {a,b,c} /\
         segment[c,a] SUBSET convex hull {a,b,c} /\
         {a} SUBSET convex hull {a,b,c} /\ {b} SUBSET convex hull {a,b,c} /\
         {c} SUBSET convex hull {a,b,c} /\
         ~(segment[a,b] SUBSET segment[b,c]) /\ ~(segment[b,c] SUBSET segment[a,b]) /\
         ~(segment[b,c] SUBSET segment[c,a]) /\ ~(segment[c,a] SUBSET segment[b,c]) /\
         ~(segment[c,a] SUBSET segment[a,b]) /\ ~(segment[a,b] SUBSET segment[c,a]) /\
         ~({a} SUBSET segment[b,c]) /\ ~({b} SUBSET segment[c,a]) /\
         ~({c} SUBSET segment[a,b]) /\
         ~(segment[b,c] SUBSET {a}) /\ ~(segment[c,a] SUBSET {b}) /\
         ~(segment[a,b] SUBSET {c}) /\
         ~(segment[a,b] SUBSET {a}) /\ ~(segment[a,b] SUBSET {b}) /\
         ~(segment[b,c] SUBSET {b}) /\ ~(segment[b,c] SUBSET {c}) /\
         ~(segment[c,a] SUBSET {c}) /\ ~(segment[c,a] SUBSET {a}) /\
         ~({a} SUBSET {b}) /\ ~({b} SUBSET {a}) /\ ~({a} SUBSET {c}) /\
         ~({c} SUBSET {a}) /\ ~({b} SUBSET {c}) /\ ~({c} SUBSET {b}) /\
         ~(convex hull {a,b,c} SUBSET segment[a,b]) /\
         ~(convex hull {a,b,c} SUBSET segment[b,c]) /\
         ~(convex hull {a,b,c} SUBSET segment[c,a]) /\
         ~(convex hull {a,b,c} SUBSET {a}) /\ ~(convex hull {a,b,c} SUBSET {b}) /\
         ~(convex hull {a,b,c} SUBSET {c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:real^N) IN segment[b,c]) /\ ~(b IN segment[c,a]) /\
                ~(c IN segment[a,b])` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`]
      COLLINEAR_3_EQ_AFFINE_DEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
    UNDISCH_TAC `~collinear {a,b,c:real^N}` THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN convex hull {a,b,c} /\ b IN convex hull {a,b,c} /\
                c IN convex hull {a,b,c}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a,b] SUBSET convex hull {a,b,c:real^N} /\
                segment[b,c] SUBSET convex hull {a,b,c} /\
                segment[c,a] SUBSET convex hull {a,b,c}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT] THEN
  REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN
  REWRITE_TAC[SUBSET; IN_SING; NOT_FORALL_THM; NOT_IMP] THEN
  ASM_MESON_TAC[ENDS_IN_SEGMENT]);;

(* MOI_FRS_STAR_MINT with the polyhedron of t.                              *)

let MOI_FRS_STAR_MINT_T = prove
 (`!(t:(real^N->bool)->bool) s p x.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     p face_of s /\ ~(p = {}) /\
     x IN moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p}
     ==> moi_fmb_mint (UNIONS t) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `p:real^N->bool`;
                 `x:real^N`] MOI_FRS_STAR_MINT) THEN
  ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]);;

(* Gluing steps indexed by faces of s: the union of the closed stars of the *)
(* barycentres of a set P of faces, and one more face q.                    *)

let MOI_FRS_FACE_UNIONS = prove
 (`!(K:(real^N->bool)->bool) P.
     UNIONS {moi_fcl_dual K {v} | v | v IN IMAGE simplex_barycentre P} =
     UNIONS {moi_fcl_dual K {simplex_barycentre p} | p | p IN P}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; EXISTS_IN_IMAGE]);;

let MOI_FRS_FACE_STEP = prove
 (`!(t:(real^N->bool)->bool) s P q A jA.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     FINITE P /\ (!p. p IN P ==> p face_of s /\ ~(p = {})) /\
     q face_of s /\ ~(q = {}) /\ ~(q IN P) /\
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
  SUBGOAL_THEN `!p:real^N->bool. p face_of s ==> p IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
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
     [DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_FRS_STAR_MINT_T THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `q:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_FRS_STAR_MINT_T THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `p:real^N->bool`] THEN
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `q:real^N->bool`]
      MOI_FRS_STAR_CELL) THEN
    ASM_SIMP_TAC[]]);;

let MOI_FRS_FACE_BASE = prove
 (`!(t:(real^N->bool)->bool) s q.
     lf_simplicial_complex t /\ s IN t /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     q face_of s /\ ~(q = {})
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN {q}})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN {q}}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `q:real^N->bool`]
    MOI_FRS_STAR_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `simplex_barycentre (q:real^N->bool)`] MOI_FRS_GLUE_BASE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRS_STAR_MINT_T THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES]);;

(* Computing the attaching set of a star: the union over the earlier faces  *)
(* of the pairwise intersections (MOI_FRS_PAIR_INTER).                       *)

let MOI_FRS_UNION_INTER = prove
 (`!s t u:A->bool. (s UNION t) INTER u = (s INTER u) UNION (t INTER u)`,
  SET_TAC[]);;

let MOI_FRS_ATTACH_TAC =
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY;
              MOI_FRS_UNION_INTER] THEN
  ASM_SIMP_TAC[MOI_FRS_PAIR_INTER] THEN REWRITE_TAC[UNION_EMPTY];;

(* The derived neighbourhood of a triangle: gluing the seven stars.          *)

(* The eleven hypotheses of MOI_FRS_FACE_STEP in a triangle assembly; the  *)
(* attaching set and its cell are supplied by the tactics ateq and atcell.  *)

let MOI_FRS_STEP_ANTS_TAC ateq atcell =
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[IN_INSERT];
    FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[SUBSET_REFL];
    FIRST_ASSUM ACCEPT_TAC;
    ateq;
    atcell];;

let MOI_FRS_TRIANGLE_NBHD = prove
 (`!(t:(real^N->bool)->bool) a b c.
     lf_simplicial_complex t /\ convex hull {a,b,c} IN t /\
     ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     (!w. {w} IN t /\ w IN convex hull {a,b,c}
          ==> pl_sphere 2 (UNIONS (simplicial_link t w)))
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN {{c},{b},{a},segment[c,a],segment[b,c],segment[a,b],
                              convex hull {a,b,c}}})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN {{c},{b},{a},segment[c,a],segment[b,c],segment[a,b],
                               convex hull {a,b,c}}}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_TRI_FACE_LIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fl") THEN
  ABBREV_TAC `S:real^N->bool = convex hull {a,b,c}` THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p face_of S /\ ~(p = {}) <=>
                     p IN {{a},{b},{c},segment[a,b],segment[b,c],segment[c,a],S}`
  (LABEL_TAC "fiff") THENL
   [USE_THEN "fl" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `({a:real^N} face_of S /\ ~({a} = {})) /\ ({b} face_of S /\ ~({b} = {})) /\
    ({c} face_of S /\ ~({c} = {})) /\
    (segment[a,b] face_of S /\ ~(segment[a,b] = {})) /\
    (segment[b,c] face_of S /\ ~(segment[b,c] = {})) /\
    (segment[c,a] face_of S /\ ~(segment[c,a] = {})) /\
    (S face_of S /\ ~(S = {}))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REMOVE_THEN "fiff" (K ALL_TAC) THEN REMOVE_THEN "fl" (K ALL_TAC) THEN
  SUBGOAL_THEN `~(segment[a,b] = S:real^N->bool) /\ ~(segment[b,c] = S) /\
                ~(segment[c,a] = S)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET_REFL]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N->bool. p face_of S ==> p IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN t /\ {b} IN t /\ {c} IN t /\ segment[a,b] IN t /\
                segment[b,c] IN t /\ segment[c,a] IN t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim {a:real^N} = &0 /\ aff_dim {b:real^N} = &0 /\
                aff_dim {c:real^N} = &0 /\
                aff_dim (segment[a,b]) = &1 /\ aff_dim (segment[b,c]) = &1 /\
                aff_dim (segment[c,a]) = &1 /\ aff_dim (S:real^N->bool) = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_SEGMENT] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{a,b,c:real^N}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_FRS_CARD3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  (* the two tetrahedra on S *)
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link t (a:real^N)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "pl_sphere"
                                with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `c:real^N`]
    MOI_FRS_TWO_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X1:real^N->bool` (X_CHOOSE_THEN `X2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  (* step 1: the star of b(S) *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `S:real^N->bool`]
    MOI_FRS_FACE_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* step 2: the edge ab *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `segment[a:real^N,b]`;
                 `S:real^N->bool`] MOI_FRS_EDGE_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{S:real^N->bool}`;
                 `segment[a:real^N,b]`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[a,b]),
                             simplex_barycentre (S:real^N->bool)])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[a,b]),
                             simplex_barycentre (S:real^N->bool)])`]
    MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  (* steps 3 and 4: the edges bc and ca *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `segment[b:real^N,c]`;
                 `S:real^N->bool`] MOI_FRS_EDGE_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`;
                 `{segment[a:real^N,b],S}`; `segment[b:real^N,c]`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[b,c]),
                             simplex_barycentre (S:real^N->bool)])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[b,c]),
                             simplex_barycentre (S:real^N->bool)])`]
    MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `segment[c:real^N,a]`;
                 `S:real^N->bool`] MOI_FRS_EDGE_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`;
                 `{segment[b:real^N,c],segment[a,b],S}`; `segment[c:real^N,a]`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[c,a]),
                             simplex_barycentre (S:real^N->bool)])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre (segment[c,a]),
                             simplex_barycentre (S:real^N->bool)])`]
    MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  (* steps 5, 6, 7: the corners a, b, c *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{a:real^N}`; `segment[a:real^N,b]`; `segment[c:real^N,a]`;
                 `S:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_CORNER_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `j1:real^N->bool`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{segment[c:real^N,a],segment[b,c],segment[a,b],S}`; `{a:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},simplex_barycentre (segment[a:real^N,b])]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},simplex_barycentre (S:real^N->bool)]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},simplex_barycentre (segment[c:real^N,a])])`;
                 `j1:real^N->bool`] MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{b:real^N}`; `segment[b:real^N,c]`; `segment[a:real^N,b]`;
                 `S:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_CORNER_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `j2:real^N->bool`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{{a:real^N},segment[c,a],segment[b,c],segment[a,b],S}`; `{b:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},simplex_barycentre (segment[b:real^N,c])]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},simplex_barycentre (S:real^N->bool)]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},simplex_barycentre (segment[a:real^N,b])])`;
                 `j2:real^N->bool`] MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{c:real^N}`; `segment[c:real^N,a]`; `segment[b:real^N,c]`;
                 `S:real^N->bool`; `X1:real^N->bool`; `X2:real^N->bool`]
    MOI_FRS_CORNER_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `j3:real^N->bool`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{{b:real^N},{a},segment[c,a],segment[b,c],segment[a,b],S}`; `{c:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {c:real^N},simplex_barycentre (segment[c:real^N,a])]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {c:real^N},simplex_barycentre (S:real^N->bool)]) UNION
                  moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {c:real^N},simplex_barycentre (segment[b:real^N,c])])`;
                 `j3:real^N->bool`] MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* The derived neighbourhood of an edge and of a vertex, the classification  *)
(* of simplices of dimension at most 2, and the theorem                      *)
(* DERIVED_NBHD_SIMPLEX.                                                     *)
(* ========================================================================= *)

let MOI_FRS_SEG_FACE_LIST = prove
 (`!a b:real^N.
     {p | p face_of segment[a,b] /\ ~(p = {})} = {{a},{b},segment[a,b]}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `p:real^N->bool` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[IN_ELIM_THM; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC `(a:real^N) IN d` THEN ASM_CASES_TAC `(b:real^N) IN d` THENL
     [SUBGOAL_THEN `d = {a,b:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {a:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d = {b:real^N}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `d:real^N->bool = {}` SUBST_ALL_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `~(convex hull {}:real^N->bool = {})` THEN
        REWRITE_TAC[CONVEX_HULL_EMPTY]]] THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THENL
     [EXISTS_TAC `{a:real^N}`; EXISTS_TAC `{b:real^N}`; EXISTS_TAC `{a,b:real^N}`] THEN
    REWRITE_TAC[CONVEX_HULL_SING; NOT_INSERT_EMPTY; CONVEX_HULL_EQ_EMPTY] THEN
    SET_TAC[]]);;

let MOI_FRS_SING_FACE_LIST = prove
 (`!a:real^N. {p | p face_of {a} /\ ~(p = {})} = {{a}}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `p:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[FACE_OF_REFL; CONVEX_SING; NOT_INSERT_EMPTY]]);;

(* Inclusions between the faces of an edge.                                 *)

let MOI_FRS_EDGE_FACTS = prove
 (`!a b:real^N.
     ~(a = b)
     ==> {a} SUBSET segment[a,b] /\ {b} SUBSET segment[a,b] /\
         ~(segment[a,b] SUBSET {a}) /\ ~(segment[a,b] SUBSET {b}) /\
         ~({a} SUBSET {b}) /\ ~({b} SUBSET {a}) /\
         ~({a} = segment[a,b]) /\ ~({b} = segment[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET; IN_SING; SING_SUBSET]);;

(* The derived neighbourhood of an edge: the star of the edge barycentre,   *)
(* then the two vertex stars, each attached along one dual 2-cell.          *)

let MOI_FRS_EDGE_NBHD = prove
 (`!(t:(real^N->bool)->bool) a b.
     lf_simplicial_complex t /\ segment[a,b] IN t /\ ~(a = b) /\
     (!w. {w} IN t /\ w IN segment[a,b]
          ==> pl_sphere 2 (UNIONS (simplicial_link t w)))
     ==> pl_cell_with_boundary 3
           (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                    p | p IN {{b},{a},segment[a,b]}})
           ((subtopology euclidean (UNIONS t)) frontier_of
            (UNIONS {moi_fcl_dual (barycentric_subdivision t) {simplex_barycentre p} |
                     p | p IN {{b},{a},segment[a,b]}}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] MOI_FRS_EDGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] MOI_FRS_SEG_FACE_LIST) THEN
  DISCH_THEN(LABEL_TAC "fl") THEN
  ABBREV_TAC `S:real^N->bool = segment[a,b]` THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p face_of S /\ ~(p = {}) <=> p IN {{a},{b},S}`
  (LABEL_TAC "fiff") THENL
   [USE_THEN "fl" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `({a:real^N} face_of S /\ ~({a} = {})) /\ ({b} face_of S /\ ~({b} = {})) /\
    (S face_of S /\ ~(S = {}))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REMOVE_THEN "fiff" (K ALL_TAC) THEN REMOVE_THEN "fl" (K ALL_TAC) THEN
  SUBGOAL_THEN `!p:real^N->bool. p face_of S ==> p IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN t /\ {b} IN t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* step 1: the star of b(S) *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `S:real^N->bool`]
    MOI_FRS_FACE_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* step 2: the vertex a *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{a:real^N}`;
                 `S:real^N->bool`] MOI_FRS_EDGE_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{S:real^N->bool}`;
                 `{a:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},
                             simplex_barycentre (S:real^N->bool)])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre {a:real^N},
                             simplex_barycentre (S:real^N->bool)])`]
    MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  (* step 3: the vertex b *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{b:real^N}`;
                 `S:real^N->bool`] MOI_FRS_EDGE_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `S:real^N->bool`; `{{a:real^N},S}`;
                 `{b:real^N}`;
                 `moi_fcl_dual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},
                             simplex_barycentre (S:real^N->bool)])`;
                 `moi_fcl_ldual (barycentric_subdivision t)
                    (segment[simplex_barycentre {b:real^N},
                             simplex_barycentre (S:real^N->bool)])`]
    MOI_FRS_FACE_STEP) THEN
  ANTS_TAC THENL
   [MOI_FRS_STEP_ANTS_TAC
     (MOI_FRS_ATTACH_TAC THEN REWRITE_TAC[SEGMENT_SYM])
     (FIRST_ASSUM ACCEPT_TAC);
    DISCH_TAC] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* A nonempty simplex of dimension at most 2 is a point, an edge or a       *)
(* triangle.                                                                 *)

let MOI_FRS_LOWDIM_SIMPLEX_CASES = prove
 (`!s:real^N->bool.
     (?n. n simplex s) /\ ~(s = {}) /\ aff_dim s <= &2
     ==> (?a. s = {a}) \/
         (?a b. ~(a = b) /\ s = segment[a,b]) \/
         (?a b c. ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
                  s = convex hull {a,b,c})`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `n simplex (s:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (v:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(s:real^N->bool = {})` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(v:real^N->bool) = 1 \/ CARD v = 2 \/ CARD v = 3` MP_TAC THENL
   [SUBGOAL_THEN `~(CARD(v:real^N->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `CARD(v:real^N->bool) <= 3` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      UNDISCH_TAC `&(CARD(v:real^N->bool)):int = n + &1` THEN
      UNDISCH_TAC `aff_dim(s:real^N->bool) = n` THEN
      UNDISCH_TAC `aff_dim(s:real^N->bool) <= &2` THEN INT_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN
    MP_TAC(HAS_SIZE_CONV `(v:real^N->bool) HAS_SIZE 1`) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[CONVEX_HULL_SING];
    DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(HAS_SIZE_CONV `(v:real^N->bool) HAS_SIZE 2`) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    DISJ2_TAC THEN DISJ2_TAC THEN
    MP_TAC(HAS_SIZE_CONV `(v:real^N->bool) HAS_SIZE 3`) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~affine_dependent (v:real^N->bool)` THEN
    ASM_REWRITE_TAC[]]);;

(* The union of the stars, indexed by the set of nonempty faces.            *)

let MOI_FRS_STARS_INDEX = prove
 (`!(K:(real^N->bool)->bool) s.
     UNIONS {moi_fcl_dual K {simplex_barycentre p} | p | p face_of s /\ ~(p = {})} =
     UNIONS {moi_fcl_dual K {simplex_barycentre p} | p |
             p IN {q | q face_of s /\ ~(q = {})}}`,
  REWRITE_TAC[IN_ELIM_THM]);;

let DERIVED_NBHD_SIMPLEX = prove
 (MOI_FND_DERIVED_NBHD_SIMPLEX,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FRS_LOWDIM_SIMPLEX_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[derived_frontier; MOI_FRS_NBHD_STARS] THEN
  ONCE_REWRITE_TAC[MOI_FRS_STARS_INDEX] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [REWRITE_TAC[MOI_FRS_SING_FACE_LIST] THEN
    MATCH_MP_TAC MOI_FRS_FACE_BASE THEN EXISTS_TAC `{a:real^N}` THEN
    ASM_SIMP_TAC[FACE_OF_REFL; CONVEX_SING; NOT_INSERT_EMPTY];
    REWRITE_TAC[MOI_FRS_SEG_FACE_LIST] THEN
    ONCE_REWRITE_TAC[SET_RULE `{x:A,y,z} = {y,x,z}`] THEN
    MATCH_MP_TAC MOI_FRS_EDGE_NBHD THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOI_FRS_TRI_FACE_LIST] THEN
    SUBGOAL_THEN
     `{{a},{b},{c},segment[a,b],segment[b,c],segment[c,a],convex hull {a,b,c}} =
      {{c},{b},{a},segment[c,a],segment[b,c],segment[a,b],
       convex hull {a,b,c:real^N}}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N->bool` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC TAUT;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRS_TRIANGLE_NBHD THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The theorem SIMPLEX_SMALL_CELL.  The derived neighbourhood N of          *)
(* s is a PL 3-cell with s in its interior (DERIVED_NBHD_SIMPLEX,            *)
(* DERIVED_NBHD_BASIC).  A derived retriangulation (MOI_FTA_DERIVED_HOMEO)  *)
(* of the finite closed star c0 of s in the first derived, with the         *)
(* derivation points of the simplices meeting s chosen close to s, is a PL  *)
(* homeomorphism h of UNIONS c0 onto itself with s inside h(s) and h(N)     *)
(* close to s, hence inside v.                                               *)
(* ========================================================================= *)

(* Derivation points: in the relative interior, and near s for the         *)
(* simplices meeting s.                                                      *)

let MOI_FRS_SHRINK_POINTS = prove
 (`!(c:(real^N->bool)->bool) (s:real^N->bool) e.
     moi_bar_complex c /\ &0 < e
     ==> ?d:(real^N->bool)->real^N.
           (!r. r IN c /\ ~(r = {}) ==> d r IN relative_interior r) /\
           (!r. r IN c /\ ~(r INTER s = {}) ==> ?q. q IN s /\ dist(d r,q) < e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!r:real^N->bool. ?y:real^N.
      (r IN c /\ ~(r = {}) ==> y IN relative_interior r) /\
      (r IN c /\ ~(r INTER s = {}) ==> ?q. q IN s /\ dist(y,q) < e)`
  MP_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN
    ASM_CASES_TAC `(r:real^N->bool) IN c /\ ~(r = {})` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      SUBGOAL_THEN `convex (r:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `r INTER (s:real^N->bool) = {}` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
        ALL_TAC] THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^N` o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      SUBGOAL_THEN `(p:real^N) IN closure(relative_interior r)` MP_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((r:real^N->bool) IN c /\ ~(r = {}))` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~({} INTER (s:real^N->bool) = {})` THEN REWRITE_TAC[INTER_EMPTY]];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]);;

(* A convex hull of points near a convex set s stays near s.               *)

let MOI_FRS_HULL_NEAR = prove
 (`!(s:real^N->bool) X e.
     convex s /\ (!x. x IN X ==> ?q. q IN s /\ dist(x,q) < e)
     ==> !y. y IN convex hull X ==> ?q. q IN s /\ dist(y,q) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull X SUBSET {q + z:real^N | q IN s /\ z IN ball(vec 0,e)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[CONVEX_SUMS; CONVEX_BALL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`q:real^N`; `x - q:real^N`] THEN
    ASM_REWRITE_TAC[GSYM dist] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN {q + z:real^N | q IN s /\ z IN ball(vec 0,e)}` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `q:real^N` THEN
  ASM_REWRITE_TAC[dist; VECTOR_ARITH `(q + z) - q:real^N = z`]);;

(* The finite closed star of s in the first derived.                        *)

let MOI_FRS_C0 = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ s IN t
     ==> FINITE {q | ?r'. r' IN barycentric_subdivision t /\ ~(r' INTER s = {}) /\
                          q face_of r'} /\
         moi_bar_complex {q | ?r'. r' IN barycentric_subdivision t /\
                                   ~(r' INTER s = {}) /\ q face_of r'} /\
         UNIONS {q | ?r'. r' IN barycentric_subdivision t /\
                          ~(r' INTER s = {}) /\ q face_of r'} SUBSET UNIONS t /\
         (!r. r IN barycentric_subdivision t /\ ~(r INTER s = {})
              ==> r IN {q | ?r'. r' IN barycentric_subdivision t /\
                                 ~(r' INTER s = {}) /\ q face_of r'})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS t` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN t ==> s SUBSET UNIONS t`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FDN_MEETS_FACES_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FDN_MEETS_FACES_FINITE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
    MATCH_MP_TAC MOI_FDN_SUBCOMPLEX_BAR_COMPLEX THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (barycentric_subdivision t):real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[SUBSET_REFL]] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[simplicial_subcomplex];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]);;

(* Points of the derived neighbourhood lie in barycentric simplices whose  *)
(* chains consist of simplices of the first derived meeting s.              *)

let MOI_FRS_NBHD_CHAINS = prove
 (`!(t:(real^N->bool)->bool) s x.
     lf_simplicial_complex t /\ s IN t /\ x IN derived_nbhd t {f | f face_of s}
     ==> ?f. moi_bar_chain (barycentric_subdivision t) f /\ ~(f = {}) /\
             (!r. r IN f ==> ~(r INTER s = {})) /\
             x IN convex hull (IMAGE simplex_barycentre f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t {f | f face_of s}` THEN
  ASM_SIMP_TAC[MOI_FRS_NBHD_STARS; moi_fcl_dual] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplex_barycentre (p:real^N->bool) IN s` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (p:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_IN; FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `simplex_barycentre (p:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SING_SUBSET]);;

(* Every point of s lies in a simplex of the first derived inside s.        *)

let MOI_FRS_FACES_COVER = prove
 (`!(t:(real^N->bool)->bool) s x.
     lf_simplicial_complex t /\ s IN t /\ x IN s
     ==> ?r. r IN barycentric_subdivision t /\ x IN r /\ r SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex {f:real^N->bool | f face_of s}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_SUBCOMPLEX_BAR_COMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{f:real^N->bool | f face_of s}` MOI_BAR_UNIONS_SUBDIVISION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN UNIONS (barycentric_subdivision {f:real^N->bool | f face_of s})`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{f:real^N->bool | f face_of s}`; `t:(real^N->bool)->bool`]
      MOI_FDN_BAR_SUBDIVISION_MONO) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
    UNDISCH_TAC
     `(r:real^N->bool) IN barycentric_subdivision {f:real^N->bool | f face_of s}` THEN
    SET_TAC[];
    UNDISCH_TAC
     `(r:real^N->bool) IN barycentric_subdivision {f:real^N->bool | f face_of s}` THEN
    UNDISCH_TAC
     `UNIONS (barycentric_subdivision {f:real^N->bool | f face_of s}) = s` THEN
    SET_TAC[]]);;

let SIMPLEX_SMALL_CELL = prove
 (MOI_FND_SIMPLEX_SMALL_CELL,
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                       `v:real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^N->bool) /\ convex s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  (* the cell N *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] DERIVED_NBHD_SIMPLEX) THEN
  ASM_REWRITE_TAC[derived_frontier; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `fc:real^N->real^N`
    (X_CHOOSE_THEN `gc:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{f:real^N->bool | f face_of s}`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N = derived_nbhd t {f:real^N->bool | f face_of s}` THEN
  SUBGOAL_THEN
   `(!y. y IN k ==> (fc:real^N->real^N) y IN N) /\
    (!y. y IN k ==> (gc:real^N->real^N) (fc y) = y) /\
    (!x. x IN N ==> gc x IN k /\ fc (gc x) = x) /\
    pl_map_on k fc`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,N) (fc:real^N->real^N,gc)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* s lies in the image of the interior of k *)
  SUBGOAL_THEN `(s:real^N->bool) SUBSET IMAGE (fc:real^N->real^N) (relative_interior k)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN (subtopology euclidean (UNIONS t)) interior_of N`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN N` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERIOR_OF_SUBSET; SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `(gc:real^N->real^N) x` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gc:real^N->real^N) x IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gc:real^N->real^N) x IN relative_frontier k` ASSUME_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN (subtopology euclidean (UNIONS t)) frontier_of N`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gc:real^N->real^N) x` THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[frontier_of; IN_DIFF] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the closed star c0 and the separation distance e *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRS_C0) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = {q:real^N->bool | ?r'. r' IN barycentric_subdivision t /\
                                        ~(r' INTER s = {}) /\ q face_of r'}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inc0")))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS t)) (v:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N) DIFF w`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET v` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  (* the derived retriangulation h *)
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `s:real^N->bool`; `e:real`]
    MOI_FRS_SHRINK_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `d:(real^N->bool)->real^N`]
    MOI_FTA_DERIVED_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `h':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hull")
      (LABEL_TAC "fix"))))) THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS c0) (h:real^N->real^N) /\
    (!y. y IN UNIONS c0 ==> h y IN UNIONS c0) /\
    (!x y. x IN UNIONS c0 /\ y IN UNIONS c0 /\ h x = h y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (UNIONS c0,UNIONS c0) (h:real^N->real^N,h')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `IMAGE (h:real^N->real^N) u = u ==> !y. y IN u ==> h y IN u`) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* h moves N into v *)
  SUBGOAL_THEN `!x:real^N. x IN N ==> x IN UNIONS c0 /\ (h:real^N->real^N) x IN v`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
      MOI_FRS_NBHD_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET c0` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "inc0" MATCH_MP_TAC THEN
      ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain c0 (f:(real^N->bool)->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC
       `moi_bar_chain (barycentric_subdivision t) (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS c0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre f)` THEN
      UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET c0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) x IN convex hull (IMAGE (d:(real^N->bool)->real^N) f)`
    ASSUME_TAC THENL
     [USE_THEN "hull" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `moi_bar_chain c0 (f:(real^N->bool)->bool)`))) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `IMAGE (d:(real^N->bool)->real^N) f`; `e:real`]
      MOI_FRS_HULL_NEAR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "near" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:real^N->real^N) x IN UNIONS c0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(h:real^N->real^N) x IN UNIONS c0` THEN
      UNDISCH_TAC `UNIONS c0 SUBSET UNIONS (t:(real^N->bool)->bool)` THEN
      SET_TAC[];
      ASM_CASES_TAC `(h:real^N->real^N) x IN w` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `e <= dist(q:real^N,(h:real^N->real^N) x)` MP_TAC THENL
       [USE_THEN "sep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
        UNDISCH_TAC `dist((h:real^N->real^N) x,q) < e` THEN
        REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* s lies in h(s) *)
  SUBGOAL_THEN `!x:real^N. x IN s ==> ?y. y IN s /\ (h:real^N->real^N) y = x`
  (LABEL_TAC "hs") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
      MOI_FRS_FACES_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r:real^N->bool) IN c0` ASSUME_TAC THENL
     [USE_THEN "inc0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "fix" (fun th -> ASSUME_TAC(MATCH_MP th
      (ASSUME `(r:real^N->bool) IN c0`))) THEN
    SUBGOAL_THEN `(x:real^N) IN IMAGE (h:real^N->real^N) r` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  (* the composite cell map *)
  MP_TAC(ISPECL [`k:real^N->bool`; `(h:real^N->real^N) o (fc:real^N->real^N)`]
    MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS c0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(fc:real^N->real^N) y1 = fc y2` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real^N->real^N`) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `(h:real^N->real^N) o (fc:real^N->real^N)`;
                        `G:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE; o_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    USE_THEN "hs" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET IMAGE (fc:real^N->real^N) (relative_interior k)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^N` THEN ASM_MESON_TAC[]]);;

