(* ========================================================================= *)
(* pc_moi_fnd_tubecm: shared tools for the solid tori of the graph tube,    *)
(* used by pc_moi_fnd_tubec (triangle, Moise p.240) and pc_moi_fnd_tubep    *)
(* (polygon, Moise 24.11).  Contents (lemmas MOI_FTC_THETA3 and so on): the *)
(* level homeomorphism on several vertex stars (THETA3); radial tools at a  *)
(* vertex with a 2-sphere link (RAD, cones, SECTOR3, SECTOR2,               *)
(* RADIAL_PIECE); generic 2-dimensional tools in real^N (DISK_COMPLEMENT,   *)
(* GLUE_SEG); dual-cell facts (STAR_CHAIN, TRIPLE); the radial              *)
(* configuration predicate moi_ftc_rad; the product cell assembly           *)
(* (PROD_ASSEMBLY, generic in the label sets) with the nine-label disk      *)
(* combinatorics; product cells, the disk and triangle models and the spine *)
(* of a solid torus (TORUS_SPINE).  Loads pc_moi_s34_outer.                 *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s34_outer.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The level picture on several vertex stars at once.  For a               *)
(* finite set V of graph vertices, one simplex-preserving PL homeomorphism  *)
(* h of the union of the closed stars of V in t1 = sd t takes every dual    *)
(* cell C_v (v IN V) to the level region {f >= 1/2} and C_v INTER Bd N to   *)
(* the level surface {f = 1/2} in each simplex of the star of v, as         *)
(* MOI_FTA_THETA does for one star.                                          *)
(* ========================================================================= *)

let moi_ftc_cs = new_definition
 `moi_ftc_cs (c:(real^N->bool)->bool) (V:real^N->bool) =
    {s | ?v r. v IN V /\ r IN c /\ v IN r /\ s face_of r}`;;

let MOI_FTC_CS_FACTS = prove
 (`!(c:(real^N->bool)->bool) V.
     lf_simplicial_complex c /\ FINITE V /\ (!v. v IN V ==> {v} IN c)
     ==> FINITE (moi_ftc_cs c V) /\ moi_bar_complex (moi_ftc_cs c V) /\
         moi_ftc_cs c V SUBSET c /\
         (!v. v IN V ==> moi_fta_cstar c v SUBSET moi_ftc_cs c V) /\
         (!s. s IN moi_ftc_cs c V ==> ?v. v IN V /\ s IN moi_fta_cstar c v) /\
         UNIONS (moi_ftc_cs c V) = UNIONS {s | s IN c /\ ?v. v IN V /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_ftc_cs c (V:real^N->bool) = UNIONS {moi_fta_cstar c v | v IN V}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cs; moi_fta_cstar; UNIONS_GSPEC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. v IN V
       ==> FINITE (moi_fta_cstar c v) /\ moi_fta_cstar c v SUBSET c /\
           moi_bar_complex (moi_fta_cstar c v) /\
           UNIONS (moi_fta_cstar c v) = UNIONS {s | s IN c /\ v IN s}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_CSTAR_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE];
    MATCH_MP_TAC MOI_FTA_BAR_SUB THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
    REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; moi_ftc_cs; IN_ELIM_THM] THEN
      X_GEN_TAC `f:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o
        GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_ftc_cs; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_TRANS]];
    REWRITE_TAC[SUBSET; moi_ftc_cs; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `r:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; moi_ftc_cs; moi_fta_cstar; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[moi_ftc_cs; moi_fta_cstar; IN_ELIM_THM] THEN MESON_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[moi_ftc_cs; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC))
        ASSUME_TAC)) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC))
        ASSUME_TAC)) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`v:real^N`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN
      SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
       [ASM_MESON_TAC[lf_simplicial_complex]; ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]]]);;

(* The level homeomorphism on the union of the stars of V. *)

let MOI_FTC_THETA3 = prove
 (`!(t:(real^N->bool)->bool) l V.
     graph_in_complex t l /\ FINITE V /\ (!v. v IN V ==> {v} IN l) /\ ~(V = {})
     ==> ?h k. pl_homeomorphism
                 (UNIONS (moi_ftc_cs (barycentric_subdivision t) V),
                  UNIONS (moi_ftc_cs (barycentric_subdivision t) V)) (h,k) /\
               (!s. s IN moi_ftc_cs (barycentric_subdivision t) V ==> IMAGE h s = s) /\
               (!v m. v IN V /\ m IN barycentric_subdivision t /\ v IN m
                      ==> ?f. (!x y u. f((&1 - u) % x + u % y) =
                                       (&1 - u) * f x + u * f y) /\
                              (!a. a extreme_point_of m
                                   ==> f a = if a IN UNIONS l then &1 else &0) /\
                              f v = &1 /\
                              (!x. x IN IMAGE h (derived_dual_cell t l v) /\ x IN m <=>
                                   x IN m /\ &1 / &2 <= f x) /\
                              (!x. x IN IMAGE h (derived_dual_cell t l v INTER
                                                 derived_frontier t l) /\ x IN m <=>
                                   x IN m /\ f x = &1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN V
                 ==> lf_simplicial_complex t /\ simplicial_subcomplex l t /\
                     lf_simplicial_complex (barycentric_subdivision t) /\
                     moi_bar_complex (barycentric_subdivision t) /\
                     {v} IN barycentric_subdivision t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_SETUP) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v0:real^N. v0 IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool)) /\
                moi_bar_complex (barycentric_subdivision t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `V:real^N->bool`]
    MOI_FTC_CS_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `S = moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool)` THEN
  MP_TAC(ISPECL [`S:(real^N->bool)->bool`; `moi_fta_lev (l:(real^N->bool)->bool)`]
    MOI_FTA_DERIVED_HOMEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_SIMPLEX THEN
    EXISTS_TAC `S:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "fix"))))) THEN
  SUBGOAL_THEN `homeomorphism (UNIONS S,UNIONS S) (h:real^N->real^N,k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `m:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:real^N->bool) IN moi_fta_cstar (barycentric_subdivision t) v`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of m` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (m:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `W:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `\a:real^N. a IN UNIONS l`] MOI_FTA_LEVEL_FN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  EXISTS_TAC `f:real^N->real` THEN
  UNDISCH_TAC `(v:real^N) extreme_point_of convex hull W` THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_SIMP_TAC[IN_SING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  (* the property of chains inside the star of v *)
  ABBREV_TAC
   `Pv = \g:(real^N->bool)->bool. moi_fta_gp l g /\
           !r. r IN g ==> r IN moi_fta_cstar (barycentric_subdivision t) v` THEN
  ABBREV_TAC
   `Mv = \g:(real^N->bool)->bool. moi_fta_gm l g /\
           !r. r IN g ==> r IN moi_fta_cstar (barycentric_subdivision t) v` THEN
  SUBGOAL_THEN `moi_fta_cstar (barycentric_subdivision t) v SUBSET (S:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. (moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g /\ moi_fta_gp l g <=>
         moi_bar_chain S g /\ (Pv:((real^N->bool)->bool)->bool) g) /\
        (moi_bar_chain (moi_fta_cstar (barycentric_subdivision t) v) g /\ moi_fta_gm l g <=>
         moi_bar_chain S g /\ (Mv:((real^N->bool)->bool)->bool) g)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["Pv"; "Mv"] THEN REWRITE_TAC[moi_bar_chain] THEN
    UNDISCH_TAC `moi_fta_cstar (barycentric_subdivision t) v SUBSET (S:(real^N->bool)->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_dual_cell t l v INTER derived_frontier t l =
    UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
            moi_bar_chain S g /\ (Mv:((real^N->bool)->bool)->bool) g} /\
    derived_dual_cell t l v =
    UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
            moi_bar_chain S g /\ (Pv:((real^N->bool)->bool)->bool) g}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_CELL_CHAINS) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_CELL_FRONTIER_CHAINS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!g g'. (Pv:((real^N->bool)->bool)->bool) g /\ g' SUBSET g /\ ~(g' = {}) ==> Pv g') /\
    (!g g'. (Mv:((real^N->bool)->bool)->bool) g /\ g' SUBSET g /\ ~(g' = {}) ==> Mv g')`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Pv"; "Mv"] THEN
    MP_TAC(ISPEC `l:(real^N->bool)->bool` MOI_FTA_GP_GM_HER) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. moi_bar_chain {r | r face_of convex hull W} g
        ==> ((Pv:((real^N->bool)->bool)->bool) g <=> moi_fta_gp l g) /\
            ((Mv:((real^N->bool)->bool)->bool) g <=> moi_fta_gm l g)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["Pv"; "Mv"] THEN
    SUBGOAL_THEN `!r. r IN (g:(real^N->bool)->bool)
                      ==> r IN moi_fta_cstar (barycentric_subdivision t) v`
      (fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^N` THENL
   [MP_TAC(ISPECL [`S:(real^N->bool)->bool`;
      `h:real^N->real^N`; `k:real^N->real^N`;
      `moi_fta_lev (l:(real^N->bool)->bool)`; `convex hull W:real^N->bool`;
      `Pv:((real^N->bool)->bool)->bool`; `x:real^N`] MOI_FTA_TRANSFER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC); DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `?g. moi_bar_chain {r | r face_of convex hull W} g /\ moi_fta_gp l g /\
                    (x:real^N) IN convex hull (IMAGE (moi_fta_lev l) g)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `g:(real^N->bool)->bool` THEN BETA_TAC THEN
      ASM_CASES_TAC `moi_bar_chain {r | r face_of convex hull W} (g:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_SIMPLEX_LEVEL_GE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`S:(real^N->bool)->bool`;
      `h:real^N->real^N`; `k:real^N->real^N`;
      `moi_fta_lev (l:(real^N->bool)->bool)`; `convex hull W:real^N->bool`;
      `Mv:((real^N->bool)->bool)->bool`; `x:real^N`] MOI_FTA_TRANSFER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC); DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `?g. moi_bar_chain {r | r face_of convex hull W} g /\ moi_fta_gm l g /\
                    (x:real^N) IN convex hull (IMAGE (moi_fta_lev l) g)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `g:(real^N->bool)->bool` THEN BETA_TAC THEN
      ASM_CASES_TAC `moi_bar_chain {r | r face_of convex hull W} (g:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_SIMPLEX_LEVEL_EQ THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Radial tools at a vertex v of a complex c whose link L is a              *)
(* PL 2-sphere.  Y is a level region of the star of v (per simplex m with  *)
(* v IN m it is {f >= 1/2}, f affine with f v = 1) and Z its level surface  *)
(* {f = 1/2}.  Then X = Z UNION (Y INTER L) is a PL 2-sphere met once by    *)
(* every ray from v through L and Y is the cone from v over X (tubea's      *)
(* MOI_FTA_CONE_FROM_RAYS and MOI_FTA_RSS); sectors of Y over 2-cells of    *)
(* L are 3-cells and the radial pieces of X over them are 2-cells.          *)
(* ========================================================================= *)

let MOI_FTC_RAD = prove
 (`!c (v:real^N) Y Z.
     lf_simplicial_complex c /\ {v} IN c /\
     pl_sphere 2 (UNIONS (simplicial_link c v)) /\
     Y SUBSET UNIONS {s | s IN c /\ v IN s} /\ Z SUBSET Y /\
     pl_polyhedron Y /\ pl_polyhedron Z /\
     (!m. m IN c /\ v IN m
          ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                  f v = &1 /\
                  (!x. x IN Y /\ x IN m <=> x IN m /\ &1 / &2 <= f x) /\
                  (!x. x IN Z /\ x IN m <=> x IN m /\ f x = &1 / &2))
     ==> ~(v IN UNIONS (simplicial_link c v)) /\
         (!x y. x IN UNIONS (simplicial_link c v) /\
                y IN UNIONS (simplicial_link c v) /\ y IN segment[v,x] ==> y = x) /\
         UNIONS {s | s IN c /\ v IN s} =
         UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)} /\
         (!y. y IN UNIONS (simplicial_link c v)
              ==> ?!r. &0 < r /\ r <= &1 /\
                       v + r % (y - v) IN Z UNION (Y INTER UNIONS (simplicial_link c v))) /\
         ~(v IN Z UNION (Y INTER UNIONS (simplicial_link c v))) /\
         (!x y. x IN Z UNION (Y INTER UNIONS (simplicial_link c v)) /\
                y IN Z UNION (Y INTER UNIONS (simplicial_link c v)) /\
                y IN segment[v,x] ==> y = x) /\
         Y = UNIONS {segment[v,x] | x | x IN Z UNION (Y INTER UNIONS (simplicial_link c v))} /\
         pl_sphere 2 (Z UNION (Y INTER UNIONS (simplicial_link c v))) /\
         3 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lev")))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rad")) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_LINK_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `UNIONS (simplicial_link c (v:real^N))`;
                 `Y:real^N->bool`; `Z:real^N->bool`] MOI_FTA_CONE_FROM_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS {s | s IN c /\ (v:real^N) IN s} =
                 UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      X_GEN_TAC `y:real^N` THEN
      REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `qq:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
      USE_THEN "lev" (MP_TAC o SPEC `m:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `f:real^N->real`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SIMPLEX_IMP_CONVEX];
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC MOI_FTA_RSS THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(Y:real^N->bool) SUBSET UNIONS {s | s IN c /\ v IN s}` THEN
    UNDISCH_TAC `(Z:real^N->bool) SUBSET Y` THEN SET_TAC[]]);;

(* Cones from a point over polyhedra are polyhedra. *)

let MOI_FTC_POLYTOPE_CONE = prove
 (`!(v:real^N) k. polytope k ==> polytope (convex hull (v INSERT k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polytope] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(v:real^N) INSERT w` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; GSYM HULL_INSERT]);;

let MOI_FTC_CONE_POLYHEDRON = prove
 (`!(v:real^N) A. pl_polyhedron A ==> pl_polyhedron (UNIONS {segment[v,y] | y | y IN A})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\k. convex hull ((v:real^N) INSERT k)) {k | k IN cc /\ ~(k = {})}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `cc:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTC_POLYTOPE_CONE THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC)) THEN
      EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^N) IN t` THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC(`z:real^N`,`z:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?y:real^N. y IN k /\ z IN segment[v,y]` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN convex hull (v INSERT k)` THEN
        REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `convex hull (k:real^N->bool) = k` SUBST1_TAC THENL
         [REWRITE_TAC[CONVEX_HULL_EQ] THEN ASM_MESON_TAC[POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `segment[v:real^N,y]` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^N` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

(* Points on rays from v through a set L with the segment property. *)

let MOI_FTC_RAY_EQ = prove
 (`!(v:real^N) L y1 y2 r1 r2.
     ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     y1 IN L /\ y2 IN L /\ &0 < r1 /\ &0 < r2 /\
     v + r1 % (y1 - v) = v + r2 % (y2 - v)
     ==> y1 = y2 /\ r1 = r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r1 % ((y1:real^N) - v) = r2 % (y2 - v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[VECTOR_ARITH `v + a:real^N = v + b <=> a = b`]; ALL_TAC] THEN
  SUBGOAL_THEN `y1 = (y2:real^N)` ASSUME_TAC THENL
   [ASM_CASES_TAC `r1 <= r2` THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `r1 / r2` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      SUBGOAL_THEN `(r1 / r2) % ((y1:real^N) - v) = y2 - v` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        VECTOR_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `r2 / r1` THEN
      SUBGOAL_THEN `r2 <= r1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      SUBGOAL_THEN `(r2 / r1) % ((y2:real^N) - v) = y1 - v` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM(ASSUME `r1 % ((y1:real^N) - v) = r2 % (y2 - v)`)] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `r1 % ((y1:real^N) - v) = r2 % (y2 - v)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_SUB_EQ] THEN
  ASM_MESON_TAC[]);;

let MOI_FTC_CONE_RAY = prove
 (`!(v:real^N) A z.
     z IN UNIONS {segment[v,y] | y | y IN A} /\ ~(z = v)
     ==> ?y r. y IN A /\ &0 < r /\ r <= &1 /\ z = v + r % (y - v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^N) IN t` THEN ASM_REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `u:real`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `~((z:real^N) = v)` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_FTC_CONE_MONO = prove
 (`!(v:real^N) A B.
     A SUBSET B ==> UNIONS {segment[v,y] | y | y IN A} SUBSET UNIONS {segment[v,y] | y | y IN B}`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_IN_CONE = prove
 (`!(v:real^N) A y r.
     y IN A /\ &0 <= r /\ r <= &1 ==> v + r % (y - v) IN UNIONS {segment[v,y] | y | y IN A}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `segment[v:real^N,y]` THEN
  CONJ_TAC THENL [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]);;

let MOI_FTC_CONE_INTER = prove
 (`!(v:real^N) L A B.
     ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     A SUBSET L /\ B SUBSET L /\ ~(A INTER B = {})
     ==> UNIONS {segment[v,y] | y | y IN A} INTER UNIONS {segment[v,y] | y | y IN B} =
         UNIONS {segment[v,y] | y | y IN A INTER B}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER]) THEN
    ASM_CASES_TAC `z:real^N = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((A:real^N->bool) INTER B = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      MP_TAC(ISPECL [`v:real^N`; `A INTER B:real^N->bool`; `y:real^N`; `&0`]
        MOI_FTC_IN_CONE) THEN
      ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `A:real^N->bool`; `z:real^N`] MOI_FTC_CONE_RAY) THEN
    MP_TAC(ISPECL [`v:real^N`; `B:real^N->bool`; `z:real^N`] MOI_FTC_CONE_RAY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:real^N` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `y1:real^N`; `y2:real^N`;
                   `r1:real`; `r2:real`] MOI_FTC_RAY_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `A INTER B:real^N->bool`; `y1:real^N`; `r1:real`]
      MOI_FTC_IN_CONE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_INTER] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t /\ s SUBSET u ==> s SUBSET t INTER u`) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN SET_TAC[]]);;

(* The radial point of X over y IN L. *)

let MOI_FTC_RAY_POINT = prove
 (`!(v:real^N) L X y.
     (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\ y IN L
     ==> ?r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X /\
             (!s. &0 < s /\ s <= &1 /\ v + s % (y - v) IN X ==> s = r)`,
  MESON_TAC[]);;

(* A sector of a cone over X is the cone over the sector of X. *)

let MOI_FTC_CONE_SECT = prove
 (`!(v:real^N) L X Y A.
     ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     X SUBSET UNIONS {segment[v,y] | y | y IN L} /\
     Y = UNIONS {segment[v,x] | x | x IN X} /\ A SUBSET L /\ ~(A = {})
     ==> Y INTER UNIONS {segment[v,y] | y | y IN A} =
         UNIONS {segment[v,x] | x | x IN X INTER UNIONS {segment[v,y] | y | y IN A}}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. x IN X ==> ?y r. y IN L /\ &0 < r /\ r <= &1 /\ x = v + r % (y - v)`
  (LABEL_TAC "xr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_CONE_RAY THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER]) THEN
    ASM_CASES_TAC `z:real^N = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(A:real^N->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `y:real^N`]
        MOI_FTC_RAY_POINT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(A:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(y:real^N) IN A` THEN
        SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[v:real^N,v + r % (y - v)]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `v + r % (y - v):real^N` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC MOI_FTC_IN_CONE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^N) IN Y` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    USE_THEN "xr" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN X`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:real^N` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`v:real^N`; `A:real^N->bool`; `z:real^N`] MOI_FTC_CONE_RAY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(z:real^N) IN t` THEN
    REWRITE_TAC[ASSUME `t = segment[v:real^N,x]`; MOI_STA_SEGMENT_PARAM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `~((z:real^N) = v)` THEN
      REWRITE_TAC[ASSUME `z:real^N = v + &0 % (x - v)`; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `y1:real^N`; `y2:real^N`;
                   `r1:real`; `u * r2:real`] MOI_FTC_RAY_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_SIMP_TAC[REAL_LT_MUL];
        UNDISCH_TAC `z:real^N = v + r1 % (y1 - v)` THEN
        UNDISCH_TAC `z:real^N = v + u % (x - v)` THEN
        UNDISCH_TAC `x:real^N = v + r2 % (y2 - v)` THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC];
      STRIP_TAC] THEN
    UNDISCH_TAC `x:real^N = v + r2 % (y2 - v)` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTC_IN_CONE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:real^N) IN X INTER UNIONS {segment[v,y] | y | y IN A}` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `A:real^N->bool`; `x:real^N`] MOI_FTC_CONE_RAY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(z:real^N) IN t` THEN ASM_REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v + u % ((v + r % (y - v)) - v):real^N = v + (u * r) % (y - v)`
    SUBST1_TAC THENL [REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTC_IN_CONE THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `u * r <= &1 * &1 ==> u * r <= &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* A cell is not contained in its boundary. *)

let MOI_FTC_CELL_NOT_SUBSET = prove
 (`!n (d:real^N->bool) j. 1 <= n /\ pl_cell_with_boundary n d j ==> ~(d SUBSET j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `closed (k:real^N->bool) /\ convex k /\ ~(k = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&(CARD({}:real^N->bool)):int = &n + &1` THEN
      REWRITE_TAC[CARD_CLAUSES] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN relative_interior k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k,d) (f:real^N->real^N,g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) y IN IMAGE f (relative_frontier k)` MP_TAC THENL
   [UNDISCH_TAC `(d:real^N->bool) SUBSET j` THEN
    UNDISCH_TAC `j = IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y':real^N) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(y':real^N) IN relative_frontier k` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_SIMP_TAC[CLOSURE_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `y:real^N = y'` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `(g:real^N->real^N) (f y) = y /\ g (f y') = y'` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(y':real^N) IN relative_frontier k` THEN
  ASM_REWRITE_TAC[relative_frontier; IN_DIFF]);;

(* The radial piece of the sphere X over a 2-cell D of L (L = D UNION D',   *)
(* D INTER D' = J) is a 2-cell bounded by the radial piece over J.          *)

let MOI_FTC_CONE_UNION = prove
 (`!(v:real^N) A B.
     UNIONS {segment[v,y] | y | y IN A UNION B} =
     UNIONS {segment[v,y] | y | y IN A} UNION UNIONS {segment[v,y] | y | y IN B}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_RAY_OF = prove
 (`!(v:real^N) L y r A.
     ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     y IN L /\ &0 < r /\ A SUBSET L /\
     v + r % (y - v) IN UNIONS {segment[v,y] | y | y IN A}
     ==> y IN A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `A:real^N->bool`; `v + r % (y - v):real^N`]
    MOI_FTC_CONE_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `v + r % (y - v):real^N = v <=> r % (y - v) = vec 0`;
                    VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` (X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `y:real^N`; `y':real^N`;
                 `r:real`; `r':real`] MOI_FTC_RAY_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_MESON_TAC[]]);;

let MOI_FTC_RADIAL_PIECE = prove
 (`!(v:real^N) L X D D' J.
     pl_sphere 2 X /\ ~(v IN L) /\
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     X SUBSET UNIONS {segment[v,y] | y | y IN L} /\
     pl_cell_with_boundary 2 D J /\ pl_cell_with_boundary 2 D' J /\
     D UNION D' = L /\ D INTER D' = J
     ==> pl_cell_with_boundary 2 (X INTER UNIONS {segment[v,y] | y | y IN D})
                                 (X INTER UNIONS {segment[v,y] | y | y IN J})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (J:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `D:real^N->bool`; `J:real^N->bool`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(J:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET D /\ D SUBSET L /\ D' SUBSET L /\ J SUBSET L`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(D:real^N->bool) UNION D' = L` THEN
    UNDISCH_TAC `(D:real^N->bool) INTER D' = J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (X:real^N->bool) /\ pl_polyhedron (D:real^N->bool) /\
                pl_polyhedron (D':real^N->bool) /\ pl_polyhedron (J:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY; MOI_S4O_CELL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!A:real^N->bool. pl_polyhedron A ==> closed (UNIONS {segment[v,y] | y | y IN A})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_SIMP_TAC[MOI_FTC_CONE_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x y:real^N. x IN J /\ y IN J /\ y IN segment[v,x] ==> y = x) /\
                ~((v:real^N) IN J)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN L ==> ?r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X`
  (LABEL_TAC "rx") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN X ==> ?y r. y IN L /\ &0 < r /\ r <= &1 /\ x = v + r % (y - v)`
  (LABEL_TAC "xr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_CONE_RAY THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN EXISTS_TAC `X:real^N->bool` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4O_RADIAL_CIRCLE THEN
    MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_SIMP_TAC[MOI_FTC_CONE_POLYHEDRON];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(y:real^N) IN J` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN
    USE_THEN "rx" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN L`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_IN_CONE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `J:real^N->bool`)) (concl th)) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "?!"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `r:real` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC(SET_RULE `(a:real^N->bool) SUBSET b ==> x INTER a SUBSET x INTER b`) THEN
    MATCH_MP_TAC MOI_FTC_CONE_MONO THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED;
      PL_POLYHEDRON_IMP_COMPACT];
    (* the frontier condition *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(X INTER UNIONS {segment[v:real^N,y] | y | y IN D'}) INTER
                (X INTER UNIONS {segment[v,y] | y | y IN D})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(c:real^N->bool) SUBSET a ==> c INTER b SUBSET a INTER b`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [UNDISCH_TAC `(X:real^N->bool) SUBSET UNIONS {segment[v,y] | y | y IN L}` THEN
        UNDISCH_TAC `(D:real^N->bool) UNION D' = L` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[MOI_FTC_CONE_UNION] THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED;
          PL_POLYHEDRON_IMP_COMPACT]];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^N->bool) INTER b SUBSET c
                           ==> (x INTER a) INTER (x INTER b) SUBSET x INTER c`) THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `D':real^N->bool`; `D:real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(D:real^N->bool) INTER D' = J` THEN UNDISCH_TAC `~(J:real^N->bool = {})` THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOI_FTC_CONE_MONO THEN
    UNDISCH_TAC `(D:real^N->bool) INTER D' = J` THEN SET_TAC[];
    (* ~(XD SUBSET XJ) *)
    MP_TAC(ISPECL [`2`; `D:real^N->bool`; `J:real^N->bool`] MOI_FTC_CELL_NOT_SUBSET) THEN
    ASM_REWRITE_TAC[ARITH] THEN REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL
     [UNDISCH_TAC `(D:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(y:real^N) IN D` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "rx" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN L`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v + r % (y - v):real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_FTC_IN_CONE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
                    ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN J)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTC_RAY_OF THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `L:real^N->bool`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    (* ~(X SUBSET XD) *)
    MP_TAC(ISPECL [`2`; `D':real^N->bool`; `J:real^N->bool`] MOI_FTC_CELL_NOT_SUBSET) THEN
    ASM_REWRITE_TAC[ARITH] THEN REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL
     [UNDISCH_TAC `(D':real^N->bool) SUBSET L` THEN UNDISCH_TAC `(y:real^N) IN D'` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "rx" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN L`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v + r % (y - v):real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN D` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTC_RAY_OF THEN
      MAP_EVERY EXISTS_TAC [`v:real^N`; `L:real^N->bool`; `r:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^N) IN J)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(D:real^N->bool) INTER D' = J` THEN
    UNDISCH_TAC `(y:real^N) IN D` THEN UNDISCH_TAC `(y:real^N) IN D'` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Sectors of a level region over pieces of the link: over a               *)
(* 2-cell of L a 3-cell (cone over the radial piece of X), over an arc of a *)
(* circle of L a 2-cell, and the radial piece of X over an arc is an arc.   *)
(* ========================================================================= *)

let MOI_FTC_SECTOR3 = prove
 (`!(v:real^N) L X Y D D' J.
     pl_sphere 2 X /\ ~(v IN L) /\
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x) /\
     X SUBSET UNIONS {segment[v,y] | y | y IN L} /\
     Y = UNIONS {segment[v,x] | x | x IN X} /\ 3 <= dimindex(:N) /\
     pl_cell_with_boundary 2 D J /\ pl_cell_with_boundary 2 D' J /\
     D UNION D' = L /\ D INTER D' = J
     ==> pl_cell_with_boundary 3 (Y INTER UNIONS {segment[v,y] | y | y IN D})
           ((X INTER UNIONS {segment[v,y] | y | y IN D}) UNION
            (Y INTER UNIONS {segment[v,y] | y | y IN J}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `D:real^N->bool`;
                 `D':real^N->bool`; `J:real^N->bool`] MOI_FTC_RADIAL_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(J:real^N->bool = {}) /\ ~(D:real^N->bool = {}) /\
                (J:real^N->bool) SUBSET L /\ D SUBSET L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_sphere 1 (J:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`1`; `D:real^N->bool`; `J:real^N->bool`] MOI_S4O_CELL_SPHERE) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(J:real^N->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(D:real^N->bool) UNION D' = L` THEN
    UNDISCH_TAC `(D:real^N->bool) INTER D' = J` THEN
    UNDISCH_TAC `~(J:real^N->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `D:real^N->bool`] MOI_FTC_CONE_SECT) THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `J:real^N->bool`] MOI_FTC_CONE_SECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`2`; `X INTER UNIONS {segment[v:real^N,y] | y | y IN D}`;
                 `X INTER UNIONS {segment[v:real^N,y] | y | y IN J}`; `v:real^N`]
    MOI_FCL_CONE_CELL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[IN_INTER] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Generic 2-dimensional tools in real^N: the complement of a                *)
(* disk in a 2-sphere (DISK_COMPLEMENT, for real^N), two disks glued         *)
(* along a common boundary segment, and the sector of a level region over an *)
(* arc of the link.                                                          *)
(* ========================================================================= *)

let MOI_FTC_DISK_COMPLEMENT = prove
 (`!s d j:real^N->bool.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
     ==> pl_cell_with_boundary 2 ((s DIFF d) UNION j) j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_sphere])
    STRIP_ASSUME_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `vec 0:real^3` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k3:real^3->bool`; `k:real^N->bool`; `&3:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `G = (f:real^N->real^N) o (p:real^3->real^N)` THEN
  ABBREV_TAC `G' = (q:real^N->real^3) o (g:real^N->real^N)` THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier k3,s:real^N->bool)
                  ((G:real^3->real^N),(G':real^N->real^3))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "G'"] THEN
    MATCH_MP_TAC(ISPECL [`relative_frontier k3:real^3->bool`;
       `relative_frontier k:real^N->bool`; `s:real^N->bool`;
       `p:real^3->real^N`; `q:real^N->real^3`; `f:real^N->real^N`;
       `g:real^N->real^N`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (s:real^N->bool,relative_frontier k3)
                  ((G':real^N->real^3),(G:real^3->real^N))`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_SIMPLEX) THEN
    DISCH_THEN(MP_TAC o SPEC `&3:int`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> can (find_term ((=) `relative_frontier (k3:real^3->bool)`))
                         (concl th) &&
                     can (find_term ((=) `G:real^3->real^N`)) (concl th) &&
                     can (find_term ((=) `s:real^N->bool`)) (concl th) &&
                     fst(dest_pair(rand(concl th))) = `G:real^3->real^N`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET d` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      can (find_term ((=) `d:real^N->bool`)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (G':real^N->real^3) d) (IMAGE G' j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `relative_frontier k3:real^3->bool`;
                          `G:real^3->real^N`] THEN
    ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k3:real^3->bool`; `IMAGE (G':real^N->real^3) d`;
                 `IMAGE (G':real^N->real^3) j`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[ARITH_RULE `2 + 1 = 3`]
        (SPEC `2` PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX)) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `j = IMAGE (G:real^3->real^N) (IMAGE G' j)`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(s DIFF d) UNION j =
    IMAGE (G:real^3->real^N)
      ((relative_frontier k3 DIFF IMAGE (G':real^N->real^3) d) UNION IMAGE G' j)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`relative_frontier k3:real^3->bool`; `s:real^N->bool`;
                        `G':real^N->real^3`] THEN
  ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL] THEN
  UNDISCH_TAC `IMAGE (G':real^N->real^3) s = relative_frontier k3` THEN
  UNDISCH_TAC `(j:real^N->bool) SUBSET d` THEN UNDISCH_TAC `(d:real^N->bool) SUBSET s` THEN
  SET_TAC[]);;

(* Two PL 2-cells meeting exactly in a common boundary segment. *)

let MOI_FTC_GLUE_SEG = prove
 (`!(d1:real^N->bool) j1 d2 j2 p q.
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\ ~(p = q) /\
     d1 INTER d2 = segment[p,q] /\ segment[p,q] SUBSET j1 /\ segment[p,q] SUBSET j2
     ==> pl_cell_with_boundary 2 (d1 UNION d2)
           ((j1 UNION j2) DIFF (segment[p,q] DIFF {p,q}))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN CONJ_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d1:real^N->bool) j1` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_SIMPLEX) THEN
    DISCH_THEN(MP_TAC o SPEC `&2:int`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d1:real^N->bool`; `j1:real^N->bool`; `d2:real^N->bool`;
                 `j2:real^N->bool`; `linepath(p:real^N,q)`] MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
               PATH_IMAGE_LINEPATH; ARC_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
  REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]);;

(* The radial trace on X of a circle of the link is a circle. *)

let MOI_FTC_RADIAL_J = prove
 (`!(v:real^N) L X J.
     pl_polyhedron X /\ ~(v IN L) /\
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     pl_sphere 1 J /\ J SUBSET L
     ==> pl_sphere 1 (X INTER UNIONS {segment[v,y] | y | y IN J})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4O_RADIAL_CIRCLE THEN
  MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `v:real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTC_CONE_POLYHEDRON THEN ASM_MESON_TAC[MOI_S4O_SPHERE_POLY];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_IN_CONE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_MESON_TAC[]]);;

(* On a ray through a point of the link lying on X, X is met only there. *)

let MOI_FTC_X_SEG = prove
 (`!(v:real^N) L X y.
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     y IN L /\ y IN X
     ==> X INTER segment[v,y] = {y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `(v + r % (y - v):real^N) IN X` ASSUME_TAC THENL
   [UNDISCH_TAC `((&1 - r) % v + r % y:real^N) IN X` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [UNDISCH_TAC `(v + r % (y - v):real^N) IN X` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `r:real` th) THEN MP_TAC(SPEC `&1` th)) THEN
  REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `v + (y - v):real^N = y`] THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `r = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

let MOI_FTC_CONE_PAIR = prove
 (`!(v:real^N) a b.
     UNIONS {segment[v,y] | y | y IN {a,b}} = segment[v,a] UNION segment[v,b]`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
  MESON_TAC[]);;

(* A point of B SUBSET L off the two points gives a point of the radial    *)
(* trace of B on X off them.                                               *)

let MOI_FTC_TRACE_NOT_SUBSET = prove
 (`!(v:real^N) L X B e1 e2.
     ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     B SUBSET L /\ ~(B SUBSET {e1,e2}) /\ e1 IN L /\ e2 IN L
     ==> ~(X INTER UNIONS {segment[v,y] | y | y IN B} SUBSET {e1,e2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~((B:real^N->bool) SUBSET {e1,e2})` THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC))) THEN
  EXISTS_TAC `v + r % (y - v):real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_IN_CONE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `y:real^N`; `e1:real^N`; `r:real`; `&1`]
      MOI_FTC_RAY_EQ);
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `y:real^N`; `e2:real^N`; `r:real`; `&1`]
      MOI_FTC_RAY_EQ)] THEN
  ASM_REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; VECTOR_ARITH `v + (e - v):real^N = e`] THEN
  ASM SET_TAC[]);;

(* The sector of the level region over an arc A of a circle A UNION A' of  *)
(* the link (A, A' meeting in the two points e1, e2 of X).                 *)

let MOI_FTC_SECTOR2 = prove
 (`!(v:real^N) L X Y A A' e1 e2.
     pl_sphere 2 X /\ ~(v IN L) /\
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
     (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x) /\
     X SUBSET UNIONS {segment[v,y] | y | y IN L} /\
     Y = UNIONS {segment[v,x] | x | x IN X} /\ 3 <= dimindex(:N) /\
     pl_sphere 1 (A UNION A') /\ A UNION A' SUBSET L /\
     pl_polyhedron A /\ pl_polyhedron A' /\
     A INTER A' = {e1,e2} /\ ~(e1 = e2) /\ ~(A SUBSET {e1,e2}) /\ ~(A' SUBSET {e1,e2}) /\
     e1 IN X /\ e2 IN X
     ==> pl_cell_with_boundary 1 (X INTER UNIONS {segment[v,y] | y | y IN A}) {e1,e2} /\
         pl_cell_with_boundary 2 (Y INTER UNIONS {segment[v,y] | y | y IN A})
           ((X INTER UNIONS {segment[v,y] | y | y IN A}) UNION
            segment[v,e1] UNION segment[v,e2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^N->bool) SUBSET L /\ A' SUBSET L /\ (e1:real^N) IN L /\ e2 IN L /\
                ~(A:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(A:real^N->bool) INTER A' = {e1,e2}` THEN
    UNDISCH_TAC `(A:real^N->bool) UNION A' SUBSET L` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (X:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!B:real^N->bool. pl_polyhedron B
                     ==> closed (X INTER UNIONS {segment[v,y] | y | y IN B})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_SIMP_TAC[MOI_FTC_CONE_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 1 (X INTER UNIONS {segment[v:real^N,y] | y | y IN A}) {e1,e2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
    MAP_EVERY EXISTS_TAC
     [`X INTER UNIONS {segment[v:real^N,y] | y | y IN A UNION A'}`;
      `X INTER UNIONS {segment[v:real^N,y] | y | y IN A'}`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_RADIAL_J THEN EXISTS_TAC `L:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_FTC_CONE_UNION] THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `UNIONS {segment[v:real^N,y] | y | y IN A'} INTER
        UNIONS {segment[v,y] | y | y IN A} = segment[v,e1] UNION segment[v,e2]`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `A':real^N->bool`; `A:real^N->bool`]
          MOI_FTC_CONE_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(A:real^N->bool) INTER A' = {e1,e2}` THEN SET_TAC[];
          DISCH_THEN SUBST1_TAC] THEN
        SUBGOAL_THEN `(A':real^N->bool) INTER A = {e1,e2}` SUBST1_TAC THENL
         [UNDISCH_TAC `(A:real^N->bool) INTER A' = {e1,e2}` THEN SET_TAC[];
          REWRITE_TAC[MOI_FTC_CONE_PAIR]];
        ALL_TAC] THEN
      REWRITE_TAC[SET_RULE `((x:real^N->bool) INTER a) INTER (x INTER b) =
                            x INTER (a INTER b)`] THEN
      ASM_REWRITE_TAC[UNION_OVER_INTER] THEN
      MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `e1:real^N`]
        MOI_FTC_X_SEG) THEN
      MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `e2:real^N`]
        MOI_FTC_X_SEG) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FTC_TRACE_NOT_SUBSET THEN EXISTS_TAC `L:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FTC_TRACE_NOT_SUBSET THEN EXISTS_TAC `L:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `A:real^N->bool`] MOI_FTC_CONE_SECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_S4O_CONE_ARC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Simplicial facts in the first barycentric subdivision near                *)
(* the triangle s = conv{a,b,c} and the 3-simplex sigma1 = conv{a,b,c,x}:    *)
(* the closed star of a vertex meets the hull of a chain in the hull of the  *)
(* subchain of the simplices containing the vertex; three dual cells of     *)
(* distinct vertices of the graph never meet.                               *)
(* ========================================================================= *)

let MOI_FTC_STAR_CHAIN = prove
 (`!(t:(real^N->bool)->bool) v h.
     lf_simplicial_complex t /\ {v} IN t /\ moi_bar_chain t h
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER
         convex hull (IMAGE simplex_barycentre h) =
         convex hull (IMAGE simplex_barycentre {c | c IN h /\ v IN c})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain t {c:real^N->bool | c IN h /\ v IN c}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{c:real^N->bool | c IN h /\ v IN c} = h INTER {c | v IN c}`
    SUBST1_TAC THENL [SET_TAC[]; ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[MOI_FTA_IN_STAR1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (g INTER h))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                     `h:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_CHAIN_VERTEX_ALL) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]] THEN
  ASM_CASES_TAC `{c:real^N->bool | c IN h /\ v IN c} = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                ({v:real^N} INSERT {c | c IN h /\ v IN c}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
  REWRITE_TAC[IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN CONJ_TAC THENL
   [EXISTS_TAC `{v:real^N} INSERT {c | c IN h /\ v IN c}` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
    EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING]]);;

(* Three dual cells of distinct vertices of the graph never meet (as in     *)
(* MOI_FTA_CELLS_DISJOINT: a common point lies in the hull of a chain of    *)
(* simplices containing all three vertices, which has no member in l).     *)
(* Same statement as MOI_S4L_CELLS_TRIPLE of pc_moi_s34_tinf, which is not  *)
(* in this closure (it would add six files).                                *)

let MOI_FTC_TRIPLE = prove
 (`!(t:(real^N->bool)->bool) l u v w.
     graph_in_complex t l /\ {u} IN l /\ {v} IN l /\ {w} IN l /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w)
     ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
         derived_dual_cell t l w = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{u:real^N} IN t /\ {v:real^N} IN t /\ {w:real^N} IN t`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
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
  SUBGOAL_THEN `moi_bar_chain t ((h1 INTER h2):(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre ((h1 INTER h2) INTER h3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1 INTER h2:(real^N->bool)->bool`;
                   `h3:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h1:(real^N->bool)->bool`;
                   `h2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
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
  SUBGOAL_THEN `sg = segment[u:real^N,v]` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_GRAPH_TWO_VERTICES THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of segment[u,v]` MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_EXTREME_SEGMENT) THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The radial configuration at a vertex v (moi_ftc_rad) and                 *)
(* the cone from v over a set; radial traces on the link.                   *)
(* ========================================================================= *)

let moi_ftc_cone = new_definition
 `moi_ftc_cone (v:real^N) A = UNIONS {segment[v,y] | y | y IN A}`;;

let moi_ftc_rad = new_definition
 `moi_ftc_rad (v:real^N) L X Y <=>
    ~(v IN L) /\ (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
    ~(v IN X) /\ (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X) /\
    (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x) /\
    X SUBSET moi_ftc_cone v L /\ Y = moi_ftc_cone v X /\
    pl_sphere 2 X /\ pl_sphere 2 L /\ 3 <= dimindex(:N)`;;

(* Radial traces on L and on X over the pieces of the link. *)

let MOI_FTC_RAD_LINK = prove
 (`!(v:real^N) L X Y P.
     moi_ftc_rad v L X Y /\ P SUBSET L ==> L INTER moi_ftc_cone v P = P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_rad; moi_ftc_cone] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    SUBGOAL_THEN `y:real^N = z` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L:real^N->bool`)) (concl th) &&
      not(can (find_term ((=) `X:real^N->bool`)) (concl th)))) THEN
    ASM SET_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The product structure of the cell decomposition.  Six                   *)
(* block labels (0, 1, 2 the arcs C_a, C_b, C_c; 3, 4, 5 the points C_a     *)
(* INTER C_b, C_b INTER C_c, C_a INTER C_c) and nine disk labels (0 Om,     *)
(* 1 Op, 2 S, 3 F, 4 Xs INTER Om, 5 Xs INTER Op, 6 K, 7 S INTER Xs,         *)
(* 8 F INTER Xs); the cells are block set INTER disk set.  The face and     *)
(* intersection structure is checked once for arbitrary sets, and the cell  *)
(* assembly of pc_moi_fnd_collar is restated for product labels.            *)
(* ========================================================================= *)

let moi_ftc_zd = new_definition
 `moi_ftc_zd (Om:real^N->bool) Op S Fn Xs Kc (j:num) =
    if j = 0 then Om else if j = 1 then Op else if j = 2 then S else
    if j = 3 then Fn else if j = 4 then Xs INTER Om else if j = 5 then Xs INTER Op else
    if j = 6 then Kc else if j = 7 then S INTER Xs else Fn INTER Xs`;;

let moi_ftc_dface = new_definition
 `moi_ftc_dface (j:num) (j':num) <=>
    j' = j \/
    (j = 0 /\ (j' = 2 \/ j' = 3 \/ j' = 4 \/ j' = 6 \/ j' = 7 \/ j' = 8)) \/
    (j = 1 /\ (j' = 2 \/ j' = 3 \/ j' = 5 \/ j' = 6 \/ j' = 7 \/ j' = 8)) \/
    (j = 2 /\ (j' = 6 \/ j' = 7)) \/ (j = 3 /\ (j' = 6 \/ j' = 8)) \/
    (j = 4 /\ (j' = 7 \/ j' = 8)) \/ (j = 5 /\ (j' = 7 \/ j' = 8))`;;

let moi_ftc_dd = new_definition
 `moi_ftc_dd (j:num) = if j <= 1 then 2 else if j <= 5 then 1 else 0`;;

let moi_ftc_cb = new_definition
 `moi_ftc_cb (Ca:real^N->bool) Cb Cc (i:num) =
    if i = 0 then Ca else if i = 1 then Cb else if i = 2 then Cc else
    if i = 3 then Ca INTER Cb else if i = 4 then Cb INTER Cc else Ca INTER Cc`;;

let moi_ftc_bface = new_definition
 `moi_ftc_bface (i:num) (i':num) <=>
    i' = i \/ (i = 0 /\ (i' = 3 \/ i' = 5)) \/ (i = 1 /\ (i' = 3 \/ i' = 4)) \/
    (i = 2 /\ (i' = 4 \/ i' = 5))`;;

let moi_ftc_bd = new_definition
 `moi_ftc_bd (i:num) = if i <= 2 then 1 else 0`;;

let MOI_FTC_LT9 = prove
 (`!j. j < 9 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                 j = 8`,
  ARITH_TAC);;

let MOI_FTC_LT6 = prove
 (`!i. i < 6 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`,
  ARITH_TAC);;

let MOI_FTC_IN_UNIONS_GSPEC = prove
 (`!(f:B->A->bool) P x. x IN UNIONS {f j | j | P j} <=> ?j. P j /\ x IN f j`,
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_EX9 = prove
 (`!P. (?j. j < 9 /\ P j) <=> P 0 \/ P 1 \/ P 2 \/ P 3 \/ P 4 \/ P 5 \/ P 6 \/ P 7 \/ P 8`,
  REWRITE_TAC[MOI_FTC_LT9; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2]);;

let MOI_FTC_EX6 = prove
 (`!P. (?i. i < 6 /\ P i) <=> P 0 \/ P 1 \/ P 2 \/ P 3 \/ P 4 \/ P 5`,
  REWRITE_TAC[MOI_FTC_LT6; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2]);;

(* The disk sets meet in the union of their common faces, given the three  *)
(* relations R1 (Om INTER Op = S UNION Fn), R3 (S INTER Fn = Kc) and R4     *)
(* (Kc INTER Xs = {}).                                                       *)

let MOI_FTC_ZD_INTER = prove
 (`!(Om:real^N->bool) Op S Fn Xs Kc.
     Om INTER Op = S UNION Fn /\ S INTER Fn = Kc /\ Kc INTER Xs = {}
     ==> !j j'. j < 9 /\ j' < 9
                ==> moi_ftc_zd Om Op S Fn Xs Kc j INTER moi_ftc_zd Om Op S Fn Xs Kc j' =
                    UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j'' | j'' |
                            j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
    GEN_REWRITE_RULE I [MOI_FTC_LT9])) THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FTC_IN_UNIONS_GSPEC; GSYM CONJ_ASSOC; MOI_FTC_EX9] THEN
  REWRITE_TAC[moi_ftc_dface; moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[IN_INTER] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN CONV_TAC TAUT);;

(* The block sets meet in the union of their common faces when the three   *)
(* arcs have no common point.                                               *)

let MOI_FTC_CB_INTER = prove
 (`!(Ca:real^N->bool) Cb Cc.
     Ca INTER Cb INTER Cc = {}
     ==> !i i'. i < 6 /\ i' < 6
                ==> moi_ftc_cb Ca Cb Cc i INTER moi_ftc_cb Ca Cb Cc i' =
                    UNIONS {moi_ftc_cb Ca Cb Cc i'' | i'' |
                            i'' < 6 /\ moi_ftc_bface i i'' /\ moi_ftc_bface i' i''}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
    GEN_REWRITE_RULE I [MOI_FTC_LT6])) THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FTC_IN_UNIONS_GSPEC; GSYM CONJ_ASSOC; MOI_FTC_EX6] THEN
  REWRITE_TAC[moi_ftc_bface; moi_ftc_cb] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[IN_INTER] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN CONV_TAC TAUT);;

(* The proper faces of each disk label and of each block label. *)

let MOI_FTC_ZD_BD = prove
 (`!(Om:real^N->bool) Op S Fn Xs Kc.
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 0 j' /\ ~(j' = 0)} =
     S UNION Fn UNION (Xs INTER Om) UNION Kc UNION (S INTER Xs) UNION (Fn INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 1 j' /\ ~(j' = 1)} =
     S UNION Fn UNION (Xs INTER Op) UNION Kc UNION (S INTER Xs) UNION (Fn INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 2 j' /\ ~(j' = 2)} = Kc UNION (S INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 3 j' /\ ~(j' = 3)} = Kc UNION (Fn INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 4 j' /\ ~(j' = 4)} = (S INTER Xs) UNION (Fn INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 5 j' /\ ~(j' = 5)} = (S INTER Xs) UNION (Fn INTER Xs) /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 6 j' /\ ~(j' = 6)} = {} /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 7 j' /\ ~(j' = 7)} = {} /\
     UNIONS {moi_ftc_zd Om Op S Fn Xs Kc j' | j' |
             j' < 9 /\ moi_ftc_dface 8 j' /\ ~(j' = 8)} = {}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; MOI_FTC_IN_UNIONS_GSPEC; GSYM CONJ_ASSOC; MOI_FTC_EX9] THEN
  REWRITE_TAC[moi_ftc_dface; moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[IN_UNION; IN_INTER; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN CONV_TAC TAUT));;

let MOI_FTC_CB_BD = prove
 (`!(Ca:real^N->bool) Cb Cc.
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 0 i' /\ ~(i' = 0)} =
     (Ca INTER Cb) UNION (Ca INTER Cc) /\
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 1 i' /\ ~(i' = 1)} =
     (Ca INTER Cb) UNION (Cb INTER Cc) /\
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 2 i' /\ ~(i' = 2)} =
     (Cb INTER Cc) UNION (Ca INTER Cc) /\
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 3 i' /\ ~(i' = 3)} = {} /\
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 4 i' /\ ~(i' = 4)} = {} /\
     UNIONS {moi_ftc_cb Ca Cb Cc i' | i' | i' < 6 /\ moi_ftc_bface 5 i' /\ ~(i' = 5)} = {}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; MOI_FTC_IN_UNIONS_GSPEC; GSYM CONJ_ASSOC; MOI_FTC_EX6] THEN
  REWRITE_TAC[moi_ftc_bface; moi_ftc_cb] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[IN_UNION; IN_INTER; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN CONV_TAC TAUT));;

(* ------------------------------------------------------------------------- *)
(* The cell assembly of pc_moi_fnd_collar for product labels (i,j): cells    *)
(* CA i INTER ZA j, faces (i,j) <= (i',j') iff bface i i' and dface j j'.    *)
(* Generic in the label sets, so it serves any number of blocks.            *)
(* ------------------------------------------------------------------------- *)

let MOI_FTC_PROD_BD = prove
 (`!(blab:num->bool) bface (dlab:num->bool) dface (CA:num->real^N->bool)
    (ZA:num->real^N->bool) i j.
     i IN blab /\ j IN dlab /\ bface i i /\ dface j j /\
     (!i'. bface i i' ==> i' IN blab) /\ (!j'. dface j j' ==> j' IN dlab) /\
     (!j'. dface j j' ==> ZA j' SUBSET ZA j)
     ==> UNIONS {CA (FST m) INTER ZA (SND m) | m |
                 (bface i (FST m) /\ dface j (SND m)) /\ ~(m = (i,j))} =
         (CA i INTER UNIONS {ZA j' | j' | j' IN dlab /\ dface j j' /\ ~(j' = j)}) UNION
         (UNIONS {CA i' | i' | i' IN blab /\ bface i i' /\ ~(i' = i)} INTER ZA j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNION; IN_INTER; MOI_FTC_IN_UNIONS_GSPEC; EXISTS_PAIR_THM; FST; SND;
              PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let MOI_FTC_PROD_INTER = prove
 (`!(blab:num->bool) bface (dlab:num->bool) dface (CA:num->real^N->bool)
    (ZA:num->real^N->bool) i j i' j'.
     CA i INTER CA i' = UNIONS {CA i'' | i'' | i'' IN blab /\ bface i i'' /\ bface i' i''} /\
     ZA j INTER ZA j' = UNIONS {ZA j'' | j'' | j'' IN dlab /\ dface j j'' /\ dface j' j''} /\
     (!i''. bface i i'' ==> i'' IN blab) /\ (!j''. dface j j'' ==> j'' IN dlab)
     ==> (CA i INTER ZA j) INTER (CA i' INTER ZA j') =
         UNIONS {CA (FST n) INTER ZA (SND n) | n |
                 (bface i (FST n) /\ dface j (SND n)) /\ bface i' (FST n) /\ dface j' (SND n)}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; MOI_FTC_IN_UNIONS_GSPEC; EXISTS_PAIR_THM; FST; SND] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN ASM_MESON_TAC[]);;

let MOI_FTC_PAIR_GSPEC = prove
 (`!(CC:num->A->bool) (ZZ:num->A->bool) (blab:num->bool) (dlab:num->bool).
      {CC (FST l) INTER ZZ (SND l) | l IN {(i,j) | i IN blab /\ j IN dlab}} =
      {CC i INTER ZZ j | i IN blab /\ j IN dlab}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM; FST; SND] THEN MESON_TAC[]);;

let MOI_FTC_PROD_ASSEMBLY = prove
 (`!(blab:num->bool) bface (bd:num->num) (dlab:num->bool) dface (dd:num->num)
    (CA:num->real^N->bool) (ZA:num->real^N->bool)
    (CB:num->real^M->bool) (ZB:num->real^M->bool).
     FINITE blab /\ FINITE dlab /\
     (!i. i IN blab ==> bface i i) /\ (!j. j IN dlab ==> dface j j) /\
     (!i j. i IN blab /\ j IN dlab ==> bd i + dd j <= 3) /\
     (!i i'. i IN blab /\ bface i i' ==> i' IN blab /\ (i' = i \/ bd i' < bd i)) /\
     (!j j'. j IN dlab /\ dface j j' ==> j' IN dlab /\ (j' = j \/ dd j' < dd j)) /\
     (!i i'. i IN blab /\ i' IN blab
             ==> CA i INTER CA i' =
                 UNIONS {CA i'' | i'' | i'' IN blab /\ bface i i'' /\ bface i' i''} /\
                 CB i INTER CB i' =
                 UNIONS {CB i'' | i'' | i'' IN blab /\ bface i i'' /\ bface i' i''}) /\
     (!j j'. j IN dlab /\ j' IN dlab
             ==> ZA j INTER ZA j' =
                 UNIONS {ZA j'' | j'' | j'' IN dlab /\ dface j j'' /\ dface j' j''} /\
                 ZB j INTER ZB j' =
                 UNIONS {ZB j'' | j'' | j'' IN dlab /\ dface j j'' /\ dface j' j''}) /\
     (!i j. i IN blab /\ j IN dlab
            ==> pl_cell_with_boundary (bd i + dd j) (CA i INTER ZA j)
                  ((CA i INTER UNIONS {ZA j' | j' | j' IN dlab /\ dface j j' /\ ~(j' = j)}) UNION
                   (UNIONS {CA i' | i' | i' IN blab /\ bface i i' /\ ~(i' = i)} INTER ZA j)) /\
                pl_cell_with_boundary (bd i + dd j) (CB i INTER ZB j)
                  ((CB i INTER UNIONS {ZB j' | j' | j' IN dlab /\ dface j j' /\ ~(j' = j)}) UNION
                   (UNIONS {CB i' | i' | i' IN blab /\ bface i i' /\ ~(i' = i)} INTER ZB j)))
     ==> ?f. pl_map_on (UNIONS {CA i INTER ZA j | i IN blab /\ j IN dlab}) f /\
             (!x y. x IN UNIONS {CA i INTER ZA j | i IN blab /\ j IN dlab} /\
                    y IN UNIONS {CA i INTER ZA j | i IN blab /\ j IN dlab} /\ f x = f y
                    ==> x = y) /\
             (!i j. i IN blab /\ j IN dlab ==> IMAGE f (CA i INTER ZA j) = CB i INTER ZB j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!j j'. j IN dlab /\ dface j j' ==> (ZA:num->real^N->bool) j' SUBSET ZA j) /\
    (!j j'. j IN dlab /\ dface j j' ==> (ZB:num->real^M->bool) j' SUBSET ZB j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `j:num`] o check (fun th ->
      can (find_term ((=) `dface:num->num->bool`)) (concl th) &&
      can (find_term ((=) `ZA:num->real^N->bool`)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "pl_cell_with_boundary"
                                   with Failure _ -> false)) (concl th)))) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; MOI_FTC_IN_UNIONS_GSPEC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{(i,j) | (i:num) IN blab /\ (j:num) IN dlab}`;
                 `\l:num#num. (CA:num->real^N->bool) (FST l) INTER ZA (SND l)`;
                 `\l:num#num. (CB:num->real^M->bool) (FST l) INTER ZB (SND l)`;
                 `\l:num#num. (bd:num->num) (FST l) + dd (SND l)`;
                 `\(l:num#num) (m:num#num). (bface:num->num->bool) (FST l) (FST m) /\
                                            (dface:num->num->bool) (SND l) (SND m)`]
    MOI_FCL_ASSEMBLY) THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; FST; SND] THEN
  REWRITE_TAC[MOI_FTC_PAIR_GSPEC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `i':num`; `j':num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(i':num) IN blab /\ (i' = i \/ (bd:num->num) i' < bd i) /\
                  (j':num) IN dlab /\ (j' = j \/ (dd:num->num) j' < dd j)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`blab:num->bool`; `bface:num->num->bool`; `dlab:num->bool`;
                   `dface:num->num->bool`; `CA:num->real^N->bool`; `ZA:num->real^N->bool`;
                   `i:num`; `j:num`] MOI_FTC_PROD_BD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`blab:num->bool`; `bface:num->num->bool`; `dlab:num->bool`;
                   `dface:num->num->bool`; `CB:num->real^M->bool`; `ZB:num->real^M->bool`;
                   `i:num`; `j:num`] MOI_FTC_PROD_BD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_PROD_INTER THEN
    MAP_EVERY EXISTS_TAC [`blab:num->bool`; `dlab:num->bool`] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_PROD_INTER THEN
    MAP_EVERY EXISTS_TAC [`blab:num->bool`; `dlab:num->bool`] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(i,j) | (i:num) IN blab /\ (j:num) IN dlab}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT] THEN SET_TAC[];
    REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^M)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(i,j) | (i:num) IN blab /\ (j:num) IN dlab}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Products with a polytope as FIRST factor (pc_moi_fnd_collar has them with *)
(* the polytope second), the relative frontier of a product of compact       *)
(* convex sets, polytope cells of dimension at most 3, and the product of a  *)
(* point or segment with a PL cell (generic, for the model).                 *)
(* ========================================================================= *)

let MOI_FTC_LP_PCROSS2 = prove
 (`!(t:real^P->bool) (s:real^M->bool).
     polytope t /\ locally_polyhedral s ==> locally_polyhedral (t PCROSS s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`y:real^P`; `x:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` (X_CHOOSE_THEN `u:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (\k:real^M->bool. (t:real^P->bool) PCROSS k) c` THEN
  EXISTS_TAC `(:real^P) PCROSS (u:real^M->bool)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV;
               FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS; IN_UNIV;
                IN_UNIONS; EXISTS_IN_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [`b:real^P`; `a:real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^M) IN UNIONS c` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_PCROSS THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_SIMP_TAC[SUBSET_REFL]]]);;

let MOI_FTC_PL_PCROSS_ID2 = prove
 (`!(t:real^P->bool) (s:real^M->bool) (f:real^M->real^N).
     polytope t /\ pl_map_on s f
     ==> pl_map_on (t PCROSS s) (\z. pastecart (fstcart z) (f (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `locally_polyhedral ((t:real^P->bool) PCROSS (s:real^M->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_LP_PCROSS2 THEN
    ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(P,M)finite_sum. fstcart z + vec 0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_FSTCART]];
    SUBGOAL_THEN
     `(\z:real^(P,M)finite_sum. (f:real^M->real^N) (sndcart z)) = f o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\z:real^(P,M)finite_sum. sndcart z + vec 0` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ADD_RID];
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_SNDCART]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[]]]);;

let MOI_FTC_PLH_PCROSS_ID2 = prove
 (`!(t:real^P->bool) (s:real^M->bool) (s':real^N->bool) f g.
     polytope t /\ pl_homeomorphism (s,s') (f,g)
     ==> pl_homeomorphism (t PCROSS s,t PCROSS s')
           ((\z. pastecart (fstcart z) (f (sndcart z))),
            (\z. pastecart (fstcart z) (g (sndcart z))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTC_PL_PCROSS_ID2] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[MOI_FTC_PL_PCROSS_ID2] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ] THEN
  ASM SET_TAC[]);;

let MOI_FTC_IMAGE_PCROSS_ID2 = prove
 (`!(f:real^M->real^N) (t:real^P->bool) s.
     IMAGE (\z. pastecart (fstcart z) (f (sndcart z))) (t PCROSS s) =
     t PCROSS (IMAGE f s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ] THEN
  MESON_TAC[]);;

(* The relative frontier of a product of closed convex sets. *)

let MOI_FTC_RF_PCROSS = prove
 (`!(s:real^M->bool) (t:real^N->bool).
     closed s /\ closed t
     ==> relative_frontier (s PCROSS t) =
         (relative_frontier s PCROSS t) UNION (s PCROSS relative_frontier t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[relative_frontier; CLOSURE_PCROSS; RELATIVE_INTERIOR_PCROSS] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `s:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  REWRITE_TAC[SUBSET; EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DIFF;
              IN_UNION] THEN
  MESON_TAC[]);;

(* Polytopes of dimension at most 3 are PL cells with their relative       *)
(* frontier as boundary.                                                    *)

let MOI_FTC_POLY_CELL = prove
 (`!d (P:real^N->bool).
     polytope P /\ aff_dim P = &d /\ d <= 3
     ==> pl_cell_with_boundary d P (relative_frontier P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d = 0 \/ d = 1 \/ d = 2 \/ d = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    REWRITE_TAC[RELATIVE_FRONTIER_SING; MOI_FCL_POINT_CELL];
    MATCH_MP_TAC MOI_S4A_POLY_CELL_1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN ASM_REWRITE_TAC[]]);;

(* A point or a segment (any polytope of dimension m) times a PL n-cell is a *)
(* PL (m+n)-cell, with the product boundary.                                  *)

let MOI_FTC_PROD_CELL = prove
 (`!m n (A:real^M->bool) (P:real^N->bool) bP.
     polytope A /\ aff_dim A = &m /\ pl_cell_with_boundary n P bP /\ m + n <= 3
     ==> pl_cell_with_boundary (m + n) (A PCROSS P)
           ((relative_frontier A PCROSS P) UNION (A PCROSS bP))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `polytope (k:real^N->bool) /\ closed k /\ ~(k = {}) /\ aff_dim k = &n`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_CLOSED; AFF_DIM_SIMPLEX;
                  AFF_DIM_EMPTY; INT_ARITH `~(&n:int = -- &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(A:real^M->bool = {}) /\ closed A` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[POLYTOPE_IMP_CLOSED; AFF_DIM_EMPTY; INT_ARITH `~(&m:int = -- &1)`];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary (m + n) ((A:real^M->bool) PCROSS (k:real^N->bool))
      (relative_frontier (A PCROSS k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_POLY_CELL THEN
    ASM_SIMP_TAC[POLYTOPE_PCROSS; AFF_DIM_PCROSS; INT_OF_NUM_ADD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m + n:num`; `(A:real^M->bool) PCROSS (k:real^N->bool)`;
                 `relative_frontier ((A:real^M->bool) PCROSS (k:real^N->bool))`;
                 `(A:real^M->bool) PCROSS (P:real^N->bool)`;
                 `\z:real^(M,N)finite_sum.
                    pastecart (fstcart z) ((f:real^N->real^N) (sndcart z))`;
                 `\z:real^(M,N)finite_sum.
                    pastecart (fstcart z) ((g:real^N->real^N) (sndcart z))`]
    MOI_FCL_CELL_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_PLH_PCROSS_ID2 THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `A:real^M->bool` AFF_DIM_LE_UNIV) THEN
      MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; INT_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[MOI_FTC_RF_PCROSS; IMAGE_UNION; MOI_FTC_IMAGE_PCROSS_ID2]);;

(* ------------------------------------------------------------------------- *)
(* The spine of a solid torus from a PL homeomorphism of circle times square *)
(* (generic: any PL 1-sphere C in real^2 as circle factor).                  *)
(* ------------------------------------------------------------------------- *)

(* The spine step inlined in the proof of PL_SOLID_TORUS_BASIC (pc_moi_fnd_ *)
(* plst), stated as a lemma.                                                  *)

let MOI_FTC_SQ_SPINE = prove
 (`!(s:real^N->bool) h k.
     pl_homeomorphism (moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1],s) (h,k)
     ==> spine (IMAGE h (moi_fps_sq PCROSS {vec 0:real^2})) s`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `a:real^2->real^2` (X_CHOOSE_THEN `a':real^2->real^2` STRIP_ASSUME_TAC)
    MOI_FPS_DISC_SQUARE THEN
  SUBGOAL_THEN `?b b'. homeomorphism (sphere(vec 0:real^2,&1),moi_fps_sq) (b,b')`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM homeomorphic] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[moi_fps_sq; MOI_FPS_VEC1_2] THEN
    MATCH_MP_TAC MOI_FH1_SQUARE_FRONTIER_CIRCLE THEN REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `interval[--vec 1:real^2,vec 1]`;
                 `sphere(vec 0:real^2,&1)`; `moi_fps_sq`;
                 `a:real^2->real^2`; `a':real^2->real^2`;
                 `b:real^2->real^2`; `b':real^2->real^2`]
                MOI_FPS_HOMEOMORPHISM_PCROSS_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),s)
      ((h:real^(2,2)finite_sum->real^N) o
       (\z. pastecart ((b:real^2->real^2)(sndcart z)) ((a:real^2->real^2)(fstcart z))),
       (\w. pastecart ((a':real^2->real^2)(sndcart w)) ((b':real^2->real^2)(fstcart w))) o
       (k:real^N->real^(2,2)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]` THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[spine] THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(2,2)finite_sum->real^N) o
     (\z. pastecart ((b:real^2->real^2)(sndcart z)) ((a:real^2->real^2)(fstcart z)))`;
    `(\w. pastecart ((a':real^2->real^2)(sndcart w)) ((b':real^2->real^2)(fstcart w))) o
     (k:real^N->real^(2,2)finite_sum)`;
    `(a':real^2->real^2)(vec 0)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_FPS_SPINE_IMAGE THEN EXISTS_TAC `b':real^2->real^2` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTC_TORUS_SPINE = prove
 (`!(C:real^2->bool) (s:real^N->bool) h k.
     pl_sphere 1 C /\
     pl_homeomorphism (C PCROSS interval[--vec 1:real^2,vec 1],s) (h,k)
     ==> pl_solid_torus s /\ spine (IMAGE h (C PCROSS {vec 0:real^2})) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p q. pl_homeomorphism (moi_fps_sq,C:real^2->bool) (p,q)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_sphere] o check (fun th ->
      concl th = `pl_sphere 1 (C:real^2->bool)`)) THEN
    MP_TAC MOI_FPS_SQ_PL_SPHERE THEN REWRITE_TAC[pl_sphere] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:real^2->bool` (X_CHOOSE_THEN `f2:real^2->real^2`
      (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^2`
      (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`k2:real^2->bool`; `k1:real^2->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p0:real^2->real^2` (X_CHOOSE_THEN `q0:real^2->real^2`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `((f1:real^2->real^2) o (p0:real^2->real^2)) o (g2:real^2->real^2)` THEN
    EXISTS_TAC `(f2:real^2->real^2) o (q0:real^2->real^2) o (g1:real^2->real^2)` THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier(k2:real^2->bool)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `relative_frontier(k1:real^2->bool)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1],
                      (C:real^2->bool) PCROSS interval[--vec 1:real^2,vec 1])
      ((\z. pastecart ((p:real^2->real^2) (fstcart z)) (sndcart z)),
       (\z. pastecart ((q:real^2->real^2) (fstcart z)) (sndcart z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_PLH_PCROSS_ID THEN ASM_REWRITE_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1],s:real^N->bool)
      ((h:real^(2,2)finite_sum->real^N) o
       (\z. pastecart ((p:real^2->real^2) (fstcart z)) (sndcart z)),
       (\z. pastecart ((q:real^2->real^2) (fstcart z)) (sndcart z)) o
       (k:real^N->real^(2,2)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(C:real^2->bool) PCROSS interval[--vec 1:real^2,vec 1]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT] THEN
    X_CHOOSE_TAC `th':real^(2,2)finite_sum->real^(2,1)finite_sum` MOI_FPS_TH_PLH THEN
    MAP_EVERY EXISTS_TAC
     [`((h:real^(2,2)finite_sum->real^N) o
        (\z. pastecart ((p:real^2->real^2) (fstcart z)) (sndcart z))) o moi_fps_th`;
      `(th':real^(2,2)finite_sum->real^(2,1)finite_sum) o
       (\z. pastecart ((q:real^2->real^2) (fstcart z)) (sndcart z)) o
       (k:real^N->real^(2,2)finite_sum)`] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_FTC_SQ_SPINE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_o; MOI_FCL_IMAGE_PCROSS_ID] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
    `pl_homeomorphism (moi_fps_sq,C:real^2->bool) (p,q)`)) THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

(* ------------------------------------------------------------------------- *)
(* The disk factor of the model: the square interval[--vec 1,vec 1] of      *)
(* real^2 with its top and bottom halves, the two fins on the x-axis, the    *)
(* boundary square moi_fps_sq and the centre (generic, nine disk labels).    *)
(* ------------------------------------------------------------------------- *)

let moi_ftc_dom = new_definition
 `moi_ftc_dom = interval[vector[-- &1; &0]:real^2,vector[&1; &1]]`;;

let moi_ftc_dop = new_definition
 `moi_ftc_dop = interval[vector[-- &1; -- &1]:real^2,vector[&1; &0]]`;;

let moi_ftc_dsf = new_definition
 `moi_ftc_dsf = segment[vec 0:real^2,vector[&1; &0]]`;;

let moi_ftc_dff = new_definition
 `moi_ftc_dff = segment[vector[-- &1; &0]:real^2,vec 0]`;;

let MOI_FTC_DISK_IN = prove
 (`!x:real^2.
     (x IN moi_ftc_dom <=> -- &1 <= x$1 /\ x$1 <= &1 /\ &0 <= x$2 /\ x$2 <= &1) /\
     (x IN moi_ftc_dop <=> -- &1 <= x$1 /\ x$1 <= &1 /\ -- &1 <= x$2 /\ x$2 <= &0) /\
     (x IN moi_ftc_dsf <=> &0 <= x$1 /\ x$1 <= &1 /\ x$2 = &0) /\
     (x IN moi_ftc_dff <=> -- &1 <= x$1 /\ x$1 <= &0 /\ x$2 = &0) /\
     (x IN moi_fps_sq <=> max (abs(x$1)) (abs(x$2)) = &1) /\
     (x IN interval[--vec 1,vec 1] <=>
      -- &1 <= x$1 /\ x$1 <= &1 /\ -- &1 <= x$2 /\ x$2 <= &1) /\
     (x = vec 0 <=> x$1 = &0 /\ x$2 = &0) /\
     (x = vector[&1; &0] <=> x$1 = &1 /\ x$2 = &0) /\
     (x = vector[-- &1; &0] <=> x$1 = -- &1 /\ x$2 = &0)`,
  GEN_TAC THEN
  REWRITE_TAC[moi_ftc_dom; moi_ftc_dop; moi_ftc_dsf; moi_ftc_dff; MOI_FPS_SQ;
              IN_INTERVAL; IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VEC_COMPONENT; VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `(x:real^2)$1` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `&1 + (x:real^2)$1` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_FTC_DISK_REL = prove
 (`moi_ftc_dom INTER moi_ftc_dop = moi_ftc_dsf UNION moi_ftc_dff /\
   moi_ftc_dsf INTER moi_ftc_dff = {vec 0:real^2} /\
   {vec 0:real^2} INTER moi_fps_sq = {} /\
   moi_ftc_dsf INTER moi_fps_sq = {vector[&1; &0]} /\
   moi_ftc_dff INTER moi_fps_sq = {vector[-- &1; &0]} /\
   (moi_fps_sq INTER moi_ftc_dop) INTER (moi_fps_sq INTER moi_ftc_dom) =
   {vector[&1; &0], vector[-- &1; &0]} /\
   (moi_fps_sq INTER moi_ftc_dop) UNION (moi_fps_sq INTER moi_ftc_dom) = moi_fps_sq /\
   moi_ftc_dom SUBSET interval[--vec 1,vec 1] /\ moi_ftc_dop SUBSET interval[--vec 1,vec 1] /\
   moi_ftc_dsf SUBSET interval[--vec 1,vec 1] /\ moi_ftc_dff SUBSET interval[--vec 1,vec 1] /\
   moi_fps_sq SUBSET interval[--vec 1,vec 1] /\ {vec 0:real^2} SUBSET interval[--vec 1,vec 1]`,
  REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
              MOI_FTC_DISK_IN] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTC_DISK_RF = prove
 (`polytope moi_ftc_dom /\ aff_dim moi_ftc_dom = &2 /\
   relative_frontier moi_ftc_dom =
   moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dom) /\
   polytope moi_ftc_dop /\ aff_dim moi_ftc_dop = &2 /\
   relative_frontier moi_ftc_dop =
   moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dop)`,
  SUBGOAL_THEN `~(interior moi_ftc_dom = {}) /\ ~(interior moi_ftc_dop = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_dom; moi_ftc_dop; INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY;
                DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2] THEN
  REWRITE_TAC[moi_ftc_dom; moi_ftc_dop; POLYTOPE_INTERVAL; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[GSYM moi_ftc_dom; GSYM moi_ftc_dop] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_INTER; MOI_FTC_DISK_IN] THEN
  REWRITE_TAC[moi_ftc_dom; moi_ftc_dop; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTC_DISK_CELLS = prove
 (`pl_cell_with_boundary 2 moi_ftc_dom
     (moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dom) UNION {vec 0} UNION
      (moi_ftc_dsf INTER moi_fps_sq) UNION (moi_ftc_dff INTER moi_fps_sq)) /\
   pl_cell_with_boundary 2 moi_ftc_dop
     (moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dop) UNION {vec 0} UNION
      (moi_ftc_dsf INTER moi_fps_sq) UNION (moi_ftc_dff INTER moi_fps_sq)) /\
   pl_cell_with_boundary 1 moi_ftc_dsf ({vec 0} UNION (moi_ftc_dsf INTER moi_fps_sq)) /\
   pl_cell_with_boundary 1 moi_ftc_dff ({vec 0} UNION (moi_ftc_dff INTER moi_fps_sq)) /\
   pl_cell_with_boundary 1 (moi_fps_sq INTER moi_ftc_dom)
     ((moi_ftc_dsf INTER moi_fps_sq) UNION (moi_ftc_dff INTER moi_fps_sq)) /\
   pl_cell_with_boundary 1 (moi_fps_sq INTER moi_ftc_dop)
     ((moi_ftc_dsf INTER moi_fps_sq) UNION (moi_ftc_dff INTER moi_fps_sq)) /\
   pl_cell_with_boundary 0 {vec 0:real^2} {} /\
   pl_cell_with_boundary 0 (moi_ftc_dsf INTER moi_fps_sq) {} /\
   pl_cell_with_boundary 0 (moi_ftc_dff INTER moi_fps_sq) {}`,
  REWRITE_TAC[MOI_FTC_DISK_REL; MOI_FCL_POINT_CELL] THEN
  SUBGOAL_THEN `~(vec 0:real^2 = vector[&1; &0]) /\ ~(vector[-- &1; &0]:real^2 = vec 0) /\
                ~(vector[&1; &0]:real^2 = vector[-- &1; &0])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FTC_DISK_IN; VECTOR_2; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dom) UNION {vec 0} UNION
      {vector[&1; &0]} UNION {vector[-- &1; &0]} = relative_frontier moi_ftc_dom`
    SUBST1_TAC THENL
     [REWRITE_TAC[MOI_FTC_DISK_RF] THEN
      MP_TAC(ISPECL [`vec 0:real^2`; `vector[&1; &0]:real^2`] ENDS_IN_SEGMENT) THEN
      MP_TAC(ISPECL [`vector[-- &1; &0]:real^2`; `vec 0:real^2`] ENDS_IN_SEGMENT) THEN
      REWRITE_TAC[GSYM moi_ftc_dsf; GSYM moi_ftc_dff] THEN SET_TAC[];
      MATCH_MP_TAC MOI_FTC_POLY_CELL THEN REWRITE_TAC[MOI_FTC_DISK_RF] THEN ARITH_TAC];
    SUBGOAL_THEN
     `moi_ftc_dsf UNION moi_ftc_dff UNION (moi_fps_sq INTER moi_ftc_dop) UNION {vec 0} UNION
      {vector[&1; &0]} UNION {vector[-- &1; &0]} = relative_frontier moi_ftc_dop`
    SUBST1_TAC THENL
     [REWRITE_TAC[MOI_FTC_DISK_RF] THEN
      MP_TAC(ISPECL [`vec 0:real^2`; `vector[&1; &0]:real^2`] ENDS_IN_SEGMENT) THEN
      MP_TAC(ISPECL [`vector[-- &1; &0]:real^2`; `vec 0:real^2`] ENDS_IN_SEGMENT) THEN
      REWRITE_TAC[GSYM moi_ftc_dsf; GSYM moi_ftc_dff] THEN SET_TAC[];
      MATCH_MP_TAC MOI_FTC_POLY_CELL THEN REWRITE_TAC[MOI_FTC_DISK_RF] THEN ARITH_TAC];
    REWRITE_TAC[SET_RULE `{a:real^2} UNION {b} = {a,b}`; moi_ftc_dsf] THEN
    MATCH_MP_TAC MOI_FCL_SEGMENT_CELL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SET_RULE `{a:real^2} UNION {b} = {b,a}`; moi_ftc_dff] THEN
    MATCH_MP_TAC MOI_FCL_SEGMENT_CELL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SET_RULE `{a:real^2} UNION {b} = {a,b}`] THEN
    MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_sq`; `moi_fps_sq INTER moi_ftc_dop`] THEN
    ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE; MOI_FTC_DISK_REL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN
      SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FPS_SQ_COMPACT; moi_ftc_dop; CLOSED_INTERVAL];
      MATCH_MP_TAC CLOSED_INTER THEN
      SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FPS_SQ_COMPACT; moi_ftc_dom; CLOSED_INTERVAL];
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vector[&0; -- &1]:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY; MOI_FTC_DISK_IN; VECTOR_2] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vector[&0; &1]:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY; MOI_FTC_DISK_IN; VECTOR_2] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SET_RULE `{a:real^2} UNION {b} = {a,b}`] THEN
    MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_sq`; `moi_fps_sq INTER moi_ftc_dom`] THEN
    ONCE_REWRITE_TAC[UNION_COMM; INTER_COMM] THEN
    ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE; MOI_FTC_DISK_REL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN
      SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FPS_SQ_COMPACT; moi_ftc_dom; CLOSED_INTERVAL];
      MATCH_MP_TAC CLOSED_INTER THEN
      SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FPS_SQ_COMPACT; moi_ftc_dop; CLOSED_INTERVAL];
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vector[&0; &1]:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY; MOI_FTC_DISK_IN; VECTOR_2] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vector[&0; -- &1]:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY; MOI_FTC_DISK_IN; VECTOR_2] THEN
      REAL_ARITH_TAC]]);;

let MOI_FTC_DISK_MODEL = prove
 (`(!j j'. j < 9 /\ j' < 9
           ==> moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                          {vec 0:real^2} j INTER
               moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                          {vec 0:real^2} j' =
               UNIONS {moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                                  {vec 0:real^2} j'' | j'' |
                       j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''}) /\
   (!j. j < 9
        ==> pl_cell_with_boundary (moi_ftc_dd j)
              (moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                          {vec 0:real^2} j)
              (UNIONS {moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                                  {vec 0:real^2} j' | j' |
                       j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})) /\
   (!j. j < 9 ==> moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                             {vec 0:real^2} j SUBSET interval[--vec 1,vec 1])`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_ZD_INTER THEN REWRITE_TAC[MOI_FTC_DISK_REL];
    GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT9]) THEN
    REWRITE_TAC[MOI_FTC_ZD_BD] THEN REWRITE_TAC[moi_ftc_zd; moi_ftc_dd] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOI_FTC_DISK_CELLS];
    GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT9]) THEN
    REWRITE_TAC[moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC MOI_FTC_DISK_REL THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The model: circle factor the boundary of a triangle conv{a,b,c} of real^2 *)
(* (arcs [c,a], [a,b], [b,c], points a, b, c), disk factor the square.        *)
(* ------------------------------------------------------------------------- *)

let moi_ftc_mcb = new_definition
 `moi_ftc_mcb (a:real^2) b c (i:num) =
    moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i PCROSS
    interval[--vec 1:real^2,vec 1]`;;

let moi_ftc_mzd = new_definition
 `moi_ftc_mzd (a:real^2) b c (j:num) =
    relative_frontier(convex hull {a,b,c}) PCROSS
    moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq {vec 0:real^2} j`;;

let MOI_FTC_PCROSS_UNIONS_GSPEC = prove
 (`(!(f:B->real^M->bool) (t:real^N->bool) P.
      UNIONS {f i PCROSS t | i | P i} = UNIONS {f i | i | P i} PCROSS t) /\
   (!(s:real^M->bool) (g:B->real^N->bool) P.
      UNIONS {s PCROSS g j | j | P j} = s PCROSS UNIONS {g j | j | P j})`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; MOI_FTC_IN_UNIONS_GSPEC] THEN
  MESON_TAC[]);;

let MOI_FTC_MCB_FACTS = prove
 (`!a b c:real^2.
     ~collinear {a,b,c}
     ==> !i. i < 6
             ==> moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i SUBSET
                 relative_frontier(convex hull {a,b,c}) /\
                 polytope (moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i) /\
                 aff_dim (moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i) =
                 &(moi_ftc_bd i) /\
                 relative_frontier (moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i) =
                 UNIONS {moi_ftc_cb (segment[c,a]) (segment[a,b]) (segment[b,c]) i' | i' |
                         i' < 6 /\ moi_ftc_bface i i' /\ ~(i' = i)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_TRI_EDGES) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP RELATIVE_FRONTIER_OF_TRIANGLE) THEN
  SUBGOAL_THEN `~(a:real^2 = b) /\ ~(b:real^2 = c) /\ ~(c:real^2 = a)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~collinear {a:real^2,b,c}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[c,a] INTER segment[b,c] = {c:real^2}` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`b:real^2`; `c:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`c:real^2`; `a:real^2`] ENDS_IN_SEGMENT) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT6]) THEN
  REWRITE_TAC[MOI_FTC_CB_BD] THEN REWRITE_TAC[moi_ftc_cb; moi_ftc_bd] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[POLYTOPE_SEGMENT; AFF_DIM_SEGMENT; POLYTOPE_SING; AFF_DIM_SING;
                  RELATIVE_FRONTIER_SING] THEN
  ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT] THEN ASM SET_TAC[]);;

let MOI_FTC_PCROSS_CELL_SETS = prove
 (`!(A:real^M->bool) C V D (P:real^N->bool) U.
     A SUBSET C /\ V SUBSET C /\ P SUBSET D /\ U SUBSET D
     ==> (A PCROSS D) INTER (C PCROSS P) = A PCROSS P /\
         ((A PCROSS D) INTER (C PCROSS U)) UNION ((V PCROSS D) INTER (C PCROSS P)) =
         (V PCROSS P) UNION (A PCROSS U)`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTER; IN_UNION;
              SUBSET] THEN
  MESON_TAC[]);;

let MOI_FTC_DISK_UNION = prove
 (`moi_ftc_dom UNION moi_ftc_dop = interval[--vec 1:real^2,vec 1]`,
  REWRITE_TAC[EXTENSION; IN_UNION; MOI_FTC_DISK_IN] THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTC_MODEL = prove
 (`!a b c:real^2.
     ~collinear {a,b,c}
     ==> (!i i'. i < 6 /\ i' < 6
                 ==> moi_ftc_mcb a b c i INTER moi_ftc_mcb a b c i' =
                     UNIONS {moi_ftc_mcb a b c i'' | i'' |
                             i'' < 6 /\ moi_ftc_bface i i'' /\ moi_ftc_bface i' i''}) /\
         (!j j'. j < 9 /\ j' < 9
                 ==> moi_ftc_mzd a b c j INTER moi_ftc_mzd a b c j' =
                     UNIONS {moi_ftc_mzd a b c j'' | j'' |
                             j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''}) /\
         (!i j. i < 6 /\ j < 9
                ==> pl_cell_with_boundary (moi_ftc_bd i + moi_ftc_dd j)
                      (moi_ftc_mcb a b c i INTER moi_ftc_mzd a b c j)
                      ((moi_ftc_mcb a b c i INTER
                        UNIONS {moi_ftc_mzd a b c j' | j' |
                                j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                       (UNIONS {moi_ftc_mcb a b c i' | i' |
                                i' < 6 /\ moi_ftc_bface i i' /\ ~(i' = i)} INTER
                        moi_ftc_mzd a b c j))) /\
         UNIONS {moi_ftc_mcb a b c i INTER moi_ftc_mzd a b c j | i < 6 /\ j < 9} =
         relative_frontier(convex hull {a,b,c}) PCROSS interval[--vec 1:real^2,vec 1] /\
         UNIONS {moi_ftc_mcb a b c i INTER moi_ftc_mzd a b c 6 | i | i < 6} =
         relative_frontier(convex hull {a,b,c}) PCROSS {vec 0:real^2}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "mcb" o MATCH_MP MOI_FTC_MCB_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_TRI_EDGES) THEN
  SUBGOAL_THEN `~(a:real^2 = b)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {a:real^2,b,c}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[c,a] UNION segment[a,b] UNION segment[b,c:real^2] =
    relative_frontier(convex hull {a,b,c})`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP RELATIVE_FRONTIER_OF_TRIANGLE) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_FTC_DISK_MODEL THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dint")
    (CONJUNCTS_THEN2 (LABEL_TAC "dcell") (LABEL_TAC "dsub"))) THEN
  ABBREV_TAC `C = relative_frontier(convex hull {a:real^2,b,c})` THEN
  ABBREV_TAC `D = interval[--vec 1:real^2,vec 1]` THEN
  ABBREV_TAC `cb = moi_ftc_cb (segment[c:real^2,a]) (segment[a,b]) (segment[b,c])` THEN
  ABBREV_TAC `zd = moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                              {vec 0:real^2}` THEN
  SUBGOAL_THEN
   `(!i. moi_ftc_mcb a b c i = (cb:num->real^2->bool) i PCROSS (D:real^2->bool)) /\
    (!j. moi_ftc_mzd a b c j = (C:real^2->bool) PCROSS (zd:num->real^2->bool) j)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[moi_ftc_mcb; moi_ftc_mzd] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cb:num->real^2->bool) 0 = segment[c,a] /\ cb 1 = segment[a,b] /\ cb 2 = segment[b,c] /\
    (zd:num->real^2->bool) 0 = moi_ftc_dom /\ zd 1 = moi_ftc_dop /\ zd 6 = {vec 0}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cb"; "zd"] THEN REWRITE_TAC[moi_ftc_cb; moi_ftc_zd] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[INTER_PCROSS; INTER_IDEMPOT; MOI_FTC_PCROSS_UNIONS_GSPEC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`segment[c:real^2,a]`; `segment[a:real^2,b]`; `segment[b:real^2,c]`]
      MOI_FTC_CB_INTER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`segment[c:real^2,a] INTER segment[a,b] = {a}`;
        `segment[a:real^2,b] INTER segment[b,c] = {b}`; `~(a:real^2 = b)`] THEN
      SET_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[INTER_PCROSS; INTER_IDEMPOT; MOI_FTC_PCROSS_UNIONS_GSPEC] THEN
    AP_TERM_TAC THEN USE_THEN "dint" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "mcb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `i:num` th) (ASSUME `i < 6`))) THEN
    USE_THEN "dcell" (fun th -> ASSUME_TAC(MATCH_MP (SPEC `j:num` th) (ASSUME `j < 9`))) THEN
    USE_THEN "dsub" (fun th -> ASSUME_TAC(MATCH_MP (SPEC `j:num` th) (ASSUME `j < 9`))) THEN
    SUBGOAL_THEN
     `UNIONS {(zd:num->real^2->bool) j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}
      SUBSET D`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; MOI_FTC_IN_UNIONS_GSPEC] THEN X_GEN_TAC `y:real^2` THEN
      DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
      USE_THEN "dsub" (fun th -> MP_TAC(MATCH_MP (SPEC `j':num` th) (ASSUME `j' < 9`))) THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `relative_frontier ((cb:num->real^2->bool) i) SUBSET C`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(cb:num->real^2->bool) i` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[relative_frontier] THEN
        MP_TAC(ISPEC `(cb:num->real^2->bool) i` CLOSURE_CLOSED) THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_FTC_PCROSS_UNIONS_GSPEC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `relative_frontier ((cb:num->real^2->bool) i)`)) THEN
    MP_TAC(ISPECL [`(cb:num->real^2->bool) i`; `C:real^2->bool`;
                   `relative_frontier ((cb:num->real^2->bool) i)`; `D:real^2->bool`;
                   `(zd:num->real^2->bool) j`;
                   `UNIONS {(zd:num->real^2->bool) j' | j' |
                            j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}`]
      MOI_FTC_PCROSS_CELL_SETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC MOI_FTC_PROD_CELL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_ftc_bd; moi_ftc_dd] THEN
    REPEAT COND_CASES_TAC THEN ARITH_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^(2,2)finite_sum->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `?i. i < 6 /\ (x:real^2) IN (cb:num->real^2->bool) i` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN C` THEN
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
          check (fun th -> concl th =
            `segment[c,a] UNION segment[a,b] UNION segment[b,c:real^2] = C`)) THEN
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
         [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`] THEN ASM_REWRITE_TAC[ARITH];
        ALL_TAC] THEN
      SUBGOAL_THEN `?j. j < 9 /\ (y:real^2) IN (zd:num->real^2->bool) j` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN D` THEN EXPAND_TAC "D" THEN
        REWRITE_TAC[GSYM MOI_FTC_DISK_UNION; IN_UNION] THEN STRIP_TAC THENL
         [EXISTS_TAC `0`; EXISTS_TAC `1`] THEN ASM_REWRITE_TAC[ARITH];
        ALL_TAC] THEN
      EXISTS_TAC `((cb:num->real^2->bool) i PCROSS D) INTER (C PCROSS (zd:num->real^2->bool) j)` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS]]];
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM;
                IN_INTER; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^(2,2)finite_sum->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_SING] THEN MESON_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `?i. i < 6 /\ (x:real^2) IN (cb:num->real^2->bool) i` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN C` THEN
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
          check (fun th -> concl th =
            `segment[c,a] UNION segment[a,b] UNION segment[b,c:real^2] = C`)) THEN
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
         [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`] THEN ASM_REWRITE_TAC[ARITH];
        ALL_TAC] THEN
      EXISTS_TAC `((cb:num->real^2->bool) i PCROSS D) INTER (C PCROSS {vec 0:real^2})` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_SING] THEN
        EXPAND_TAC "D" THEN REWRITE_TAC[MOI_FTC_DISK_IN; VEC_COMPONENT] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV]]]);;

