needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_scella: the source cells of the Sec 34 cell diagram are PL     *)
(* cells (Moise, Geometric Topology in Dimensions 2 and 3, GTM 47, Sec 34,   *)
(* p.244: the face disks D_sigma, the tetra balls C(sigma^3), the patches    *)
(* X(sigma^3,v), and their arcs and marked points), towards the statement    *)
(* of pc_moi_s34_stmt.ml:                                                    *)
(*   SCELL_A = MOI_S34_SCELL_A                                               *)
(* Route.  Every cell inside a simplex q of kk is described by chains of    *)
(* the first barycentric subdivision of q (the regular neighbourhood N of   *)
(* the 1-skeleton is the union of the second-derived simplices meeting the  *)
(* graph).  A derived retriangulation h of q (MOI_FTA_DERIVED_HOMEO) with   *)
(* "flat" derived points (on the level 2/5 of the largest barycentric       *)
(* coordinate of q) maps these cells onto convex polytopes cut out by       *)
(* barycentric inequalities: the tetra ball onto a truncated tetrahedron,   *)
(* the patches onto hexagons, the arcs onto segments, the marked points     *)
(* onto points.  Convex polytopes are PL cells bounded by their relative    *)
(* frontiers, which are read off the inequalities.                          *)
(* Clauses 1-6 of moi_s34_scell_facts are MOI_S4A_CLAUSE1 to                *)
(* MOI_S4A_CLAUSE6.  The outer cells at boundary vertices and boundary      *)
(* edges of kk (clauses 7-8, collected verbatim in moi_s4a_outer) need the  *)
(* complement of a PL 2-disk in a PL 2-sphere (link spheres in real^N) and  *)
(* the second-derived structure in simplices of tt outside kk; here they    *)
(* are a hypothesis of MOI_S4A_SCELL_FACTS_OUTER and                        *)
(* MOI_S4A_SCELL_A_FROM_OUTER (whose consequent is MOI_S34_SCELL_A), and    *)
(* pc_moi_s34_outer.ml proves them (OUTER_CELLS) and SCELL_A.               *)
(* First, barycentric coordinates of a simplex.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. Barycentric coordinates: for an affinely independent V and a in V,    *)
(* an affine function (in dot form) equal to 1 at a and 0 at the other      *)
(* points of V.  It is unique on affine hull V, which is all that is used.  *)
(* ------------------------------------------------------------------------- *)

let moi_s4a_bc = new_definition
 `moi_s4a_bc (V:real^N->bool) (a:real^N) =
    @f:real^N->real. (?w k. !x. f x = w dot x + k) /\
                     (!b. b IN V ==> f b = if b = a then &1 else &0)`;;

let MOI_S4A_BC_EXISTS = prove
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

let MOI_S4A_BC = prove
 (`!(V:real^N->bool) (a:real^N).
     ~affine_dependent V
     ==> (?w k. !x. moi_s4a_bc V a x = w dot x + k) /\
         (!b. b IN V ==> moi_s4a_bc V a b = if b = a then &1 else &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    SPEC `a:real^N` o MATCH_MP MOI_S4A_BC_EXISTS) THEN
  SUBGOAL_THEN
   `?f:real^N->real. (?w k. !x. f x = w dot x + k) /\
                     (!b. b IN V ==> f b = if b = (a:real^N) then &1 else &0)`
  MP_TAC THENL
   [EXISTS_TAC `\x:real^N. (w:real^N) dot x + k` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`w:real^N`; `k:real`] THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM moi_s4a_bc]]);;

(* Dot forms of all coordinates at once. *)

let MOI_S4A_BC_DOT = prove
 (`!(V:real^N->bool).
     ~affine_dependent V
     ==> ?w k. !a x. a IN V ==> moi_s4a_bc V a x = w a dot x + k a`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. ?w k. a IN V ==> !x. moi_s4a_bc V a x = w dot x + k`
  MP_TAC THENL
   [X_GEN_TAC `a:real^N` THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`] MOI_S4A_BC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[]]);;

let MOI_S4A_BC_AFFINE = prove
 (`!(V:real^N->bool) a x y u.
     ~affine_dependent V
     ==> moi_s4a_bc V a ((&1 - u) % x + u % y) =
         (&1 - u) * moi_s4a_bc V a x + u * moi_s4a_bc V a y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    CONJUNCT1 o SPEC `a:real^N` o MATCH_MP MOI_S4A_BC) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* The coordinates of an affine combination of the points of V.            *)

let MOI_S4A_BC_AFF = prove
 (`!(V:real^N->bool) (u:real^N->real) a.
     ~affine_dependent V /\ a IN V /\ sum V u = &1
     ==> moi_s4a_bc V a (vsum V (\v. u v % v)) = u a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^N` o MATCH_MP MOI_S4A_BC) THEN
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

(* Points of the affine hull: the coordinates sum to 1 and reproduce x.    *)

let MOI_S4A_BC_HULL_EXPAND = prove
 (`!(V:real^N->bool) x.
     ~affine_dependent V /\ x IN affine hull V
     ==> sum V (\a. moi_s4a_bc V a x) = &1 /\
         vsum V (\a. moi_s4a_bc V a x % a) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN affine hull V` THEN
  ASM_SIMP_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `!a:real^N. a IN V
      ==> moi_s4a_bc V a (vsum V (\v. (u:real^N->real) v % v)) = u a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_BC_AFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS `sum V (u:real^N->real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]]);;

(* The simplex is cut out by the nonnegative coordinates; its faces by the  *)
(* vanishing of the coordinates of the missing vertices.                    *)

let MOI_S4A_BC_CONVEX_HULL = prove
 (`!(V:real^N->bool).
     ~affine_dependent V
     ==> convex hull V =
         {x | x IN affine hull V /\ !a. a IN V ==> &0 <= moi_s4a_bc V a x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull V` THEN
    ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N->real`; `a:real^N`]
      MOI_S4A_BC_AFF) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `x:real^N`] MOI_S4A_BC_HULL_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `\a:real^N. moi_s4a_bc V a x` THEN ASM_SIMP_TAC[]]);;

let MOI_S4A_BC_SUBHULL = prove
 (`!(V:real^N->bool) E.
     ~affine_dependent V /\ E SUBSET V
     ==> convex hull E =
         {x | x IN convex hull V /\
              !a. a IN V /\ ~(a IN E) ==> moi_s4a_bc V a x = &0}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ FINITE (E:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HULL_MONO; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull E` THEN
    ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`;
                   `\v:real^N. if v IN E then (u:real^N->real) v else &0`;
                   `a:real^N`] MOI_S4A_BC_AFF) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
      SUBGOAL_THEN `{v:real^N | v IN V /\ v IN E} = E`
       (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `vsum V (\v:real^N. (if v IN E then (u:real^N->real) v else &0) % v) =
      vsum E (\v. u v % v)`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum E (\v:real^N. (if v IN E then (u:real^N->real) v else &0) % v)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO];
      MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[]];
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull V /\
                  !a. a IN V ==> &0 <= moi_s4a_bc V a x`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BC_CONVEX_HULL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N` o
        REWRITE_RULE[EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `x:real^N`] MOI_S4A_BC_HULL_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `\a:real^N. moi_s4a_bc V a x` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      TRANS_TAC EQ_TRANS `sum V (\a:real^N. moi_s4a_bc V a x)` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      TRANS_TAC EQ_TRANS `vsum V (\a:real^N. moi_s4a_bc V a x % a)` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
        ASM_SIMP_TAC[VECTOR_MUL_LZERO];
        ASM_REWRITE_TAC[]]]]);;

(* Coordinates of barycentres of faces.                                      *)

let MOI_S4A_BC_BARY = prove
 (`!(V:real^N->bool) E a.
     ~affine_dependent V /\ E SUBSET V /\ ~(E = {}) /\ a IN V
     ==> moi_s4a_bc V a (simplex_barycentre (convex hull E)) =
         if a IN E then inv(&(CARD E)) else &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ FINITE (E:real^N->bool) /\
                ~affine_dependent (E:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_SUBSET;
                  AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(E:real^N->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL; barycentre] THEN
  MP_TAC(ISPECL [`V:real^N->bool`;
                 `\v:real^N. if v IN E then inv(&(CARD(E:real^N->bool))) else &0`;
                 `a:real^N`] MOI_S4A_BC_AFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{v:real^N | v IN V /\ v IN E} = E`
     (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum E (\v:real^N. (if v IN E then inv(&(CARD(E:real^N->bool)))
                                  else &0) % v)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* A vertex of V lying in the hull of E SUBSET V belongs to E.               *)

let MOI_S4A_BC_VERTEX_IN = prove
 (`!(V:real^N->bool) E a.
     ~affine_dependent V /\ E SUBSET V /\ a IN V /\ a IN convex hull E
     ==> a IN E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `E:real^N->bool`] MOI_S4A_BC_SUBHULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N` o
    REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`] MOI_S4A_BC) THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

(* Coordinates of convex (affine) combinations of arbitrary finite sets.    *)

let MOI_S4A_BC_VSUM = prove
 (`!(V:real^N->bool) a (s:real^N->bool) (u:real^N->real).
     ~affine_dependent V /\ FINITE s /\ sum s u = &1
     ==> moi_s4a_bc V a (vsum s (\y. u y % y)) =
         sum s (\y. u y * moi_s4a_bc V a y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o
    CONJUNCT1 o SPEC `a:real^N` o MATCH_MP MOI_S4A_BC) THEN
  ASM_SIMP_TAC[DOT_RSUM; DOT_RMUL; REAL_ADD_LDISTRIB; SUM_ADD; SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID]);;

(* On a simplex of the first barycentric subdivision of convex hull V, the  *)
(* coordinate of a vertex of its least face is the largest coordinate.     *)

let MOI_S4A_BC_CHAIN_MAX = prove
 (`!(V:real^N->bool) ch a0 a x.
     ~affine_dependent V /\ moi_bar_chain {f | f face_of convex hull V} ch /\
     (!e. e IN ch ==> a0 IN e) /\ a0 IN V /\ a IN V /\
     x IN convex hull (IMAGE simplex_barycentre ch)
     ==> moi_s4a_bc V a x <= moi_s4a_bc V a0 x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. moi_s4a_bc V a0 y - moi_s4a_bc V a y`; `&0`;
                 `IMAGE simplex_barycentre (ch:(real^N->bool)->bool)`]
    MOI_FTA_LEVEL_HULL_GE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S4A_BC_AFFINE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) face_of convex hull V /\ ~(e = {})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain {f | f face_of convex hull V} (ch:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(e:real^N->bool) face_of convex hull V` THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(E:real^N->bool = {}) /\ (a0:real^N) IN E` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(convex hull E:real^N->bool = {})` THEN
        ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
        MATCH_MP_TAC MOI_S4A_BC_VERTEX_IN THEN EXISTS_TAC `V:real^N->bool` THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_BC_BARY] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_LE_REFL; REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

(* The closed star of a vertex v of convex hull V in its first barycentric  *)
(* subdivision is where the coordinate of v is the largest.                 *)

let MOI_S4A_BC_STAR = prove
 (`!(V:real^N->bool) v.
     ~affine_dependent V /\ v IN V
     ==> UNIONS {m | m IN barycentric_subdivision {f | f face_of convex hull V} /\
                     v IN m} =
         {x | x IN convex hull V /\
              !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} face_of convex hull V` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision {f | f face_of convex hull V}` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `ch:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`{f:real^N->bool | f face_of convex hull V}`;
                   `ch:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`;
                     `ch:(real^N->bool)->bool`] MOI_BAR_FACE_CHAIN_HULL_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S4A_BC_CHAIN_MAX THEN
      EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`; `x:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(ch:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull IMAGE simplex_barycentre (ch:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a0:real^N. a0 IN V /\ !e. e IN ch ==> a0 IN e`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex hull V:real^N->bool`; `ch:(real^N->bool)->bool`]
      MOI_FTA_FACE_CHAIN_MIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `INTERS ch face_of convex hull (V:real^N->bool)` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain {r | r face_of convex hull V} (ch:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `E0:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?a0:real^N. a0 IN E0` MP_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(INTERS ch:real^N->bool = {})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a0:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a0:real^N) IN INTERS ch` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4a_bc V v (x:real^N) = moi_s4a_bc V a0 x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4A_BC_CHAIN_MAX THEN
      EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE simplex_barycentre (ch:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (S:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull S` THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[CONVEX_HULL_FINITE; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!e. e IN ch /\ ~((v:real^N) IN e) ==> (mu:real^N->real) (simplex_barycentre e) = &0`
  (LABEL_TAC "zero") THENL
   [SUBGOAL_THEN
     `!y:real^N. y IN S ==> &0 <= (mu:real^N->real) y *
                             (moi_s4a_bc V a0 y - moi_s4a_bc V v y)`
    ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `ch:(real^N->bool)->bool`; `a0:real^N`;
                     `v:real^N`; `simplex_barycentre (e:real^N->bool)`]
        MOI_S4A_BC_CHAIN_MAX) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN EXPAND_TAC "S" THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum S (\y:real^N. (mu:real^N->real) y *
                        (moi_s4a_bc V a0 y - moi_s4a_bc V v y)) = &0`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN ASM_SIMP_TAC[SUM_SUB] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a0:real^N`; `S:real^N->bool`;
                     `mu:real^N->real`] MOI_S4A_BC_VSUM) THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `v:real^N`; `S:real^N->bool`;
                     `mu:real^N->real`] MOI_S4A_BC_VSUM) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[REAL_SUB_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\y:real^N. (mu:real^N->real) y *
                               (moi_s4a_bc V a0 y - moi_s4a_bc V v y)`;
                   `S:real^N->bool`] SUM_POS_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `simplex_barycentre (e:real^N->bool)`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:real^N->bool) face_of convex hull V /\ ~(e = {})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain {t | t face_of convex hull V} (ch:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(e:real^N->bool) face_of convex hull V` THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(E:real^N->bool = {}) /\ (a0:real^N) IN E /\ ~(v IN E) /\
                  FINITE E`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(convex hull E:real^N->bool = {})` THEN
        ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
        MATCH_MP_TAC MOI_S4A_BC_VERTEX_IN THEN EXISTS_TAC `V:real^N->bool` THEN
        ASM_SIMP_TAC[];
        ASM_MESON_TAC[HULL_INC];
        ASM_MESON_TAC[FINITE_SUBSET]];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s4a_bc V a0 (simplex_barycentre (convex hull E)) -
                 moi_s4a_bc V v (simplex_barycentre (convex hull (E:real^N->bool))) = &0` THEN
    ASM_SIMP_TAC[MOI_S4A_BC_BARY] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                (({v:real^N}) INSERT {e | e IN ch /\ v IN e}))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `({v:real^N}) INSERT {e | e IN ch /\ v IN e}` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
      EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SIMP_TAC[IN_ELIM_THM; SING_SUBSET]];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING; IN_INSERT];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre {e | e IN ch /\ (v:real^N) IN e})` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC HULL_MONO THEN SET_TAC[]] THEN
  SUBGOAL_THEN `FINITE (IMAGE simplex_barycentre {e | e IN ch /\ (v:real^N) IN e})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  EXISTS_TAC `mu:real^N->real` THEN
  SUBGOAL_THEN
   `!y:real^N. y IN S /\ ~(y IN IMAGE simplex_barycentre {e | e IN ch /\ v IN e})
               ==> (mu:real^N->real) y = &0`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "zero" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE simplex_barycentre {e | e IN ch /\ (v:real^N) IN e} SUBSET S`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `&1`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `x:real^N`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* ========================================================================= *)
(* Level sets of affine functions on derived subdivisions.                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 2. Level sets of affine functions on derived subdivisions with arbitrary *)
(* derived points (generalizing MOI_FTA_SIMPLEX_LEVEL_GE, _EQ from the     *)
(* midpoint level points and 0/1 vertex values to any affine G that is     *)
(* above c on the graph vertices and below c on the others, with derived   *)
(* points of the mixed faces on the level G = c).                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_STRICT_HULL = prove
 (`!(f:real^N->real) c s.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     (!x. x IN s ==> f x < c)
     ==> !x. x IN convex hull s ==> f x < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull s SUBSET {x:real^N | f x < c}`
   (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < (&1 - u) * (c - a) + u * (c - b)
                           ==> (&1 - u) * a + u * b < c`) THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let MOI_S4A_HULL_LEVEL_GE = prove
 (`!(f:real^N->real) S1 S2 c x.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     (!y. y IN S1 ==> f y < c) /\ (!y. y IN S2 ==> f y = c) /\
     x IN convex hull (S1 UNION S2) /\ c <= f x
     ==> x IN convex hull S2 /\ ~(S2 = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `S2:real^N->bool = {}` THENL
   [UNDISCH_TAC `(x:real^N) IN convex hull (S1 UNION S2)` THEN
    ASM_REWRITE_TAC[UNION_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `c:real`; `S1:real^N->bool`]
      MOI_S4A_STRICT_HULL) THEN
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
  SUBGOAL_THEN `(f:real^N->real) y1 < c /\ f y2 = c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^N->real`; `c:real`; `S1:real^N->bool`]
        MOI_S4A_STRICT_HULL);
      MP_TAC(ISPECL [`f:real^N->real`; `c:real`; `S2:real^N->bool`]
        MOI_FTA_LEVEL_HULL)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `c <= (f:real^N->real) x` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(&0 < &1 - u) ==> &1 <= u`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&1 - u`; `c - (f:real^N->real) y1`] REAL_LT_MUL) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN UNDISCH_TAC
     `c <= (&1 - u) * (f:real^N->real) y1 + u * c` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
                    VECTOR_MUL_LID]]);;

(* The derived simplices of any choice of derived points cover the simplex. *)

let MOI_S4A_DCOVER = prove
 (`!n m (d:(real^N->bool)->real^N) x.
     n simplex m /\ x IN m /\
     (!r. r face_of m /\ ~(r = {}) ==> d r IN relative_interior r)
     ==> ?g. moi_bar_chain {r | r face_of m} g /\
             x IN convex hull (IMAGE d g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:int`; `m:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of m}`; `d:(real^N->bool)->real^N`]
    MOI_FTA_DERIVED_HOMEO) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
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

(* Values of G at the derived points of the faces of convex hull V.         *)

let MOI_S4A_DVAL = prove
 (`!(l:(real^N->bool)->bool) (G:real^N->real) c (d:(real^N->bool)->real^N) V r.
     ~affine_dependent V /\
     (!x y u. G((&1 - u) % x + u % y) = (&1 - u) * G x + u * G y) /\
     (!a. a IN V /\ a IN UNIONS l ==> c < G a) /\
     (!a. a IN V /\ ~(a IN UNIONS l) ==> G a < c) /\
     (!r. r face_of convex hull V /\ ~(r = {}) ==> d r IN relative_interior r) /\
     (!r. r face_of convex hull V /\
          (?a. a extreme_point_of r /\ a IN UNIONS l) /\
          (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
          ==> G(d r) = c) /\
     r face_of convex hull V /\ ~(r = {})
     ==> d r IN r /\
         ((?a. a extreme_point_of r /\ a IN UNIONS l) /\
          (?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> G(d r) = c) /\
         (~(?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> c < G(d r)) /\
         (~(?a. a extreme_point_of r /\ a IN UNIONS l) ==> G(d r) < c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:(real^N->bool)->real^N) r IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(r:real^N->bool) face_of convex hull V` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (W:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. --((G:real^N->real) x)`; `--c:real`;
                   `W:real^N->bool`] MOI_S4A_STRICT_HULL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_NEG2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o SPEC `(d:(real^N->bool)->real^N) (convex hull W)`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`G:real^N->real`; `c:real`; `W:real^N->bool`]
      MOI_S4A_STRICT_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o SPEC `(d:(real^N->bool)->real^N) (convex hull W)`) THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S4A_LEVEL_GE = prove
 (`!(l:(real^N->bool)->bool) (G:real^N->real) c (d:(real^N->bool)->real^N) V x.
     ~affine_dependent V /\
     (!x y u. G((&1 - u) % x + u % y) = (&1 - u) * G x + u * G y) /\
     (!a. a IN V /\ a IN UNIONS l ==> c < G a) /\
     (!a. a IN V /\ ~(a IN UNIONS l) ==> G a < c) /\
     (!r. r face_of convex hull V /\ ~(r = {}) ==> d r IN relative_interior r) /\
     (!r. r face_of convex hull V /\
          (?a. a extreme_point_of r /\ a IN UNIONS l) /\
          (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
          ==> G(d r) = c)
     ==> ((?g. moi_bar_chain {r | r face_of convex hull V} g /\ moi_fta_gp l g /\
               x IN convex hull (IMAGE d g)) <=>
          x IN convex hull V /\ c <= G x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (convex hull (V:real^N->bool)) /\ compact (convex hull V)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r face_of convex hull V /\ ~(r = {})
        ==> (d:(real^N->bool)->real^N) r IN r /\
            ((?a. a extreme_point_of r /\ a IN UNIONS l) /\
             (?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> G(d r) = c) /\
            (~(?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> c < G(d r)) /\
            (~(?a. a extreme_point_of r /\ a IN UNIONS l) ==> G(d r) < c)`
  (LABEL_TAC "val") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_DVAL THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r g. moi_bar_chain {r | r face_of convex hull V} g /\ r IN g
          ==> r face_of convex hull (V:real^N->bool) /\ ~(r = {})`
  (LABEL_TAC "elt") THENL
   [REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. moi_bar_chain {r | r face_of convex hull V} g
        ==> convex hull (IMAGE (d:(real^N->bool)->real^N) g) SUBSET
            convex hull V`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `g:(real^N->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^N->real`; `c:real`;
      `IMAGE (d:(real^N->bool)->real^N) g`] MOI_FTA_LEVEL_HULL_GE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `moi_fta_gp l (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fta_gp] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `?b:real^N. b extreme_point_of r /\ ~(b IN UNIONS l)` THENL
       [ASM_MESON_TAC[REAL_LE_REFL]; ASM_MESON_TAC[REAL_LT_IMP_LE]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`;
                 `d:(real^N->bool)->real^N`; `x:real^N`] MOI_S4A_DCOVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull (IMAGE (d:(real^N->bool)->real^N) g)` THEN
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
  MP_TAC(ISPECL [`G:real^N->real`;
    `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     ~(?a. a extreme_point_of r /\ a IN UNIONS l)}`;
    `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     (?a. a extreme_point_of r /\ a IN UNIONS l)}`;
    `c:real`; `x:real^N`] MOI_S4A_HULL_LEVEL_GE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`convex hull V:real^N->bool`; `g:(real^N->bool)->bool`;
        `r1:real^N->bool`; `r:real^N->bool`; `UNIONS l:real^N->bool`]
        MOI_FTA_CHAIN_EXT_UP) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      SUBGOAL_THEN
       `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     ~(?a. a extreme_point_of r /\ a IN UNIONS l)} UNION
        IMAGE d {r:real^N->bool | r IN g /\
                     (?a. a extreme_point_of r /\ a IN UNIONS l)} =
        IMAGE d g` SUBST1_TAC THENL
       [SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gpmin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S4A_LEVEL_EQ = prove
 (`!(l:(real^N->bool)->bool) (G:real^N->real) c (d:(real^N->bool)->real^N) V x.
     ~affine_dependent V /\
     (!x y u. G((&1 - u) % x + u % y) = (&1 - u) * G x + u * G y) /\
     (!a. a IN V /\ a IN UNIONS l ==> c < G a) /\
     (!a. a IN V /\ ~(a IN UNIONS l) ==> G a < c) /\
     (!r. r face_of convex hull V /\ ~(r = {}) ==> d r IN relative_interior r) /\
     (!r. r face_of convex hull V /\
          (?a. a extreme_point_of r /\ a IN UNIONS l) /\
          (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
          ==> G(d r) = c)
     ==> ((?g. moi_bar_chain {r | r face_of convex hull V} g /\ moi_fta_gm l g /\
               x IN convex hull (IMAGE d g)) <=>
          x IN convex hull V /\ G x = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `G:real^N->real`; `c:real`;
                 `d:(real^N->bool)->real^N`; `V:real^N->bool`; `x:real^N`]
    MOI_S4A_LEVEL_GE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ge") THEN
  SUBGOAL_THEN
   `!r. r face_of convex hull V /\ ~(r = {})
        ==> (d:(real^N->bool)->real^N) r IN r /\
            ((?a. a extreme_point_of r /\ a IN UNIONS l) /\
             (?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> G(d r) = c) /\
            (~(?b. b extreme_point_of r /\ ~(b IN UNIONS l)) ==> c < G(d r)) /\
            (~(?a. a extreme_point_of r /\ a IN UNIONS l) ==> G(d r) < c)`
  (LABEL_TAC "val") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_DVAL THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r g. moi_bar_chain {r | r face_of convex hull V} g /\ r IN g
          ==> r face_of convex hull (V:real^N->bool) /\ ~(r = {})`
  (LABEL_TAC "elt") THENL
   [REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `x IN convex hull (V:real^N->bool) /\ c <= G x`
       (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ge" (SUBST1_TAC o SYM) THEN
      EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fta_gm l (g:(real^N->bool)->bool)` THEN
      SIMP_TAC[moi_fta_gm];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^N->real`; `c:real`;
      `IMAGE (d:(real^N->bool)->real^N) g`] MOI_FTA_LEVEL_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_fta_gm l (g:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_fta_gm; moi_fta_gp] THEN ASM_MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ge" (MP_TAC o snd o EQ_IMP_RULE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{r:real^N->bool | r IN g /\
                               (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}` THEN
  SUBGOAL_THEN
   `moi_bar_chain {r | r face_of convex hull V}
      {r:real^N->bool | r IN g /\ (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> ?a. a extreme_point_of r /\ a IN UNIONS l`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fta_gp l (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fta_gp] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^N. --((G:real^N->real) y)`;
    `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     ~(?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`;
    `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`;
    `--c:real`; `x:real^N`] MOI_S4A_HULL_LEVEL_GE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      USE_THEN "elt" (MP_TAC o SPECL [`r:real^N->bool`; `g:(real^N->bool)->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "val" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `IMAGE (d:(real^N->bool)->real^N) {r:real^N->bool | r IN g /\
                     ~(?b. b extreme_point_of r /\ ~(b IN UNIONS l))} UNION
        IMAGE d {r:real^N->bool | r IN g /\
                     (?b. b extreme_point_of r /\ ~(b IN UNIONS l))} =
        IMAGE d g` SUBST1_TAC THENL
       [SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `convex hull V:real^N->bool`;
    `{r:real^N->bool | r IN g /\ (?b. b extreme_point_of r /\ ~(b IN UNIONS l))}`]
    MOI_FTA_GP_GM_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Chains whose members share a vertex off the graph (the closure of the    *)
(* complement of the regular neighbourhood).                                *)

let moi_s4a_gq = new_definition
 `moi_s4a_gq (l:(real^N->bool)->bool) (g:(real^N->bool)->bool) <=>
    ~(g = {}) /\ ?b. ~(b IN UNIONS l) /\ !r. r IN g ==> b extreme_point_of r`;;

let MOI_S4A_GQ_GP = prove
 (`!(l:(real^N->bool)->bool) g.
     moi_s4a_gq l g <=> moi_fta_gp {(:real^N) DIFF UNIONS l} g`,
  REWRITE_TAC[moi_s4a_gq; moi_fta_gp; UNIONS_1; IN_DIFF; IN_UNIV]);;

let MOI_S4A_GQ_HER = prove
 (`!(l:(real^N->bool)->bool) g g'.
     moi_s4a_gq l g /\ g' SUBSET g /\ ~(g' = {}) ==> moi_s4a_gq l g'`,
  REWRITE_TAC[moi_s4a_gq; SUBSET] THEN MESON_TAC[]);;

let MOI_S4A_LEVEL_LE = prove
 (`!(l:(real^N->bool)->bool) (G:real^N->real) c (d:(real^N->bool)->real^N) V x.
     ~affine_dependent V /\
     (!x y u. G((&1 - u) % x + u % y) = (&1 - u) * G x + u * G y) /\
     (!a. a IN V /\ a IN UNIONS l ==> c < G a) /\
     (!a. a IN V /\ ~(a IN UNIONS l) ==> G a < c) /\
     (!r. r face_of convex hull V /\ ~(r = {}) ==> d r IN relative_interior r) /\
     (!r. r face_of convex hull V /\
          (?a. a extreme_point_of r /\ a IN UNIONS l) /\
          (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
          ==> G(d r) = c)
     ==> ((?g. moi_bar_chain {r | r face_of convex hull V} g /\ moi_s4a_gq l g /\
               x IN convex hull (IMAGE d g)) <=>
          x IN convex hull V /\ G x <= c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_S4A_GQ_GP] THEN
  MP_TAC(ISPECL [`{(:real^N) DIFF UNIONS l}`; `\y:real^N. --((G:real^N->real) y)`;
                 `--c:real`; `d:(real^N->bool)->real^N`; `V:real^N->bool`;
                 `x:real^N`] MOI_S4A_LEVEL_GE) THEN
  REWRITE_TAC[UNIONS_1; IN_DIFF; IN_UNIV; REAL_LE_NEG2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_NEG2] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Flat derived points and the flat retriangulation of a simplex.          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 3. Flat derived points.  In a simplex convex hull V whose t1-vertices on  *)
(* the graph are exactly the barycentres of its vertices and edges, the     *)
(* derived point of a mixed simplex of the first barycentric subdivision is *)
(* chosen on the level 2/5 of the largest barycentric coordinate.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_TWO_BARY_RELINT = prove
 (`!(W:real^N->bool) P t.
     ~affine_dependent W /\
     ~({x | x IN W /\ P x} = {}) /\ ~({x | x IN W /\ ~P x} = {}) /\
     &0 < t /\ t < &1
     ==> (&1 - t) % barycentre {x | x IN W /\ P x} +
         t % barycentre {x | x IN W /\ ~P x} IN
         relative_interior(convex hull W)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(W:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `A = {x:real^N | x IN W /\ P x}` THEN
  ABBREV_TAC `B = {x:real^N | x IN W /\ ~P x}` THEN
  SUBGOAL_THEN `FINITE(A:real^N->bool) /\ FINITE(B:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(A:real^N->bool) = 0) /\ ~(CARD(B:real^N->bool) = 0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `\x:real^N. if P x then (&1 - t) * inv(&(CARD(A:real^N->bool)))
                         else t * inv(&(CARD(B:real^N->bool)))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CASES; SUM_CONST] THEN
    SUBGOAL_THEN `&(CARD(A:real^N->bool)) * inv(&(CARD A)) = &1 /\
                  &(CARD(B:real^N->bool)) * inv(&(CARD B)) = &1`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD];
    SUBGOAL_THEN
     `vsum W (\x:real^N. (if P x then (&1 - t) * inv(&(CARD(A:real^N->bool)))
                          else t * inv(&(CARD(B:real^N->bool)))) % x) =
      vsum W (\x. if P x then ((&1 - t) * inv(&(CARD A))) % x
                  else (t * inv(&(CARD B))) % x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VSUM_CASES; barycentre] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL]]);;

(* A nonempty chain of faces of convex hull V has a vertex of V in all of   *)
(* its members; the values of that coordinate at the t1-vertices.          *)

let MOI_S4A_CHAIN_BOTTOM = prove
 (`!(V:real^N->bool) ch.
     ~affine_dependent V /\ moi_bar_chain {f | f face_of convex hull V} ch /\
     ~(ch = {})
     ==> ?a0. a0 IN V /\ !e. e IN ch ==> a0 IN e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull V:real^N->bool`; `ch:(real^N->bool)->bool`]
    MOI_FTA_FACE_CHAIN_MIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `INTERS ch face_of convex hull (V:real^N->bool)` MP_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {f | f face_of convex hull V} (ch:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?a0:real^N. a0 IN E0` MP_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(INTERS ch:real^N->bool = {})` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a0:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a0:real^N) IN INTERS ch` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_S4A_VERT_VAL = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool) ch a0 e.
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2)) /\
     moi_bar_chain {f | f face_of convex hull V} ch /\
     a0 IN V /\ (!e. e IN ch ==> a0 IN e) /\ e IN ch
     ==> (simplex_barycentre e IN UNIONS l
          ==> &2 / &5 < moi_s4a_bc V a0 (simplex_barycentre e)) /\
         (~(simplex_barycentre e IN UNIONS l)
          ==> moi_s4a_bc V a0 (simplex_barycentre e) < &2 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of convex hull V /\ ~(e = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {f | f face_of convex hull V} (ch:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(e:real^N->bool) face_of convex hull V` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~(E:real^N->bool = {}) /\ (a0:real^N) IN E /\ FINITE E`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(convex hull E:real^N->bool = {})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
      MATCH_MP_TAC MOI_S4A_BC_VERTEX_IN THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[FINITE_SUBSET; AFFINE_INDEPENDENT_IMP_FINITE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4A_BC_BARY] THEN
  SUBGOAL_THEN `1 <= CARD(E:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `CARD(E:real^N->bool) = 1 \/ CARD E = 2` MP_TAC THENL
     [ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    TRANS_TAC REAL_LET_TRANS `inv(&3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let moi_s4a_fd = new_definition
 `moi_s4a_fd (L:real^N->bool) (V:real^N->bool) (s:real^N->bool) =
    if (?a. a extreme_point_of s /\ a IN L) /\ (?b. b extreme_point_of s /\ ~(b IN L))
    then @z. z IN relative_interior s /\
             (!a. a IN V ==> moi_s4a_bc V a z <= &2 / &5) /\
             (?a. a IN V /\ moi_s4a_bc V a z = &2 / &5)
    else simplex_barycentre s`;;

let MOI_S4A_REAL_T = prove
 (`!p q c. q < c /\ c < p
           ==> &0 < (p - c) / (p - q) /\ (p - c) / (p - q) < &1 /\
               (&1 - (p - c) / (p - q)) * p + ((p - c) / (p - q)) * q = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p - q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < p - q` THEN CONV_TAC REAL_FIELD);;

let MOI_S4A_FD_EXISTS = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool) m.
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2)) /\
     m IN barycentric_subdivision {f | f face_of convex hull V} /\
     (?a. a extreme_point_of m /\ a IN UNIONS l) /\
     (?b. b extreme_point_of m /\ ~(b IN UNIONS l))
     ==> ?z. z IN relative_interior m /\
             (!a. a IN V ==> moi_s4a_bc V a z <= &2 / &5) /\
             (?a. a IN V /\ moi_s4a_bc V a z = &2 / &5)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN ASSUME_TAC)))) THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = IMAGE simplex_barycentre (ch:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `~affine_dependent (W:real^N->bool) /\ FINITE W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `{f:real^N->bool | f face_of convex hull V}` THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT
    (ASSUME `~affine_dependent (W:real^N->bool)`)]) THEN
  SUBGOAL_THEN `~(ch:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `IMAGE simplex_barycentre ch = (W:real^N->bool)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `ch:(real^N->bool)->bool`] MOI_S4A_CHAIN_BOTTOM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!w:real^N. w IN W /\ w IN UNIONS l ==> &2 / &5 < moi_s4a_bc V a0 w) /\
    (!w:real^N. w IN W /\ ~(w IN UNIONS l) ==> moi_s4a_bc V a0 w < &2 / &5)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
    CONJ_TAC THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`;
                   `ch:(real^N->bool)->bool`; `a0:real^N`; `e:real^N->bool`]
      MOI_S4A_VERT_VAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `BP = barycentre {w:real^N | w IN W /\ w IN UNIONS l}` THEN
  ABBREV_TAC `BN = barycentre {w:real^N | w IN W /\ ~(w IN UNIONS l)}` THEN
  SUBGOAL_THEN
   `&2 / &5 < moi_s4a_bc V a0 (BP:real^N) /\ moi_s4a_bc V a0 (BN:real^N) < &2 / &5`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y:real^N. --(moi_s4a_bc V a0 y)`; `--(&2 / &5)`;
                     `{w:real^N | w IN W /\ w IN UNIONS l}`] MOI_S4A_STRICT_HULL) THEN
      ASM_SIMP_TAC[MOI_S4A_BC_AFFINE; IN_ELIM_THM; REAL_LT_NEG2] THEN
      ANTS_TAC THENL [REPEAT GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `BP:real^N`) THEN
      ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      EXPAND_TAC "BP" THEN MATCH_MP_TAC BARYCENTRE_IN_CONVEX_HULL THEN
      ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`\y:real^N. moi_s4a_bc V a0 y`; `&2 / &5`;
                     `{w:real^N | w IN W /\ ~(w IN UNIONS l)}`] MOI_S4A_STRICT_HULL) THEN
      ASM_SIMP_TAC[MOI_S4A_BC_AFFINE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `BN:real^N`) THEN
      ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      EXPAND_TAC "BN" THEN MATCH_MP_TAC BARYCENTRE_IN_CONVEX_HULL THEN
      ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s4a_bc V a0 (BP:real^N)`; `moi_s4a_bc V a0 (BN:real^N)`;
                 `&2 / &5`] MOI_S4A_REAL_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t = (moi_s4a_bc V a0 (BP:real^N) - &2 / &5) /
                  (moi_s4a_bc V a0 BP - moi_s4a_bc V a0 (BN:real^N))` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(&1 - t) % (BP:real^N) + t % BN` THEN
  SUBGOAL_THEN `(&1 - t) % (BP:real^N) + t % BN IN relative_interior (convex hull W)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["BP"; "BN"] THEN
    MP_TAC(ISPECL [`W:real^N->bool`; `\x:real^N. x IN UNIONS l`; `t:real`]
      MOI_S4A_TWO_BARY_RELINT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s4a_bc V a0 ((&1 - t) % (BP:real^N) + t % BN) = &2 / &5`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_S4A_BC_AFFINE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S4A_BC_CHAIN_MAX THEN
    EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    EXISTS_TAC `a0:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_S4A_C1_FACTS = prove
 (`!(V:real^N->bool).
     ~affine_dependent V
     ==> FINITE (barycentric_subdivision {f | f face_of convex hull V}) /\
         moi_bar_complex {f | f face_of convex hull V} /\
         moi_bar_complex (barycentric_subdivision {f | f face_of convex hull V}) /\
         UNIONS (barycentric_subdivision {f | f face_of convex hull V}) =
         convex hull V`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex convex hull (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    REWRITE_TAC[simplex] THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `convex hull V:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; MOI_BAR_SUBDIVISION_COMPLEX;
               MOI_BAR_UNIONS_SUBDIVISION]);;

let MOI_S4A_FD = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool) m.
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2)) /\
     m IN barycentric_subdivision {f | f face_of convex hull V} /\ ~(m = {})
     ==> moi_s4a_fd (UNIONS l) V m IN relative_interior m /\
         ((?a. a extreme_point_of m /\ a IN UNIONS l) /\
          (?b. b extreme_point_of m /\ ~(b IN UNIONS l))
          ==> (!a. a IN V
                   ==> moi_s4a_bc V a (moi_s4a_fd (UNIONS l) V m) <= &2 / &5) /\
              (?a. a IN V /\ moi_s4a_bc V a (moi_s4a_fd (UNIONS l) V m) = &2 / &5))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s4a_fd] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`; `m:real^N->bool`]
      MOI_S4A_FD_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SIMPLEX THEN
    EXISTS_TAC `barycentric_subdivision {f:real^N->bool | f face_of convex hull V}` THEN
    ASM_SIMP_TAC[MOI_S4A_C1_FACTS]]);;

let MOI_S4A_FLAT_HOMEO = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool).
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2))
     ==> ?h k. pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
               (!f. moi_bar_chain
                      (barycentric_subdivision {f | f face_of convex hull V}) f
                    ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
                        convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) f)) /\
               (!s. s IN barycentric_subdivision {f | f face_of convex hull V}
                    ==> IMAGE h s = s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision {f:real^N->bool | f face_of convex hull V}`;
                 `moi_s4a_fd (UNIONS l) (V:real^N->bool)`] MOI_FTA_DERIVED_HOMEO) THEN
  ASM_SIMP_TAC[MOI_S4A_C1_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4A_FD) THEN
  ASM_SIMP_TAC[]);;

(* Level descriptions on one simplex m of the first barycentric subdivision. *)

let MOI_S4A_FLAT_M = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool) m x.
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2)) /\
     m IN barycentric_subdivision {f | f face_of convex hull V}
     ==> ((?g. moi_bar_chain {r | r face_of m} g /\ moi_fta_gp l g /\
               x IN convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) g)) <=>
          x IN m /\ ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a x) /\
         ((?g. moi_bar_chain {r | r face_of m} g /\ moi_fta_gm l g /\
               x IN convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) g)) <=>
          x IN m /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
          ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5) /\
         ((?g. moi_bar_chain {r | r face_of m} g /\ moi_s4a_gq l g /\
               x IN convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) g)) <=>
          x IN m /\ !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_C1_FACTS) THEN
  UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision {f | f face_of convex hull V}` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `ch:(real^N->bool)->bool = {}` THENL
   [SUBGOAL_THEN `!g:(real^N->bool)->bool. moi_bar_chain {r | r face_of {}} g ==> g = {}`
    (LABEL_TAC "emp") THENL
     [REWRITE_TAC[moi_bar_chain; FACE_OF_EMPTY; SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
    USE_THEN "emp" (MP_TAC o SPEC `g:(real^N->bool)->bool`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) g)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `ch:(real^N->bool)->bool`] MOI_S4A_CHAIN_BOTTOM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y a. y IN convex hull (IMAGE simplex_barycentre ch) /\ a IN V
          ==> moi_s4a_bc V a y <= moi_s4a_bc V (a0:real^N) y`
  (LABEL_TAC "max") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_BC_CHAIN_MAX THEN
    EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent (IMAGE simplex_barycentre (ch:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `{f:real^N->bool | f face_of convex hull V}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a. a IN IMAGE simplex_barycentre ch /\ a IN UNIONS l
         ==> &2 / &5 < moi_s4a_bc V (a0:real^N) a) /\
    (!a. a IN IMAGE simplex_barycentre ch /\ ~(a IN UNIONS l)
         ==> moi_s4a_bc V (a0:real^N) a < &2 / &5) /\
    (!r. r face_of convex hull (IMAGE simplex_barycentre ch) /\ ~(r = {})
         ==> moi_s4a_fd (UNIONS l) V r IN relative_interior r) /\
    (!r. r face_of convex hull (IMAGE simplex_barycentre ch) /\
         (?a. a extreme_point_of r /\ a IN UNIONS l) /\
         (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
         ==> moi_s4a_bc V a0 (moi_s4a_fd (UNIONS l) V r) = &2 / &5)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!r. r face_of convex hull (IMAGE simplex_barycentre ch)
          ==> r IN barycentric_subdivision {f:real^N->bool | f face_of convex hull V}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (ch:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `ch:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `e:real^N->bool` THEN REPEAT DISCH_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`;
                     `ch:(real^N->bool)->bool`; `a0:real^N`; `e:real^N->bool`]
        MOI_S4A_VERT_VAL) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `e:real^N->bool` THEN REPEAT DISCH_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`;
                     `ch:(real^N->bool)->bool`; `a0:real^N`; `e:real^N->bool`]
        MOI_S4A_VERT_VAL) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
        MOI_S4A_FD) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      DISCH_THEN(LABEL_TAC "pa") THEN DISCH_THEN(LABEL_TAC "nb") THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
        MOI_S4A_FD) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
        USE_THEN "pa" MP_TAC THEN REWRITE_TAC[EXTREME_POINT_OF_EMPTY];
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "pa" ACCEPT_TAC; USE_THEN "nb" ACCEPT_TAC];
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a1:real^N`
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN USE_THEN "max" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(r:real^N->bool) SUBSET convex hull (IMAGE simplex_barycentre ch)`
        MP_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
        MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `moi_s4a_bc V (a0:real^N)`; `&2 / &5`;
                 `moi_s4a_fd (UNIONS l) (V:real^N->bool)`;
                 `IMAGE simplex_barycentre (ch:(real^N->bool)->bool)`; `x:real^N`]
    MOI_S4A_LEVEL_GE) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `moi_s4a_bc V (a0:real^N)`; `&2 / &5`;
                 `moi_s4a_fd (UNIONS l) (V:real^N->bool)`;
                 `IMAGE simplex_barycentre (ch:(real^N->bool)->bool)`; `x:real^N`]
    MOI_S4A_LEVEL_EQ) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `moi_s4a_bc V (a0:real^N)`; `&2 / &5`;
                 `moi_s4a_fd (UNIONS l) (V:real^N->bool)`;
                 `IMAGE simplex_barycentre (ch:(real^N->bool)->bool)`; `x:real^N`]
    MOI_S4A_LEVEL_LE) THEN
  ASM_SIMP_TAC[MOI_S4A_BC_AFFINE] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REPEAT CONJ_TAC THEN
  (EQ_TAC THENL [ALL_TAC; ALL_TAC]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `a0:real^N` THEN ASM_REWRITE_TAC[];
    TRANS_TAC REAL_LE_TRANS `moi_s4a_bc V (a:real^N) x` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN USE_THEN "max" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `a0:real^N` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN USE_THEN "max" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `moi_s4a_bc V (a0:real^N) x` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The image of a union of chain simplices under the flat retriangulation,  *)
(* from its trace on each simplex of the first barycentric subdivision.     *)

let MOI_S4A_FLAT_IMAGE_GEN = prove
 (`!(V:real^N->bool) (d:(real^N->bool)->real^N) h k P Q.
     ~affine_dependent V /\
     pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
     (!f. moi_bar_chain (barycentric_subdivision {f | f face_of convex hull V}) f
          ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
              convex hull (IMAGE d f)) /\
     (!s. s IN barycentric_subdivision {f | f face_of convex hull V}
          ==> IMAGE h s = s) /\
     (!g g'. P g /\ g' SUBSET g /\ ~(g' = {}) ==> P g') /\
     (!m x. m IN barycentric_subdivision {f | f face_of convex hull V}
            ==> ((?g. moi_bar_chain {r | r face_of m} g /\ P g /\
                      x IN convex hull (IMAGE d g)) <=> x IN m /\ Q x))
     ==> IMAGE h (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                          moi_bar_chain
                            (barycentric_subdivision {f | f face_of convex hull V}) g /\
                          P g}) =
         {x | x IN convex hull V /\ Q x}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_C1_FACTS) THEN
  ABBREV_TAC `c1 = barycentric_subdivision {f:real^N->bool | f face_of convex hull V}` THEN
  SUBGOAL_THEN `homeomorphism (UNIONS c1,UNIONS c1) ((h:real^N->real^N),k)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m x. m IN c1
          ==> (x IN IMAGE (h:real^N->real^N)
                (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                         moi_bar_chain c1 g /\ P g}) /\ x IN m <=>
               x IN m /\ Q x)`
  (LABEL_TAC "tr") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "q" (fun th ->
      REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(m:real^N->bool) IN c1`))]) THEN
    MATCH_MP_TAC MOI_FTA_TRANSFER THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
            moi_bar_chain c1 g /\ P g} SUBSET convex hull (V:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET] THEN
    MP_TAC(ISPECL [`c1:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
     `(t:real^N->bool) SUBSET u ==> (s:real^N->bool) SUBSET t ==> s SUBSET u`) THEN
    GEN_REWRITE_TAC RAND_CONV
      [SYM(ASSUME `UNIONS c1 = convex hull (V:real^N->bool)`)] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN
    UNDISCH_TAC `moi_bar_chain c1 (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (convex hull V) = convex hull V`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull V` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `?m:real^N->bool. m IN c1 /\ x IN m` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPECL [`m:real^N->bool`; `x:real^N`] (ASSUME
     `!m x. m IN c1
            ==> (x IN IMAGE (h:real^N->real^N)
                  (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                           moi_bar_chain c1 g /\ P g}) /\ x IN m <=>
                 x IN m /\ Q x)`)) (ASSUME `(m:real^N->bool) IN c1`)) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `?m:real^N->bool. m IN c1 /\ x IN m` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPECL [`m:real^N->bool`; `x:real^N`] (ASSUME
     `!m x. m IN c1
            ==> (x IN IMAGE (h:real^N->real^N)
                  (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                           moi_bar_chain c1 g /\ P g}) /\ x IN m <=>
                 x IN m /\ Q x)`)) (ASSUME `(m:real^N->bool) IN c1`)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* The flat images of N, Bd N and the closure of the complement of N in a   *)
(* simplex (in chain form): cut out by the largest barycentric coordinate. *)

let MOI_S4A_FLAT_IMAGES = prove
 (`!(V:real^N->bool) (l:(real^N->bool)->bool) h k.
     ~affine_dependent V /\
     (!E. E SUBSET V /\ ~(E = {})
          ==> (simplex_barycentre (convex hull E) IN UNIONS l <=> CARD E <= 2)) /\
     pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
     (!f. moi_bar_chain (barycentric_subdivision {f | f face_of convex hull V}) f
          ==> IMAGE h (convex hull (IMAGE simplex_barycentre f)) =
              convex hull (IMAGE (moi_s4a_fd (UNIONS l) V) f)) /\
     (!s. s IN barycentric_subdivision {f | f face_of convex hull V}
          ==> IMAGE h s = s)
     ==> IMAGE h (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                          moi_bar_chain
                            (barycentric_subdivision {f | f face_of convex hull V}) g /\
                          moi_fta_gp l g}) =
         {x | x IN convex hull V /\ ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a x} /\
         IMAGE h (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                          moi_bar_chain
                            (barycentric_subdivision {f | f face_of convex hull V}) g /\
                          moi_fta_gm l g}) =
         {x | x IN convex hull V /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5} /\
         IMAGE h (UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                          moi_bar_chain
                            (barycentric_subdivision {f | f face_of convex hull V}) g /\
                          moi_s4a_gq l g}) =
         {x | x IN convex hull V /\ !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC MOI_S4A_FLAT_IMAGE_GEN THEN
  MAP_EVERY EXISTS_TAC [`moi_s4a_fd (UNIONS l) (V:real^N->bool)`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[MOI_FTA_GP_GM_HER; MOI_S4A_GQ_HER] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `l:(real^N->bool)->bool`; `m:real^N->bool`;
                 `x:real^N`] MOI_S4A_FLAT_M) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Polytopes cut out by inequalities; polytopes are PL cells.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 4. Polytopes cut out of an affine set by finitely many affine            *)
(* inequalities with a strict interior point: their affine hull and         *)
(* relative frontier.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_RF = prove
 (`!(A:real^N->bool) (ix:K->bool) (w:K->real^N) (k:K->real) x0.
     affine A /\ FINITE ix /\ x0 IN A /\ (!i. i IN ix ==> &0 < w i dot x0 + k i) /\
     bounded {x | x IN A /\ !i. i IN ix ==> &0 <= w i dot x + k i}
     ==> polytope {x | x IN A /\ !i. i IN ix ==> &0 <= w i dot x + k i} /\
         affine hull {x | x IN A /\ !i. i IN ix ==> &0 <= w i dot x + k i} = A /\
         relative_frontier {x | x IN A /\ !i. i IN ix ==> &0 <= w i dot x + k i} =
         {x | x IN A /\ (!i. i IN ix ==> &0 <= w i dot x + k i) /\
              ?i. i IN ix /\ w i dot x + k i = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s0 = INTERS (IMAGE (\i:K. {x:real^N | w i dot x >= --(k i)}) ix)` THEN
  SUBGOAL_THEN
   `{x | x IN A /\ !i. i IN ix ==> &0 <= (w:K->real^N) i dot x + k i} = A INTER s0`
  SUBST1_TAC THENL
   [EXPAND_TAC "s0" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERS; IN_ELIM_THM;
      FORALL_IN_IMAGE] THEN
    GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polyhedron (s0:real^N->bool) /\ convex s0 /\ closed s0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_INTERS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYHEDRON_HALFSPACE_GE];
      MATCH_MP_TAC CONVEX_INTERS THEN
      REWRITE_TAC[FORALL_IN_IMAGE; CONVEX_HALFSPACE_GE];
      MATCH_MP_TAC CLOSED_INTERS THEN
      REWRITE_TAC[FORALL_IN_IMAGE; CLOSED_HALFSPACE_GE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior s0 = {x:real^N | !i. i IN ix ==> &0 < (w:K->real^N) i dot x + k i}`
  ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[INTERIOR_FINITE_INTERS; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    SUBGOAL_THEN
     `!i. i IN ix ==> interior {x:real^N | (w:K->real^N) i dot x >= --(k i)} =
                     {x | w i dot x > --(k i)}`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(w:K->real^N) i = vec 0` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `x0:real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[DOT_LZERO] THEN DISCH_TAC THEN
        SUBGOAL_THEN `{x:real^N | &0 >= --(k:K->real) i} = (:real^N) /\
                      {x:real^N | &0 > --(k:K->real) i} = (:real^N)`
         (fun th -> REWRITE_TAC[th; INTERIOR_UNIV]) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[INTERIOR_HALFSPACE_GE]];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(A INTER interior s0 = {}:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x0:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_INTER THEN ASM_SIMP_TAC[AFFINE_IMP_POLYHEDRON];
      UNDISCH_TAC `bounded {x | x IN A /\
                     !i. i IN ix ==> &0 <= (w:K->real^N) i dot x + k i}` THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN EXPAND_TAC "s0" THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERS; IN_ELIM_THM; FORALL_IN_IMAGE] THEN
      GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC];
    MATCH_MP_TAC AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (A INTER s0) = A INTER interior (s0:real^N->bool)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_CONVEX_INTER_AFFINE THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; CLOSED_INTER; CLOSED_AFFINE] THEN
  EXPAND_TAC "s0" THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_INTERS; IN_ELIM_THM;
              FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN `!i:K. (w:K->real^N) i dot x >= --(k i) <=> &0 <= w i dot x + k i`
   (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  ASM_MESON_TAC[REAL_LE_LT; REAL_LT_REFL]);;

(* A convex polytope of affine dimension n (the dimension of a model space  *)
(* real^M) is a PL n-cell bounded by its relative frontier: transfer the   *)
(* frontier to real^M by an isometry of the direction space (a PL sphere   *)
(* there, being star-shaped), back to real^N, and cone it from a relative  *)
(* interior point.                                                           *)

let MOI_S4A_POLY_CELL = prove
 (`!P:real^N->bool.
     polytope P /\ aff_dim P = &(dimindex(:M))
     ==> pl_cell_with_boundary (dimindex(:M)) P (relative_frontier P)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (P:real^N->bool) /\ compact P /\ bounded P /\ closed P`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_BOUNDED;
                 POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (P:real^N->bool) = &(dimindex(:M))` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN relative_interior P` (X_CHOOSE_TAC `b:real^N`) THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N) IN P` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier (P:real^N->bool) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `P:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `aff_dim {a:real^N} = &(dimindex(:M))` THEN
    REWRITE_TAC[AFF_DIM_SING; INT_OF_NUM_EQ] THEN
    MP_TAC(ISPEC `(:M)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = {x - b | x IN affine hull (P:real^N->bool)}` THEN
  SUBGOAL_THEN `subspace (S:real^N->bool) /\ dim S = dimindex(:M)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC AFFINE_DIFFS_SUBSPACE THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
      ASM_MESON_TAC[HULL_INC];
      MP_TAC(ISPECL [`b:real^N`; `affine hull P:real^N->bool`]
        AFF_DIM_DIM_AFFINE_DIFFS) THEN
      ASM_SIMP_TAC[HULL_INC; AFF_DIM_AFFINE_HULL; INT_OF_NUM_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `(:real^M)`] ISOMETRIES_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^M` (X_CHOOSE_THEN `g:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x:real^N. x IN affine hull P ==> (g:real^M->real^N)(f(x - b)) + b = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) - b IN S` ASSUME_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `{x - b | x IN affine hull (P:real^N->bool)} = S`)] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Q = IMAGE (\x:real^N. (f:real^N->real^M)(x - b)) P` THEN
  SUBGOAL_THEN `P = IMAGE (\y:real^M. (g:real^M->real^N) y + b) Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
    ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (Q:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    SUBGOAL_THEN `IMAGE (\x:real^N. (f:real^N->real^M)(x - b)) P =
                  IMAGE f (IMAGE (\x. --b + x) P)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim (Q:real^M->bool) = &(dimindex(:M)) /\
    relative_frontier (P:real^N->bool) =
    IMAGE (\y:real^M. (g:real^M->real^N) y + b) (relative_frontier Q) /\
    relative_interior P = IMAGE (\y:real^M. g y + b) (relative_interior Q)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y y'. (g:real^M->real^N) y = g y' ==> y = y'` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (\y:real^M. (g:real^M->real^N) y + b) =
                  IMAGE (\x. b + x) o IMAGE g` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM IMAGE_o; o_DEF] THEN
      REWRITE_TAC[VECTOR_ADD_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^M->real^N`; `Q:real^M->bool`]
      RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
    MP_TAC(ISPECL [`g:real^M->real^N`; `Q:real^M->bool`]
      RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE) THEN
    MP_TAC(ISPECL [`g:real^M->real^N`; `Q:real^M->bool`]
      AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(ASSUME_TAC o SYM)) THEN
    UNDISCH_TAC `aff_dim (P:real^N->bool) = &(dimindex(:M))` THEN
    SUBST1_TAC(ASSUME `P = IMAGE (\y:real^M. (g:real^M->real^N) y + b) Q`) THEN
    REWRITE_TAC[ASSUME `IMAGE (\y:real^M. (g:real^M->real^N) y + b) =
                        IMAGE (\x. b + x) o IMAGE g`; o_THM;
                AFF_DIM_TRANSLATION_EQ; RELATIVE_FRONTIER_TRANSLATION;
                RELATIVE_INTERIOR_TRANSLATION] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0:real^M IN relative_interior Q` ASSUME_TAC THENL
   [UNDISCH_TAC `(b:real^N) IN relative_interior P` THEN
    REWRITE_TAC[ASSUME `relative_interior (P:real^N->bool) =
      IMAGE (\y:real^M. (g:real^M->real^N) y + b) (relative_interior Q)`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y0:real^M = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(g:real^M->real^N) y0 = vec 0` ASSUME_TAC THENL
     [UNDISCH_TAC `(b:real^N) = g(y0:real^M) + b` THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `f:real^N->real^M` LINEAR_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(g:real^M->real^N) y0`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere (dimindex(:M) - 1) (relative_frontier (Q:real^M->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_STAR_SHAPED_PL_SPHERE_0 THEN
    ASM_SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER] THEN CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`Q:real^M->bool`; `vec 0:real^M`; `u:real^M`]
        RAY_TO_RELATIVE_FRONTIER) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED; VECTOR_ADD_LID] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `aff_dim (Q:real^M->bool) = &(dimindex(:M))` THEN
        REWRITE_TAC[AFF_DIM_EQ_FULL] THEN SIMP_TAC[IN_UNIV];
        MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!r1 r2. &0 < r1 /\ &0 < r2 /\ r1 <= r2 /\
              r1 % u IN relative_frontier (Q:real^M->bool) /\
              r2 % u IN relative_frontier Q ==> r1 = r2`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`Q:real^M->bool`; `vec 0:real^M`; `r2 % u:real^M`;
                     `r1 % u:real^M`] MOI_CON_RF_SEGMENT) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `r1 / r2` THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                     REAL_MUL_LID] THEN
        REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_ASSOC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < r2` THEN CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL]];
      ASM_MESON_TAC[REAL_LE_TOTAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere (dimindex(:M) - 1) (relative_frontier (P:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_PL_SPHERE_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier (Q:real^M->bool)`;
      `\y:real^M. (g:real^M->real^N) y + b`; `\x:real^N. (f:real^N->real^M)(x - b)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      UNDISCH_TAC `aff_dim (P:real^N->bool) = &(dimindex(:M))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[] THEN ASM_SIMP_TAC[VECTOR_ARITH `(y + b) - b:real^N = y`];
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HULL_INC THEN
        SUBGOAL_THEN `(x:real^N) IN relative_frontier P` MP_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SIMP_TAC[relative_frontier; IN_DIFF; CLOSURE_CLOSED;
                 ASSUME `closed (P:real^N->bool)`];
        ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
        ASM_SIMP_TAC[VECTOR_ARITH `(y + b) - b:real^N = y`; IMAGE_ID];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      ASM_SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dimindex(:M) - 1`; `relative_frontier (P:real^N->bool)`; `b:real^N`]
    MOI_FTA_CONE_CELL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      REWRITE_TAC[ASSUME `(b:real^N) IN relative_interior P`];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `b:real^N`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^N->bool`; `b:real^N`] MOI_CON_CONE_RF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `dimindex(:M) - 1 + 1 = dimindex(:M)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `(:M)` DIMINDEX_GE_1) THEN ARITH_TAC;
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Polytope cells in dimensions 1-3; N, Bd N, the closure of the           *)
(* complement and t1-stars traced on one simplex q of t, in chain form.    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 5. Model polytope cells in dimensions 1, 2, 3.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_POLY_CELL_1 = prove
 (`!P:real^N->bool.
     polytope P /\ aff_dim P = &1 ==> pl_cell_with_boundary 1 P (relative_frontier P)`,
  MP_TAC(INST_TYPE [`:1`,`:M`] MOI_S4A_POLY_CELL) THEN
  REWRITE_TAC[DIMINDEX_1]);;

let MOI_S4A_POLY_CELL_2 = prove
 (`!P:real^N->bool.
     polytope P /\ aff_dim P = &2 ==> pl_cell_with_boundary 2 P (relative_frontier P)`,
  MP_TAC(INST_TYPE [`:2`,`:M`] MOI_S4A_POLY_CELL) THEN
  REWRITE_TAC[DIMINDEX_2]);;

let MOI_S4A_POLY_CELL_3 = prove
 (`!P:real^N->bool.
     polytope P /\ aff_dim P = &3 ==> pl_cell_with_boundary 3 P (relative_frontier P)`,
  MP_TAC(INST_TYPE [`:3`,`:M`] MOI_S4A_POLY_CELL) THEN
  REWRITE_TAC[DIMINDEX_3]);;

(* ------------------------------------------------------------------------- *)
(* 6. The first barycentric subdivision of one simplex q of an lf complex t *)
(* as a subcomplex of that of t; chains of t1 meeting the subdivided graph. *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_C1Q = prove
 (`!(t:(real^N->bool)->bool) q.
     lf_simplicial_complex t /\ q IN t
     ==> FINITE (barycentric_subdivision {f | f face_of q}) /\
         moi_bar_complex {f | f face_of q} /\
         moi_bar_complex (barycentric_subdivision {f | f face_of q}) /\
         UNIONS (barycentric_subdivision {f | f face_of q}) = q /\
         barycentric_subdivision {f | f face_of q} SUBSET barycentric_subdivision t /\
         (!g. moi_bar_chain (barycentric_subdivision {f | f face_of q}) g
              ==> moi_bar_chain (barycentric_subdivision t) g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (q:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `q:real^N->bool`] MOI_FTA_FACE_COMPLEX_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; MOI_BAR_SUBDIVISION_COMPLEX;
               MOI_BAR_UNIONS_SUBDIVISION] THEN
  SUBGOAL_THEN `barycentric_subdivision {f:real^N->bool | f face_of q} SUBSET
                barycentric_subdivision t`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `m:real^N->bool` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `F0:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `{f:real^N->bool | f face_of q}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FM3_LF_FACE];
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `barycentric_subdivision {f:real^N->bool | f face_of q}` THEN
    ASM_REWRITE_TAC[]]);;

(* A chain of t1 with a member in the subdivided graph has a common graph   *)
(* vertex.                                                                   *)

let MOI_S4A_L1_GP = prove
 (`!(t:(real^N->bool)->bool) l g.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) g /\
     ~(g INTER barycentric_subdivision l = {})
     ==> moi_fta_gp l g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `m0 = INTERS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(m0:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[moi_bar_chain; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m0:real^N->bool = {}) /\ ?n. n simplex m0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a extreme_point_of m0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fta_gp] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(a:real^N) IN m0` MP_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(m0:real^N->bool) IN barycentric_subdivision l` THEN SET_TAC[];
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`m0:real^N->bool`; `r:real^N->bool`; `a:real^N`]
      EXTREME_POINT_OF_FACE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ASM_MESON_TAC[]]]);;

(* A point of a t1-chain simplex lying in q lies in the simplex of a        *)
(* nonempty subchain made of t1-simplices inside q.                          *)

let MOI_S4A_RESTRICT = prove
 (`!(t:(real^N->bool)->bool) q g x.
     lf_simplicial_complex t /\ q IN t /\
     moi_bar_chain (barycentric_subdivision t) g /\
     x IN convex hull (IMAGE simplex_barycentre g) /\ x IN q
     ==> ?g'. g' SUBSET g /\ ~(g' = {}) /\
              moi_bar_chain (barycentric_subdivision {f | f face_of q}) g' /\
              x IN convex hull (IMAGE simplex_barycentre g')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_BS_FACTS) THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN barycentric_subdivision {f | f face_of q} /\ x IN s`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(g:(real^N->bool)->bool) INTER {u | u face_of s}` THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
    MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull IMAGE simplex_barycentre
                    ((g:(real^N->bool)->bool) INTER {u | u face_of s})` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[FINITE_INTER];
    ASM SET_TAC[];
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]);;

let MOI_S4A_CHAIN_HULL_IN = prove
 (`!c g:(real^N->bool)->bool.
     moi_bar_complex c /\ moi_bar_chain c g
     ==> convex hull (IMAGE simplex_barycentre g) SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
   `(t:real^N->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[moi_bar_chain]);;

(* The regular neighbourhood, its frontier, the closure of its complement  *)
(* and the closed t1-star of a vertex, inside one simplex q of t.          *)

let MOI_S4A_NBHD_IN = prove
 (`!(t:(real^N->bool)->bool) l q.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ q IN t
     ==> derived_nbhd t l INTER q =
         UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                 moi_bar_chain (barycentric_subdivision {f | f face_of q}) g /\
                 moi_fta_gp l g}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; MOI_FTA_IN_UNIONS_HULLS] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTA_IN_NBHD) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_S4A_L1_GP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`;
                   `g:(real^N->bool)->bool`; `x:real^N`] MOI_S4A_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g':(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FTA_GP_GM_HER];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_GP_IN_NBHD THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`barycentric_subdivision {f:real^N->bool | f face_of q}`;
                     `g:(real^N->bool)->bool`] MOI_S4A_CHAIN_HULL_IN) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

let MOI_S4A_FRONTIER_IN = prove
 (`!(t:(real^N->bool)->bool) l q.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ q IN t
     ==> derived_frontier t l INTER q =
         UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                 moi_bar_chain (barycentric_subdivision {f | f face_of q}) g /\
                 moi_fta_gm l g}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; MOI_FTA_IN_UNIONS_HULLS] THEN
  X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTA_FRONTIER_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_FTA_IN_NBHD) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?g. moi_bar_chain (barycentric_subdivision t) g /\ moi_fta_gm l g /\
          (x:real^N) IN convex hull (IMAGE simplex_barycentre g)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x:real^N) IN subtopology euclidean (UNIONS t) interior_of
                                   derived_nbhd t l)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTA_NOT_GM_INTERIOR THEN
      EXISTS_TAC `g0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4A_L1_GP]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`;
                   `g:(real^N->bool)->bool`; `x:real^N`] MOI_S4A_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g':(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FTA_GP_GM_HER];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_GP_IN_NBHD THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[] THEN UNDISCH_TAC `moi_fta_gm l (g:(real^N->bool)->bool)` THEN
      SIMP_TAC[moi_fta_gm];
      MATCH_MP_TAC MOI_FTA_GM_NOT_INTERIOR THEN
      EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`barycentric_subdivision {f:real^N->bool | f face_of q}`;
                     `g:(real^N->bool)->bool`] MOI_S4A_CHAIN_HULL_IN) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

let MOI_S4A_RCLOS_IN = prove
 (`!(t:(real^N->bool)->bool) l q.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ q IN t
     ==> closure (q DIFF derived_nbhd t l) =
         UNIONS {convex hull (IMAGE simplex_barycentre g) | g |
                 moi_bar_chain (barycentric_subdivision {f | f face_of q}) g /\
                 moi_s4a_gq l g}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c1 = barycentric_subdivision {f:real^N->bool | f face_of q}` THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
      MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; MOI_FTA_IN_UNIONS_HULLS] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?m:real^N->bool. m IN c1 /\ x IN m` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (m:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`n:int`; `m:real^N->bool`; `x:real^N`] MOI_BAR_SIMPLEX_COVERED) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_bar_chain (c1:(real^N->bool)->bool) g` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `{u:real^N->bool | u face_of m}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `m:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `(x:real^N) IN convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `g:(real^N->bool)->bool`]
      MOI_FTA_FACE_CHAIN_MIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?b0:real^N. b0 extreme_point_of INTERS g` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?n. n simplex (INTERS g:real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_CASES_TAC `?a:real^N. a extreme_point_of INTERS g /\ a IN UNIONS l` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^N) IN derived_nbhd t l` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC MOI_FTA_GP_IN_NBHD THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[moi_fta_gp] THEN EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[];
      REWRITE_TAC[moi_s4a_gq] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `b0:real^N` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; MOI_FTA_IN_UNIONS_HULLS] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_s4a_gq l (g:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_s4a_gq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b0:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{b0:real^N} IN c1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `r0:real^N->bool` o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o check (fun th ->
        concl th = `~(g:(real^N->bool)->bool = {})`)) THEN
    MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `r0:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_SING] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `g' = ({b0:real^N}) INSERT g` THEN
  SUBGOAL_THEN `moi_bar_chain (c1:(real^N->bool)->bool) g'` ASSUME_TAC THENL
   [EXPAND_TAC "g'" THEN MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN X_GEN_TAC `r:real^N->bool` THEN
    DISCH_TAC THEN DISJ1_TAC THEN REWRITE_TAC[SING_SUBSET] THEN
    ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  ABBREV_TAC `Qp = convex hull (IMAGE simplex_barycentre (g':(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(x:real^N) IN Qp` ASSUME_TAC THENL
   [EXPAND_TAC "Qp" THEN
    MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HULL_MONO THEN EXPAND_TAC "g'" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior Qp SUBSET q DIFF derived_nbhd t (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`c1:(real^N->bool)->bool`; `g':(real^N->bool)->bool`]
        MOI_S4A_CHAIN_HULL_IN) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `Qp:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
      MOI_FTA_IN_NBHD) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g'':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (g':(real^N->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `g':(real^N->bool)->bool`; `g'':(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_INTER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre
                    ((g':(real^N->bool)->bool) INTER g'')) = Qp`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_FACE_RI THEN EXISTS_TAC `y:real^N` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Qp" THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g':(real^N->bool)->bool) INTER g'' = g'` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_INJ THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `{b0:real^N} IN g''` ASSUME_TAC THENL
     [UNDISCH_TAC `(g':(real^N->bool)->bool) INTER g'' = g'` THEN
      EXPAND_TAC "g'" THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER] o check (fun th ->
        is_neg(concl th) && can (find_term ((=) `g'':(real^N->bool)->bool`)) (concl th))) THEN
    SUBGOAL_THEN `(b0:real^N) IN UNIONS l` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `{b0:real^N} SUBSET e \/ e SUBSET {b0}` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g'':(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    UNDISCH_TAC `(e:real^N->bool) IN barycentric_subdivision l` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `~(e:real^N->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (relative_interior Qp) = (Qp:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Qp" THEN
    SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_interior Qp:real^N->bool`;
                 `q DIFF derived_nbhd t (l:(real^N->bool)->bool)`] SUBSET_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S4A_STAR_IN = prove
 (`!(t:(real^N->bool)->bool) q v.
     lf_simplicial_complex t /\ q IN t /\ {v} IN t /\ v IN q
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER q =
         UNIONS {m | m IN barycentric_subdivision {f | f face_of q} /\ v IN m}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  UNDISCH_TAC `(s:real^N->bool) IN barycentric_subdivision t` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `F0:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_VERTEX_IN_HULL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `F0:(real^N->bool)->bool`;
                 `q:real^N->bool`; `x:real^N`] MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{v:real^N} face_of q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{v:real^N}`; `q:real^N->bool`]
      MOI_FM3_LF_INTER) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{v:real^N} INTER q = {v}` (fun th -> SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                (F0 INTER {u:real^N->bool | u face_of q}))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `F0 INTER {u:real^N->bool | u face_of q}` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain t (F0:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; FINITE_INTER];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Barycentric boxes (the polytopes of the flat picture), their            *)
(* affine dimensions, the pull-back of polytope cells, fixed faces, sums. *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 7. Barycentric boxes: the polytopes of the flat picture.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_RF2 = prove
 (`!(A:real^N->bool) (ix:K->bool) (f:K->real^N->real) x0.
     affine A /\ FINITE ix /\ (!i. i IN ix ==> ?w k. !x. f i x = w dot x + k) /\
     x0 IN A /\ (!i. i IN ix ==> &0 < f i x0) /\
     bounded {x | x IN A /\ !i. i IN ix ==> &0 <= f i x}
     ==> polytope {x | x IN A /\ !i. i IN ix ==> &0 <= f i x} /\
         affine hull {x | x IN A /\ !i. i IN ix ==> &0 <= f i x} = A /\
         relative_frontier {x | x IN A /\ !i. i IN ix ==> &0 <= f i x} =
         {x | x IN A /\ (!i. i IN ix ==> &0 <= f i x) /\
              ?i. i IN ix /\ f i x = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:K->real^N` (X_CHOOSE_TAC `Kf:K->real`)) THEN
  SUBGOAL_THEN `!i x. i IN ix ==> (f:K->real^N->real) i x = W i dot x + Kf i`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN A /\ !i. i IN ix ==> &0 <= (f:K->real^N->real) i x} =
    {x | x IN A /\ !i. i IN ix ==> &0 <= W i dot x + Kf i}`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN A /\ (!i. i IN ix ==> &0 <= (f:K->real^N->real) i x) /\
         ?i. i IN ix /\ f i x = &0} =
    {x | x IN A /\ (!i. i IN ix ==> &0 <= W i dot x + Kf i) /\
         ?i. i IN ix /\ W i dot x + Kf i = &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_RF THEN EXISTS_TAC `x0:real^N` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The box of the flat picture with the coordinates in U0 fixed at 2/5. *)

let MOI_S4A_BOX = prove
 (`!(V:real^N->bool) U0 x0.
     ~affine_dependent V /\ U0 SUBSET V /\ x0 IN affine hull V /\
     (!a. a IN U0 ==> moi_s4a_bc V a x0 = &2 / &5) /\
     (!a. a IN V /\ ~(a IN U0)
          ==> &0 < moi_s4a_bc V a x0 /\ moi_s4a_bc V a x0 < &2 / &5)
     ==> polytope {x | x IN convex hull V /\
                       (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
                       (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)} /\
         affine hull {x | x IN convex hull V /\
                          (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
                          (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)} =
         {x | x IN affine hull V /\ !a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5} /\
         relative_frontier {x | x IN convex hull V /\
                                (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
                                (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)} =
         {x | x IN convex hull V /\
              (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
              (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ ~(a IN U0) /\
                  (moi_s4a_bc V a x = &0 \/ moi_s4a_bc V a x = &2 / &5)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `fb = \(i:real^N#bool) (x:real^N).
                     if SND i then moi_s4a_bc V (FST i) x
                     else &2 / &5 - moi_s4a_bc V (FST i) x` THEN
  ABBREV_TAC `A = {x:real^N | x IN affine hull V /\
                              !a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5}` THEN
  SUBGOAL_THEN
   `!x:real^N.
      (x IN convex hull V /\
       (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
       (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)) <=>
      x IN A /\ !i. i IN (V DIFF U0) CROSS (:bool) ==> &0 <= fb i x`
  (LABEL_TAC "box") THENL
   [X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BC_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXPAND_TAC ["A"; "fb"] THEN
    REWRITE_TAC[IN_ELIM_THM; FORALL_IN_CROSS; FORALL_BOOL_THM; IN_UNIV; IN_DIFF] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_LE];
      CONJ_TAC THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(a:real^N) IN U0` THEN ASM_SIMP_TAC[] THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV;
        CONV_TAC REAL_RAT_REDUCE_CONV;
        FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `&2 / &5`)) (concl th) &&
          can (find_term ((=) `(&0)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^N | x IN convex hull V /\
                (!a. a IN U0 ==> moi_s4a_bc V a x = &2 / &5) /\
                (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5)} =
    {x | x IN A /\ !i. i IN (V DIFF U0) CROSS (:bool) ==> &0 <= fb i x}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN USE_THEN "box" (fun th ->
      REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N->bool`; `(V DIFF (U0:real^N->bool)) CROSS (:bool)`;
                 `fb:real^N#bool->real^N->real`; `x0:real^N`] MOI_S4A_RF2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[affine; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[VECTOR_ARITH
          `u % (x:real^N) + (&1 - u) % y = (&1 - (&1 - u)) % x + (&1 - u) % y`] THEN
        ASM_SIMP_TAC[MOI_S4A_BC_AFFINE] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[FINITE_CROSS; FINITE_DIFF; FINITE_BOOL];
      REWRITE_TAC[FORALL_IN_CROSS; FORALL_BOOL_THM; IN_UNIV; IN_DIFF] THEN
      EXPAND_TAC "fb" THEN REWRITE_TAC[] THEN
      REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
      X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`] MOI_S4A_BC) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`w:real^N`; `k:real`] THEN REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`--w:real^N`; `&2 / &5 - k`] THEN
        REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC];
      EXPAND_TAC "A" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[FORALL_IN_CROSS; FORALL_BOOL_THM; IN_UNIV; IN_DIFF] THEN
      EXPAND_TAC "fb" THEN REWRITE_TAC[] THEN
      REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
      X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(&0)`)) (concl th) &&
        can (find_term ((=) `x0:real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `convex hull V:real^N->bool` THEN
      ASM_SIMP_TAC[BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      USE_THEN "box" (fun th -> REWRITE_TAC[GSYM th]) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  USE_THEN "box" (MP_TAC o SPEC `x:real^N`) THEN
  REWRITE_TAC[EXISTS_IN_CROSS; EXISTS_BOOL_THM; IN_UNIV; IN_DIFF] THEN
  EXPAND_TAC "fb" THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 / &5 - b = &0 <=> b = &2 / &5`] THEN MESON_TAC[]);;

(* Affine dimensions of the affine sets of the boxes.                        *)

let MOI_S4A_AFFDIM_HYP = prove
 (`!(V:real^N->bool) (S:real^N->bool) v.
     ~affine_dependent V /\ v IN V /\ affine S /\
     (?p. p IN S /\ moi_s4a_bc V v p = &2 / &5) /\
     (?q. q IN S /\ ~(moi_s4a_bc V v q = &2 / &5))
     ==> aff_dim {x | x IN S /\ moi_s4a_bc V v x = &2 / &5} = aff_dim S - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `v:real^N`] MOI_S4A_BC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_TAC `k:real`) o CONJUNCT1) THEN
  SUBGOAL_THEN `{x | x IN S /\ moi_s4a_bc V v x = &2 / &5} =
                S INTER {x:real^N | w dot x = &2 / &5 - k}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    REWRITE_TAC[REAL_ARITH `a + b = c <=> a = c - b`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `S INTER {v:real^N | w dot v = &2 / &5 - k} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    UNDISCH_TAC `moi_s4a_bc V v (p:real^N) = &2 / &5` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `S SUBSET {v:real^N | w dot v = &2 / &5 - k}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N`) THEN
    UNDISCH_TAC `~(moi_s4a_bc V v (q:real^N) = &2 / &5)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

let MOI_S4A_AFFINE_HULL_COMB = prove
 (`!(V:real^N->bool) x y u.
     x IN affine hull V /\ y IN affine hull V
     ==> (&1 - u) % x + u % y IN affine hull V`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S4A_AFFDIM_BOX = prove
 (`!(V:real^N->bool) u w.
     ~affine_dependent V /\ u IN V /\ w IN V /\ ~(u = w)
     ==> aff_dim {x | x IN affine hull V /\
                      !a. a IN {} ==> moi_s4a_bc V a x = &2 / &5} =
         &(CARD V) - &1 /\
         aff_dim {x | x IN affine hull V /\
                      !a. a IN {u} ==> moi_s4a_bc V a x = &2 / &5} =
         &(CARD V) - &2 /\
         (3 <= CARD V
          ==> aff_dim {x | x IN affine hull V /\
                           !a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5} =
              &(CARD V) - &3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^N. a IN V /\ b IN V
                 ==> moi_s4a_bc V a b = if b = a then &1 else &0`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S4A_BC]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (affine hull V:real^N->bool) = &(CARD V) - &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[SET_RULE `{x:real^N | x IN s} = s`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `aff_dim {x | x IN affine hull V /\ moi_s4a_bc V u x = &2 / &5} =
    &(CARD (V:real^N->bool)) - &2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `affine hull V:real^N->bool`; `u:real^N`]
      MOI_S4A_AFFDIM_HYP) THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `(&1 - &2 / &5) % w + &2 / &5 % u:real^N` THEN
        ASM_SIMP_TAC[MOI_S4A_AFFINE_HULL_COMB; HULL_INC; MOI_S4A_BC_AFFINE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        EXISTS_TAC `u:real^N` THEN ASM_SIMP_TAC[HULL_INC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^N. c IN V /\ ~(c = u) /\ ~(c = w)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~((V:real^N->bool) SUBSET {u,w}) ==>
                           ?c. c IN V /\ ~(c = u) /\ ~(c = w)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w}`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN affine hull V /\ moi_s4a_bc V u x = &2 / &5 /\
         moi_s4a_bc V w x = &2 / &5} =
    {x | x IN {x | x IN affine hull V /\ moi_s4a_bc V u x = &2 / &5} /\
         moi_s4a_bc V (w:real^N) x = &2 / &5}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`;
                 `{x | x IN affine hull (V:real^N->bool) /\
                       moi_s4a_bc V u x = &2 / &5}`;
                 `w:real^N`] MOI_S4A_AFFDIM_HYP) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[affine; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `s:real`; `t:real`] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `t = &1 - s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[VECTOR_ARITH
          `s % (x:real^N) + (&1 - s) % y = (&1 - (&1 - s)) % x + (&1 - s) % y`] THEN
        ASM_SIMP_TAC[MOI_S4A_BC_AFFINE] THEN REAL_ARITH_TAC];
      EXISTS_TAC `(&1 - &1 / &5) % (inv(&2) % u + inv(&2) % w) +
                  &1 / &5 % c:real^N` THEN
      SUBGOAL_THEN `inv(&2) % u + inv(&2) % w:real^N =
                    (&1 - inv(&2)) % u + inv(&2) % w` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_S4A_AFFINE_HULL_COMB; HULL_INC; MOI_S4A_BC_AFFINE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      EXISTS_TAC `(&1 - &2 / &5) % c + &2 / &5 % u:real^N` THEN
      ASM_SIMP_TAC[MOI_S4A_AFFINE_HULL_COMB; HULL_INC; MOI_S4A_BC_AFFINE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* Pulling a polytope cell back along the flat retriangulation.             *)

let MOI_S4A_PULLBACK = prove
 (`!(V:real^N->bool) h k C B S n.
     pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
     C SUBSET convex hull V /\ B SUBSET convex hull V /\
     IMAGE h C = S /\ polytope S /\
     pl_cell_with_boundary n S (relative_frontier S) /\
     relative_frontier S = IMAGE h B
     ==> pl_cell_with_boundary n C B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN convex hull V ==> (k:real^N->real^N)((h:real^N->real^N) x) = x`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (convex hull V) = convex hull V`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET convex hull (V:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^N) C = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull V:real^N->bool`; `convex hull V:real^N->bool`;
                 `k:real^N->real^N`; `h:real^N->real^N`; `S:real^N->bool`]
    MOI_FMB_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:real^N->bool`; `relative_frontier S:real^N->bool`;
                 `k:real^N->real^N`; `h:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) S = C /\
                IMAGE k (IMAGE (h:real^N->real^N) B) = B`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^N) C = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN ASM SET_TAC[]]);;

(* The flat retriangulation fixes every face of the simplex.                 *)

let MOI_S4A_FACE_FIXED = prove
 (`!(V:real^N->bool) (h:real^N->real^N) E.
     ~affine_dependent V /\ E SUBSET V /\
     (!s. s IN barycentric_subdivision {f | f face_of convex hull V}
          ==> IMAGE h s = s)
     ==> IMAGE h (convex hull E) = convex hull E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (E:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_C1_FACTS) THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV)
    [SYM(ASSUME `UNIONS (barycentric_subdivision {f | f face_of convex hull E}) =
                 convex hull (E:real^N->bool)`)] THEN
  REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN X_GEN_TAC `m:real^N->bool` THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision {f | f face_of convex hull E}` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `ch:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
  EXISTS_TAC `{f:real^N->bool | f face_of convex hull E}` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `convex hull E:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Sums of coordinates.                                                       *)

let MOI_S4A_BC_SUMS = prove
 (`!(V:real^N->bool) Z x.
     ~affine_dependent V /\ x IN convex hull V /\ Z SUBSET V
     ==> sum Z (\a. moi_s4a_bc V a x) + sum (V DIFF Z) (\a. moi_s4a_bc V a x) = &1 /\
         &0 <= sum Z (\a. moi_s4a_bc V a x) /\
         &0 <= sum (V DIFF Z) (\a. moi_s4a_bc V a x) /\
         (!c. (!a. a IN V DIFF Z ==> moi_s4a_bc V a x <= c)
              ==> sum (V DIFF Z) (\a. moi_s4a_bc V a x) <= &(CARD(V DIFF Z)) * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN V ==> &0 <= moi_s4a_bc V a x` ASSUME_TAC THENL
   [MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BC_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N` o
      REWRITE_RULE[EXTENSION]) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `x:real^N`] MOI_S4A_BC_HULL_EXPAND) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC SUM_POS_LE THEN ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_BOUND THEN
    ASM_SIMP_TAC[FINITE_DIFF]]);;

(* ========================================================================= *)
(* The tube - simplices of kk, graph vertices, subsimplices,               *)
(* splitting disks of edges, and the flat picture of a simplex of kk.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 8. The tube: simplices of kk, the graph t1-vertices of a simplex of kk,  *)
(* subsimplices, splitting disks of edges.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_TUBE = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> lf_simplicial_complex tt /\ simplicial_subcomplex kk tt /\
         simplicial_subcomplex (skeleton 1 kk) tt /\ moi_bar_complex tt /\
         (!s. s IN kk ==> s IN tt) /\
         (!s f. s IN kk /\ f face_of s ==> f IN kk)`,
  REWRITE_TAC[moi_s34_tube; graph_in_complex] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
  ASM_MESON_TAC[simplicial_subcomplex; SUBSET]);;

let MOI_S4A_AFF_DIM_HULL = prove
 (`!E:real^N->bool. ~affine_dependent E ==> aff_dim (convex hull E) = &(CARD E) - &1`,
  SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT]);;

let MOI_S4A_KK_SIMPLEX = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ q IN kk
     ==> ?V. ~affine_dependent V /\ q = convex hull V /\
             aff_dim q = &(CARD V) - &1 /\ FINITE V`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `?n. n simplex (q:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:real^N->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S4A_AFF_DIM_HULL; AFFINE_INDEPENDENT_IMP_FINITE]);;

let MOI_S4A_HP = prove
 (`!(tt:(real^N->bool)->bool) kk V.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V
     ==> !E. E SUBSET V /\ ~(E = {})
             ==> (simplex_barycentre (convex hull E) IN UNIONS (skeleton 1 kk) <=>
                  CARD E <= 2)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `~affine_dependent (E:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (E:real^N->bool) IN kk` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of")) (concl th))) THEN
    EXISTS_TAC `convex hull V:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 kk:(real^N->bool)->bool`;
                   `convex hull E:real^N->bool`] MOI_FTA_BARY_IN_SUBCOMPLEX) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_SIMP_TAC[MOI_S4A_AFF_DIM_HULL] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int <= &1 <=> a <= &2`; INT_OF_NUM_LE] THEN
    SIMP_TAC[];
    DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull E:real^N->bool` THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_SIMP_TAC[MOI_S4A_AFF_DIM_HULL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_ARITH `a - &1:int <= &1 <=> a <= &2`; INT_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
      EXISTS_TAC `&(CARD(E:real^N->bool)) - &1:int` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
      REWRITE_TAC[simplex] THEN EXISTS_TAC `E:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* The n-simplices of kk inside a simplex convex hull V of kk.             *)

let MOI_S4A_SIMP_IN = prove
 (`!(tt:(real^N->bool)->bool) kk V s n.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V
     ==> (s IN moi_s34_simp kk (&n) /\ s SUBSET convex hull V <=>
          ?E. E SUBSET V /\ CARD E = n + 1 /\ s = convex hull E)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`;
                   `convex hull V:real^N->bool`] MOI_FM3_LF_INTER) THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^N->bool) SUBSET t ==> s INTER t = s`] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim (s:real^N->bool) = &n` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~affine_dependent (E:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_AFF_DIM_HULL] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int = b <=> a = b + &1`; INT_OF_NUM_ADD;
                INT_OF_NUM_EQ];
    DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~affine_dependent (E:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of"))
          (concl th))) THEN
      EXISTS_TAC `convex hull V:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_S4A_AFF_DIM_HULL] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
      MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]]]);;

(* Small combinatorics of vertex sets.                                       *)

let MOI_S4A_CARD_DELETE1 = prove
 (`!(V:real^N->bool) E.
     FINITE V /\ E SUBSET V /\ CARD E + 1 = CARD V
     ==> ?a. a IN V /\ E = V DELETE a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(V DIFF E:real^N->bool) HAS_SIZE 1` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF] THEN ASM_ARITH_TAC;
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[]]);;

let MOI_S4A_CARD_PAIR = prove
 (`!(E:real^N->bool) v.
     FINITE E /\ CARD E = 2 /\ v IN E ==> ?a. ~(a = v) /\ E = {v,a}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(E DELETE (v:real^N)) HAS_SIZE 1` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC;
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[]]);;

(* Vertices of kk inside a simplex of kk are among its vertices; splitting  *)
(* disks of edges.                                                           *)

let MOI_S4A_VTX = prove
 (`!(tt:(real^N->bool)->bool) kk V v.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     {v} IN kk /\ v IN convex hull V
     ==> v IN V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `{v:real^N}`; `0`] MOI_S4A_SIMP_IN) THEN
  ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `E = {v:real^N}` (fun th -> ASM_MESON_TAC[th; SUBSET; IN_SING]) THEN
  SUBGOAL_THEN `(E:real^N->bool) SUBSET {v}` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REWRITE_TAC[HULL_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(E:real^N->bool = {})` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(E:real^N->bool) = 0 + 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    SET_TAC[]]);;

let MOI_S4A_SD_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk u w.
     moi_s34_tube tt kk /\ ~(u = w) /\ convex hull {u,w} IN kk
     ==> moi_s34_sd tt kk (convex hull {u,w}) =
         moi_s34_vb tt kk u INTER moi_s34_vb tt kk w`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `~affine_dependent {u:real^N,w}` ASSUME_TAC THENL
   [REWRITE_TAC[AFFINE_INDEPENDENT_2]; ALL_TAC] THEN
  SUBGOAL_THEN `{v | v IN convex hull {u,w} /\ {v} IN kk} = {u:real^N,w}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `{u:real^N,w}`; `v:real^N`] MOI_S4A_VTX) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of"))
        (concl th))) THEN
    EXISTS_TAC `convex hull {u:real^N,w}` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN
    MESON_TAC[SET_RULE `{u:real^N} SUBSET {u,w} /\ {w} SUBSET {u,w}`;
              CONVEX_HULL_SING];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_sd] THEN
  SUBGOAL_THEN
   `{moi_s34_vb tt kk v | v | v IN convex hull {u,w} /\ {v} IN kk} =
    {moi_s34_vb tt kk (v:real^N) | v IN {u,w}}`
  SUBST1_TAC THENL
   [UNDISCH_TAC `{v | v IN convex hull {u,w} /\ {v} IN kk} = {u:real^N,w}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; INTERS_INSERT; INTERS_0;
                INTER_UNIV]]);;

let MOI_S4A_VTX_KK = prove
 (`!(tt:(real^N->bool)->bool) kk V v.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\ v IN V
     ==> {v} IN kk /\ {v} IN tt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `{v:real^N} IN kk` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of"))
      (concl th))) THEN
  EXISTS_TAC `convex hull V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

(* The flat picture of a simplex convex hull V of kk.                        *)

let MOI_S4A_FLAT_KK = prove
 (`!(tt:(real^N->bool)->bool) kk V.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V
     ==> ?h k.
           pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
           (!x. x IN convex hull V ==> k(h x) = x) /\
           (!E. E SUBSET V ==> IMAGE h (convex hull E) = convex hull E) /\
           (!v. v IN V
                ==> moi_s34_vb tt kk v INTER convex hull V =
                    (moi_s34_nb tt kk INTER convex hull V) INTER
                    {x | x IN convex hull V /\
                         !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x} /\
                    IMAGE h {x | x IN convex hull V /\
                                 !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x} =
                    {x | x IN convex hull V /\
                         !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x}) /\
           moi_s34_bd tt kk SUBSET moi_s34_nb tt kk /\
           IMAGE h (moi_s34_nb tt kk INTER convex hull V) =
           {x | x IN convex hull V /\ ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a x} /\
           IMAGE h (moi_s34_bd tt kk INTER convex hull V) =
           {x | x IN convex hull V /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
                ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5} /\
           IMAGE h (closure (convex hull V DIFF moi_s34_nb tt kk)) =
           {x | x IN convex hull V /\ !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_HP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `skeleton 1 kk:(real^N->bool)->bool`]
    MOI_S4A_FLAT_HOMEO) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `skeleton 1 kk:(real^N->bool)->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4A_FLAT_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull V IN (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s34_nb; moi_s34_bd] THEN
  ASM_SIMP_TAC[MOI_S4A_NBHD_IN; MOI_S4A_FRONTIER_IN; MOI_S4A_RCLOS_IN] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_FACE_FIXED THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `V:real^N->bool`; `v:real^N`] MOI_S4A_VTX_KK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN convex hull V` ASSUME_TAC THENL
     [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `v:real^N`] MOI_S4A_BC_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s34_vb; derived_dual_cell] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `convex hull V:real^N->bool`;
                     `v:real^N`] MOI_S4A_STAR_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 kk:(real^N->bool)->bool`;
                     `convex hull V:real^N->bool`] MOI_S4A_NBHD_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
      REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET] THEN
    ASM_MESON_TAC[MOI_FTA_FRONTIER_IFF]]);;

(* ========================================================================= *)
(* Coordinate bounds, enumerations of faces, the flat traces, and          *)
(* the clauses of moi_s34_scell_facts.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 9. Coordinate bounds and the clauses of moi_s34_scell_facts.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4A_BC_SUM_LE = prove
 (`!(V:real^N->bool) Z x c.
     ~affine_dependent V /\ x IN convex hull V /\ Z SUBSET V /\
     (!b. b IN V DIFF Z ==> moi_s4a_bc V b x <= c)
     ==> &1 <= sum Z (\a. moi_s4a_bc V a x) + &(CARD(V DIFF Z)) * c /\
         sum Z (\a. moi_s4a_bc V a x) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `Z:real^N->bool`; `x:real^N`] MOI_S4A_BC_SUMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `c:real`)))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S4A_BARY_POINT = prove
 (`!(V:real^N->bool).
     ~affine_dependent V /\ ~(V = {})
     ==> simplex_barycentre (convex hull V) IN convex hull V /\
         !a. a IN V ==> moi_s4a_bc V a (simplex_barycentre (convex hull V)) =
                        inv(&(CARD V))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
    EXISTS_TAC `&(CARD(V:real^N->bool)) - &1:int` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN REWRITE_TAC[simplex] THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`V:real^N->bool`; `V:real^N->bool`; `a:real^N`] MOI_S4A_BC_BARY) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* Clause 2: the face disk of a 2-simplex.                                   *)

let MOI_S4A_CLAUSE2 = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> pl_cell_with_boundary 2 (closure (s DIFF moi_s34_nb tt kk))
                                 (s INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_AFF_DIM_HULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull V:real^N->bool) = &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(V:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(V:real^N->bool) = 3` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BARY_POINT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x0 = simplex_barycentre (convex hull V:real^N->bool)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{}:real^N->bool`; `x0:real^N`] MOI_S4A_BOX) THEN
  ASM_SIMP_TAC[EMPTY_SUBSET; NOT_IN_EMPTY] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{x:real^N | x IN s /\ P x} = {x | x IN s /\ P x}`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `S = {x | x IN convex hull V /\
                       !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5}` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 S (relative_frontier (S:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `{x:real^N | x IN s} = s`; AFF_DIM_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                        `S:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[SUBSET_DIFF] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT];
    REWRITE_TAC[INTER_SUBSET];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THENL
       [MP_TAC(ISPECL [`V:real^N->bool`; `{a:real^N}`; `x:real^N`; `&2 / &5`]
          MOI_S4A_BC_SUM_LE) THEN
        ASM_SIMP_TAC[SING_SUBSET; IN_DIFF; SUM_SING] THEN
        ASM_SIMP_TAC[CARD_DIFF; FINITE_SING; SING_SUBSET; CARD_SING] THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN
      ASM_REWRITE_TAC[]]]);;

(* Interior points of the boxes.                                              *)

let MOI_S4A_SUBBARY = prove
 (`!(V:real^N->bool) E.
     ~affine_dependent V /\ E SUBSET V /\ ~(E = {})
     ==> simplex_barycentre (convex hull E) IN convex hull V /\
         simplex_barycentre (convex hull E) IN affine hull V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (convex hull E) IN convex hull (V:real^N->bool)`
   (fun th -> ASM_MESON_TAC[th; CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]) THEN
  MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull E:real^N->bool` THEN
  ASM_SIMP_TAC[HULL_MONO] THEN
  MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
  EXISTS_TAC `&(CARD(E:real^N->bool)) - &1:int` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `E:real^N->bool` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; INT_ARITH_TAC]);;

let MOI_S4A_X0 = prove
 (`!(V:real^N->bool) U0.
     ~affine_dependent V /\ U0 SUBSET V /\ ~(U0 = {}) /\ ~(V DIFF U0 = {})
     ==> ?x0. x0 IN affine hull V /\
              (!a. a IN U0 ==> moi_s4a_bc V a x0 = &2 / &5) /\
              (!a. a IN V DIFF U0
                   ==> moi_s4a_bc V a x0 =
                       (&1 - &2 / &5 * &(CARD U0)) / &(CARD(V DIFF U0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (U0:real^N->bool) /\ ~(CARD U0 = 0) /\
                FINITE (V DIFF U0:real^N->bool) /\ ~(CARD (V DIFF U0) = 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF; CARD_EQ_0]; ALL_TAC] THEN
  ABBREV_TAC `t = &2 / &5 * &(CARD(U0:real^N->bool))` THEN
  EXISTS_TAC `(&1 - t) % simplex_barycentre (convex hull (V DIFF U0)) +
              t % simplex_barycentre (convex hull (U0:real^N->bool))` THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `V DIFF U0:real^N->bool`] MOI_S4A_SUBBARY) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `U0:real^N->bool`] MOI_S4A_SUBBARY) THEN
  ASM_REWRITE_TAC[SUBSET_DIFF] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S4A_AFFINE_HULL_COMB THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(a:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_BC_AFFINE; MOI_S4A_BC_BARY; SUBSET_DIFF; IN_DIFF] THEN
    EXPAND_TAC "t" THEN UNDISCH_TAC `~(CARD (U0:real^N->bool) = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    SUBGOAL_THEN `(a:real^N) IN V /\ ~(a IN U0)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_BC_AFFINE; MOI_S4A_BC_BARY; SUBSET_DIFF; IN_DIFF] THEN
    UNDISCH_TAC `~(CARD (V DIFF U0:real^N->bool) = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD]);;

let MOI_S4A_IMAGE_UNIONS_GSPEC = prove
 (`!(h:real^N->real^N) (f:A->real^N->bool) P.
     IMAGE h (UNIONS {f a | a | P a}) = UNIONS {IMAGE h (f a) | a | P a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* Facets and edges of a simplex of kk.                                       *)

let MOI_S4A_FACET_COORD = prove
 (`!(V:real^N->bool) a.
     ~affine_dependent V /\ a IN V
     ==> convex hull (V DELETE a) = {x | x IN convex hull V /\ moi_s4a_bc V a x = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `V DELETE (a:real^N)`] MOI_S4A_BC_SUBHULL) THEN
  ASM_REWRITE_TAC[DELETE_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `b:real^N = a` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[]]);;

let MOI_S4A_VERT_IN_FACET = prove
 (`!(V:real^N->bool) a v.
     ~affine_dependent V /\ a IN V /\ v IN V
     ==> (v IN convex hull (V DELETE a) <=> ~(v = a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `V DELETE (a:real^N)`; `v:real^N`]
      MOI_S4A_BC_VERTEX_IN) THEN
    ASM_REWRITE_TAC[DELETE_SUBSET; IN_DELETE] THEN MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_DELETE]]);;

let MOI_S4A_EDGES_AT = prove
 (`!(tt:(real^N->bool)->bool) kk V v g.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\ v IN V
     ==> (g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET convex hull V <=>
          ?a. a IN V /\ ~(a = v) /\ g = convex hull {v,a})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `g:real^N->bool`; `1`] MOI_S4A_SIMP_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[TAUT `(a /\ b /\ c <=> d) <=>
                                          (b /\ (a /\ c) <=> d)`; th]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^N) IN E` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4A_BC_VERTEX_IN THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`E:real^N->bool`; `v:real^N`] MOI_S4A_CARD_PAIR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{v:real^N,a}` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                   NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV]]);;

let MOI_S4A_FACETS = prove
 (`!(tt:(real^N->bool)->bool) kk V s.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\ CARD V = 4
     ==> (s IN moi_s34_simp kk (&2) /\ s SUBSET convex hull V <=>
          ?a. a IN V /\ s = convex hull (V DELETE a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `s:real^N->bool`; `2`] MOI_S4A_SIMP_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `E:real^N->bool`] MOI_S4A_CARD_DELETE1) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `V DELETE (a:real^N)` THEN ASM_SIMP_TAC[DELETE_SUBSET; CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let MOI_S4A_FACETS_AT = prove
 (`!(tt:(real^N->bool)->bool) kk V s v.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     CARD V = 4 /\ v IN V
     ==> (s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET convex hull V <=>
          ?a. a IN V /\ ~(a = v) /\ s = convex hull (V DELETE a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `s:real^N->bool`] MOI_S4A_FACETS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?a:real^N. a IN V /\ s = convex hull (V DELETE a)`
     (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S4A_VERT_IN_FACET];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[MOI_S4A_VERT_IN_FACET] THEN ASM_MESON_TAC[]]);;

let MOI_S4A_FACETS_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk V s u w.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     CARD V = 4 /\ u IN V /\ w IN V
     ==> (s IN moi_s34_simp kk (&2) /\ convex hull {u,w} SUBSET s /\
          s SUBSET convex hull V <=>
          ?a. a IN V /\ ~(a = u) /\ ~(a = w) /\ s = convex hull (V DELETE a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `s:real^N->bool`] MOI_S4A_FACETS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?a:real^N. a IN V /\ s = convex hull (V DELETE a)`
     (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N) IN convex hull (V DELETE a) /\ w IN convex hull (V DELETE a)`
    MP_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `convex hull {u:real^N,w}` THEN
      (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ASM_MESON_TAC[]]);
      ASM_SIMP_TAC[MOI_S4A_VERT_IN_FACET] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
      ASM_MESON_TAC[]]]);;

(* The flat picture with the traces of the vertex balls and of the          *)
(* splitting disks on Bd N inside a simplex of kk.                          *)

let MOI_S4A_FLAT_KK2 = prove
 (`!(tt:(real^N->bool)->bool) kk V.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V
     ==> ?h k.
           pl_homeomorphism (convex hull V,convex hull V) (h,k) /\
           (!x. x IN convex hull V ==> k(h x) = x) /\
           (!E. E SUBSET V ==> IMAGE h (convex hull E) = convex hull E) /\
           IMAGE h (closure (convex hull V DIFF moi_s34_nb tt kk)) =
           {x | x IN convex hull V /\ (!a. a IN {} ==> moi_s4a_bc V a x = &2 / &5) /\
                !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5} /\
           IMAGE h (convex hull V INTER moi_s34_bd tt kk) =
           {x | x IN convex hull V /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
                ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5} /\
           (!v. v IN V
                ==> IMAGE h (convex hull V INTER moi_s34_vb tt kk v INTER
                             moi_s34_bd tt kk) =
                    {x | x IN convex hull V /\
                         (!a. a IN {v} ==> moi_s4a_bc V a x = &2 / &5) /\
                         !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5}) /\
           (!u w. u IN V /\ w IN V /\ ~(u = w)
                  ==> convex hull V INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
                      moi_s34_bd tt kk =
                      (convex hull V INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)
                      INTER moi_s34_vb tt kk w /\
                      IMAGE h (convex hull V INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
                               moi_s34_bd tt kk) =
                      {x | x IN convex hull V /\
                           (!a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5) /\
                           !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5})`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vb")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bdim") (LABEL_TAC "rcim")))))))))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  SUBGOAL_THEN
   `!A B:real^N->bool. A SUBSET convex hull V /\ B SUBSET convex hull V
                       ==> IMAGE (h:real^N->real^N) (A INTER B) = IMAGE h A INTER IMAGE h B`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
    EXISTS_TAC `k:real^N->real^N` THEN
    EXISTS_TAC `convex hull V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (convex hull V INTER moi_s34_bd tt kk) =
    {x | x IN convex hull V /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
         ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5}`
  (LABEL_TAC "G") THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN USE_THEN "bdim" ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!v:real^N. v IN V
      ==> convex hull V INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk =
          (convex hull V INTER moi_s34_bd tt kk) INTER
          {x | x IN convex hull V /\
               !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x}`
  (LABEL_TAC "tr") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vb" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `moi_s34_bd tt kk SUBSET moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. v IN V
      ==> IMAGE h {x | x IN convex hull V /\
                       !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x} =
          {x | x IN convex hull V /\
               !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V v x}`
  (LABEL_TAC "sq") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vb" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "tr" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "inj" (fun th -> W(MP_TAC o PART_MATCH (lhs o rand) th o lhs o snd)) THEN
    ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "G" SUBST1_TAC THEN
    USE_THEN "sq" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `w:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {u:real^N,w} IN kk` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of"))
        (concl th))) THEN
    EXISTS_TAC `convex hull V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{u:real^N,w}` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `u:real^N`; `w:real^N`] MOI_S4A_SD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPEC `u:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPEC `w:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `convex hull V INTER (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) INTER
    moi_s34_bd tt kk =
    (convex hull V INTER moi_s34_bd tt kk) INTER
    ({x | x IN convex hull V /\
          !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V u x} INTER
     {x | x IN convex hull V /\
          !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V (w:real^N) x})`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`convex hull V INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk =
       (convex hull V INTER moi_s34_bd tt kk) INTER
       {x | x IN convex hull V /\
            !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V (u:real^N) x}`;
      `convex hull V INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk =
       (convex hull V INTER moi_s34_bd tt kk) INTER
       {x | x IN convex hull V /\
            !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V (w:real^N) x}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "inj" (fun th -> W(MP_TAC o PART_MATCH (lhs o rand) th o lhs o snd)) THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "inj" (fun th -> W(MP_TAC o PART_MATCH (lhs o rand) th o
    rand o lhs o snd)) THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "G" SUBST1_TAC THEN
  USE_THEN "sq" (MP_TAC o SPEC `u:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "sq" (MP_TAC o SPEC `w:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]]);;


(* Re-indexing families of sets.                                              *)

let MOI_S4A_GSPEC_EQ = prove
 (`!(P:A->bool) (f:A->real^N->bool) g.
     (!a. P a ==> f a = g a) ==> {f a | a | P a} = {g a | a | P a}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S4A_GSPEC_REINDEX = prove
 (`!(P:B->bool) (Q:A->bool) (j:A->B) (f:B->real^N->bool).
     (!b. P b <=> ?a. Q a /\ b = j a)
     ==> {f b | b | P b} = {f (j a) | a | Q a}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Clause 4: the arc of a vertex ball on a 2-simplex.                         *)

let MOI_S4A_CLAUSE4 = prove
 (`!(tt:(real^N->bool)->bool) kk s v.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk
     ==> pl_cell_with_boundary 1 (s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
           (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_simp; IN_ELIM_THM] o
    check (fun th -> concl th = `(s:real^N->bool) IN moi_s34_simp kk (&2)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_AFF_DIM_HULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull V:real^N->bool) = &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_VTX THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V DIFF {v:real^N}) = 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF; FINITE_SING; SING_SUBSET; CARD_SING] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN V /\ ~(w = v)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~((V:real^N->bool) SUBSET {v}) ==> ?w. w IN V /\ ~(w = v)`) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`] MOI_S4A_X0) THEN
  ASM_REWRITE_TAC[SING_SUBSET; NOT_INSERT_EMPTY; CARD_SING] THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(V DIFF {v:real^N}) = 2` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`; `x0:real^N`] MOI_S4A_BOX) THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `x0:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN convex hull V /\
                       (!a. a IN {v} ==> moi_s4a_bc V a x = &2 / &5) /\
                       !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 S (relative_frontier (S:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_1 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `v:real^N`; `w:real^N`] MOI_S4A_AFFDIM_BOX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{convex hull V INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
     g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET convex hull V} =
    {convex hull V INTER moi_s34_sd tt kk (convex hull {v,a}) INTER moi_s34_bd tt kk |
     a | a IN V /\ ~(a = (v:real^N))}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\g:real^N->bool. g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET convex hull V`;
      `\a:real^N. a IN V /\ ~(a = v)`; `\a:real^N. convex hull {v,a}`;
      `\g:real^N->bool. convex hull V INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk`]
      MOI_S4A_GSPEC_REINDEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `b:real^N->bool` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`;
      `kk:(real^N->bool)->bool`; `V:real^N->bool`; `v:real^N`; `b:real^N->bool`]
      MOI_S4A_EDGES_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                        `S:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SET_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[];
    ASM_SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S4A_IMAGE_UNIONS_GSPEC] THEN
  SUBGOAL_THEN
   `{IMAGE h (convex hull V INTER moi_s34_sd tt kk (convex hull {v,a}) INTER
              moi_s34_bd tt kk) | a | a IN V /\ ~(a = (v:real^N))} =
    {{x | x IN convex hull V /\
          (!b. b IN {v,a} ==> moi_s4a_bc V b x = &2 / &5) /\
          !b. b IN V ==> moi_s4a_bc V b x <= &2 / &5} | a | a IN V /\ ~(a = v)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `a:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))))) THENL
     [MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N,a}`; `x:real^N`; `&2 / &5`]
        MOI_S4A_BC_SUM_LE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[IN_DIFF]];
        ALL_TAC] THEN
      SUBGOAL_THEN `CARD(V DIFF {v:real^N,a}) = 1` SUBST1_TAC THENL
       [SUBGOAL_THEN `{v:real^N,a} SUBSET V` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[CARD_DIFF; FINITE_INSERT; FINITE_EMPTY] THEN
        SUBGOAL_THEN `~(a:real^N = v)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                     NOT_IN_EMPTY] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(v:real^N = a)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                   NOT_IN_EMPTY] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      EXISTS_TAC `{x | x IN convex hull V /\
                       (!b. b IN {v,a} ==> moi_s4a_bc V b x = &2 / &5) /\
                       !b. b IN V ==> moi_s4a_bc V b (x:real^N) <= &2 / &5}` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `a:real^N` THEN REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
        ASM SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC))
      MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[IN_SING]]);;


(* Clause 6: a splitting disk meets a 2-simplex in one point of the tube    *)
(* boundary.                                                                 *)

let MOI_S4A_CARD_DIM = prove
 (`!(V:real^N->bool) n.
     ~affine_dependent V /\ aff_dim (convex hull V) = &n ==> CARD V = n + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_AFF_DIM_HULL) THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MOI_S4A_IMAGE_SING = prove
 (`!(h:real^N->real^N) k C D p.
     C SUBSET D /\ (!x. x IN D ==> k(h x) = x) /\ IMAGE h C = {p}
     ==> C = {k p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
  X_GEN_TAC `x:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_IMAGE; IN_SING] THEN ASM_MESON_TAC[SUBSET]);;

let MOI_S4A_PAIR_DIFF = prove
 (`!(V:real^N->bool) u w.
     FINITE V /\ CARD V = 3 /\ u IN V /\ w IN V /\ ~(u = w)
     ==> CARD {u,w} = 2 /\ CARD(V DIFF {u,w}) = 1 /\ ~(V DIFF {u,w} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD {u:real^N,w} = 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V DIFF {u:real^N,w}) = 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `{u:real^N,w} SUBSET V` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_DIFF; FINITE_INSERT; FINITE_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `CARD(V DIFF {u:real^N,w}) = 1` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let MOI_S4A_CLAUSE6 = prove
 (`!(tt:(real^N->bool)->bool) kk s g.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET s
     ==> ?p. s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk = {p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_simp; IN_ELIM_THM] o
    check (fun th -> concl th = `(s:real^N->bool) IN moi_s34_simp kk (&2)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `2`] MOI_S4A_CARD_DIM) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `g:real^N->bool`; `1`] MOI_S4A_SIMP_IN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(E:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE; FINITE_SUBSET]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(u:real^N) IN V /\ w IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`] MOI_S4A_PAIR_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w}`] MOI_S4A_X0) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w}`; `x0:real^N`] MOI_S4A_BOX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `x0:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `aff_dim {x | x IN convex hull V /\
                 (!a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5) /\
                 !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5} = &0`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`] MOI_S4A_AFFDIM_BOX) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^N`) THEN
  EXISTS_TAC `(k:real^N->real^N) p` THEN
  MATCH_MP_TAC MOI_S4A_IMAGE_SING THEN
  EXISTS_TAC `h:real^N->real^N` THEN EXISTS_TAC `convex hull V:real^N->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN ASM_MESON_TAC[]);;


(* Images of facet traces; the closure of a face minus the tube.             *)

let MOI_S4A_IMAGE_FILTER = prove
 (`!(h:real^N->real^N) k D A C (P:real^N->bool).
     A SUBSET D /\ C SUBSET D /\ IMAGE h D = D /\
     (!x. x IN D ==> k(h x) = x) /\ IMAGE h A = {x | x IN D /\ P x}
     ==> IMAGE h (A INTER C) = {x | x IN IMAGE h C /\ P x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_S4A_FACET_IMAGE = prove
 (`!(V:real^N->bool) (h:real^N->real^N) k a C.
     ~affine_dependent V /\ a IN V /\
     (!x. x IN convex hull V ==> k(h x) = x) /\
     (!E. E SUBSET V ==> IMAGE h (convex hull E) = convex hull E) /\
     C SUBSET convex hull V
     ==> IMAGE h (convex hull (V DELETE a) INTER C) =
         {x | x IN IMAGE h C /\ moi_s4a_bc V a x = &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_IMAGE_FILTER THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `convex hull V:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ASM_MESON_TAC[SUBSET_REFL];
    ASM_SIMP_TAC[DELETE_SUBSET] THEN MATCH_MP_TAC MOI_S4A_FACET_COORD THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4A_THREE_NOT = prove
 (`!(V:real^N->bool) u w a x.
     ~affine_dependent V /\ x IN convex hull V /\
     u IN V /\ w IN V /\ a IN V /\ ~(u = w) /\ ~(a = u) /\ ~(a = w) /\
     moi_s4a_bc V u x = &2 / &5 /\ moi_s4a_bc V w x = &2 / &5 /\
     (!b. b IN V ==> moi_s4a_bc V b x <= &2 / &5)
     ==> ~(moi_s4a_bc V a x = &2 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w,a}`; `x:real^N`; `&2 / &5`]
    MOI_S4A_BC_SUM_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `b:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `~(u:real^N = a) /\ ~(w = a)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_S4A_PAIR_DIFF4 = prove
 (`!(V:real^N->bool) u w.
     FINITE V /\ CARD V = 4 /\ u IN V /\ w IN V /\ ~(u = w)
     ==> CARD {u,w} = 2 /\ CARD(V DIFF {u,w}) = 2 /\ ~(V DIFF {u,w} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD {u:real^N,w} = 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V DIFF {u:real^N,w}) = 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `{u:real^N,w} SUBSET V` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_DIFF; FINITE_INSERT; FINITE_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `CARD(V DIFF {u:real^N,w}) = 2` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let MOI_S4A_RCLOS_FACE = prove
 (`!(t:(real^N->bool)->bool) l q s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ q IN t /\ s IN t /\
     s SUBSET q
     ==> closure (s DIFF derived_nbhd t l) =
         s INTER closure (q DIFF derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[SUBSET_DIFF] THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4A_RCLOS_IN] THEN
  REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g:(real^N->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4A_C1Q) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                 `g:(real^N->bool)->bool`; `x:real^N`] MOI_S4A_RESTRICT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_S4A_GQ_HER]);;

(* The relative frontiers of the boxes as unions of their faces.            *)

let MOI_S4A_RF5 = prove
 (`!(V:real^N->bool) u w S.
     ~affine_dependent V /\ u IN V /\ w IN V /\ ~(u = w) /\
     {x | x IN convex hull V /\
          (!a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5) /\
          !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5} = S
     ==> {x | x IN convex hull V /\
              (!a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5) /\
              (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ ~(a IN {u,w}) /\
                  (moi_s4a_bc V a x = &0 \/ moi_s4a_bc V a x = &2 / &5)} =
         UNIONS {{x | x IN S /\ moi_s4a_bc V a x = &0} | a |
                 a IN V /\ ~(a = u) /\ ~(a = w)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY;
              IN_INSERT; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`; `a:real^N`;
                     `x:real^N`] MOI_S4A_THREE_NOT) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_S4A_RF3 = prove
 (`!(V:real^N->bool) v S.
     ~affine_dependent V /\ v IN V /\
     {x | x IN convex hull V /\
          (!a. a IN {v} ==> moi_s4a_bc V a x = &2 / &5) /\
          !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5} = S
     ==> {x | x IN convex hull V /\
              (!a. a IN {v} ==> moi_s4a_bc V a x = &2 / &5) /\
              (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ ~(a IN {v}) /\
                  (moi_s4a_bc V a x = &0 \/ moi_s4a_bc V a x = &2 / &5)} =
         UNIONS {{x | x IN S /\ moi_s4a_bc V a x = &0} | a | a IN V /\ ~(a = v)} UNION
         UNIONS {{x | x IN convex hull V /\
                      (!b. b IN {v,a} ==> moi_s4a_bc V b x = &2 / &5) /\
                      !b. b IN V ==> moi_s4a_bc V b x <= &2 / &5} | a |
                 a IN V /\ ~(a = v)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; FORALL_IN_INSERT; NOT_IN_EMPTY;
              IN_INSERT] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_S4A_RF1 = prove
 (`!(V:real^N->bool) S.
     {x | x IN convex hull V /\
          (!a. a IN {} ==> moi_s4a_bc V a x = &2 / &5) /\
          !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5} = S
     ==> {x | x IN convex hull V /\
              (!a. a IN {} ==> moi_s4a_bc V a x = &2 / &5) /\
              (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ ~(a IN {}) /\
                  (moi_s4a_bc V a x = &0 \/ moi_s4a_bc V a x = &2 / &5)} =
         UNIONS {{x | x IN S /\ moi_s4a_bc V a x = &0} | a | a IN V} UNION
         {x | x IN convex hull V /\ (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
              ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5}`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]]);;


(* Clause 5: the arc of a splitting disk in a 3-simplex.                     *)

let MOI_S4A_CLAUSE5 = prove
 (`!(tt:(real^N->bool)->bool) kk r g.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r
     ==> pl_cell_with_boundary 1 (r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
           (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_simp; IN_ELIM_THM] o
    check (fun th -> concl th = `(r:real^N->bool) IN moi_s34_simp kk (&3)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 4` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `3`] MOI_S4A_CARD_DIM) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `g:real^N->bool`; `1`] MOI_S4A_SIMP_IN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(E:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE; FINITE_SUBSET]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(u:real^N) IN V /\ w IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`] MOI_S4A_PAIR_DIFF4) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w}`] MOI_S4A_X0) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N,w}`; `x0:real^N`] MOI_S4A_BOX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `x0:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN convex hull V /\
                       (!a. a IN {u,w} ==> moi_s4a_bc V a x = &2 / &5) /\
                       !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 S (relative_frontier (S:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_1 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`] MOI_S4A_AFFDIM_BOX) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 <= 4`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s INTER moi_s34_sd tt kk (convex hull {u,w}) INTER moi_s34_bd tt kk | s |
     s IN moi_s34_simp kk (&2) /\ convex hull {u,w} SUBSET s /\
     s SUBSET convex hull V} =
    {convex hull (V DELETE a) INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
     moi_s34_bd tt kk | a | a IN V /\ ~(a = u) /\ ~(a = (w:real^N))}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\s:real^N->bool. s IN moi_s34_simp kk (&2) /\ convex hull {u,w} SUBSET s /\
                        s SUBSET convex hull V`;
      `\a:real^N. a IN V /\ ~(a = u) /\ ~(a = w)`;
      `\a:real^N. convex hull (V DELETE a)`;
      `\s:real^N->bool. s INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
                        moi_s34_bd tt kk`]
      MOI_S4A_GSPEC_REINDEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `b:real^N->bool` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `V:real^N->bool`; `b:real^N->bool`; `u:real^N`; `w:real^N`]
      MOI_S4A_FACETS_EDGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                        `S:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SET_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `a:real^N` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(s:real^N->bool) SUBSET t ==> s INTER x INTER y SUBSET t`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S4A_IMAGE_UNIONS_GSPEC] THEN
  SUBGOAL_THEN
   `{IMAGE h (convex hull (V DELETE a) INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
              moi_s34_bd tt kk) | a | a IN V /\ ~(a = u) /\ ~(a = (w:real^N))} =
    {{x | x IN S /\ moi_s4a_bc V a x = &0} | a | a IN V /\ ~(a = u) /\ ~(a = w)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `convex hull (V DELETE a) INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
      moi_s34_bd tt kk =
      convex hull (V DELETE a) INTER
      (convex hull V INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
       moi_s34_bd tt (kk:(real^N->bool)->bool))` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(a:real^N->bool) SUBSET v ==> a INTER x = a INTER (v INTER x)`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`; `a:real^N`;
      `convex hull V INTER moi_s34_sd tt kk (convex hull {u,w}) INTER
       moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      MOI_S4A_FACET_IMAGE) THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4A_RF5 THEN ASM_REWRITE_TAC[]);;

(* Clause 3: the patch of a vertex ball on a 3-simplex.                       *)

let MOI_S4A_CLAUSE3 = prove
 (`!(tt:(real^N->bool)->bool) kk r v.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk
     ==> pl_cell_with_boundary 2 (r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
           (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
            UNIONS {r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_simp; IN_ELIM_THM] o
    check (fun th -> concl th = `(r:real^N->bool) IN moi_s34_simp kk (&3)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 4` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `3`] MOI_S4A_CARD_DIM) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_VTX THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V DIFF {v:real^N}) = 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF; FINITE_SING; SING_SUBSET; CARD_SING] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN V /\ ~(w = v)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~((V:real^N->bool) SUBSET {v}) ==> ?w. w IN V /\ ~(w = v)`) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_vb"))
      (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
      (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`] MOI_S4A_X0) THEN
  ASM_REWRITE_TAC[SING_SUBSET; NOT_INSERT_EMPTY; CARD_SING] THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(V DIFF {v:real^N}) = 3` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{v:real^N}`; `x0:real^N`] MOI_S4A_BOX) THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `x0:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN convex hull V /\
                       (!a. a IN {v} ==> moi_s4a_bc V a x = &2 / &5) /\
                       !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 S (relative_frontier (S:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `v:real^N`; `w:real^N`] MOI_S4A_AFFDIM_BOX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
     s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET convex hull V} =
    {convex hull (V DELETE a) INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | a |
     a IN V /\ ~(a = (v:real^N))}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\s:real^N->bool. s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET convex hull V`;
      `\a:real^N. a IN V /\ ~(a = v)`; `\a:real^N. convex hull (V DELETE a)`;
      `\s:real^N->bool. s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk`]
      MOI_S4A_GSPEC_REINDEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `b:real^N->bool` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `V:real^N->bool`; `b:real^N->bool`; `v:real^N`] MOI_S4A_FACETS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{convex hull V INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
     g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET convex hull V} =
    {convex hull V INTER moi_s34_sd tt kk (convex hull {v,a}) INTER moi_s34_bd tt kk |
     a | a IN V /\ ~(a = (v:real^N))}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\g:real^N->bool. g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET convex hull V`;
      `\a:real^N. a IN V /\ ~(a = v)`; `\a:real^N. convex hull {v,a}`;
      `\g:real^N->bool. convex hull V INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk`]
      MOI_S4A_GSPEC_REINDEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `b:real^N->bool` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`;
      `kk:(real^N->bool)->bool`; `V:real^N->bool`; `v:real^N`; `b:real^N->bool`]
      MOI_S4A_EDGES_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                        `S:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SET_TAC[];
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THEN
    X_GEN_TAC `a:real^N` THEN STRIP_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(p:real^N->bool) SUBSET q ==> p INTER x INTER y SUBSET q`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      SET_TAC[]];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION; MOI_S4A_IMAGE_UNIONS_GSPEC] THEN
  SUBGOAL_THEN
   `{IMAGE h (convex hull (V DELETE a) INTER moi_s34_vb tt kk v INTER
              moi_s34_bd tt kk) | a | a IN V /\ ~(a = (v:real^N))} =
    {{x | x IN S /\ moi_s4a_bc V a x = &0} | a | a IN V /\ ~(a = v)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `convex hull (V DELETE a) INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk =
      convex hull (V DELETE a) INTER
      (convex hull V INTER moi_s34_vb tt kk v INTER
       moi_s34_bd tt (kk:(real^N->bool)->bool))` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(p:real^N->bool) SUBSET q ==> p INTER x = p INTER (q INTER x)`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`; `a:real^N`;
      `convex hull V INTER moi_s34_vb tt kk v INTER
       moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      MOI_S4A_FACET_IMAGE) THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{IMAGE h (convex hull V INTER moi_s34_sd tt kk (convex hull {v,a}) INTER
              moi_s34_bd tt kk) | a | a IN V /\ ~(a = (v:real^N))} =
    {{x | x IN convex hull V /\
          (!b. b IN {v,a} ==> moi_s4a_bc V b x = &2 / &5) /\
          !b. b IN V ==> moi_s4a_bc V b x <= &2 / &5} | a | a IN V /\ ~(a = v)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `a:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4A_RF3 THEN ASM_REWRITE_TAC[]);;

(* Clause 1: a 3-simplex minus the open tube is a 3-ball.                    *)

let MOI_S4A_FACET_KK = prove
 (`!(tt:(real^N->bool)->bool) kk V a.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     CARD V = 4 /\ a IN V
     ==> convex hull (V DELETE a) IN kk /\ convex hull (V DELETE a) IN tt /\
         convex hull (V DELETE a) SUBSET convex hull V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
    `V:real^N->bool`; `convex hull (V DELETE a):real^N->bool`] MOI_S4A_FACETS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> ((a <=> b) ==> c)`) THEN CONJ_TAC THENL
   [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_S4A_CLAUSE1 = prove
 (`!(tt:(real^N->bool)->bool) kk r.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3)
     ==> pl_cell_with_boundary 3 (closure (r DIFF moi_s34_nb tt kk))
           (UNIONS {closure (s DIFF moi_s34_nb tt kk) | s |
                    s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
            (r INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_simp; IN_ELIM_THM] o
    check (fun th -> concl th = `(r:real^N->bool) IN moi_s34_simp kk (&3)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 4` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `3`] MOI_S4A_CARD_DIM) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(V:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(V:real^N->bool) = 4` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u w:real^N. u IN V /\ w IN V /\ ~(u = w)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `u:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `~((V:real^N->bool) SUBSET {u}) ==> ?w. w IN V /\ ~(u = w)`) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`V:real^N->bool`; `{u:real^N}`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`]
    MOI_S4A_FLAT_KK2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BARY_POINT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x0 = simplex_barycentre (convex hull V:real^N->bool)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{}:real^N->bool`; `x0:real^N`] MOI_S4A_BOX) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY] THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN convex hull V /\
                       (!a. a IN {} ==> moi_s4a_bc V a x = &2 / &5) /\
                       !a. a IN V ==> moi_s4a_bc V a (x:real^N) <= &2 / &5}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 3 S (relative_frontier (S:real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `u:real^N`; `w:real^N`] MOI_S4A_AFFDIM_BOX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(convex hull V:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure(convex hull V DIFF moi_s34_nb tt kk) SUBSET convex hull (V:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[SUBSET_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{closure (s DIFF moi_s34_nb tt kk) | s |
     s IN moi_s34_simp kk (&2) /\ s SUBSET convex hull V} =
    {closure (convex hull (V DELETE a) DIFF moi_s34_nb tt kk) | a |
     a IN (V:real^N->bool)}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\s:real^N->bool. s IN moi_s34_simp kk (&2) /\ s SUBSET convex hull V`;
      `\a:real^N. a IN V`; `\a:real^N. convex hull (V DELETE a)`;
      `\s:real^N->bool. closure (s DIFF moi_s34_nb tt kk)`]
      MOI_S4A_GSPEC_REINDEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `b:real^N->bool` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `V:real^N->bool`; `b:real^N->bool`] MOI_S4A_FACETS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. a IN V
      ==> closure (convex hull (V DELETE a) DIFF moi_s34_nb tt kk) =
          convex hull (V DELETE a) INTER closure (convex hull V DIFF moi_s34_nb tt kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `V:real^N->bool`; `a:real^N`] MOI_S4A_FACET_KK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_nb] THEN
    MATCH_MP_TAC MOI_S4A_RCLOS_FACE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4A_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                        `S:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC; INTER_SUBSET] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(p:real^N->bool) SUBSET q ==> p INTER x SUBSET q`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION; MOI_S4A_IMAGE_UNIONS_GSPEC] THEN
  SUBGOAL_THEN
   `{IMAGE h (closure (convex hull (V DELETE a) DIFF moi_s34_nb tt kk)) | a |
     a IN (V:real^N->bool)} =
    {{x | x IN S /\ moi_s4a_bc V a x = &0} | a | a IN V}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`; `a:real^N`;
      `closure (convex hull V DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))`]
      MOI_S4A_FACET_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4A_RF1 THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* 12. Assembly.  Clauses 1-6 of moi_s34_scell_facts are proved above.  The  *)
(* outer cells at boundary vertices and boundary edges of kk (clauses 7-8)  *)
(* are collected in moi_s4a_outer, verbatim; SCELL_A follows from them.     *)
(* ------------------------------------------------------------------------- *)

let moi_s4a_outer = new_definition
 `moi_s4a_outer (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) <=>
   (!v. {v} IN kk /\ v IN complex_boundary kk
        ==> pl_cell_with_boundary 2
              (closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk))
              (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                       s IN moi_s34_simp kk (&2) /\ v IN s /\
                       s SUBSET complex_boundary kk} UNION
               UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                UNIONS kk) | g |
                       g IN moi_s34_simp kk (&1) /\ v IN g /\
                       g SUBSET complex_boundary kk})) /\
   (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
        ==> pl_cell_with_boundary 1
              (closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk))
              (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                       s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                       s SUBSET complex_boundary kk}))`;;

let MOI_S4A_SCELL_FACTS_OUTER = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk /\ moi_s4a_outer tt kk ==> moi_s34_scell_facts tt kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4a_outer] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s34_scell_facts] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S4A_CLAUSE1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_CLAUSE2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_CLAUSE3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_CLAUSE4 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_CLAUSE5 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4A_CLAUSE6 THEN ASM_REWRITE_TAC[]]);;

let MOI_S4A_SCELL_A_FROM_OUTER = prove
 (`(!(tt:(real^N->bool)->bool) kk. moi_s34_tube tt kk ==> moi_s4a_outer tt kk)
   ==> !(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool).
         moi_s34_tube tt kk ==> moi_s34_scell_facts tt kk`,
  MESON_TAC[MOI_S4A_SCELL_FACTS_OUTER]);;

