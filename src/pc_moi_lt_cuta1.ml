needs "src/pc_moi_loop_stmt3.ml";;
needs "src/pc_moi_lt_cutc.ml";;
needs "src/pc_moi_pl1m.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_cuta1: the innermost double polygon of the C25 cut (lt_cut_a1, *)
(* Moise p.185).  Main theorem INNERMOST_FROM_EXCL :                        *)
(* |- MOI_LT3_INNERMOST_FROM_EXCL (pc_moi_loop_stmt3.ml): if no closed      *)
(* double component of a normal2 disk has a connected preimage (Case 1      *)
(* excluded; proved from orientability in pc_moi_lt_case1), an innermost    *)
(* double polygon exists as in MOI_LT2_CUT_INNERMOST.  Route: the source    *)
(* double set is triangulated by MOI_LCC_SOURCE_COMPLEX; its components are *)
(* finitely many, each maps onto a double component (local preimages), and *)
(* those missing the frontier of the triangle are polygons                  *)
(* (MOI_S4L_CM1_CIRCLES); the preimage of a closed double component that is *)
(* not connected consists of two such polygons; insides of polygons are     *)
(* nested and lie in the open triangle, so an innermost polygon contains no *)
(* point of the source double set.  Also exported: MOI_LA1_CASE2_BIJ (for  *)
(* lt_cut_a2).                                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A1. Components: finitely many for finite unions of connected sets, then  *)
(* open and closed; a compact piece of the source over a double component   *)
(* that is open in its preimage maps onto the component; the Case 2         *)
(* bijections.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LA1_COMPONENTS_FINITE_UNIONS = prove
 (`!K:(real^N->bool)->bool.
     FINITE K /\ (!t. t IN K ==> connected t) ==> FINITE (components (UNIONS K))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\t. connected_component (UNIONS K) (CHOICE t))
                    {t:real^N->bool | t IN K /\ ~(t = {})}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_COMPONENTS; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `cc:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  SUBGOAL_THEN `(CHOICE t:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[CHOICE_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET connected_component (UNIONS K) x`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `CHOICE t:real^N`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[CONNECTED_COMPONENT_EQ]);;

let MOI_LA1_COMPONENT_CLOPEN = prove
 (`!(s:real^N->bool) k.
     FINITE (components s) /\ k IN components s
     ==> open_in (subtopology euclidean s) k /\
         closed_in (subtopology euclidean s) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOSED_IN_COMPONENT] THEN
  SUBGOAL_THEN `k = s DIFF UNIONS (components s DELETE (k:real^N->bool))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_DELETE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`; `c':real^N->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_DELETE] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPEC `s:real^N->bool` UNIONS_COMPONENTS) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; CLOSED_IN_COMPONENT]]);;

let MOI_LA1_IMAGE_COMPONENT = prove
 (`!c (f:real^2->real^N) k j.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     j SUBSET {x | x IN std_triangle /\ f x IN k} /\ compact j /\ ~(j = {}) /\
     closed ({x | x IN std_triangle /\ f x IN k} DIFF j)
     ==> IMAGE f j = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `k SUBSET moi_lt_double_image (f:real^2->real^N) /\ connected k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) j SUBSET k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^2->real^N) j`) THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q \/ r) ==> r`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (f:real^2->real^N) x IN k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} DIFF j`;
                 `x:real^2`] SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sep"))) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x:real^2`; `d:real`]
    MOI_LCC_LOCAL_PREIMAGE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pre")) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  REMOVE_THEN "pre" (MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[DIST_SYM]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  REMOVE_THEN "sep" (MP_TAC o SPEC `x':real^2`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  UNDISCH_TAC `(f:real^2->real^N) x' = y` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_LA1_CASE2_BIJ = prove
 (`!c (f:real^2->real^N) k j1 j2.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\ DISJOINT j1 j2 /\
     compact j1 /\ compact j2 /\ connected j1 /\ connected j2 /\
     ~(j1 = {}) /\ ~(j2 = {})
     ==> IMAGE f j1 = k /\ IMAGE f j2 = k /\
         (!x y. x IN j1 /\ y IN j1 /\ f x = f y ==> x = y) /\
         (!x y. x IN j2 /\ y IN j2 /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) j1 = k /\ IMAGE f j2 = k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LA1_IMAGE_COMPONENT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THENL
     [SUBGOAL_THEN `(j1 UNION j2) DIFF j1 = j2:real^2->bool` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(j1 UNION j2) DIFF j2 = j1:real^2->bool` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y:real^N. FINITE {x | x IN std_triangle /\ (f:real^2->real^N) x = y} /\
               CARD {x | x IN std_triangle /\ f x = y} <= 2`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `(j1 UNION j2) SUBSET (std_triangle:real^2->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `j1 UNION j2:real^2->bool`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `?z:real^2. z IN j2 /\ (f:real^2->real^N) z = f x` STRIP_ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `?z:real^2. z IN j1 /\ (f:real^2->real^N) z = f x` STRIP_ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC]] THEN
  MP_TAC(ISPECL [`{w | w IN std_triangle /\ (f:real^2->real^N) w = f x}`;
                 `x:real^2`; `x':real^2`; `z:real^2`] MOI_LCC_CARD_LE2) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ASM SET_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* A2. The source complex of a normal disk with its vertex count; edges at  *)
(* a vertex; components of the source double set: finitely many, each maps  *)
(* onto a double component, and those missing the frontier are polygons.    *)
(* ------------------------------------------------------------------------- *)

let MOI_LA1_SRC = prove
 (`!c (f:real^2->real^N).
     moi_lt_normal_disk c f
     ==> ?s0. simplicial_complex s0 /\
              UNIONS s0 =
                {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
              (!t. t IN s0
                   ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                       ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
              (!v. {v} IN s0
                   ==> (UNIONS (simplicial_link s0 v) HAS_SIZE 1 /\
                        v IN relative_frontier std_triangle) \/
                       (UNIONS (simplicial_link s0 v) HAS_SIZE 2 /\
                        ~(v IN relative_frontier std_triangle)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
                `l:(real^N->bool)->bool`] MOI_LCC_SOURCE_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold_with_boundary;
                      lf_simplicial_complex];
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
      ASM_MESON_TAC[MOI_LCC_CMWB1_DIM]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s0:(real^2->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_LCC_SRC_VERTEX THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LA1_EDGES_AT_VERTEX = prove
 (`!(K:(real^N->bool)->bool) v.
     simplicial_complex K /\ (!t. t IN K ==> aff_dim t <= &1) /\ {v} IN K
     ==> {e | e IN K /\ aff_dim e = &1 /\ v IN e} =
         IMAGE (\u. segment[v,u]) {u | ~(u = v) /\ segment[v,u] IN K} /\
         (!u u'. ~(u = v) /\ ~(u' = v) /\ segment[v,u] = segment[v,u'] ==> u = u')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_EQ] THEN SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `a:real^N`; `b:real^N`]
      MOI_LCC_VERTEX_OF_EDGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; AFF_DIM_SEGMENT] THEN
    ASM_MESON_TAC[]]);;

let MOI_LA1_SOURCE_COMPONENTS = prove
 (`!c (f:real^2->real^N).
     moi_lt_normal_disk c f
     ==> compact {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
         FINITE (components
                   {x | x IN std_triangle /\ f x IN moi_lt_double_image f}) /\
         compact (moi_lt_double_image f) /\
         FINITE (components (moi_lt_double_image f))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LA1_SRC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE (s0:(real^2->bool)->bool) /\
                (!t. t IN s0 ==> compact t /\ connected t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX;
                  CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\
                (!t. t IN l ==> compact t /\ connected t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex;
                  SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (UNIONS (s0:(real^2->bool)->bool)) /\
    FINITE (components (UNIONS s0)) /\
    compact (UNIONS (l:(real^N->bool)->bool)) /\
    FINITE (components (UNIONS l))`
  MP_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNIONS; MOI_LA1_COMPONENTS_FINITE_UNIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LA1_COMPONENT_IMAGE = prove
 (`!c (f:real^2->real^N) C.
     moi_lt_normal_disk c f /\
     C IN components {x | x IN std_triangle /\ f x IN moi_lt_double_image f}
     ==> IMAGE f C IN components (moi_lt_double_image f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA1_SOURCE_COMPONENTS) THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  SUBGOAL_THEN `(C:real^2->bool) SUBSET S /\ connected C /\ ~(C = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED;
                  IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`;
                 `IMAGE (f:real^2->real^N) C`] EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(C:real^2->bool) SUBSET S` THEN EXPAND_TAC "S" THEN SET_TAC[];
      UNDISCH_TAC `(C:real^2->bool) SUBSET S` THEN
      UNDISCH_TAC `~(C:real^2->bool = {})` THEN EXPAND_TAC "S" THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) C = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_LA1_IMAGE_COMPONENT THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
    ASM_SIMP_TAC[CLOSED_IN_COMPONENT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean S) (C:real^2->bool) /\
                closed_in (subtopology euclidean S) C`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LA1_COMPONENT_CLOPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(C:real^2->bool) SUBSET S` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) C SUBSET k` THEN
    EXPAND_TAC "S" THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `S:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} DIFF C =
      {x | x IN std_triangle /\ f x IN k} INTER (S DIFF C)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(k:real^N->bool) IN components (moi_lt_double_image f)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      EXPAND_TAC "S" THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
      MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL]]]);;

let MOI_LA1_POLYGON_COMPONENT = prove
 (`!c (f:real^2->real^N) C.
     moi_lt_normal_disk c f /\
     C IN components {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     C INTER relative_frontier std_triangle = {}
     ==> pl_sphere 1 C`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `s0:(real^2->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_LA1_SRC) THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  SUBGOAL_THEN `(C:real^2->bool) SUBSET S /\ connected C /\ ~(C = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED;
                  IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^2->bool. t IN s0 /\ ~(t INTER C = {}) ==> t SUBSET C`
  (LABEL_TAC "max") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K = {t:real^2->bool | t IN s0 /\ t SUBSET C}` THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^2->bool)->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `K = {t:real^2->bool | t IN s0 /\ ?q. q IN {C} /\ t SUBSET q}`
    SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[IN_SING] THEN SET_TAC[];
      MATCH_MP_TAC MOI_LCC_SUBCOMPLEX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS K = C:real^2->bool` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS s0` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^2->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "max" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^2->bool. t IN K ==> aff_dim t <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `K:(real^2->bool)->bool` MOI_S4L_CM1_CIRCLES) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ANTS_TAC THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `v:real^2`] MOI_LA1_EDGES_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `{v:real^2} IN s0 /\ (v:real^2) IN C` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{v:real^2} IN K` THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{u | ~(u = v) /\ segment[v:real^2,u] IN K} =
      {u | ~(u = v) /\ segment[v:real^2,u] IN s0}`
    SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `u:real^2` THEN
      ASM_CASES_TAC `u:real^2 = v` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `segment[v:real^2,u] IN s0` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `v:real^2` THEN
      ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{u | ~(u = v) /\ segment[v:real^2,u] IN s0} HAS_SIZE 2`
    MP_TAC THENL
     [MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `v:real^2`] MOI_LCC_LINK_1) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^2` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "HAS_SIZE"))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((v:real^2) IN relative_frontier std_triangle)`
        ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SIMP_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_COMPONENTS_SELF]);;

(* ------------------------------------------------------------------------- *)
(* A3. The preimage of a double component as a union of source components; *)
(* two components when it is not connected; insides of polygons in the     *)
(* open triangle; an innermost polygon.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LA1_SK_UNION = prove
 (`!c (f:real^2->real^N) k.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f)
     ==> {x | x IN std_triangle /\ f x IN k} =
         UNIONS {C | C IN components {x | x IN std_triangle /\
                                          f x IN moi_lt_double_image f} /\
                     IMAGE f C = k}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(x:real^2) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `connected_component S (x:real^2)` THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
    SUBGOAL_THEN `(x:real^2) IN connected_component S x` ASSUME_TAC THENL
     [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
                  `connected_component S (x:real^2)`] MOI_LA1_COMPONENT_IMAGE) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`;
                   `IMAGE (f:real^2->real^N) (connected_component S x)`;
                   `k:real^N->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (p <=> ~q) ==> q`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(f:real^2->real^N) x` THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^2) IN S` MP_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `k:real^N->bool`)) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let MOI_LA1_CLOSED_TWO = prove
 (`!c (f:real^2->real^N) k.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f) /\
     ~connected {x | x IN std_triangle /\ f x IN k}
     ==> ?j1 j2.
           j1 IN components {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
           j2 IN components {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
           ~(j1 = j2) /\ IMAGE f j1 = k /\ IMAGE f j2 = k /\
           {x | x IN std_triangle /\ f x IN k} = j1 UNION j2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LA1_SK_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  ABBREV_TAC `Q = {C | C IN components S /\ IMAGE (f:real^2->real^N) C = k}` THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `!C. C IN Q ==> ?x:real^2. x IN C /\ (f:real^2->real^N) x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!C:real^2->bool. C IN Q ==> C IN components S /\ C SUBSET std_triangle`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `C:real^2->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:real^2->bool` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!D1 D2 z:real^2. D1 IN Q /\ D2 IN Q /\ z IN D1 /\ z IN D2 ==> D1 = D2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^2->bool`; `D1:real^2->bool`; `D2:real^2->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C1 C2 C3:real^2->bool. C1 IN Q /\ C2 IN Q /\ C3 IN Q
                            ==> C1 = C2 \/ C1 = C3 \/ C2 = C3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(C1:real^2->bool) IN Q`)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(C2:real^2->bool) IN Q`)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `x3:real^2` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(C3:real^2->bool) IN Q`)) THEN
    MP_TAC(ISPECL [`{w | w IN std_triangle /\ (f:real^2->real^N) w = y}`;
                   `x1:real^2`; `x2:real^2`; `x3:real^2`] MOI_LCC_CARD_LE2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `FINITE {w | w IN std_triangle /\ (f:real^2->real^N) w = y} /\
        CARD {w | w IN std_triangle /\ f w = y} <= 2`
      (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
        REWRITE_TAC[moi_lt_singular_disk] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?C1:real^2->bool. C1 IN Q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` MP_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS Q` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `UNIONS Q:real^2->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?C2:real^2->bool. C2 IN Q /\ ~(C2 = C1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~connected {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Q = {C1:real^2->bool}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `C:real^2->bool` THEN
      REWRITE_TAC[IN_SING] THEN
      UNDISCH_TAC `(C1:real^2->bool) IN Q` THEN
      UNDISCH_TAC `~(?C2:real^2->bool. C2 IN Q /\ ~(C2 = C1))` THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNIONS_1] THEN MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
    EXISTS_TAC `S:real^2->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`C1:real^2->bool`; `C2:real^2->bool`] THEN
  SUBGOAL_THEN
   `(C1:real^2->bool) IN components S /\ IMAGE (f:real^2->real^N) C1 = k /\
    C2 IN components S /\ IMAGE f C2 = k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(C1:real^2->bool) IN Q` THEN
    UNDISCH_TAC `(C2:real^2->bool) IN Q` THEN EXPAND_TAC "Q" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(C1:real^2->bool = C2)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^2->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`C1:real^2->bool`; `C2:real^2->bool`;
                                  `C:real^2->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    STRIP_TAC THENL
     [EXISTS_TAC `C1:real^2->bool`; EXISTS_TAC `C2:real^2->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LA1_INSIDE_TRIANGLE = prove
 (`!j:real^2->bool.
     j SUBSET std_triangle
     ==> inside j SUBSET std_triangle DIFF relative_frontier std_triangle`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `interior std_triangle` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_INTERIOR_CONVEX THEN
    ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
    MP_TAC(ISPEC `std_triangle` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    MP_TAC(ISPEC `std_triangle` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[relative_frontier] THEN SET_TAC[]]);;

let MOI_LA1_CONNECTED_INSIDE = prove
 (`!s t:real^2->bool.
     closed s /\ connected t /\ DISJOINT s t /\ ~(t INTER inside s = {})
     ==> t SUBSET inside s`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected(t:real^2->bool)` THEN REWRITE_TAC[connected] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`inside s:real^2->bool`; `outside s:real^2->bool`]) THEN
  ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE] THEN
  MP_TAC(ISPEC `s:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `s:real^2->bool` INSIDE_OUTSIDE) THEN ASM SET_TAC[]);;

let MOI_LA1_INNERMOST_EXISTS = prove
 (`!P:(real^2->bool)->bool.
     FINITE P /\ ~(P = {}) /\
     (!j. j IN P ==> compact j /\ connected j /\ ~(j = {}))
     ==> ?j1. j1 IN P /\ !j. j IN P ==> ~(j SUBSET inside j1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?m j:real^2->bool. j IN P /\ CARD {j' | j' IN P /\ j' SUBSET inside j} = m`
  MP_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j1:real^2->bool` STRIP_ASSUME_TAC) (LABEL_TAC "min"))) THEN
  EXISTS_TAC `j1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:real^2->bool` THEN REPEAT DISCH_TAC THEN
  REMOVE_THEN "min" (MP_TAC o SPEC
    `CARD {j' | j' IN P /\ j' SUBSET inside (j:real^2->bool)}`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC; EXISTS_TAC `j:real^2->bool` THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `m:num`)) THEN
  MATCH_MP_TAC CARD_PSUBSET THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  SUBGOAL_THEN `inside j SUBSET inside(j1:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM; EXTENSION] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `j:real^2->bool` INSIDE_NO_OVERLAP) THEN
  SUBGOAL_THEN `~(j:real^2->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A4. The main theorem: with Case 1 excluded, an innermost double polygon. *)
(* ------------------------------------------------------------------------- *)

let INNERMOST_FROM_EXCL = prove
 (MOI_LT3_INNERMOST_FROM_EXCL,
  DISCH_THEN(LABEL_TAC "excl") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `k0:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `moi_lt_normal_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN std_triangle
               ==> ((f:real^2->real^N) x IN complex_boundary c <=>
                    x IN relative_frontier std_triangle)`
  (LABEL_TAC "prop") THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA1_SOURCE_COMPONENTS) THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  SUBGOAL_THEN `(S:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!C:real^2->bool. C IN components S
                     ==> compact C /\ connected C /\ ~(C = {}) /\ C SUBSET S /\
                         IMAGE (f:real^2->real^N) C IN
                         components (moi_lt_double_image f)`
  (LABEL_TAC "comp") THENL
   [X_GEN_TAC `C:real^2->bool` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `S:real^2->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
      MATCH_MP_TAC MOI_LA1_COMPONENT_IMAGE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = {C:real^2->bool | C IN components S /\
                          C INTER relative_frontier std_triangle = {}}` THEN
  SUBGOAL_THEN
   `!C:real^2->bool. C IN P
                     ==> C IN components S /\ pl_sphere 1 C /\ compact C /\
                         connected C /\ ~(C = {}) /\
                         C SUBSET std_triangle DIFF relative_frontier std_triangle`
  (LABEL_TAC "poly") THENL
   [X_GEN_TAC `C:real^2->bool` THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "comp" (MP_TAC o SPEC `C:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `pl_sphere 1 (C:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LA1_POLYGON_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C:real^2->bool. C IN components S /\
                     IMAGE (f:real^2->real^N) C INTER complex_boundary c = {}
                     ==> C IN P`
  (LABEL_TAC "inP") THENL
   [X_GEN_TAC `C:real^2->bool` THEN STRIP_TAC THEN EXPAND_TAC "P" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "comp" (MP_TAC o SPEC `C:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    USE_THEN "prop" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (P:(real^2->bool)->bool) /\ ~(P = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "P" THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
    SUBGOAL_THEN `?y:real^N. y IN k0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` MP_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `connected_component S (x:real^2)` THEN
    USE_THEN "inP" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) (connected_component S x) = k0`
      SUBST1_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    USE_THEN "comp" (MP_TAC o SPEC `connected_component S (x:real^2)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`;
                   `IMAGE (f:real^2->real^N) (connected_component S x)`;
                   `k0:real^N->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (p <=> ~q) ==> q`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(f:real^2->real^N) x` THEN
    SUBGOAL_THEN `(x:real^2) IN connected_component S x` ASSUME_TAC THENL
     [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:(real^2->bool)->bool` MOI_LA1_INNERMOST_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inn"))) THEN
  USE_THEN "poly" (MP_TAC o SPEC `j1:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LA1_INSIDE_TRIANGLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!C:real^2->bool. C IN components S ==> DISJOINT C (inside j1)`
  (LABEL_TAC "disj") THENL
   [X_GEN_TAC `C:real^2->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `C:real^2->bool = j1` THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `j1:real^2->bool` INSIDE_NO_OVERLAP) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(C:real^2->bool) SUBSET inside j1` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LA1_CONNECTED_INSIDE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      MP_TAC(ISPECL [`S:real^2->bool`; `j1:real^2->bool`; `C:real^2->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(C:real^2->bool) IN P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "inn" (MP_TAC o C MATCH_MP (ASSUME `(C:real^2->bool) IN P`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = IMAGE (f:real^2->real^N) j1` THEN
  SUBGOAL_THEN
   `k IN components (moi_lt_double_image (f:real^2->real^N)) /\
    k INTER complex_boundary c = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "k" THEN USE_THEN "comp" (MP_TAC o SPEC `j1:real^2->bool`) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "k" THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      USE_THEN "prop" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "excl" (MP_TAC o SPECL
    [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    MOI_LA1_CLOSED_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^2->bool` (X_CHOOSE_THEN `a2:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?j2:real^2->bool. j2 IN components S /\ ~(j2 = j1) /\
                      IMAGE (f:real^2->real^N) j2 = k /\
                      {x | x IN std_triangle /\ f x IN k} = j1 UNION j2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `j1:real^2->bool = a1 \/ j1 = a2` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(j1:real^2->bool) SUBSET a1 UNION a2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `a1 UNION a2:real^2->bool`)) THEN
        EXPAND_TAC "k" THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?x:real^2. x IN j1` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) IN a1 \/ x IN a2` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL
       [DISJ1_TAC THEN
        MP_TAC(ISPECL [`S:real^2->bool`; `j1:real^2->bool`; `a1:real^2->bool`]
          COMPONENTS_NONOVERLAP);
        DISJ2_TAC THEN
        MP_TAC(ISPECL [`S:real^2->bool`; `j1:real^2->bool`; `a2:real^2->bool`]
          COMPONENTS_NONOVERLAP)] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_INTER; NOT_IN_EMPTY];
      EXISTS_TAC `a2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `a1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[UNION_COMM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j2:real^2->bool) IN P` ASSUME_TAC THENL
   [USE_THEN "inP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "poly" (MP_TAC o SPEC `j2:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^2->bool`; `j1:real^2->bool`; `j2:real^2->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!s t u:real^2->bool. s SUBSET u /\ t SUBSET u ==> s UNION t SUBSET u`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LA1_INSIDE_TRIANGLE THEN ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^2` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "disj" (MP_TAC o SPEC `connected_component S (x:real^2)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]; REWRITE_TAC[DISJOINT]] THEN
    SUBGOAL_THEN `(x:real^2) IN connected_component S x` MP_TAC THENL
     [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
      ASM SET_TAC[]];
    USE_THEN "disj" (ACCEPT_TAC o C MATCH_MP
      (ASSUME `(j2:real^2->bool) IN components S`))]);;

