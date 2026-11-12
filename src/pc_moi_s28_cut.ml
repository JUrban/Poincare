(* ========================================================================= *)
(* pc_moi_s28_cut: cutting combinatorial surfaces along bicollared polygons  *)
(* (Moise GTM 47, p.150 (21.10) and p.192).  STRIP_REMOVE: removing an open  *)
(* strip between two levels of a bicollar leaves a combinatorial surface     *)
(* whose boundary gains the two levels, with the same Euler characteristic.  *)
(* CUT_SEPARATING: a separating bicollared polygon in a closed connected     *)
(* surface cuts it into two surfaces bounded by it, with chi adding up.      *)
(* COMPONENT_COMPLEX: components of a combinatorial surface are subcomplexes *)
(* and chi is additive.  Charts route: the new triangulations satisfy the    *)
(* chart hypotheses of SURF_LOCAL (pc_moi_s28_trib).                         *)
(* ========================================================================= *)

needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_plmap.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Components of a polyhedron.  A nonempty simplex is connected, so it lies *)
(* in exactly one component; each component k is the polyhedron of the      *)
(* subcomplex of the simplices of c inside k, which has the links and edge *)
(* counts of c; chi is additive over the components (valuations of          *)
(* pc_moi_fnd_euler).  Gives COMPONENT_COMPLEX.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_SIMPLEX_IN_COMPONENT = prove
 (`!(c:(real^N->bool)->bool) s k.
     simplicial_complex c /\ s IN c /\ k IN components (UNIONS c) /\
     ~(s INTER k = {})
     ==> s SUBSET k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX; CONVEX_CONNECTED];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S8CU_COMPONENT_UNIONS = prove
 (`!(c:(real^N->bool)->bool) k.
     simplicial_complex c /\ k IN components (UNIONS c)
     ==> UNIONS {s | s IN c /\ s SUBSET k} = k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS c` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S8CU_SIMPLEX_IN_COMPONENT THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S8CU_FINITE_COMPONENTS = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c ==> FINITE(components(UNIONS c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\s:real^N->bool. connected_component (UNIONS c) (CHOICE s))
                    (c:(real^N->bool)->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `k:real^N->bool`] IN_COMPONENTS_NONEMPTY) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN c /\ x IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET; IN_UNIONS]; ALL_TAC] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_SIMPLEX_IN_COMPONENT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CHOICE(s:real^N->bool) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC CHOICE_DEF THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(k:real^N->bool) IN components (UNIONS c)` THEN
  REWRITE_TAC[IN_COMPONENTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM SET_TAC[]);;

let MOI_S8CU_SUBCOMPLEX = prove
 (`!(c:(real^N->bool)->bool) k.
     simplicial_complex c ==> simplicial_complex {s | s IN c /\ s SUBSET k}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
    ASM_MESON_TAC[]]);;

let MOI_S8CU_LINK_EQ = prove
 (`!(c:(real^N->bool)->bool) k v.
     simplicial_complex c /\ k IN components (UNIONS c) /\ v IN k
     ==> simplicial_link {s | s IN c /\ s SUBSET k} v = simplicial_link c v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_SIMPLEX_IN_COMPONENT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S8CU_BOUNDARY_EQ = prove
 (`!(c:(real^N->bool)->bool) k.
     simplicial_complex c /\ k IN components (UNIONS c)
     ==> surface_boundary {s | s IN c /\ s SUBSET k} = surface_boundary c INTER k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN c /\ e SUBSET k /\ ~(e = {})
     ==> {r | (r IN c /\ r SUBSET k) /\ aff_dim r = &2 /\ e SUBSET r} =
         {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r}`
  (LABEL_TAC "same") THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8CU_SIMPLEX_IN_COMPONENT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN {s | s IN c /\ s SUBSET k} /\ aff_dim e = &1 /\
         CARD {r | r IN {s | s IN c /\ s SUBSET k} /\ aff_dim r = &2 /\ e SUBSET r} = 1} =
    {e | e IN {e | e IN c /\ aff_dim e = &1 /\
                   CARD {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = 1} /\
         e SUBSET (k:real^N->bool)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(e:real^N->bool) IN c` THEN
    ASM_CASES_TAC `(e:real^N->bool) SUBSET k` THEN
    ASM_CASES_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "same" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `(e:real^N->bool) IN c`) (CONJ (ASSUME `(e:real^N->bool) SUBSET k`)
         (ASSUME `~(e:real^N->bool = {})`)))]);
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_INTER; IN_ELIM_THM] THEN
  EQ_TAC THENL [MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S8CU_SIMPLEX_IN_COMPONENT THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM SET_TAC[]);;

let MOI_S8CU_EULER_SUM = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c
     ==> complex_euler c =
         sum (components (UNIONS c)) (\k. complex_euler {s | s IN c /\ s SUBSET k})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FEU_EULER_UNIQUE THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`components(UNIONS c:real^N->bool)`; `\k:real^N->bool. k`;
                 `\k. complex_euler {s | s IN c /\ s SUBSET (k:real^N->bool)}`]
    MOI_FEU_EULER_UNIONS) THEN
  REWRITE_TAC[IMAGE_ID; GSYM UNIONS_COMPONENTS] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_FINITE_COMPONENTS THEN ASM_REWRITE_TAC[];
    MESON_TAC[PAIRWISE_DISJOINT_COMPONENTS; pairwise];
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{s | s IN c /\ s SUBSET (k:real^N->bool)}`
      MOI_FEU_EULER_SIMPLICIAL_COMPLEX) THEN
    ASM_SIMP_TAC[MOI_S8CU_SUBCOMPLEX; MOI_S8CU_COMPONENT_UNIONS]]);;

(* The target.                                                               *)

let COMPONENT_COMPLEX = prove
 (MOI_S28_COMPONENT_COMPLEX,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_FINITE_COMPONENTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S8CU_EULER_SUM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `simplicial_complex {s | s IN c /\ s SUBSET (k:real^N->bool)}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_S8CU_SUBCOMPLEX]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SC_FINITE];
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S8CU_LINK_EQ] THEN USE_THEN "lk" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S8CU_COMPONENT_UNIONS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S8CU_BOUNDARY_EQ THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite combinatorial 1-manifolds: simplices of dimension at most 1 (as   *)
(* MOI_FGB_CM1_DIM of pc_moi_fnd_gpb, which is not in this closure), every  *)
(* vertex on exactly two edges (the link is two points), components PL      *)
(* 1-spheres (MOI_S4L_CM1_CIRCLES), line charts, and Euler characteristic 0. *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_PL_SPHERE_0_TWO = prove
 (`!s:real^N->bool. pl_sphere 0 s ==> ?p q. ~(p = q) /\ s = {p,q}`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `&1 simplex (k:real^N->bool)` THEN REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `relative_frontier(k:real^N->bool) = {a,b}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL; AFFINE_INDEPENDENT_2] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
    ASM_SIMP_TAC[SET_RULE `~(p:real^N = q) ==> {p,q} DELETE p = {q} /\ {p,q} DELETE q = {p}`;
                 CONVEX_HULL_SING] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MAP_EVERY EXISTS_TAC [`(f:real^N->real^N) a`; `(f:real^N->real^N) b`] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real^N->real^N)((f:real^N->real^N) a) = a /\ g(f b) = b` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `s = IMAGE (f:real^N->real^N) {a,b}` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[IMAGE_CLAUSES]]]);;

(* A convex subset of a two-point set has dimension at most 0.              *)

let MOI_S8CU_CONVEX_IN_TWO = prove
 (`!s p q:real^N. convex s /\ s SUBSET {p,q} ==> aff_dim s <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `s = {a:real^N}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SING] THEN X_GEN_TAC `b:real^N` THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `segment[a:real^N,b] SUBSET {p,q}` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `convex(s:real^N->bool)` THEN
        REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC THEN SUBGOAL_THEN `FINITE(segment[a:real^N,b])` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:real^N,q}` THEN
          ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
          REWRITE_TAC[FINITE_SEGMENT] THEN ASM_MESON_TAC[]]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_S8CU_CM1_FACTS = prove
 (`!l:(real^N->bool)->bool.
     FINITE l /\ combinatorial_manifold 1 l
     ==> simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
         (!v. {v} IN l ==> CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = 2)`,
  GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))) THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  (* the link of a vertex is two points *)
  SUBGOAL_THEN `!v:real^N. {v} IN l
                ==> ?p q. ~(p = q) /\ UNIONS (simplicial_link l v) = {p,q}`
  (LABEL_TAC "two") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8CU_PL_SPHERE_0_TWO THEN
    USE_THEN "lk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* link simplices are empty or points *)
  SUBGOAL_THEN `!v s':real^N->bool. {v} IN l /\ s' IN simplicial_link l v
                ==> aff_dim s' <= &0`
  (LABEL_TAC "lk0") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "two" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S8CU_CONVEX_IN_TWO THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(s':real^N->bool) IN l` MP_TAC THENL
       [UNDISCH_TAC `(s':real^N->bool) IN simplicial_link l v` THEN
        REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
        ASM_MESON_TAC[MOI_CON_SC_CONVEX]];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (term_match [] `UNIONS (simplicial_link l (v:real^N)) = x`) (concl th))) THEN
      MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> aff_dim s <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_SCF_LINK_OPP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lk0" (MP_TAC o C MATCH_MP (CONJ (ASSUME `{v:real^N} IN l`)
      (ASSUME `(s':real^N->bool) IN simplicial_link l v`))) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  USE_THEN "two" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  (* the link points are the other ends of the edges at v *)
  SUBGOAL_THEN
   `!u:real^N. u IN UNIONS (simplicial_link l v) <=>
               ~(u = v) /\ segment[v,u] IN l`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `u:real^N` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "lk0" (MP_TAC o C MATCH_MP (CONJ (ASSUME `{v:real^N} IN l`)
        (ASSUME `(s':real^N->bool) IN simplicial_link l v`))) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `s' = {u:real^N}` SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(s':real^N->bool) IN l` ASSUME_TAC THENL
         [UNDISCH_TAC `(s':real^N->bool) IN simplicial_link l v` THEN
          REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `convex(s':real^N->bool)` MP_TAC THENL
         [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
        UNDISCH_TAC `aff_dim(s':real^N->bool) <= &0` THEN
        UNDISCH_TAC `(u:real^N) IN s'` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
        X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`{u:real^N,y}`; `s':real^N->bool`] AFF_DIM_SUBSET) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[AFF_DIM_2] THEN ASM_INT_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
      REWRITE_TAC[IN_SING; simplicial_link; IN_ELIM_THM] THEN
      SUBGOAL_THEN `{u:real^N} IN l` ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_S8TB_SEG_ENDS]; ALL_TAC] THEN
      SUBGOAL_THEN `~(v:real^N = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_SING] THEN
      EXISTS_TAC `segment[v:real^N,u]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{e | e IN l /\ aff_dim e = &1 /\ (v:real^N) IN e} =
                {segment[v,p], segment[v,q]}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
        MOI_S4L_K1_EDGE_AT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(u:real^N) IN {p,q}` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (term_match [] `UNIONS (simplicial_link l (v:real^N)) = x`) (concl th))) THEN
        USE_THEN "ends" (fun th -> REWRITE_TAC[th]) THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(e:real^N->bool) IN l` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(~(p:real^N = v) /\ segment[v,p] IN l) /\
                    (~(q:real^N = v) /\ segment[v,q] IN l)` STRIP_ASSUME_TAC THENL
       [USE_THEN "ends" (fun th -> REWRITE_TAC[GSYM th]) THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
          can (term_match [] `UNIONS (simplicial_link l (v:real^N)) = x`) (concl th))) THEN
        REWRITE_TAC[IN_INSERT];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[SEGMENT_EQ; SET_RULE `{a:real^N,b} = {a,c} <=> b = c`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MOI_S8CU_CM1_CIRCLES = prove
 (`!l:(real^N->bool)->bool.
     2 <= dimindex(:N) /\ FINITE l /\ combinatorial_manifold 1 l
     ==> FINITE(components(UNIONS l)) /\
         !j. j IN components(UNIONS l) ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_S8CU_CM1_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_CM1_CIRCLES THEN ASM_REWRITE_TAC[]);;

let MOI_S8CU_CM1_EULER = prove
 (`!l:(real^N->bool)->bool.
     2 <= dimindex(:N) /\ FINITE l /\ combinatorial_manifold 1 l
     ==> complex_euler l = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_S8CU_CM1_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_S8CU_CM1_CIRCLES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S8CU_EULER_SUM] THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `j:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `{s | s IN l /\ s SUBSET (j:real^N->bool)}` COMPLEX_EULER_VALUES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S8CU_SUBCOMPLEX; IN_ELIM_THM] THEN
    ASM_MESON_TAC[INT_ARITH `x <= &1 ==> x <= &2:int`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S8CU_COMPONENT_UNIONS] THEN SIMP_TAC[]);;

let MOI_S8CU_CM1_LINE_CHARTS = prove
 (`!l:(real^N->bool)->bool.
     2 <= dimindex(:N) /\ FINITE l /\ combinatorial_manifold 1 l
     ==> moi_s4l_line_charts (UNIONS l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_S8CU_CM1_CIRCLES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[moi_s4l_line_charts] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ABBREV_TAC `j = connected_component (UNIONS l) (x:real^N)` THEN
  SUBGOAL_THEN `(j:real^N->bool) IN components (UNIONS l)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN j` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS l)) (j:real^N->bool)` MP_TAC THENL
   [EXPAND_TAC "j" THEN MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT THEN
    ASM_REWRITE_TAC[GSYM components];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPEC `j:real^N->bool` MOI_S8TA_SPHERE1_LINE_CHARTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s4l_line_charts] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`u INTER oo:real^N->bool`; `h:real^N->real^1`;
                        `h':real^1->real^N`] THEN
  SUBGOAL_THEN `UNIONS l INTER (u INTER oo) = j INTER (u:real^N->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of domain for surfaces and product charts of a bicollar.      *)
(* An injective continuous image of an open subset of R^2 inside a set with *)
(* 2D charts at all its points is open (local form of MOI_S8TA_EMB_OPEN).   *)
(* With a line chart h of m, (s,t) |-> p(h^-1 s, t) parametrises the         *)
(* bicollar, so p maps open product pieces A x (alpha,beta) to open sets.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_IOD = prove
 (`!(x:real^N->bool) (g:real^2->real^N) w.
     open w /\ g continuous_on w /\
     (!p q. p IN w /\ q IN w /\ g p = g q ==> p = q) /\
     IMAGE g w SUBSET x /\ (!y. y IN IMAGE g w ==> moi_s8ta_emb2 x y)
     ==> open_in (subtopology euclidean x) (IMAGE g w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "emb"))))) THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  USE_THEN "emb" (MP_TAC o SPEC `(g:real^2->real^N) z`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s8ta_emb2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
    (X_CHOOSE_THEN `phi':real^2->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (g:real^2->real^N) {r | r IN w /\ g r IN u}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_EMB_OPEN THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `phi:real^N->real^2`; `phi':real^2->real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `w:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
      EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    SET_TAC[]]);;

let MOI_S8CU_R2_DIMINDEX = prove
 (`!(x:real^N->bool) y. moi_s28_locally_r2 x y ==> 2 <= dimindex(:N)`,
  REWRITE_TAC[moi_s28_locally_r2; homeomorphic; homeomorphism] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^N`; `(:real^2)`] INVARIANCE_OF_DIMENSION) THEN
  REWRITE_TAC[OPEN_UNIV; UNIV_NOT_EMPTY; DIMINDEX_2] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[IN_UNIV]);;

(* Open product pieces of a bicollar.                                         *)

let MOI_S8CU_PRODUCT_OPEN = prove
 (`!(x:real^N->bool) (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q
    (A:real^N->bool) alpha beta.
     moi_s4l_line_charts m /\ moi_s26_bicollar m w p q /\ w SUBSET x /\
     (!y. y IN w ==> moi_s8ta_emb2 x y) /\
     open_in (subtopology euclidean m) A /\ --(&1) <= alpha /\ beta <= &1
     ==> open_in (subtopology euclidean x)
           (IMAGE p (A PCROSS {t:real^1 | alpha < drop t /\ drop t < beta}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(A:real^N->bool) SUBSET m` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x0:real^N`; `t0:real^1`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `moi_s4l_line_charts (m:real^N->bool)` THEN REWRITE_TAC[moi_s4l_line_charts] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^N`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    concl th = `open_in (subtopology euclidean m) (A:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `oa:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `V = IMAGE (h:real^N->real^1) (m INTER u INTER oa)` THEN
  SUBGOAL_THEN `open (V:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^N->real^1) (m INTER u)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h':real^1->real^N`; `m INTER u:real^N->bool`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m INTER u INTER oa = (m INTER u) INTER (oa:real^N->bool)` SUBST1_TAC
    THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. v IN V ==> (h':real^1->real^N) v IN m INTER u INTER oa /\
                                      h (h' v) = v`
  ASSUME_TAC THENL [EXPAND_TAC "V" THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = {z:real^2 | lift(z$1) IN V /\ alpha < z$2 /\ z$2 < beta}` THEN
  SUBGOAL_THEN
   `!z:real^2. z IN W
               ==> pastecart ((h':real^1->real^N) (lift(z$1))) (lift(z$2)) IN
                   m PCROSS interval[--vec 1,vec 1] /\
                   h' (lift(z$1)) IN A`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift((z:real^2)$1)` o check (fun th ->
      can (term_match [] `!v:real^1. v IN V ==> P v`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
                           ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (W:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    SUBGOAL_THEN
     `{z:real^2 | lift(z$1) IN V /\ alpha < z$2 /\ z$2 < beta} =
      {z | (\z:real^2. lift(z$1)) z IN V} INTER {z | z$2 > alpha} INTER
      {z | z$2 < beta}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_2; ARITH];
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT]];
    ALL_TAC] THEN
  ABBREV_TAC `G = \z:real^2. (p:real^(N,1)finite_sum->real^N)
                   (pastecart ((h':real^1->real^N) (lift(z$1))) (lift(z$2)))` THEN
  SUBGOAL_THEN `(G:real^2->real^N) continuous_on W` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    SUBGOAL_THEN
     `(\z:real^2. (p:real^(N,1)finite_sum->real^N)
                  (pastecart ((h':real^1->real^N) (lift(z$1))) (lift(z$2)))) =
      p o (\z. pastecart (h' (lift(z$1))) (lift(z$2)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH] THEN
      SUBGOAL_THEN `(\z:real^2. (h':real^1->real^N) (lift(z$1))) = h' o (\z. lift(z$1))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^N->real^1) (m INTER u)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "W" THEN EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z1 z2:real^2. z1 IN W /\ z2 IN W /\ (G:real^2->real^N) z1 = G z2 ==> z1 = z2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `pastecart ((h':real^1->real^N) (lift((z1:real^2)$1))) (lift((z1:real^2)$2)) =
      pastecart (h' (lift((z2:real^2)$1))) (lift((z2:real^2)$2))`
    MP_TAC THENL
     [MP_TAC(AP_TERM `q:real^N->real^(N,1)finite_sum`
        (ASSUME `(G:real^2->real^N) z1 = G z2`)) THEN
      EXPAND_TAC "G" THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `lift((z1:real^2)$1) IN V /\ lift((z2:real^2)$1) IN V` STRIP_ASSUME_TAC
    THENL [UNDISCH_TAC `(z1:real^2) IN W` THEN UNDISCH_TAC `(z2:real^2) IN W` THEN
           EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
           ALL_TAC] THEN
    SUBGOAL_THEN `lift((z1:real^2)$1) = lift((z2:real^2)$1)` MP_TAC THENL
     [MP_TAC(AP_TERM `h:real^N->real^1`
        (ASSUME `(h':real^1->real^N) (lift((z1:real^2)$1)) = h' (lift((z2:real^2)$1))`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_EQ] THEN DISCH_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (G:real^2->real^N) W` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_IOD THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (G:real^2->real^N) W SUBSET w` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vector[drop((h:real^N->real^1) x0); drop t0]:real^2` THEN
    EXPAND_TAC "G" THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_2; LIFT_DROP] THEN
    SUBGOAL_THEN `(x0:real^N) IN m INTER u INTER oa` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "V" THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; LIFT_DROP] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `(z:real^2) IN W` THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Chart restriction.  The half disc of radius r maps onto the closed upper *)
(* half plane by z |-> z / (r - |z|) (as in HOMEOMORPHIC_BALL_UNIV), which  *)
(* keeps the half plane and 0; so a homeomorphism of an open subset of the  *)
(* polyhedron onto an open subset of H with y |-> 0 gives a half-plane      *)
(* chart, and likewise for plane charts; charts restrict to open subsets.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_SCAL1 = prove
 (`!r n. n < r /\ &0 <= n ==> (r * inv(&1 + inv(r - n) * n)) * inv(r - n) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + inv(r - n) * n = r * inv(r - n)` SUBST1_TAC THENL
   [UNDISCH_TAC `n < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r - n /\ &0 < r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < r - n` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let MOI_S8CU_SCAL2 = prove
 (`!r n. &0 < r /\ &0 <= n ==> (r * inv(&1 + n)) * n < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r * inv(&1 + n)) * n = r * (n / (&1 + n))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < &1 + n`] THEN
  REAL_ARITH_TAC);;

let MOI_S8CU_SCAL3 = prove
 (`!r n. &0 < r /\ &0 <= n ==> inv(r - (r * inv(&1 + n)) * n) * (r * inv(&1 + n)) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r - (r * inv(&1 + n)) * n = r * inv(&1 + n)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 <= n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC);;

let MOI_S8CU_HALF_DISC = prove
 (`!r. &0 < r
       ==> homeomorphism ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r),
                          {z:real^2 | &0 <= z$2})
                         ((\z. inv(r - norm z) % z), (\w. (r * inv(&1 + norm w)) % w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homeomorphism] THEN
  SUBGOAL_THEN
   `!z:real^2. norm z < r
     ==> (r * inv(&1 + norm(inv(r - norm z) % z))) % (inv(r - norm z) % z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < r ==> abs(r - x) = r - x`] THEN
    ASM_SIMP_TAC[MOI_S8CU_SCAL1; NORM_POS_LE; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^2. norm((r * inv(&1 + norm w)) % w) < r /\
               inv(r - norm((r * inv(&1 + norm w)) % w)) % ((r * inv(&1 + norm w)) % w) = w`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`;
                 REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
    ASM_SIMP_TAC[MOI_S8CU_SCAL2; MOI_S8CU_SCAL3; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. &0 <= w$2 ==> &0 <= ((r * inv(&1 + norm w)) % w)$2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
    MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. &0 <= z$2 /\ norm z < r ==> &0 <= (inv(r - norm z) % z)$2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN
    X_GEN_TAC `w:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(r * inv(&1 + norm(w:real^2))) % w` THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,r)` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[IN_BALL_0; REAL_SUB_0; REAL_ARITH `x < r ==> ~(r = x)`] THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    ASM_SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN
    X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `inv(r - norm(z:real^2)) % z` THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SUBGOAL_THEN `lift o (\w:real^2. r * inv(&1 + norm w)) =
                  (\w. r % (lift o inv o (\w. &1 + norm w)) w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID]]);;

let MOI_S8CU_HALF_FROM_LOCAL = prove
 (`!(x:real^N->bool) n (psi:real^N->real^2) psi' y.
     open_in (subtopology euclidean x) n /\ y IN n /\
     homeomorphism (n,IMAGE psi n) (psi,psi') /\
     open_in (subtopology euclidean {z:real^2 | &0 <= z$2}) (IMAGE psi n) /\
     psi y = vec 0
     ==> moi_s28_locally_half x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`IMAGE (psi:real^N->real^2) n`; `{z:real^2 | &0 <= z$2}`]
    OPEN_IN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `vec 0:real^2`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{z:real^2 | &0 <= z$2} INTER ball(vec 0,r) =
                IMAGE (psi:real^N->real^2) n INTER ball(vec 0,r)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_half] THEN
  EXISTS_TAC `IMAGE (psi':real^2->real^N) ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r))` THEN
  EXISTS_TAC `(\z:real^2. inv(r - norm z) % z) o (psi:real^N->real^2)` THEN
  EXISTS_TAC `(psi':real^2->real^N) o (\w:real^2. (r * inv(&1 + norm w)) % w)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`psi:real^N->real^2`; `IMAGE (psi:real^N->real^2) n`] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL; VEC_COMPONENT; REAL_LE_REFL] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `{z:real^2 | &0 <= z$2} INTER ball(vec 0,r)` THEN
    ASM_SIMP_TAC[MOI_S8CU_HALF_DISC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`n:real^N->bool`; `IMAGE (psi:real^N->real^2) n`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[o_THM; NORM_0; VECTOR_MUL_RZERO]]);;

let MOI_S8CU_R2_FROM_LOCAL = prove
 (`!(x:real^N->bool) n (psi:real^N->real^2) psi' y.
     open_in (subtopology euclidean x) n /\ y IN n /\
     homeomorphism (n,IMAGE psi n) (psi,psi') /\ open (IMAGE psi n)
     ==> moi_s28_locally_r2 x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  UNDISCH_TAC `open (IMAGE (psi:real^N->real^2) n)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:real^N->real^2) y`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  EXISTS_TAC `IMAGE (psi':real^2->real^N) (ball((psi:real^N->real^2) y,r))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`psi:real^N->real^2`; `IMAGE (psi:real^N->real^2) n`] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ball((psi:real^N->real^2) y,r) = IMAGE psi n INTER ball(psi y,r)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(psi:real^N->real^2) y` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`; `:2`,`:N`; `:2`,`:P`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `ball((psi:real^N->real^2) y,r)` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`psi:real^N->real^2`; `psi':real^2->real^N`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:real^N->real^2) n`; `n:real^N->bool`] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

let MOI_S8CU_R2_RESTRICT = prove
 (`!(x:real^N->bool) x' v y.
     moi_s28_locally_r2 x y /\ open_in (subtopology euclidean x) v /\ y IN v /\
     v SUBSET x' /\ x' SUBSET x
     ==> moi_s28_locally_r2 x' y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[GSYM moi_s28_locally_r2] THEN
  UNDISCH_TAC `(u:real^N->bool) homeomorphic (:real^2)` THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^N->real^2` (X_CHOOSE_TAC `phi':real^2->real^N`)) THEN
  MATCH_MP_TAC MOI_S8CU_R2_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`u INTER v:real^N->bool`; `phi:real^N->real^2`;
                        `phi':real^2->real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN SET_TAC[];
    MP_TAC(ISPECL [`phi:real^N->real^2`; `phi':real^2->real^N`; `u:real^N->bool`;
                   `(:real^2)`; `u INTER v:real^N->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_S8TB_OPEN_IN_CHART THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S8CU_HALF_RESTRICT = prove
 (`!(x:real^N->bool) x' v y.
     moi_s28_locally_half x y /\ open_in (subtopology euclidean x) v /\ y IN v /\
     v SUBSET x' /\ x' SUBSET x
     ==> moi_s28_locally_half x' y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `k:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM moi_s28_locally_half] THEN
  MATCH_MP_TAC MOI_S8CU_HALF_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`u INTER v:real^N->bool`; `h:real^N->real^2`;
                        `k:real^2->real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `{z:real^2 | &0 <= z$2}`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_S8TB_OPEN_IN_CHART THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Half-plane charts at the levels of a bicollar.  If near the level t = a  *)
(* a set E is the product piece on one side of the level (sg = 1: t <= a;   *)
(* sg = -1: t >= a), then the points of the level have half-plane charts in *)
(* E: y = p(x1,t1) |-> (h x1 - h x0, sg (a - t1)) with a line chart h.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_OPEN_IN_SUBSET_INTER = prove
 (`!(E:real^N->bool) x o1.
     E SUBSET x /\ open_in (subtopology euclidean x) o1
     ==> open_in (subtopology euclidean E) (E INTER o1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S8CU_COLLAR_HALF = prove
 (`!(x:real^N->bool) (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q
    (E:real^N->bool) x0 a alpha beta sg.
     moi_s4l_line_charts m /\ moi_s26_bicollar m w p q /\ w SUBSET x /\
     (!y. y IN w ==> moi_s8ta_emb2 x y) /\
     x0 IN m /\ --(&1) <= alpha /\ alpha < a /\ a < beta /\ beta <= &1 /\
     sg * sg = &1 /\ E SUBSET x /\
     E INTER IMAGE p (m PCROSS {t:real^1 | alpha < drop t /\ drop t < beta}) =
     IMAGE p (m PCROSS {t:real^1 | alpha < drop t /\ drop t < beta /\
                                   &0 <= sg * (a - drop t)})
     ==> moi_s28_locally_half E (p (pastecart x0 (lift a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s26_bicollar]) THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(SPEC `x0:real^N` (GEN_REWRITE_RULE I [moi_s4l_line_charts]
    (ASSUME `moi_s4l_line_charts (m:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `J = {t:real^1 | alpha < drop t /\ drop t < beta}` THEN
  ABBREV_TAC `Jh = {t:real^1 | alpha < drop t /\ drop t < beta /\ &0 <= sg * (a - drop t)}` THEN
  ABBREV_TAC `s0 = drop((h:real^N->real^1) x0)` THEN
  ABBREV_TAC `V = IMAGE (h:real^N->real^1) (m INTER u)` THEN
  SUBGOAL_THEN `!t:real^1. t IN J ==> t IN interval[--vec 1,vec 1]` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Jh:real^1->bool) SUBSET J` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["J"; "Jh"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^1. t IN Jh ==> t IN J` (LABEL_TAC "JhJ") THENL
   [UNDISCH_TAC `(Jh:real^1->bool) SUBSET J` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(x1:real^N) (t1:real^1). x1 IN m INTER u /\ t1 IN J
      ==> pastecart x1 t1 IN m PCROSS interval[--vec 1,vec 1]`
  (LABEL_TAC "inI") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x1:real^N) IN m INTER u` THEN SET_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t:real^1. t IN J ==> t IN interval[--vec 1,vec 1]`) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(x1:real^N) (t1:real^1) x2 t2. x1 IN m /\ t1 IN J /\ x2 IN m /\ t2 IN J /\
                  (p:real^(N,1)finite_sum->real^N) (pastecart x1 t1) = p (pastecart x2 t2)
                  ==> x1 = x2 /\ t1 = t2`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM PASTECART_INJ] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `q:real^N->real^(N,1)finite_sum`) THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  ABBREV_TAC `N = IMAGE (p:real^(N,1)finite_sum->real^N) ((m INTER u) PCROSS Jh)` THEN
  ABBREV_TAC
   `psi = \y:real^N.
      (drop((h:real^N->real^1) (fstcart((q:real^N->real^(N,1)finite_sum) y))) - s0) %
      basis 1 +
      (sg * (a - drop(sndcart(q y)))) % basis 2:real^2` THEN
  ABBREV_TAC
   `phi = \v:real^2. (p:real^(N,1)finite_sum->real^N)
            (pastecart ((h':real^1->real^N) (lift(v$1 + s0))) (lift(a - sg * v$2)))` THEN
  (* psi on the parametrised points *)
  SUBGOAL_THEN
   `!(x1:real^N) (t1:real^1). x1 IN m INTER u /\ t1 IN J
            ==> (psi:real^N->real^2) ((p:real^(N,1)finite_sum->real^N) (pastecart x1 t1))$1 =
                drop((h:real^N->real^1) x1) - s0 /\
                psi (p(pastecart x1 t1))$2 = sg * (a - drop t1)`
  (LABEL_TAC "psival") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "psi" THEN
    SUBGOAL_THEN
     `(q:real^N->real^(N,1)finite_sum) ((p:real^(N,1)finite_sum->real^N) (pastecart (x1:real^N) (t1:real^1))) = pastecart x1 t1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^2. lift(v$1 + s0) IN V
               ==> (h':real^1->real^N) (lift(v$1 + s0)) IN m INTER u /\
                   drop(h(h'(lift(v$1 + s0)))) - s0 = v$1`
  (LABEL_TAC "hinv") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `lift((v:real^2)$1 + s0) IN V`)]) THEN
      REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_HALF_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `psi:real^N->real^2`; `phi:real^2->real^N`] THEN
  (* phi inverts psi on N *)
  SUBGOAL_THEN `!y:real^N. y IN N ==> (phi:real^2->real^N) (psi y) = y` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `t1:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t1:real^1) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "psival" (MP_TAC o SPECL [`x1:real^N`; `t1:real^1`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "phi" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `(x - s) + s = x:real`; LIFT_DROP] THEN
    SUBGOAL_THEN `a - sg * sg * (a - drop(t1:real^1)) = drop t1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN AP_TERM_TAC THEN REWRITE_TAC[PASTECART_INJ] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* the image of psi *)
  SUBGOAL_THEN
   `IMAGE (psi:real^N->real^2) N =
    {z:real^2 | &0 <= z$2} INTER
    ({v | (\v:real^2. lift(v$1 + s0)) v IN V} INTER
     {v | (\v:real^2. lift(a - sg * v$2)) v IN interval(lift alpha,lift beta)})`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `v:real^2` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN EQ_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(t1:real^1) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "psival" (MP_TAC o SPECL [`x1:real^N`; `t1:real^1`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `(x - s) + s = x:real`; LIFT_DROP] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ARITH `a - (a - t) = t:real`] THEN
      UNDISCH_TAC `(t1:real^1) IN Jh` THEN EXPAND_TAC "Jh" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "V" THEN ASM SET_TAC[];
      STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(phi:real^2->real^N) v` THEN
      USE_THEN "hinv" (MP_TAC o C MATCH_MP (ASSUME `lift((v:real^2)$1 + s0) IN V`)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `lift(a - sg * (v:real^2)$2) IN Jh` ASSUME_TAC THENL
       [EXPAND_TAC "Jh" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
        ASM_REWRITE_TAC[REAL_ARITH `a - (a - s * x) = s * x:real`; REAL_MUL_ASSOC;
                        REAL_MUL_LID];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        EXPAND_TAC "N" THEN EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS]] THEN
      EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN
      USE_THEN "psival" (MP_TAC o SPECL [`(h':real^1->real^N) (lift((v:real^2)$1 + s0))`;
                                         `lift(a - sg * (v:real^2)$2)`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `a - (a - s * x) = s * x:real`; REAL_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `N SUBSET (w:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS interval[--vec 1,vec 1]) = w`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "inI" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "JhJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN N ==> fstcart((q:real^N->real^(N,1)finite_sum) y) IN m INTER u`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `t1:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(q:real^N->real^(N,1)finite_sum) ((p:real^(N,1)finite_sum->real^N) (pastecart x1 t1)) =
      pastecart x1 t1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "inI" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "JhJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[FSTCART_PASTECART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^N->real^2) continuous_on N` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y:real^N. fstcart((q:real^N->real^(N,1)finite_sum) y)) continuous_on N /\
                  (\y:real^N. sndcart((q:real^N->real^(N,1)finite_sum) y)) continuous_on N`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_CMUL; LIFT_DROP] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SUBGOAL_THEN `(\y:real^N. (h:real^N->real^1) (fstcart((q:real^N->real^(N,1)finite_sum) y))) =
                    h o (\y. fstcart(q y))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m INTER u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^N) continuous_on IMAGE (psi:real^N->real^2) N` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!v:real^2. v IN IMAGE (psi:real^N->real^2) N
                 ==> lift(v$1 + s0) IN V /\ lift(a - sg * v$2) IN J`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "phi" THEN
    SUBGOAL_THEN
     `(\v:real^2. (p:real^(N,1)finite_sum->real^N)
          (pastecart ((h':real^1->real^N) (lift(v$1 + s0))) (lift(a - sg * v$2)))) =
      p o (\v. pastecart (h' (lift(v$1 + s0))) (lift(a - sg * v$2)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\v:real^2. (h':real^1->real^N) (lift(v$1 + s0))) =
                      h' o (\v. lift(v$1 + s0))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          SIMP_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^1->bool` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
          ASM_SIMP_TAC[]];
        REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^2` o check (fun th ->
        can (term_match [] `!v:real^2. v IN IMAGE (psi:real^N->real^2) N ==> P v`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "hinv" (MP_TAC o C MATCH_MP (ASSUME `lift((v:real^2)$1 + s0) IN V`)) THEN
        SET_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* N open in E *)
    SUBGOAL_THEN
     `N = (E:real^N->bool) INTER IMAGE (p:real^(N,1)finite_sum->real^N)
                                       ((m INTER u) PCROSS J)`
    SUBST1_TAC THENL
     [EXPAND_TAC "N" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
      REWRITE_TAC[IN_INTER] THEN EQ_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
        DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1`
          STRIP_ASSUME_TAC)) THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        SUBGOAL_THEN `(y:real^N) IN IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS Jh)` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC
         `E INTER IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS J) =
          IMAGE p (m PCROSS Jh)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
        STRIP_TAC THEN
        SUBGOAL_THEN `(y:real^N) IN IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS Jh)` MP_TAC THENL
         [UNDISCH_TAC
           `E INTER IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS J) =
            IMAGE p (m PCROSS Jh)` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y:real^N) IN IMAGE (p:real^(N,1)finite_sum->real^N) ((m INTER u) PCROSS J)` THEN
          MATCH_MP_TAC(SET_RULE `!s t (f:real^(N,1)finite_sum->real^N) x.
                                   s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_INTER] THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(y:real^N) IN IMAGE (p:real^(N,1)finite_sum->real^N) ((m INTER u) PCROSS J)` THEN
        REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1`
          STRIP_ASSUME_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `x2:real^N` (X_CHOOSE_THEN `t2:real^1`
          STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`x1:real^N`; `t1:real^1`] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "inj" (MP_TAC o SPECL [`x1:real^N`; `t1:real^1`; `x2:real^N`;
                                        `t2:real^1`]) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S8CU_OPEN_IN_SUBSET_INTER THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN
    MATCH_MP_TAC MOI_S8CU_PRODUCT_OPEN THEN
    MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `w:real^N->bool`;
                          `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    ASM_REWRITE_TAC[];
    (* the point is in N *)
    EXPAND_TAC "N" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Jh" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_LE_REFL];
    (* homeomorphism *)
    REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC;
      ASM SET_TAC[];
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    (* open in H *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN GEN_TAC THEN
    REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_CMUL] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ADD) THEN TRY(MATCH_MP_TAC CONTINUOUS_SUB) THEN
    TRY(MATCH_MP_TAC CONTINUOUS_CMUL) THEN
    SIMP_TAC[CONTINUOUS_CONST; CONTINUOUS_CMUL; CONTINUOUS_AT_LIFT_COMPONENT;
             DIMINDEX_2; ARITH];
    (* the point maps to 0 *)
    USE_THEN "psival" (MP_TAC o SPECL [`x0:real^N`; `lift a`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "J" THEN
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Euler characteristic of products |l| x relint g as valuations (cells     *)
(* relint s x relint g, as MOI_FEU_EULER_SIMPLICIAL_COMPLEX): chi(l) times   *)
(* (-1)^dim g; hence |l| x [a,b] and |l| x {a} have chi(l).                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_EULER_PCROSS = prove
 (`!(c:(real^N->bool)->bool) (g:real^1->bool).
     simplicial_complex c /\ polytope g /\ ~(g = {})
     ==> moi_feu_euler (UNIONS c PCROSS relative_interior g)
                       (complex_euler c * (-- &1) pow (num_of_int(aff_dim g)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM; GSYM SUM_RMUL] THEN
  SUBGOAL_THEN
   `UNIONS c PCROSS relative_interior g =
    UNIONS (IMAGE (\s:real^N->bool. relative_interior s PCROSS
                                    relative_interior (g:real^1->bool))
                  {s | s IN c /\ ~(s = {})})`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
      [MATCH_MP MOI_FEU_UNIONS_RELATIVE_INTERIORS th]) THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    REWRITE_TAC[IN_ELIM_THM; DISJOINT_PCROSS] THEN REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[DISJOINT] THEN
    MATCH_MP_TAC SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FEU_EULER_RELINT_PCROSS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]]);;

let MOI_S8CU_EULER_LEVEL = prove
 (`!(c:(real^N->bool)->bool) a.
     simplicial_complex c
     ==> moi_feu_euler (UNIONS c PCROSS {lift a}) (complex_euler c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{lift a}`] MOI_S8CU_EULER_PCROSS) THEN
  ASM_REWRITE_TAC[POLYTOPE_SING; NOT_INSERT_EMPTY; RELATIVE_INTERIOR_SING;
                  AFF_DIM_SING; NUM_OF_INT_OF_NUM; real_pow; REAL_MUL_RID]);;

let MOI_S8CU_EULER_SLAB = prove
 (`!(c:(real^N->bool)->bool) a b.
     simplicial_complex c /\ a < b
     ==> moi_feu_euler (UNIONS c PCROSS {t:real^1 | a <= drop t /\ drop t <= b})
                       (complex_euler c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior(interval[lift a,lift b]) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `interval[lift a,lift b]`]
    MOI_S8CU_EULER_PCROSS) THEN
  ASM_SIMP_TAC[POLYTOPE_INTERVAL; INTERVAL_NE_EMPTY_1; LIFT_DROP; REAL_LT_IMP_LE;
               RELATIVE_INTERIOR_NONEMPTY_INTERIOR; AFF_DIM_NONEMPTY_INTERIOR;
               DIMINDEX_1; NUM_OF_INT_OF_NUM; INTERIOR_INTERVAL; REAL_POW_1] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `{t:real^1 | a <= drop t /\ drop t <= b} =
    ({lift a} UNION interval(lift a,lift b)) UNION {lift b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PCROSS_UNION] THEN
  SUBGOAL_THEN `complex_euler (c:(real^N->bool)->bool) =
                (complex_euler c + complex_euler c * -- &1) + complex_euler c`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S8CU_EULER_LEVEL];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[DISJOINT_PCROSS] THEN DISJ2_TAC THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[MOI_S8CU_EULER_LEVEL];
    REWRITE_TAC[GSYM PCROSS_UNION; DISJOINT_PCROSS] THEN DISJ2_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY;
                IN_INTERVAL_1; LIFT_DROP; IN_UNION] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Compact pieces of a bicollar: the image of |l| x J under the bicollar    *)
(* (J a polytope in [-1,1]) is a compact polyhedron PL homeomorphic to      *)
(* |l| x J, so it carries the valuation of |l| x J                         *)
(* (MOI_FEU_PL_HOMEOMORPHIC_EULER on a triangulation).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_SLAB_INTERVAL = prove
 (`!a b. {t:real^1 | a <= drop t /\ drop t <= b} = interval[lift a,lift b]`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP]);;

let MOI_S8CU_PCROSS_POLYHEDRON = prove
 (`!(l:(real^N->bool)->bool) (J:real^1->bool).
     simplicial_complex l /\ polytope J
     ==> pl_polyhedron (UNIONS l PCROSS J) /\ compact (UNIONS l PCROSS J)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{s PCROSS (J:real^1->bool) | (s:real^N->bool) IN l}` THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[MOI_SCF_SC_FINITE];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC POLYTOPE_PCROSS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]];
    MATCH_MP_TAC COMPACT_PCROSS THEN ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[MOI_SCF_SC_FINITE; MOI_CON_SC_COMPACT]]);;

let MOI_S8CU_COLLAR_PIECE = prove
 (`!(l:(real^N->bool)->bool) w (p:real^(N,1)finite_sum->real^N) q (J:real^1->bool) v.
     simplicial_complex l /\ moi_s26_bicollar (UNIONS l) w p q /\
     polytope J /\ J SUBSET interval[--vec 1,vec 1] /\
     moi_feu_euler (UNIONS l PCROSS J) v
     ==> compact (IMAGE p (UNIONS l PCROSS J)) /\
         pl_polyhedron (IMAGE p (UNIONS l PCROSS J)) /\
         moi_feu_euler (IMAGE p (UNIONS l PCROSS J)) v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `J:real^1->bool`] MOI_S8CU_PCROSS_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool) SUBSET
                UNIONS l PCROSS interval[--vec 1,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool)) (p:real^(N,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (l:(real^N->bool)->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool),IMAGE (p:real^(N,1)finite_sum->real^N)
                                               (UNIONS l PCROSS J)) (p,q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`UNIONS (l:(real^N->bool)->bool) PCROSS interval[--vec 1:real^1,vec 1]`;
                          `w:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (p:real^(N,1)finite_sum->real^N) (UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] o
    check (fun th -> concl th = `pl_polyhedron (IMAGE (p:real^(N,1)finite_sum->real^N)
                                     (UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool)))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `complex_euler (tt:(real^N->bool)->bool) = v` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC(INST_TYPE [`:(N,1)finite_sum`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`UNIONS (l:(real^N->bool)->bool) PCROSS (J:real^1->bool)`;
                          `p:real^(N,1)finite_sum->real^N`;
                          `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Removing an open piece O = S minus L of a polyhedron (S, L compact       *)
(* polyhedra, O open in |c|): after refining c so that S and L are unions   *)
(* of simplices (SIMPLICIAL_COMPLEX_REFINE_POLYTOPES), the simplices        *)
(* missing O form a subcomplex whose polyhedron is |c| minus O (a simplex   *)
(* whose relative interior met O and its complement would meet L, hence lie *)
(* in L).                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_PL_POLYHEDRON_COMPACT = prove
 (`!s:real^N->bool. pl_polyhedron s ==> compact s`,
  REWRITE_TAC[pl_polyhedron] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[POLYTOPE_IMP_COMPACT]);;

let MOI_S8CU_REMOVE_OPEN = prove
 (`!(c:(real^N->bool)->bool) S L.
     simplicial_complex c /\ pl_polyhedron S /\ pl_polyhedron L /\
     L SUBSET S /\ S SUBSET UNIONS c /\
     open_in (subtopology euclidean (UNIONS c)) (S DIFF L)
     ==> ?e. simplicial_complex e /\ UNIONS e = UNIONS c DIFF (S DIFF L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(GEN_REWRITE_RULE I [pl_polyhedron]
    (ASSUME `pl_polyhedron (S:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(GEN_REWRITE_RULE I [pl_polyhedron]
    (ASSUME `pl_polyhedron (L:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P UNION Q:(real^N->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^N. z IN L ==> ?r. r IN t /\ r SUBSET L /\ z IN r`
  (LABEL_TAC "Lcov") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^N->bool. k IN Q /\ z IN k` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (fun th ->
      can (term_match [] `!k:real^N->bool. k IN P UNION Q ==> ?f. f SUBSET t /\ k = UNIONS f`)
          (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:real^N->bool. r IN f /\ z IN r` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{s | s IN t /\ s SUBSET UNIONS c DIFF (S DIFF L:real^N->bool)}` THEN
  ASM_SIMP_TAC[MOI_S8CU_SUBCOMPLEX] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_S8TA_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN]
    (ASSUME `open_in (subtopology euclidean (UNIONS c)) (S DIFF L:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC) THEN
  (* the relative interior misses S DIFF L *)
  SUBGOAL_THEN `relative_interior s INTER (S DIFF L:real^N->bool) = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `relative_interior s INTER (L:real^N->bool) = {}` THENL
     [MP_TAC(ISPECL [`relative_interior s:real^N->bool`; `UNIONS c DIFF (L:real^N->bool)`;
                     `g1:real^N->bool`; `(:real^N) DIFF S`] MOI_S8TB_SIDE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[MOI_CON_SC_CONVEX];
          MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
          ASM_REWRITE_TAC[];
          REWRITE_TAC[GSYM closed] THEN
          ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_S8CU_PL_POLYHEDRON_COMPACT];
          ASM SET_TAC[];
          ASM SET_TAC[];
          ASM SET_TAC[]];
        MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]];
      FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      USE_THEN "Lcov" (MP_TAC o SPEC `z:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `z:real^N`] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `~(relative_interior s INTER (S DIFF L:real^N->bool) = {})` THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* hence s misses S DIFF L, which is open in |c| *)
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN g1` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `open(g1:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN closure(relative_interior s)` MP_TAC THENL
   [SUBGOAL_THEN `closure(relative_interior s) = (s:real^N->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure(s:real^N->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN ASM_MESON_TAC[MOI_CON_SC_CONVEX];
        MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[MOI_SCF_SC_CLOSED]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^N) IN g1` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(y:real^N,r) SUBSET g1` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* STRIP_REMOVE.  e = the simplices of a refinement of c missing the open   *)
(* strip; |e| has plane or half-plane charts (charts of c off the closed    *)
(* strip, MOI_S8CU_COLLAR_HALF at the levels), so SURF_LOCAL makes e a      *)
(* combinatorial surface whose boundary is that of c plus the two levels;   *)
(* chi by valuations (the closed strip and the levels have chi(l) = 0).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_BICOLLAR_SETS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q A B.
     moi_s26_bicollar m w p q /\
     A SUBSET interval[--vec 1,vec 1] /\ B SUBSET interval[--vec 1,vec 1]
     ==> IMAGE p (m PCROSS A) DIFF IMAGE p (m PCROSS B) = IMAGE p (m PCROSS (A DIFF B)) /\
         IMAGE p (m PCROSS A) INTER IMAGE p (m PCROSS B) =
         IMAGE p (m PCROSS (A INTER B)) /\
         IMAGE p (m PCROSS A) UNION IMAGE p (m PCROSS B) =
         IMAGE p (m PCROSS (A UNION B)) /\
         IMAGE p (m PCROSS A) SUBSET w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(m:real^N->bool) PCROSS (A:real^1->bool) SUBSET m PCROSS interval[--vec 1,vec 1] /\
    m PCROSS (B:real^1->bool) SUBSET m PCROSS interval[--vec 1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PCROSS_DIFF; PCROSS_INTER; PCROSS_UNION] THEN
  REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

let MOI_S8CU_STRIP_INTERVALS = prove
 (`!a b. --(&1) < a /\ a < b /\ b < &1
         ==> {x:real^1 | a < drop x /\ drop x < b} =
             {t | a <= drop t /\ drop t <= b} DIFF ({lift a} UNION {lift b}) /\
             {t:real^1 | --(&1) < drop t /\ drop t < b} DIFF {x | a < drop x /\ drop x < b} =
             {t | --(&1) < drop t /\ drop t < b /\ &0 <= &1 * (a - drop t)} /\
             {t:real^1 | a < drop t /\ drop t < &1} DIFF {x | a < drop x /\ drop x < b} =
             {t | a < drop t /\ drop t < &1 /\ &0 <= -- &1 * (b - drop t)} /\
             {t:real^1 | a <= drop t /\ drop t <= b} SUBSET interval[--vec 1,vec 1] /\
             {t:real^1 | --(&1) < drop t /\ drop t < b} SUBSET interval[--vec 1,vec 1] /\
             {t:real^1 | a < drop t /\ drop t < &1} SUBSET interval[--vec 1,vec 1] /\
             {x:real^1 | a < drop x /\ drop x < b} SUBSET interval[--vec 1,vec 1] /\
             {lift a} SUBSET interval[--vec 1,vec 1] /\
             {lift b} SUBSET interval[--vec 1,vec 1] /\
             DISJOINT {lift a} {lift b}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_DIFF; IN_UNION; IN_SING; IN_ELIM_THM; IN_INTERVAL_1;
              DROP_NEG; DROP_VEC; DISJOINT; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S8CU_R2_SUPER = prove
 (`!(x:real^N->bool) x' y.
     moi_s28_locally_r2 x' y /\ open_in (subtopology euclidean x) x'
     ==> moi_s28_locally_r2 x y`,
  REWRITE_TAC[moi_s28_locally_r2] THEN MESON_TAC[OPEN_IN_TRANS]);;

(* The target.                                                               *)

let STRIP_REMOVE = prove
 (MOI_S28_STRIP_REMOVE,
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                       `q:real^N->real^(N,1)finite_sum`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[moi_s26_strip; moi_s26_level] THEN
  ASM_CASES_TAC `UNIONS l:real^N->bool = {}` THENL
   [EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES; DIFF_EMPTY; UNION_EMPTY];
    ALL_TAC] THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP SURF_CHARTS (CONJ (ASSUME `FINITE (c:(real^N->bool)->bool)`)
    (ASSUME `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
    (K ALL_TAC))) THEN
  SUBGOAL_THEN `!y:real^N. y IN w ==> moi_s28_locally_r2 (UNIONS c) y` (LABEL_TAC "Rw") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN w ==> moi_s8ta_emb2 (UNIONS c) y` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S8TA_EMB2_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `y0:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(UNIONS l:real^N->bool = {})`)) THEN
    MATCH_MP_TAC MOI_S8CU_R2_DIMINDEX THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `y0:real^N`] THEN
    USE_THEN "Rw" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`; `w:real^N->bool`]
      INTERIOR_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_S8CU_CM1_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s4l_line_charts (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CM1_LINE_CHARTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (l:(real^N->bool)->bool) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CM1_EULER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`] MOI_S8CU_STRIP_INTERVALS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `m = UNIONS l:real^N->bool` THEN
  ABBREV_TAC `S = IMAGE (p:real^(N,1)finite_sum->real^N)
                        (m PCROSS {t:real^1 | a <= drop t /\ drop t <= b})` THEN
  ABBREV_TAC `La = IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift a})` THEN
  ABBREV_TAC `Lb = IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift b})` THEN
  ABBREV_TAC `St = IMAGE (p:real^(N,1)finite_sum->real^N)
                         (m PCROSS {x:real^1 | a < drop x /\ drop x < b})` THEN
  (* set facts *)
  SUBGOAL_THEN `S DIFF (La UNION Lb:real^N->bool) = St /\ La INTER Lb = {} /\
                La UNION Lb SUBSET S /\ S SUBSET w /\ w SUBSET UNIONS c /\ St SUBSET S`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{lift a} UNION {lift b} SUBSET interval[--vec 1:real^1,vec 1]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{t:real^1 | a <= drop t /\ drop t <= b}`; `{lift a} UNION {lift b}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`; `{lift a}`; `{lift b}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `{x:real^1 | a < drop x /\ drop x < b} =
                             {t | a <= drop t /\ drop t <= b} DIFF ({lift a} UNION {lift b})`)] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT {lift a} {lift b}` THEN REWRITE_TAC[DISJOINT] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `La UNION Lb SUBSET (S:real^N->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_SING;
                  IN_ELIM_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `w SUBSET UNIONS c DIFF surface_boundary (c:(real^N->bool)->bool)` THEN
      SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (term_match [] `S DIFF IMAGE (p:real^(N,1)finite_sum->real^N) x = St`)
            (concl th))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the strip is open *)
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (St:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c))
                    (IMAGE (p:real^(N,1)finite_sum->real^N)
                           (m PCROSS {x:real^1 | a < drop x /\ drop x < b}))`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_S8CU_PRODUCT_OPEN THEN
      MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `w:real^N->bool`;
                            `q:real^N->real^(N,1)finite_sum`] THEN
      ASM_REWRITE_TAC[OPEN_IN_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* compact pieces and their Euler characteristics *)
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `interval[lift a,lift b]`; `complex_euler (l:(real^N->bool)->bool)`]
    MOI_S8CU_COLLAR_PIECE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]; REWRITE_TAC[POLYTOPE_INTERVAL];
      REWRITE_TAC[GSYM MOI_S8CU_SLAB_INTERVAL] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM MOI_S8CU_SLAB_INTERVAL] THEN MATCH_MP_TAC MOI_S8CU_EULER_SLAB THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[GSYM MOI_S8CU_SLAB_INTERVAL] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `{lift a}`; `complex_euler (l:(real^N->bool)->bool)`]
    MOI_S8CU_COLLAR_PIECE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]; REWRITE_TAC[POLYTOPE_SING];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S8CU_EULER_LEVEL THEN FIRST_ASSUM ACCEPT_TAC];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `{lift b}`; `complex_euler (l:(real^N->bool)->bool)`]
    MOI_S8CU_COLLAR_PIECE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]; REWRITE_TAC[POLYTOPE_SING];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S8CU_EULER_LEVEL THEN FIRST_ASSUM ACCEPT_TAC];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  (* the subcomplex e *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S:real^N->bool`; `La UNION Lb:real^N->bool`]
    MOI_S8CU_REMOVE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_UNION] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS e = UNIONS c DIFF (St:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (UNIONS c DIFF S:real^N->bool) /\
                UNIONS c DIFF S SUBSET UNIONS (e:(real^N->bool)->bool) /\
                UNIONS e SUBSET UNIONS (c:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `St SUBSET (S:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS e)) (UNIONS c DIFF S:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* half charts at the levels *)
  SUBGOAL_THEN `!y:real^N. y IN La UNION Lb ==> moi_s28_locally_half (UNIONS e) y`
  (LABEL_TAC "hlev") THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN La` THEN EXPAND_TAC "La" THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `t0:real^1`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_COLLAR_HALF THEN
      MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `m:real^N->bool`; `w:real^N->bool`;
                            `q:real^N->real^(N,1)finite_sum`; `-- &1`; `b:real`; `&1`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                     `q:real^N->real^(N,1)finite_sum`;
                     `{t:real^1 | --(&1) < drop t /\ drop t < b}`;
                     `{x:real^1 | a < drop x /\ drop x < b}`] MOI_S8CU_BICOLLAR_SETS) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_LID] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                     (m PCROSS {t | --(&1) < drop t /\ drop t < b}) SUBSET w` THEN
      UNDISCH_TAC `w SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                     (m PCROSS {t | --(&1) < drop t /\ drop t < b}) DIFF St =
                   IMAGE p (m PCROSS {t | --(&1) < drop t /\ drop t < b /\
                                          &0 <= a - drop t})` THEN
      SET_TAC[];
      UNDISCH_TAC `(y:real^N) IN Lb` THEN EXPAND_TAC "Lb" THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `t0:real^1`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_COLLAR_HALF THEN
      MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `m:real^N->bool`; `w:real^N->bool`;
                            `q:real^N->real^(N,1)finite_sum`; `a:real`; `&1`; `-- &1`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                     `q:real^N->real^(N,1)finite_sum`;
                     `{t:real^1 | a < drop t /\ drop t < &1}`;
                     `{x:real^1 | a < drop x /\ drop x < b}`] MOI_S8CU_BICOLLAR_SETS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                     (m PCROSS {t | a < drop t /\ drop t < &1}) SUBSET w` THEN
      UNDISCH_TAC `w SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                     (m PCROSS {t | a < drop t /\ drop t < &1}) DIFF St =
                   IMAGE p (m PCROSS {t | a < drop t /\ drop t < &1 /\
                                          &0 <= -- &1 * (b - drop t)})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* charts everywhere on |e| *)
  SUBGOAL_THEN
   `!y:real^N. y IN UNIONS e
               ==> moi_s28_locally_r2 (UNIONS e) y \/ moi_s28_locally_half (UNIONS e) y`
  (LABEL_TAC "che") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN S` THENL
     [DISJ2_TAC THEN USE_THEN "hlev" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS e` THEN UNDISCH_TAC `(y:real^N) IN S` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `S DIFF (La UNION Lb:real^N->bool) = St` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS c DIFF S` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS e SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS e` THEN UNDISCH_TAC `~((y:real^N) IN S)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^N) IN surface_boundary c` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `UNIONS c DIFF S:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "C2" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN surface_boundary c`)) THEN
      SIMP_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `UNIONS c DIFF S:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "C1" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS c DIFF S` THEN
      UNDISCH_TAC `~((y:real^N) IN surface_boundary c)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `e:(real^N->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN USE_THEN "che" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  EXISTS_TAC `e:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* chi by valuations *)
  SUBGOAL_THEN `moi_feu_euler (La UNION Lb:real^N->bool) (&0 + &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN ASM_REWRITE_TAC[DISJOINT];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_feu_euler (St:real^N->bool) (&0 - (&0 + &0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `S DIFF (La UNION Lb:real^N->bool) = St`)) THEN
    MATCH_MP_TAC MOI_FEU_EULER_DIFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_feu_euler (UNIONS e:real^N->bool) (complex_euler e) /\
                moi_feu_euler (UNIONS c:real^N->bool) (complex_euler c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_feu_euler (UNIONS c:real^N->bool)
                  (complex_euler (e:(real^N->bool)->bool) + (&0 - (&0 + &0)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS c = UNIONS e UNION (St:real^N->bool)` SUBST1_TAC THENL
     [UNDISCH_TAC `UNIONS e = UNIONS c DIFF (St:real^N->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `St SUBSET (S:real^N->bool)` THEN UNDISCH_TAC `S SUBSET (w:real^N->bool)` THEN
      UNDISCH_TAC `w SUBSET UNIONS (c:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS e = UNIONS c DIFF (St:real^N->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (e:(real^N->bool)->bool) = complex_euler (c:(real^N->bool)->bool)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`UNIONS c:real^N->bool`;
                   `complex_euler (e:(real^N->bool)->bool) + (&0 - (&0 + &0))`;
                   `complex_euler (c:(real^N->bool)->bool)`] MOI_FEU_EULER_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the boundary *)
  SUBGOAL_THEN `!z:real^N. z IN UNIONS c DIFF S
                ==> (moi_s28_locally_r2 (UNIONS e) z <=> moi_s28_locally_r2 (UNIONS c) z)`
  (LABEL_TAC "Req") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`UNIONS e:real^N->bool`; `UNIONS c DIFF S:real^N->bool`;
                     `UNIONS c DIFF S:real^N->bool`; `z:real^N`] MOI_S8CU_R2_RESTRICT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[SUBSET_REFL];
        DISCH_TAC] THEN
      MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN EXISTS_TAC `UNIONS c DIFF S:real^N->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `UNIONS c DIFF S:real^N->bool`;
                     `UNIONS c DIFF S:real^N->bool`; `z:real^N`] MOI_S8CU_R2_RESTRICT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        REWRITE_TAC[SUBSET_REFL; SUBSET_DIFF];
        DISCH_TAC] THEN
      MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN EXISTS_TAC `UNIONS c DIFF S:real^N->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `surface_boundary (e:(real^N->bool)->bool)`)) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN S` THENL
     [DISJ2_TAC THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS e` THEN UNDISCH_TAC `(y:real^N) IN S` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `S DIFF (La UNION Lb:real^N->bool) = St` THEN SET_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS c DIFF S` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS e SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS e` THEN UNDISCH_TAC `~((y:real^N) IN S)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~moi_s28_locally_r2 (UNIONS e) (y:real^N)` THEN REWRITE_TAC[] THEN
    USE_THEN "Req" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(y:real^N) IN UNIONS c DIFF S`)]) THEN
    USE_THEN "C1" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN UNIONS c DIFF S` THEN
    UNDISCH_TAC `~((y:real^N) IN surface_boundary c)` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN UNIONS c DIFF S` ASSUME_TAC THENL
     [SUBGOAL_THEN `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` MP_TAC THENL
       [REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN surface_boundary c` THEN
      UNDISCH_TAC `w SUBSET UNIONS c DIFF surface_boundary (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `S SUBSET (w:real^N->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS c DIFF S SUBSET UNIONS (e:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS c DIFF S` THEN SET_TAC[];
      USE_THEN "Req" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(y:real^N) IN UNIONS c DIFF S`)]) THEN
      USE_THEN "C2" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN surface_boundary c`)) THEN
      SIMP_TAC[]];
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS e = UNIONS c DIFF (St:real^N->bool)` THEN
      UNDISCH_TAC `S DIFF (La UNION Lb:real^N->bool) = St` THEN
      UNDISCH_TAC `La UNION Lb SUBSET (S:real^N->bool)` THEN
      UNDISCH_TAC `S SUBSET (w:real^N->bool)` THEN
      UNDISCH_TAC `w SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN La` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN USE_THEN "hlev" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS e = UNIONS c DIFF (St:real^N->bool)` THEN
      UNDISCH_TAC `S DIFF (La UNION Lb:real^N->bool) = St` THEN
      UNDISCH_TAC `La UNION Lb SUBSET (S:real^N->bool)` THEN
      UNDISCH_TAC `S SUBSET (w:real^N->bool)` THEN
      UNDISCH_TAC `w SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN Lb` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN USE_THEN "hlev" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Components of the complement of a closed set in a surface.  With plane   *)
(* charts everywhere, the components of x minus a closed set are open; the  *)
(* closure of such a component adds only points of the closed set; if the   *)
(* closed set is a union of simplices, the simplices inside k plus the set  *)
(* triangulate k plus the set; in a connected x, a component that is open   *)
(* meets every open neighbourhood V of the set outside the set.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_COMPONENT_OPEN = prove
 (`!(x:real^N->bool) m k.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     closed_in (subtopology euclidean x) m /\ k IN components (x DIFF m)
     ==> open_in (subtopology euclidean x) k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean x) (x DIFF m:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_REFL]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN x DIFF m` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `x DIFF m:real^N->bool`; `x DIFF m:real^N->bool`;
                 `z:real^N`] MOI_S8CU_R2_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL; SUBSET_DIFF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `x DIFF m:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; CONNECTED_UNIV];
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    ASM SET_TAC[]]);;

let MOI_S8CU_CLOSURE_COMPONENT = prove
 (`!(x:real^N->bool) m k.
     closed x /\ k IN components (x DIFF m) ==> closure k SUBSET k UNION m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x DIFF m:real^N->bool`; `k:real^N->bool`] CLOSED_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closure k SUBSET (f0:real^N->bool) /\ closure k SUBSET (x:real^N->bool)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `k = (x DIFF m) INTER (f0:real^N->bool)` THEN SET_TAC[]]);;

let MOI_S8CU_COMPONENT_COVER = prove
 (`!(c:(real^N->bool)->bool) m k.
     simplicial_complex c /\ m SUBSET UNIONS c /\
     (!z. z IN m ==> ?r. r IN c /\ r SUBSET m /\ z IN r) /\
     k IN components (UNIONS c DIFF m)
     ==> UNIONS {s | s IN c /\ s SUBSET k UNION m} = k UNION m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closure k SUBSET (k:real^N->bool) UNION m` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CLOSURE_COMPONENT THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE; MOI_CON_SC_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET UNIONS c DIFF m` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_S8TA_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^N) IN k UNION m` THEN
    UNDISCH_TAC `(k:real^N->bool) SUBSET UNIONS c DIFF m` THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  ASM_CASES_TAC `relative_interior s INTER (m:real^N->bool) = {}` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
      can (term_match [] `!z:real^N. z IN m ==> ?r. r IN c /\ r SUBSET m /\ z IN r`)
          (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET r` MP_TAC THENL
     [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `z:real^N`] THEN ASM SET_TAC[];
      UNDISCH_TAC `(r:real^N->bool) SUBSET m` THEN SET_TAC[]]] THEN
  SUBGOAL_THEN `relative_interior s SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS c DIFF m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[MOI_CON_SC_CONVEX];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `relative_interior s INTER (m:real^N->bool) = {}` THEN
      UNDISCH_TAC `(s:real^N->bool) IN c` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^N) IN relative_interior s` THEN
      UNDISCH_TAC `(x:real^N) IN k UNION m` THEN
      UNDISCH_TAC `relative_interior s INTER (m:real^N->bool) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(relative_interior s) = (s:real^N->bool)` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure(s:real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN ASM_MESON_TAC[MOI_CON_SC_CONVEX];
      MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[MOI_SCF_SC_CLOSED]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure k:real^N->bool` THEN
  ASM_SIMP_TAC[SUBSET_CLOSURE]);;

let MOI_S8CU_COMPONENT_MEETS = prove
 (`!(x:real^N->bool) m V K.
     connected x /\ closed_in (subtopology euclidean x) m /\ ~(m = {}) /\
     open_in (subtopology euclidean x) V /\ m SUBSET V /\
     K IN components (x DIFF m) /\ open_in (subtopology euclidean x) K
     ==> ~(K INTER (V DIFF m) = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:real^N->bool) SUBSET x DIFF m /\ ~(K = {}) /\ m SUBSET x /\
                V SUBSET (x:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_NONEMPTY; CLOSED_IN_IMP_SUBSET;
                  OPEN_IN_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean x) (x DIFF m:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean x) ((x DIFF m) DIFF K:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `x DIFF m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_IN_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean x) (K:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x DIFF K = ((x DIFF m) DIFF K) UNION (V:real^N->bool)` SUBST1_TAC THENL
     [UNDISCH_TAC `K INTER (V DIFF m:real^N->bool) = {}` THEN
      UNDISCH_TAC `(K:real^N->bool) SUBSET x DIFF m` THEN
      UNDISCH_TAC `V SUBSET (x:real^N->bool)` THEN
      UNDISCH_TAC `(m:real^N->bool) SUBSET V` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected(x:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `K:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(K:real^N->bool) SUBSET x DIFF m` THEN
  UNDISCH_TAC `(m:real^N->bool) SUBSET x` THEN UNDISCH_TAC `~(m:real^N->bool = {})` THEN
  SET_TAC[]);;

let MOI_S8CU_TWO_COMPONENTS = prove
 (`!(s:real^N->bool) o1 o2.
     connected o1 /\ connected o2 /\ ~(o1 = {}) /\ ~(o2 = {}) /\
     o1 SUBSET s /\ o2 SUBSET s /\
     (!K. K IN components s ==> ~(K INTER (o1 UNION o2) = {})) /\ ~connected s
     ==> ?k1 k2. components s = {k1,k2} /\ ~(k1 = k2) /\ o1 SUBSET k1 /\ o2 SUBSET k2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y1:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(o1:real^N->bool = {})`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y2:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(o2:real^N->bool = {})`)) THEN
  ABBREV_TAC `k1 = connected_component s (y1:real^N)` THEN
  ABBREV_TAC `k2 = connected_component s (y2:real^N)` THEN
  SUBGOAL_THEN `(k1:real^N->bool) IN components s /\ (k2:real^N->bool) IN components s`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k1"; "k2"] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `o1 SUBSET (k1:real^N->bool) /\ o2 SUBSET (k2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k1"; "k2"] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components s = {k1:real^N->bool,k2}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `K:real^N->bool` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `K:real^N->bool` o check (fun th ->
        can (term_match [] `!K:real^N->bool. K IN components s ==> P K`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `K INTER (o1:real^N->bool) = {}` THENL
       [DISJ2_TAC THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `K:real^N->bool`; `k2:real^N->bool`]
          COMPONENTS_NONOVERLAP) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (p <=> ~q) ==> q`) THEN
        UNDISCH_TAC `o2 SUBSET (k2:real^N->bool)` THEN
        UNDISCH_TAC `K INTER (o1:real^N->bool) = {}` THEN
        UNDISCH_TAC `~(K INTER (o1 UNION o2:real^N->bool) = {})` THEN SET_TAC[];
        DISJ1_TAC THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `K:real^N->bool`; `k1:real^N->bool`]
          COMPONENTS_NONOVERLAP) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (p <=> ~q) ==> q`) THEN
        UNDISCH_TAC `o1 SUBSET (k1:real^N->bool)` THEN
        UNDISCH_TAC `~(K INTER (o1:real^N->bool) = {})` THEN SET_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k1:real^N->bool`; `k2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~connected(s:real^N->bool)` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPONENTS_EQ_SING_EXISTS) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `k1:real^N->bool` THEN ASM_REWRITE_TAC[INSERT_AC]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two sides of a bicollar: O- = p(m x (-1,0)) and O+ = p(m x (0,1))    *)
(* are connected, disjoint from each other and from m = p(m x {0}), and the  *)
(* level m lies in the closure of each side.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_SIDE_INTERVALS = prove
 (`{t:real^1 | --(&1) < drop t /\ drop t < &1} =
   ({t | --(&1) < drop t /\ drop t < &0} UNION {lift(&0)}) UNION
   {t | &0 < drop t /\ drop t < &1} /\
   {t:real^1 | --(&1) < drop t /\ drop t < &1 /\ &0 <= &1 * (&0 - drop t)} =
   {t | --(&1) < drop t /\ drop t < &0} UNION {lift(&0)} /\
   {t:real^1 | --(&1) < drop t /\ drop t < &1 /\ &0 <= -- &1 * (&0 - drop t)} =
   {lift(&0)} UNION {t | &0 < drop t /\ drop t < &1} /\
   {t:real^1 | --(&1) < drop t /\ drop t < &0} INTER {lift(&0)} = {} /\
   {t:real^1 | &0 < drop t /\ drop t < &1} INTER {lift(&0)} = {} /\
   {t:real^1 | --(&1) < drop t /\ drop t < &0} INTER {t | &0 < drop t /\ drop t < &1} = {} /\
   {t:real^1 | --(&1) < drop t /\ drop t < &0} SUBSET interval[--vec 1,vec 1] /\
   {t:real^1 | &0 < drop t /\ drop t < &1} SUBSET interval[--vec 1,vec 1] /\
   {lift(&0)} SUBSET interval[--vec 1,vec 1] /\
   {t:real^1 | --(&1) < drop t /\ drop t < &1} SUBSET interval[--vec 1,vec 1]`,
  REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_INTER; IN_SING; IN_ELIM_THM; IN_INTERVAL_1;
              DROP_NEG; DROP_VEC; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S8CU_BICOLLAR_SIDES = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> IMAGE p (m PCROSS {lift(&0)}) = m /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) =
         (IMAGE p (m PCROSS {t | --(&1) < drop t /\ drop t < &0}) UNION m) UNION
         IMAGE p (m PCROSS {t | &0 < drop t /\ drop t < &1}) /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1 /\
                                       &0 <= &1 * (&0 - drop t)}) =
         IMAGE p (m PCROSS {t | --(&1) < drop t /\ drop t < &0}) UNION m /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1 /\
                                       &0 <= -- &1 * (&0 - drop t)}) =
         m UNION IMAGE p (m PCROSS {t | &0 < drop t /\ drop t < &1}) /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) INTER m = {} /\
         IMAGE p (m PCROSS {t:real^1 | &0 < drop t /\ drop t < &1}) INTER m = {} /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) INTER
         IMAGE p (m PCROSS {t | &0 < drop t /\ drop t < &1}) = {} /\
         IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) SUBSET w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift(&0)}) = m`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s26_bicollar]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                LIFT_NUM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^(N,1)finite_sum->real^N)
          (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) INTER m = {} /\
    IMAGE p (m PCROSS {t:real^1 | &0 < drop t /\ drop t < &1}) INTER m = {} /\
    IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0}) INTER
    IMAGE p (m PCROSS {t | &0 < drop t /\ drop t < &1}) = {} /\
    IMAGE p (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) SUBSET w`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{t:real^1 | --(&1) < drop t /\ drop t < &0}`; `{lift(&0)}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{t:real^1 | &0 < drop t /\ drop t < &1}`; `{lift(&0)}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{t:real^1 | --(&1) < drop t /\ drop t < &0}`;
                   `{t:real^1 | &0 < drop t /\ drop t < &1}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{t:real^1 | --(&1) < drop t /\ drop t < &1}`;
                   `{t:real^1 | --(&1) < drop t /\ drop t < &1}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    ASM_REWRITE_TAC[MOI_S8CU_SIDE_INTERVALS; PCROSS_EMPTY; IMAGE_CLAUSES] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_S8CU_SIDE_INTERVALS; PCROSS_UNION; IMAGE_UNION] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S8CU_SIDE_CONNECTED = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q alpha beta.
     moi_s26_bicollar m w p q /\ connected m /\ ~(m = {}) /\
     --(&1) <= alpha /\ alpha < beta /\ beta <= &1
     ==> connected (IMAGE p (m PCROSS {t:real^1 | alpha < drop t /\ drop t < beta})) /\
         ~(IMAGE p (m PCROSS {t:real^1 | alpha < drop t /\ drop t < beta}) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{t:real^1 | alpha < drop t /\ drop t < beta} = interval(lift alpha,lift beta)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                  DROP_NEG; DROP_VEC; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_PCROSS THEN ASM_REWRITE_TAC[CONNECTED_INTERVAL]];
    REWRITE_TAC[IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]]);;

let MOI_S8CU_LEVEL_IN_CLOSURE = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q alpha beta u.
     moi_s26_bicollar m w p q /\ closed m /\
     --(&1) <= alpha /\ alpha < beta /\ beta <= &1 /\ alpha <= u /\ u <= beta
     ==> IMAGE p (m PCROSS {lift u}) SUBSET
         closure (IMAGE p (m PCROSS {t:real^1 | alpha < drop t /\ drop t < beta}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{t:real^1 | alpha < drop t /\ drop t < beta} = interval(lift alpha,lift beta)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                    (closure (m PCROSS interval(lift alpha,lift beta)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_SIMP_TAC[CLOSURE_PCROSS; CLOSURE_CLOSED; CLOSURE_OPEN_INTERVAL; INTERVAL_EQ_EMPTY_1;
                 LIFT_DROP; REAL_NOT_LE] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING; IN_INTERVAL_1] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
    REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One side of a separating bicollared curve.  If k is a component of       *)
(* |tc| minus m = |l| which near m is the product piece on one side         *)
(* (sg = 1: t <= 0; sg = -1: t >= 0), then the simplices of a refinement of *)
(* tc inside k plus m form a combinatorial surface with polyhedron k plus m *)
(* and boundary m (plane charts on the open set k, MOI_S8CU_COLLAR_HALF on  *)
(* m, then SURF_LOCAL).                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S8CU_SIDE_COMPLEX = prove
 (`!(tc:(real^N->bool)->bool) (l:(real^N->bool)->bool) w
    (p:real^(N,1)finite_sum->real^N) q k sg.
     simplicial_complex tc /\ simplicial_complex l /\
     moi_s4l_line_charts (UNIONS l) /\ moi_s26_bicollar (UNIONS l) w p q /\
     UNIONS l SUBSET w /\ w SUBSET UNIONS tc /\
     (!y. y IN UNIONS tc ==> moi_s28_locally_r2 (UNIONS tc) y) /\
     k IN components (UNIONS tc DIFF UNIONS l) /\ sg * sg = &1 /\
     (k UNION UNIONS l) INTER
     IMAGE p (UNIONS l PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) =
     IMAGE p (UNIONS l PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1 /\
                                          &0 <= sg * (&0 - drop t)})
     ==> ?c. FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
             UNIONS c = k UNION UNIONS l /\ surface_boundary c = UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tc:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_POLYTOPE]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) IN l` THEN
    UNDISCH_TAC `UNIONS l SUBSET (w:real^N->bool)` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^N. z IN UNIONS l ==> ?r. r IN tt /\ r SUBSET UNIONS l /\ z IN r`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      aconv (concl th) `!s:real^N->bool. s IN l ==> ?f. f SUBSET tt /\ s = UNIONS f`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:real^N->bool. r IN f /\ z IN r` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[MOI_SCF_SC_FINITE; MOI_CON_SC_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC `m = UNIONS l:real^N->bool` THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET UNIONS tc /\ k SUBSET UNIONS tc DIFF m /\
                k UNION m SUBSET UNIONS (tc:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS tc DIFF m:real^N->bool`; `k:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET w` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS tc)) (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_COMPONENT_OPEN THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_SIMP_TAC[CLOSED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN w ==> moi_s8ta_emb2 (UNIONS tc) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN DISJ1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!y:real^N. y IN UNIONS tc ==> moi_s28_locally_r2 (UNIONS tc) y`) (concl th))) THEN
    UNDISCH_TAC `(y:real^N) IN w` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the subcomplex *)
  ABBREV_TAC `c = {s:real^N->bool | s IN tt /\ s SUBSET k UNION m}` THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ FINITE c /\
                UNIONS c = k UNION (m:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC MOI_S8CU_SUBCOMPLEX THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC MOI_S8CU_COMPONENT_COVER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* charts *)
  SUBGOAL_THEN `!y:real^N. y IN k ==> moi_s28_locally_r2 (k UNION m) y` (LABEL_TAC "Rk") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`UNIONS tc:real^N->bool`; `k:real^N->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[SUBSET_UNION] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!y:real^N. y IN UNIONS tc ==> moi_s28_locally_r2 (UNIONS tc) y`) (concl th))) THEN
    UNDISCH_TAC `(y:real^N) IN k` THEN UNDISCH_TAC `k SUBSET UNIONS tc DIFF (m:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN m ==> moi_s28_locally_half (k UNION m) y` (LABEL_TAC "Hm") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s28_locally_half (k UNION m)
                   ((p:real^(N,1)finite_sum->real^N) (pastecart y (lift(&0))))` MP_TAC THENL
     [MATCH_MP_TAC MOI_S8CU_COLLAR_HALF THEN
      MAP_EVERY EXISTS_TAC [`UNIONS tc:real^N->bool`; `m:real^N->bool`; `w:real^N->bool`;
                            `q:real^N->real^(N,1)finite_sum`; `--(&1)`; `&1`; `sg:real`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(SPEC `y:real^N` (CONJUNCT2 (GEN_REWRITE_RULE I [moi_s26_bicollar]
        (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
      ASM_REWRITE_TAC[LIFT_NUM] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS c = k UNION (m:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN USE_THEN "Rk" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN USE_THEN "Hm" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `surface_boundary (c:(real^N->bool)->bool)`)) THEN
  UNDISCH_TAC `UNIONS c = k UNION (m:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
     [UNDISCH_TAC `~moi_s28_locally_r2 (k UNION m) (y:real^N)` THEN
      MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
      USE_THEN "Rk" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_TAC THEN CONJ_TAC THENL
     [DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN USE_THEN "Hm" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* CUT_SEPARATING.  The two open sides O- and O+ of the bicollar are        *)
(* connected and lie in |t| minus m (m = |l|).  Every component of |t|      *)
(* minus m is open (plane charts) and meets a side, as otherwise it would   *)
(* be clopen in the connected |t|; a disconnected complement therefore has  *)
(* exactly two components, k1 containing O- and k2 containing O+.  Their    *)
(* closures k_i UNION m are triangulated by MOI_S8CU_SIDE_COMPLEX, and chi  *)
(* adds up by valuations (|t| = |c1| UNION (|c2| minus m), chi(l) = 0).      *)
(* ------------------------------------------------------------------------- *)

let CUT_SEPARATING = prove
 (MOI_S28_CUT_SEPARATING,
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`tc:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                       `q:real^N->real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (tc:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_S8TA_CM_CMB]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S8TA_CMB_FACTS (CONJ (ASSUME `FINITE (tc:(real^N->bool)->bool)`)
    (ASSUME `combinatorial_manifold_with_boundary 2 (tc:(real^N->bool)->bool)`))) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP SURF_CHARTS (CONJ (ASSUME `FINITE (tc:(real^N->bool)->bool)`)
    (ASSUME `combinatorial_manifold_with_boundary 2 (tc:(real^N->bool)->bool)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (K ALL_TAC)
    (fun th -> ASSUME_TAC(MP th
      (ASSUME `combinatorial_manifold 2 (tc:(real^N->bool)->bool)`))))) THEN
  SUBGOAL_THEN `!y:real^N. y IN UNIONS tc ==> moi_s28_locally_r2 (UNIONS tc) y`
  (LABEL_TAC "RX") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIFF_EMPTY];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S8CU_CM1_FACTS (CONJ (ASSUME `FINITE (l:(real^N->bool)->bool)`)
    (ASSUME `combinatorial_manifold 1 (l:(real^N->bool)->bool)`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS l SUBSET (w:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (UNIONS tc:real^N->bool)`; `w:real^N->bool`]
      INTERIOR_OF_SUBSET) THEN
    UNDISCH_TAC
     `UNIONS l SUBSET (subtopology euclidean (UNIONS tc)) interior_of (w:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `y0:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(UNIONS l:real^N->bool = {})`)) THEN
    MATCH_MP_TAC MOI_S8CU_R2_DIMINDEX THEN
    MAP_EVERY EXISTS_TAC [`UNIONS tc:real^N->bool`; `y0:real^N`] THEN
    USE_THEN "RX" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y0:real^N) IN UNIONS l` THEN
    UNDISCH_TAC `UNIONS l SUBSET (w:real^N->bool)` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4l_line_charts (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CM1_LINE_CHARTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (l:(real^N->bool)->bool) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CM1_EULER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN w ==> moi_s8ta_emb2 (UNIONS tc) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN DISJ1_TAC THEN
    USE_THEN "RX" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN w` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS l:real^N->bool) /\ closed (UNIONS tc:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[MOI_SCF_SC_FINITE; MOI_CON_SC_COMPACT];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S8CU_BICOLLAR_SIDES
    (ASSUME `moi_s26_bicollar (UNIONS l) w (p:real^(N,1)finite_sum->real^N) q`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS tc))
      (IMAGE (p:real^(N,1)finite_sum->real^N)
             (UNIONS l PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_PRODUCT_OPEN THEN
    MAP_EVERY EXISTS_TAC [`UNIONS l:real^N->bool`; `w:real^N->bool`;
                          `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `--(&1)`; `&0`] MOI_S8CU_SIDE_CONNECTED) THEN
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `&0`; `&1`] MOI_S8CU_SIDE_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `m = UNIONS l:real^N->bool` THEN
  ABBREV_TAC `Om = IMAGE (p:real^(N,1)finite_sum->real^N)
                         (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &0})` THEN
  ABBREV_TAC `Op = IMAGE (p:real^(N,1)finite_sum->real^N)
                         (m PCROSS {t:real^1 | &0 < drop t /\ drop t < &1})` THEN
  SUBGOAL_THEN `(Om:real^N->bool) SUBSET UNIONS tc DIFF m /\
                (Op:real^N->bool) SUBSET UNIONS tc DIFF m /\
                m SUBSET UNIONS (tc:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) =
                 (Om UNION m) UNION Op` THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                   (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) SUBSET w` THEN
    UNDISCH_TAC `w SUBSET UNIONS (tc:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `Om INTER (m:real^N->bool) = {}` THEN
    UNDISCH_TAC `Op INTER (m:real^N->bool) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* every component meets a side *)
  SUBGOAL_THEN `!K. K IN components (UNIONS tc DIFF m)
                    ==> ~(K INTER ((Om:real^N->bool) UNION Op) = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `K:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`UNIONS tc:real^N->bool`; `m:real^N->bool`;
                   `IMAGE (p:real^(N,1)finite_sum->real^N)
                          (m PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1})`;
                   `K:real^N->bool`] MOI_S8CU_COMPONENT_MEETS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC MOI_S8CU_COMPONENT_OPEN THEN EXISTS_TAC `m:real^N->bool` THEN
        ASM_SIMP_TAC[CLOSED_SUBSET]];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Om INTER (m:real^N->bool) = {}` THEN
      UNDISCH_TAC `Op INTER (m:real^N->bool) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* exactly two components *)
  MP_TAC(ISPECL [`UNIONS tc DIFF m:real^N->bool`; `Om:real^N->bool`; `Op:real^N->bool`]
    MOI_S8CU_TWO_COMPONENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `k2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(k1:real^N->bool) IN components (UNIONS tc DIFF m) /\
                (k2:real^N->bool) IN components (UNIONS tc DIFF m)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^N->bool) INTER k2 = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS tc DIFF m:real^N->bool`; `k1:real^N->bool`; `k2:real^N->bool`]
      COMPONENTS_NONOVERLAP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^N->bool) SUBSET UNIONS tc DIFF m /\
                (k2:real^N->bool) SUBSET UNIONS tc DIFF m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the two side complexes *)
  MP_TAC(ISPECL [`tc:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `k1:real^N->bool`; `&1`] MOI_S8CU_SIDE_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `Om SUBSET (k1:real^N->bool)` THEN UNDISCH_TAC `Op SUBSET (k2:real^N->bool)` THEN
    UNDISCH_TAC `(k1:real^N->bool) INTER k2 = {}` THEN
    UNDISCH_TAC `Op INTER (m:real^N->bool) = {}` THEN SET_TAC[];
    REWRITE_TAC[ASSUME `UNIONS l:real^N->bool = m`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(real^N->bool)->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`tc:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `k2:real^N->bool`; `-- &1`] MOI_S8CU_SIDE_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `Om SUBSET (k1:real^N->bool)` THEN UNDISCH_TAC `Op SUBSET (k2:real^N->bool)` THEN
    UNDISCH_TAC `(k1:real^N->bool) INTER k2 = {}` THEN
    UNDISCH_TAC `Om INTER (m:real^N->bool) = {}` THEN SET_TAC[];
    REWRITE_TAC[ASSUME `UNIONS l:real^N->bool = m`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c2:(real^N->bool)->bool` STRIP_ASSUME_TAC)] THEN
  (* closures *)
  SUBGOAL_THEN `closure k1 = (k1:real^N->bool) UNION m /\
                closure k2 = (k2:real^N->bool) UNION m`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(m:real^N->bool) SUBSET closure Om /\ m SUBSET closure Op`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                     `q:real^N->real^(N,1)finite_sum`; `--(&1)`; `&0`; `&0`]
        MOI_S8CU_LEVEL_IN_CLOSURE) THEN
      MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                     `q:real^N->real^(N,1)finite_sum`; `&0`; `&1`; `&0`]
        MOI_S8CU_LEVEL_IN_CLOSURE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S8CU_CLOSURE_COMPONENT THEN EXISTS_TAC `UNIONS tc:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure Om:real^N->bool` THEN
      ASM_SIMP_TAC[SUBSET_CLOSURE];
      MATCH_MP_TAC MOI_S8CU_CLOSURE_COMPONENT THEN EXISTS_TAC `UNIONS tc:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure Op:real^N->bool` THEN
      ASM_SIMP_TAC[SUBSET_CLOSURE]];
    ALL_TAC] THEN
  (* chi by valuations *)
  SUBGOAL_THEN `complex_euler (c1:(real^N->bool)->bool) +
                complex_euler (c2:(real^N->bool)->bool) =
                complex_euler (tc:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S8TA_CMB_FACTS (CONJ (ASSUME `FINITE (c1:(real^N->bool)->bool)`)
      (ASSUME `combinatorial_manifold_with_boundary 2 (c1:(real^N->bool)->bool)`))) THEN
    STRIP_TAC THEN
    MP_TAC(MATCH_MP MOI_S8TA_CMB_FACTS (CONJ (ASSUME `FINITE (c2:(real^N->bool)->bool)`)
      (ASSUME `combinatorial_manifold_with_boundary 2 (c2:(real^N->bool)->bool)`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_feu_euler (UNIONS c1:real^N->bool) (complex_euler c1) /\
                  moi_feu_euler (UNIONS c2:real^N->bool) (complex_euler c2) /\
                  moi_feu_euler (UNIONS tc:real^N->bool) (complex_euler tc) /\
                  moi_feu_euler (m:real^N->bool) (&0)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN
                                FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(SPEC `l:(real^N->bool)->bool` MOI_FEU_EULER_SIMPLICIAL_COMPLEX) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS c2:real^N->bool`; `m:real^N->bool`;
                   `complex_euler (c2:(real^N->bool)->bool)`; `&0`] MOI_FEU_EULER_DIFF) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `UNIONS c2 = k2 UNION (m:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
      SET_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`UNIONS c1:real^N->bool`; `UNIONS c2 DIFF m:real^N->bool`;
                   `complex_euler (c1:(real^N->bool)->bool)`;
                   `complex_euler (c2:(real^N->bool)->bool) - &0`]
      MOI_FEU_EULER_UNION_DISJOINT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `UNIONS c1 = k1 UNION (m:real^N->bool)` THEN
      UNDISCH_TAC `UNIONS c2 = k2 UNION (m:real^N->bool)` THEN
      UNDISCH_TAC `(k1:real^N->bool) INTER k2 = {}` THEN
      UNDISCH_TAC `(k1:real^N->bool) SUBSET UNIONS tc DIFF m` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS c1 UNION (UNIONS c2 DIFF m) = UNIONS (tc:(real^N->bool)->bool)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `UNIONS tc DIFF m:real^N->bool` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2] THEN
      UNDISCH_TAC `(m:real^N->bool) SUBSET UNIONS tc` THEN SET_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`UNIONS tc:real^N->bool`;
                   `complex_euler (c1:(real^N->bool)->bool) +
                    (complex_euler (c2:(real^N->bool)->bool) - &0)`;
                   `complex_euler (tc:(real^N->bool)->bool)`] MOI_FEU_EULER_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k1:real^N->bool`; `k2:real^N->bool`;
                        `c1:(real^N->bool)->bool`; `c2:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

