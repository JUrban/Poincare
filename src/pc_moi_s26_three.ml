(* ========================================================================= *)
(* pc_moi_s26_three: Moise Thm 26.7 (GTM 47, p.195) from 26.6, surface       *)
(* gluing, connected interiors and the local sides at a point inside a       *)
(* triangle.  Main theorem THREE_267 : |- MOI_S26_THREE                      *)
(* (pc_moi_s2628_stmt.ml).                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_gpb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Simplicial facts for finite combinatorial 2-manifolds with boundary.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S6T_CPLX = prove
 (`!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
         (!s. s IN c ==> compact s) /\ compact (UNIONS c)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` MP_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN c ==> compact s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FGB_CMB2_DIM];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[]]);;

let MOI_S6T_SIMPLEX = prove
 (`!c s:real^N->bool.
     simplicial_complex c /\ s IN c
     ==> polytope s /\ polyhedron s /\ closed s /\ convex s /\ compact s /\
         (!f. f face_of s ==> f IN c)`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `polytope (s:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_CONVEX;
               POLYTOPE_IMP_COMPACT] THEN
  X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of")) (concl th))) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S6T_RELINT_LOW = prove
 (`!c q s:real^N->bool.
     simplicial_complex c /\ q IN c /\ aff_dim q = &2 /\ s IN c /\ aff_dim s <= &1
     ==> DISJOINT s (relative_interior q)`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER q:real^N->bool) face_of q` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s INTER q:real^N->bool = q` THENL
   [SUBGOAL_THEN `aff_dim(q:real^N->bool) <= aff_dim(s:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[];
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_INT_ARITH_TAC];
    MP_TAC(ISPECL [`s INTER q:real^N->bool`; `q:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `q:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    SET_TAC[]]);;

let MOI_S6T_SB_LOW = prove
 (`!c:(real^N->bool)->bool.
     surface_boundary c SUBSET UNIONS {s | s IN c /\ aff_dim s <= &1} /\
     UNIONS {s | s IN c /\ aff_dim s <= &1} SUBSET UNIONS c /\
     surface_boundary c SUBSET UNIONS c`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE `(a:real^N->bool) SUBSET b /\ b SUBSET c ==> a SUBSET b /\ b SUBSET c /\ a SUBSET c`) THEN
  REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[INT_LE_REFL]);;

let MOI_S6T_GOOD_INT = prove
 (`!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ ~(surface_boundary c = {})
     ==> ?z. z IN UNIONS c /\ ~(z IN surface_boundary c) /\
             ~(z IN UNIONS {s | s IN c /\ aff_dim s <= &1})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^3->bool)->bool` MOI_S6T_CPLX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q:real^3->bool. q IN c /\ aff_dim q = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(surface_boundary (c:(real^3->bool)->bool) = {})` THEN
    REWRITE_TAC[surface_boundary; EMPTY_UNIONS; IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~({r | r IN c /\ aff_dim r = &2 /\ (e:real^3->bool) SUBSET r} = {})`
    MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `CARD {r | r IN c /\ aff_dim r = &2 /\ (e:real^3->bool) SUBSET r} = 1` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (q:real^3->bool) = {})` MP_TAC THENL
   [SUBGOAL_THEN `convex (q:real^3->bool) /\ ~(q = {})` MP_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6T_SIMPLEX) THEN
        ASM_SIMP_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `aff_dim({}:real^3->bool) = &2` THEN
        REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
  EXISTS_TAC `z:real^3` THEN
  SUBGOAL_THEN `~((z:real^3) IN UNIONS {s | s IN c /\ aff_dim s <= &1})` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `s:real^3->bool`]
      MOI_S6T_RELINT_LOW) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior q` THEN
    UNDISCH_TAC `(z:real^3) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior q` THEN SET_TAC[];
    MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_S6T_SB_LOW) THEN
    UNDISCH_TAC `~((z:real^3) IN UNIONS {s | s IN c /\ aff_dim s <= &1})` THEN SET_TAC[]]);;

let MOI_S6T_TRI_POINT = prove
 (`!c (y:real^3).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ y IN UNIONS c /\
     ~(y IN UNIONS {s | s IN c /\ aff_dim s <= &1})
     ==> ?q. q IN c /\ aff_dim q = &2 /\ y IN relative_interior q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^3->bool)->bool` MOI_S6T_CPLX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^3->bool` THEN
  SUBGOAL_THEN `aff_dim(q:real^3->bool) = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `(x:int) <= &2 /\ &1 + &1 <= x ==> x = &2`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[GSYM INT_LT_DISCRETE; GSYM INT_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN UNIONS {s | s IN c /\ aff_dim s <= &1})` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `q:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6T_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((y:real^3) IN relative_frontier q)` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `f:real^3->bool` THEN REWRITE_TAC[facet_of] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((y:real^3) IN UNIONS {s | s IN c /\ aff_dim s <= &1})` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `f:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* The symmetric context of three surfaces with common boundary b, the      *)
(* two complementary domains of each pair (26.6), and case A.               *)
(* ------------------------------------------------------------------------- *)

let moi_s6t_ctx = new_definition
 `moi_s6t_ctx (c1:(real^3->bool)->bool) c2 c3 b <=>
    FINITE c1 /\ combinatorial_manifold_with_boundary 2 c1 /\ connected (UNIONS c1) /\
    FINITE c2 /\ combinatorial_manifold_with_boundary 2 c2 /\ connected (UNIONS c2) /\
    FINITE c3 /\ combinatorial_manifold_with_boundary 2 c3 /\ connected (UNIONS c3) /\
    surface_boundary c1 = b /\ surface_boundary c2 = b /\ surface_boundary c3 = b /\
    ~(b = {}) /\
    DISJOINT (UNIONS c1 DIFF b) (UNIONS c2 DIFF b) /\
    DISJOINT (UNIONS c1 DIFF b) (UNIONS c3 DIFF b) /\
    DISJOINT (UNIONS c2 DIFF b) (UNIONS c3 DIFF b)`;;

let moi_s6t_pair = new_definition
 `moi_s6t_pair (s:real^3->bool) i <=>
    components ((:real^3) DIFF s) = {i, outside s} /\ bounded i /\ ~(i = outside s) /\
    frontier i = s /\ frontier (outside s) = s`;;

let MOI_S6T_CTX_PERM = prove
 (`!c1 c2 c3 b.
     moi_s6t_ctx c1 c2 c3 b
     ==> moi_s6t_ctx c2 c1 c3 b /\ moi_s6t_ctx c1 c3 c2 b /\ moi_s6t_ctx c3 c2 c1 b`,
  REWRITE_TAC[moi_s6t_ctx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_S6T_CTX_BASIC = prove
 (`!c1 c2 c3 b.
     moi_s6t_ctx c1 c2 c3 b
     ==> b SUBSET UNIONS c1 /\ b SUBSET UNIONS c2 /\ b SUBSET UNIONS c3 /\
         UNIONS c1 INTER UNIONS c2 = b /\ UNIONS c1 INTER UNIONS c3 = b /\
         UNIONS c2 INTER UNIONS c3 = b /\
         closed (UNIONS c1) /\ closed (UNIONS c2) /\ closed (UNIONS c3) /\
         ~(UNIONS c1 DIFF b = {}) /\ ~(UNIONS c2 DIFF b = {}) /\ ~(UNIONS c3 DIFF b = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6t_ctx]) THEN
  SUBGOAL_THEN `b SUBSET UNIONS (c1:(real^3->bool)->bool) /\ b SUBSET UNIONS (c2:(real^3->bool)->bool) /\
                b SUBSET UNIONS (c3:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(CONJUNCT2(CONJUNCT2(ISPEC t MOI_S6T_SB_LOW))))
      [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[];
    ASM_MESON_TAC[MOI_S6T_CPLX; COMPACT_IMP_CLOSED];
    ASM_MESON_TAC[MOI_S6T_CPLX; COMPACT_IMP_CLOSED];
    ASM_MESON_TAC[MOI_S6T_CPLX; COMPACT_IMP_CLOSED];
    MP_TAC(SPEC `c1:(real^3->bool)->bool` MOI_S6T_GOOD_INT);
    MP_TAC(SPEC `c2:(real^3->bool)->bool` MOI_S6T_GOOD_INT);
    MP_TAC(SPEC `c3:(real^3->bool)->bool` MOI_S6T_GOOD_INT)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S6T_PAIR = prove
 (mk_imp(sdd_i3 MOI_S26_SURF_GLUE_BODY,
   `!c1 c2 c3 b.
      MOISE_266_STATEMENT /\ moi_s6t_ctx c1 c2 c3 b
      ==> ?i. moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  UNDISCH_TAC `moi_s6t_ctx c1 c2 c3 b` THEN REWRITE_TAC[moi_s6t_ctx] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
                                `b:real^3->bool`] o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "complex_euler")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (e:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `MOISE_266_STATEMENT` THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:(real^3->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `b SUBSET UNIONS (c1:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `~(b:real^3->bool = {})` THEN SET_TAC[]];
    REWRITE_TAC[moi_s6t_pair]]);;

let MOI_S6T_COMP_AT = prove
 (`!s c y:real^N. c IN components s /\ y IN c ==> connected_component s y = c`,
  REWRITE_TAC[IN_COMPONENTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM_MESON_TAC[]);;

let MOI_S6T_PAIR_FACTS = prove
 (`!s i. moi_s6t_pair s i
         ==> i IN components ((:real^3) DIFF s) /\
             outside s IN components ((:real^3) DIFF s) /\
             DISJOINT i (outside s) /\ DISJOINT i s /\ DISJOINT (outside s) s /\
             connected i /\ connected (outside s) /\ open i /\ open (outside s)`,
  REWRITE_TAC[moi_s6t_pair] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i IN components ((:real^3) DIFF s) /\
                outside s IN components ((:real^3) DIFF s)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed (s:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      rator(lhs(concl th)) = `frontier:(real^3->bool)->real^3->bool` &&
      rand(lhs(concl th)) = `i:real^3->bool`)) THEN
    REWRITE_TAC[FRONTIER_CLOSED];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[COMPONENTS_NONOVERLAP];
    MP_TAC(ISPECL [`(:real^3) DIFF s`; `i:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`(:real^3) DIFF s`; `outside s:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF s` THEN
    ASM_REWRITE_TAC[GSYM closed];
    MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF s` THEN
    ASM_REWRITE_TAC[GSYM closed]]);;

let MOI_S6T_E_OUT = prove
 (`!s i x (X:real^3->bool).
     moi_s6t_pair s i /\ s SUBSET X /\ ~(x IN X) /\
     ~bounded (connected_component ((:real^3) DIFF X) x)
     ==> connected_component ((:real^3) DIFF X) x SUBSET outside s /\ x IN outside s /\
         connected_component ((:real^3) DIFF s) x = outside s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected_component ((:real^3) DIFF s) x IN components ((:real^3) DIFF s)`
  MP_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `x:real^3` THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s6t_pair s i` THEN REWRITE_TAC[moi_s6t_pair] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`(:real^3) DIFF X`; `(:real^3) DIFF s`; `x:real^3`]
    CONNECTED_COMPONENT_MONO) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN connected_component ((:real^3) DIFF s) x` ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `~bounded (connected_component ((:real^3) DIFF X) x)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `i:real^3->bool` THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S6T_SIDE = prove
 (`!s i (t:real^3->bool).
     moi_s6t_pair s i /\ connected t /\ DISJOINT t s
     ==> t SUBSET i \/ t SUBSET outside s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:real^3->bool = {}` THENL
   [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `t SUBSET connected_component ((:real^3) DIFF s) z` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component ((:real^3) DIFF s) z IN components ((:real^3) DIFF s)`
  MP_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `z:real^3` THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s6t_pair s i` THEN REWRITE_TAC[moi_s6t_pair] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S6T_CASE_A = prove
 (`!c1 c2 c3 b i x.
     moi_s6t_ctx c1 c2 c3 b /\
     moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i /\ UNIONS c3 DIFF b SUBSET i /\
     ~(x IN UNIONS c1 UNION UNIONS c2 UNION UNIONS c3) /\
     ~bounded (connected_component
                 ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x)
     ==> frontier (connected_component
                     ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) =
         UNIONS c1 UNION UNIONS c2 /\
         (!y. y IN UNIONS c3 DIFF b
              ==> bounded (connected_component ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2)) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_PAIR_FACTS) THEN
  MP_TAC(ISPECL [`UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)`; `i:real^3->bool`;
                 `x:real^3`; `UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`]
    MOI_S6T_E_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `connected_component
                    ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x =
                  outside (UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`DISJOINT (outside (UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)))
                  (UNIONS c1 UNION UNIONS c2)`;
        `DISJOINT (i:real^3->bool) (outside (UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)))`;
        `UNIONS (c3:(real^3->bool)->bool) DIFF b SUBSET i`;
        `b SUBSET UNIONS (c1:(real^3->bool)->bool)`] THEN
      SET_TAC[];
      UNDISCH_TAC `moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i` THEN
      SIMP_TAC[moi_s6t_pair]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DIFF (UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool))`;
                   `i:real^3->bool`; `y:real^3`] MOI_S6T_COMP_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i` THEN SIMP_TAC[moi_s6t_pair]]);;

(* ------------------------------------------------------------------------- *)
(* A frontier point of the unbounded component inside a triangle.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S6T_LOW_UNION = prove
 (`!c1 c2 c3 b (y:real^3).
     moi_s6t_ctx c1 c2 c3 b /\
     ~(y IN UNIONS {s | (s IN c1 \/ s IN c2 \/ s IN c3) /\ aff_dim s <= &1}) /\
     y IN UNIONS c1
     ==> y IN UNIONS c1 DIFF b /\ ?q. q IN c1 /\ aff_dim q = &2 /\ y IN relative_interior q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6t_ctx]) THEN
  SUBGOAL_THEN `~((y:real^3) IN UNIONS {s | s IN c1 /\ aff_dim s <= &1})` ASSUME_TAC THENL
   [UNDISCH_TAC `~((y:real^3) IN UNIONS {s | (s IN c1 \/ s IN c2 \/ s IN c3) /\
                                             aff_dim s <= &1})` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF] THEN
    MP_TAC(ISPEC `c1:(real^3->bool)->bool` MOI_S6T_SB_LOW) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN UNIONS {s | s IN c1 /\ aff_dim s <= &1})` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S6T_TRI_POINT THEN ASM_REWRITE_TAC[]]);;

let MOI_S6T_GOOD_POINT = prove
 (`!c1 c2 c3 b x.
     moi_s6t_ctx c1 c2 c3 b /\ ~(x IN UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)
     ==> ?y. y IN frontier (connected_component
                ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) /\
             ((y IN UNIONS c1 DIFF b /\
               ?q. q IN c1 /\ aff_dim q = &2 /\ y IN relative_interior q) \/
              (y IN UNIONS c2 DIFF b /\
               ?q. q IN c2 /\ aff_dim q = &2 /\ y IN relative_interior q) \/
              (y IN UNIONS c3 DIFF b /\
               ?q. q IN c3 /\ aff_dim q = &2 /\ y IN relative_interior q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6t_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_PERM) THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t MOI_S6T_CPLX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC)
    [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`] THEN
  ABBREV_TAC `f = {s:real^3->bool | (s IN c1 \/ s IN c2 \/ s IN c3) /\ aff_dim s <= &1}` THEN
  SUBGOAL_THEN `FINITE (f:(real^3->bool)->bool) /\ (!s. s IN f ==> aff_dim s <= &1) /\
                UNIONS f SUBSET UNIONS c1 UNION UNIONS c2 UNION UNIONS c3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(c1:(real^3->bool)->bool) UNION c2 UNION c3` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[FINITE_UNION]; SET_TAC[]];
      SIMP_TAC[IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `X = UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)` THEN
  ABBREV_TAC `E = connected_component ((:real^3) DIFF X) x` THEN
  SUBGOAL_THEN `closed (X:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[CLOSED_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `open (E:real^3->bool) /\ (x:real^3) IN E /\ E SUBSET (:real^3) DIFF X`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN ASM_REWRITE_TAC[GSYM closed];
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier E SUBSET (X:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier ((:real^3) DIFF X)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_OF_COMPONENTS_SUBSET THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      ASM_SIMP_TAC[FRONTIER_COMPLEMENT; FRONTIER_SUBSET_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier E = closure E DIFF (E:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; INTERIOR_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF UNIONS f)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM THEN
    ASM_REWRITE_TAC[CONNECTED_UNIV; AFFINE_HULL_UNIV; AFF_DIM_UNIV; DIMINDEX_3;
                    OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &1` MP_TAC THENL
     [ASM_MESON_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN frontier E /\ ~(y IN UNIONS f)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    MP_TAC(SPEC `c1:(real^3->bool)->bool` MOI_S6T_GOOD_INT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((z0:real^3) IN UNIONS f)` ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN
      ASM_CASES_TAC `(s:real^3->bool) IN c1` THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~((z0:real^3) IN UNIONS {s | s IN c1 /\ aff_dim s <= &1})` THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN
      (SUBGOAL_THEN `(z0:real^3) IN UNIONS c2 \/ z0 IN UNIONS c3` MP_TAC THENL
        [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
      MAP_EVERY UNDISCH_TAC
       [`DISJOINT (UNIONS c1 DIFF b) (UNIONS (c2:(real^3->bool)->bool) DIFF b)`;
        `DISJOINT (UNIONS c1 DIFF b) (UNIONS (c3:(real^3->bool)->bool) DIFF b)`;
        `(z0:real^3) IN UNIONS c1`; `~((z0:real^3) IN b)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `connected ((:real^3) DIFF UNIONS f)` THEN REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`E:real^3->bool`; `(:real^3) DIFF closure E`] THEN
    ASM_REWRITE_TAC[GSYM closed; CLOSED_CLOSURE] THEN
    MP_TAC(ISPEC `E:real^3->bool` CLOSURE_SUBSET) THEN
    SUBGOAL_THEN `(z0:real^3) IN X` MP_TAC THENL
     [EXPAND_TAC "X" THEN UNDISCH_TAC `(z0:real^3) IN UNIONS c1` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((x:real^3) IN UNIONS f)` MP_TAC THENL
     [UNDISCH_TAC `UNIONS f SUBSET (X:real^3->bool)` THEN
      UNDISCH_TAC `~((x:real^3) IN X)` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`!y:real^3. y IN frontier E ==> y IN UNIONS f`;
      `frontier E = closure E DIFF (E:real^3->bool)`;
      `(x:real^3) IN E`; `E SUBSET (:real^3) DIFF X`;
      `~((z0:real^3) IN UNIONS f)`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS c1 \/ y IN UNIONS c2 \/ y IN UNIONS c3` MP_TAC THENL
   [UNDISCH_TAC `frontier E SUBSET (X:real^3->bool)` THEN EXPAND_TAC "X" THEN
    UNDISCH_TAC `(y:real^3) IN frontier E` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((y:real^3) IN UNIONS f)` THEN EXPAND_TAC "f" THEN
  REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_S6T_LOW_UNION THEN
    MAP_EVERY EXISTS_TAC [`c2:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC MOI_S6T_LOW_UNION THEN
    MAP_EVERY EXISTS_TAC [`c1:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN UNIONS {s | (s IN c1 \/ s IN c2 \/ s IN c3) /\
                                             aff_dim s <= &1})` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC MOI_S6T_LOW_UNION THEN
    MAP_EVERY EXISTS_TAC [`c2:(real^3->bool)->bool`; `c1:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN UNIONS {s | (s IN c1 \/ s IN c2 \/ s IN c3) /\
                                             aff_dim s <= &1})` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Case B: the two local sides at a good frontier point force the two       *)
(* bounded domains of the pairs through c1 to coincide.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S6T_COMP_X = prove
 (`!s i (X:real^3->bool) z.
     moi_s6t_pair s i /\ s SUBSET X /\ DISJOINT i X /\ z IN i
     ==> i = connected_component ((:real^3) DIFF X) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_PAIR_FACTS) THEN
  MP_TAC(ISPECL [`(:real^3) DIFF s`; `i:real^3->bool`; `z:real^3`] MOI_S6T_COMP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]]);;

let MOI_S6T_CASE_B0 = prove
 (`!c1 c2 c3 b i2 i3 x y r (h:real^3->bool) u v.
     moi_s6t_ctx c1 c2 c3 b /\
     moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i3 /\
     UNIONS c3 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c2) /\
     moi_s6t_pair (UNIONS c1 UNION UNIONS c3) i2 /\
     UNIONS c2 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c3) /\
     ~(x IN UNIONS c1 UNION UNIONS c2 UNION UNIONS c3) /\
     ~bounded (connected_component
                 ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) /\
     y IN UNIONS c1 /\ &0 < r /\
     ball(y,r) INTER (UNIONS c2 UNION UNIONS c3) = {} /\
     ball(y,r) INTER UNIONS c1 = ball(y,r) INTER h /\ y IN h /\
     connected v /\ u UNION v = ball(y,r) DIFF h /\ ball(y,r) INTER h SUBSET closure v /\
     u SUBSET connected_component
                ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  ABBREV_TAC `E = connected_component
                   ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x` THEN
  MP_TAC(ISPECL [`UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)`; `i3:real^3->bool`;
                 `x:real^3`; `UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`]
    MOI_S6T_E_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool)`; `i2:real^3->bool`;
                 `x:real^3`; `UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`]
    MOI_S6T_E_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)`; `i3:real^3->bool`]
    MOI_S6T_PAIR_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool)`; `i2:real^3->bool`]
    MOI_S6T_PAIR_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ball(y:real^3,r) INTER h SUBSET closure {}` THEN
    REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* in each pair through c1, the side v lies in the bounded domain *)
  SUBGOAL_THEN
   `!s i. moi_s6t_pair s i /\ E SUBSET outside s /\
          ball(y:real^3,r) INTER s = ball(y,r) INTER h /\ y IN s
          ==> v SUBSET (i:real^3->bool)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_PAIR_FACTS) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `v:real^3->bool`] MOI_S6T_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`u UNION v = ball(y:real^3,r) DIFF h`; `ball(y:real^3,r) INTER s = ball(y,r) INTER h`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN closure i` MP_TAC THENL
     [UNDISCH_TAC `moi_s6t_pair s i` THEN REWRITE_TAC[moi_s6t_pair] THEN STRIP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `frontier i = (s:real^3->bool)`)) THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN ball(y,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN i`; `(z:real^3) IN ball(y,r)`;
      `ball(y:real^3,r) INTER s = ball(y,r) INTER h`; `u UNION v = ball(y:real^3,r) DIFF h`;
      `(u:real^3->bool) SUBSET E`; `E SUBSET outside (s:real^3->bool)`;
      `v SUBSET outside (s:real^3->bool)`; `DISJOINT i (outside (s:real^3->bool))`;
      `DISJOINT (i:real^3->bool) s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v SUBSET (i3:real^3->bool) /\ v SUBSET (i2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)`;
      EXISTS_TAC `UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN UNIONS c1`;
      `ball(y:real^3,r) INTER (UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)) = {}`;
      `ball(y:real^3,r) INTER UNIONS (c1:(real^3->bool)->bool) = ball(y,r) INTER h`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(v:real^3->bool = {})`)) THEN
  SUBGOAL_THEN `i3:real^3->bool = i2` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `connected_component
                  ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) (z:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S6T_COMP_X THEN
      EXISTS_TAC `UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC; UNDISCH_TAC `(z:real^3) IN v` THEN UNDISCH_TAC `v SUBSET (i3:real^3->bool)` THEN
                 SET_TAC[]] THEN
      MAP_EVERY UNDISCH_TAC
       [`DISJOINT (i3:real^3->bool) (UNIONS c1 UNION UNIONS c2)`;
        `DISJOINT (i3:real^3->bool) (outside (UNIONS c1 UNION UNIONS c2))`;
        `UNIONS (c3:(real^3->bool)->bool) DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c2)`;
        `b SUBSET UNIONS (c1:(real^3->bool)->bool)`] THEN
      SET_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S6T_COMP_X THEN
      EXISTS_TAC `UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC; UNDISCH_TAC `(z:real^3) IN v` THEN UNDISCH_TAC `v SUBSET (i2:real^3->bool)` THEN
                 SET_TAC[]] THEN
      MAP_EVERY UNDISCH_TAC
       [`DISJOINT (i2:real^3->bool) (UNIONS c1 UNION UNIONS c3)`;
        `DISJOINT (i2:real^3->bool) (outside (UNIONS c1 UNION UNIONS c3))`;
        `UNIONS (c2:(real^3->bool)->bool) DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c3)`;
        `b SUBSET UNIONS (c1:(real^3->bool)->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS c1 UNION UNIONS c2 = UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool)`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i3`;
      `moi_s6t_pair (UNIONS c1 UNION UNIONS c3) i2`;
      `i3:real^3->bool = i2`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[moi_s6t_pair] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `w:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(UNIONS (c2:(real^3->bool)->bool) DIFF b = {})`)) THEN
  MAP_EVERY UNDISCH_TAC
   [`(w:real^3) IN UNIONS c2 DIFF b`;
    `UNIONS c1 INTER UNIONS c2 = (b:real^3->bool)`;
    `UNIONS c2 INTER UNIONS c3 = (b:real^3->bool)`] THEN
  SET_TAC[]);;

(* The side conditions left when case B0 is applied to the sides (u,v) or  *)
(* (v,u) of a good point.                                                  *)

let MOI_S6T_B_TAC (asl,w) =
  if w = `(y:real^3) IN UNIONS (c1:(real^3->bool)->bool)` then
    (UNDISCH_TAC `(y:real^3) IN UNIONS c1 DIFF b` THEN SET_TAC[]) (asl,w)
  else if is_eq w then
    (UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF affine hull q` THEN SET_TAC[]) (asl,w)
  else if can (find_term (fun t -> is_const t && fst(dest_const t) = "closure")) w then
    (UNDISCH_TAC `ball(y:real^3,r) INTER affine hull q SUBSET closure u INTER closure v` THEN
     SET_TAC[]) (asl,w)
  else
    (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF affine hull q` THEN SET_TAC[];
       REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `e:real^3` THEN
       ASM_REWRITE_TAC[]]) (asl,w);;

let MOI_S6T_CASE_B = prove
 (mk_imp(MOI_S26_LOCAL_TRI,
  `!c1 c2 c3 b i2 i3 x y q.
     moi_s6t_ctx c1 c2 c3 b /\
     moi_s6t_pair (UNIONS c1 UNION UNIONS c2) i3 /\
     UNIONS c3 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c2) /\
     moi_s6t_pair (UNIONS c1 UNION UNIONS c3) i2 /\
     UNIONS c2 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c3) /\
     ~(x IN UNIONS c1 UNION UNIONS c2 UNION UNIONS c3) /\
     ~bounded (connected_component
                 ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) /\
     y IN frontier (connected_component
                      ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) /\
     y IN UNIONS c1 DIFF b /\ q IN c1 /\ aff_dim q = &2 /\ y IN relative_interior q
     ==> F`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6t_ctx]) THEN
  MP_TAC(SPEC `c1:(real^3->bool)->bool` MOI_S6T_CPLX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c1:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`] o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "hull")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(y:real^3,r1) INTER (UNIONS c2 UNION UNIONS c3) = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF (UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool))`
      OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[GSYM closed; CLOSED_UNION] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN UNIONS c1 DIFF b`; `UNIONS c1 INTER UNIONS c2 = (b:real^3->bool)`;
        `UNIONS c1 INTER UNIONS c3 = (b:real^3->bool)`] THEN
      SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min r0 r1:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = min r0 r1:real` THEN
  SUBGOAL_THEN `&0 < r /\ ball(y:real^3,r) INTER (UNIONS c2 UNION UNIONS c3) = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!t. (s:real^3->bool) SUBSET t /\ t INTER u = {} ==> s INTER u = {}`) THEN
    EXISTS_TAC `ball(y:real^3,r1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_BALL THEN EXPAND_TAC "r" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^3->bool`
    (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(y:real^3) IN affine hull q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN
    MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior q` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = connected_component
                   ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x` THEN
  SUBGOAL_THEN `?e:real^3. e IN E /\ e IN ball(y,r)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN frontier E` THEN REWRITE_TAC[frontier; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `E SUBSET (:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)`
  ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3->bool. connected w /\ w SUBSET ball(y,r) DIFF affine hull q /\
                                 ~(w INTER E = {}) ==> w SUBSET E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `e':real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `connected_component
                    ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) e' = E`
    (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "E" THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
      UNDISCH_TAC `(e':real^3) IN w INTER E` THEN EXPAND_TAC "E" THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(e':real^3) IN w INTER E` THEN SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(w:real^3->bool) SUBSET ball(y,r) DIFF affine hull q`;
      `ball(y:real^3,r) INTER UNIONS c1 = ball(y,r) INTER affine hull q`;
      `ball(y:real^3,r) INTER (UNIONS c2 UNION UNIONS c3) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3) IN u \/ e IN v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(e:real^3) IN E`; `(e:real^3) IN ball(y,r)`;
      `E SUBSET (:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)`;
      `ball(y:real^3,r) INTER UNIONS c1 = ball(y,r) INTER affine hull q`;
      `u UNION v = ball(y:real^3,r) DIFF affine hull q`] THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S6T_CASE_B0 THEN
    MAP_EVERY EXISTS_TAC [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
      `c3:(real^3->bool)->bool`; `b:real^3->bool`; `i2:real^3->bool`; `i3:real^3->bool`;
      `x:real^3`; `y:real^3`; `r:real`; `affine hull q:real^3->bool`;
      `u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MOI_S6T_B_TAC;
    MATCH_MP_TAC MOI_S6T_CASE_B0 THEN
    MAP_EVERY EXISTS_TAC [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
      `c3:(real^3->bool)->bool`; `b:real^3->bool`; `i2:real^3->bool`; `i3:real^3->bool`;
      `x:real^3`; `y:real^3`; `r:real`; `affine hull q:real^3->bool`;
      `v:real^3->bool`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MOI_S6T_B_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The three cases, and Moise 26.7 (THREE_267).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S6T_MAIN = prove
 (mk_imp(list_mk_conj [`MOISE_266_STATEMENT`; sdd_i3 MOI_S26_SURF_GLUE_BODY;
                       sdd_i3 MOI_S26_INT_CONNECTED; MOI_S26_LOCAL_TRI],
  `!c1 c2 c3 b x.
     moi_s6t_ctx c1 c2 c3 b /\ ~(x IN UNIONS c1 UNION UNIONS c2 UNION UNIONS c3) /\
     ~bounded (connected_component
                 ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x)
     ==> (frontier (connected_component
                      ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) =
          UNIONS c1 UNION UNIONS c2 /\
          !y. y IN UNIONS c3 DIFF b
              ==> bounded (connected_component ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2)) y)) \/
         (frontier (connected_component
                      ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) =
          UNIONS c1 UNION UNIONS c3 /\
          !y. y IN UNIONS c2 DIFF b
              ==> bounded (connected_component ((:real^3) DIFF (UNIONS c1 UNION UNIONS c3)) y)) \/
         (frontier (connected_component
                      ((:real^3) DIFF (UNIONS c1 UNION UNIONS c2 UNION UNIONS c3)) x) =
          UNIONS c2 UNION UNIONS c3 /\
          !y. y IN UNIONS c1 DIFF b
              ==> bounded (connected_component ((:real^3) DIFF (UNIONS c2 UNION UNIONS c3)) y))`),
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6t_ctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6T_CTX_PERM) THEN
  SUBGOAL_THEN `moi_s6t_ctx c2 c3 c1 b /\ moi_s6t_ctx c3 c1 c2 b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S6T_CTX_PERM]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S6T_PAIR (ASSUME (sdd_i3 MOI_S26_SURF_GLUE_BODY))) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`c2:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`;
                  `c1:(real^3->bool)->bool`; `b:real^3->bool`] th) THEN
    MP_TAC(SPECL [`c1:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`;
                  `c2:(real^3->bool)->bool`; `b:real^3->bool`] th) THEN
    MP_TAC(SPECL [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
                  `c3:(real^3->bool)->bool`; `b:real^3->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `i3:real^3->bool`) THEN
  DISCH_THEN(X_CHOOSE_TAC `i2:real^3->bool`) THEN
  DISCH_THEN(X_CHOOSE_TAC `i1:real^3->bool`) THEN
  SUBGOAL_THEN `connected (UNIONS c1 DIFF surface_boundary (c1:(real^3->bool)->bool)) /\
                connected (UNIONS c2 DIFF surface_boundary (c2:(real^3->bool)->bool)) /\
                connected (UNIONS (c3:(real^3->bool)->bool) DIFF surface_boundary c3)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC(ASSUME (sdd_i3 MOI_S26_INT_CONNECTED)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE
     [ASSUME `surface_boundary (c1:(real^3->bool)->bool) = b`;
      ASSUME `surface_boundary (c2:(real^3->bool)->bool) = b`;
      ASSUME `surface_boundary (c3:(real^3->bool)->bool) = b`])] THEN
  SUBGOAL_THEN
   `(UNIONS c3 DIFF b SUBSET i3 \/
     UNIONS c3 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c2)) /\
    (UNIONS c2 DIFF b SUBSET i2 \/
     UNIONS c2 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c3)) /\
    (UNIONS c1 DIFF b SUBSET i1 \/
     UNIONS c1 DIFF b SUBSET outside (UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S6T_SIDE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (UNIONS c1 DIFF b) (UNIONS (c2:(real^3->bool)->bool) DIFF b)`;
      `DISJOINT (UNIONS c1 DIFF b) (UNIONS (c3:(real^3->bool)->bool) DIFF b)`;
      `DISJOINT (UNIONS c2 DIFF b) (UNIONS (c3:(real^3->bool)->bool) DIFF b)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS c3 DIFF b SUBSET (i3:real^3->bool)` THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_S6T_CASE_A THEN EXISTS_TAC `i3:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS c2 DIFF b SUBSET (i2:real^3->bool)` THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(SPECL [`c1:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`;
                  `c2:(real^3->bool)->bool`; `b:real^3->bool`; `i2:real^3->bool`; `x:real^3`]
      MOI_S6T_CASE_A) THEN
    SUBGOAL_THEN `UNIONS c1 UNION UNIONS c3 UNION UNIONS c2 =
                  UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS c1 DIFF b SUBSET (i1:real^3->bool)` THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`c2:(real^3->bool)->bool`; `c3:(real^3->bool)->bool`;
                  `c1:(real^3->bool)->bool`; `b:real^3->bool`; `i1:real^3->bool`; `x:real^3`]
      MOI_S6T_CASE_A) THEN
    SUBGOAL_THEN `UNIONS c2 UNION UNIONS c3 UNION UNIONS c1 =
                  UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS c3 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c2) /\
    UNIONS c2 DIFF b SUBSET outside (UNIONS c1 UNION UNIONS c3) /\
    UNIONS c1 DIFF b SUBSET outside (UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(SPECL [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
                `c3:(real^3->bool)->bool`; `b:real^3->bool`; `x:real^3`]
    MOI_S6T_GOOD_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
                  `c3:(real^3->bool)->bool`; `b:real^3->bool`; `i2:real^3->bool`;
                  `i3:real^3->bool`; `x:real^3`; `y:real^3`; `q:real^3->bool`]
      (MATCH_MP MOI_S6T_CASE_B (ASSUME MOI_S26_LOCAL_TRI))) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`c2:(real^3->bool)->bool`; `c1:(real^3->bool)->bool`;
                  `c3:(real^3->bool)->bool`; `b:real^3->bool`; `i1:real^3->bool`;
                  `i3:real^3->bool`; `x:real^3`; `y:real^3`; `q:real^3->bool`]
      (MATCH_MP MOI_S6T_CASE_B (ASSUME MOI_S26_LOCAL_TRI))) THEN
    SUBGOAL_THEN `UNIONS c2 UNION UNIONS c1 = UNIONS c1 UNION UNIONS (c2:(real^3->bool)->bool) /\
                  UNIONS c2 UNION UNIONS c1 UNION UNIONS c3 =
                  UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    MP_TAC(SPECL [`c3:(real^3->bool)->bool`; `c1:(real^3->bool)->bool`;
                  `c2:(real^3->bool)->bool`; `b:real^3->bool`; `i1:real^3->bool`;
                  `i2:real^3->bool`; `x:real^3`; `y:real^3`; `q:real^3->bool`]
      (MATCH_MP MOI_S6T_CASE_B (ASSUME MOI_S26_LOCAL_TRI))) THEN
    SUBGOAL_THEN `UNIONS c3 UNION UNIONS c1 = UNIONS c1 UNION UNIONS (c3:(real^3->bool)->bool) /\
                  UNIONS c3 UNION UNIONS c2 = UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool) /\
                  UNIONS c3 UNION UNIONS c1 UNION UNIONS c2 =
                  UNIONS c1 UNION UNIONS c2 UNION UNIONS (c3:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ASM_REWRITE_TAC[]]]);;

let MOI_S6T_UNIONS3 = prove
 (`!c:num->(real^3->bool)->bool.
     UNIONS {UNIONS (c i) | i < 3} = UNIONS (c 0) UNION UNIONS (c 1) UNION UNIONS (c 2)`,
  GEN_TAC THEN
  SUBGOAL_THEN `{UNIONS ((c:num->(real^3->bool)->bool) i) | i < 3} =
                {UNIONS (c 0), UNIONS (c 1), UNIONS (c 2)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[ARITH_RULE `i < 3 <=> i = 0 \/ i = 1 \/ i = 2`; RIGHT_OR_DISTRIB;
                EXISTS_OR_THM; UNWIND_THM2];
    REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY]]);;

let THREE_267 = prove
 (MOI_S26_THREE,
  DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S6T_MAIN) THEN
  REWRITE_TAC[MOISE_267_STATEMENT; MOI_S6T_UNIONS3] THEN
  MAP_EVERY X_GEN_TAC [`c:num->(real^3->bool)->bool`; `x:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `b = surface_boundary ((c:num->(real^3->bool)->bool) 0)` THEN
  SUBGOAL_THEN `surface_boundary ((c:num->(real^3->bool)->bool) 1) = b /\
                surface_boundary (c 2) = b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s6t_ctx (c 0) (c 1) (c 2) (b:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s6t_ctx] THEN ASM_SIMP_TAC[ARITH] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `1`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "DISJOINT")) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `2`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "DISJOINT")) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `2`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "DISJOINT")) (concl th)))] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(c:num->(real^3->bool)->bool) 0`; `(c:num->(real^3->bool)->bool) 1`;
    `(c:num->(real^3->bool)->bool) 2`; `b:real^3->bool`; `x:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "moi_s6t_ctx")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `1`; `2`];
    MAP_EVERY EXISTS_TAC [`0`; `2`; `1`];
    MAP_EVERY EXISTS_TAC [`1`; `2`; `0`]] THEN
  ASM_REWRITE_TAC[ARITH]);;

