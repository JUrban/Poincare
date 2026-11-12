(* ========================================================================= *)
(* pc_moi_star: vertex-star PL atlases of combinatorial 3-manifolds, and    *)
(* combinatoriality as a property of the polyhedron.  Moise, Geometric       *)
(* Topology in Dimensions 2 and 3 (GTM 47): combinatorial manifolds (p.5,   *)
(* p.165, each vertex star a combinatorial cell), Thm 0.2 (p.4), and the     *)
(* convention of Secs 23-36 (p.197) that a PL 3-manifold is a manifold with *)
(* a fixed triangulation, charts coming from vertex stars.                   *)
(* Part 1: the open vertex stars are the domains of a PL atlas (each closed  *)
(* star is the cone from the vertex over its link, a PL 2-sphere, hence PL  *)
(* homeomorphic to a 3-simplex in real^3).                                   *)
(* Part 2: any locally finite complex whose polyhedron is an open subset of *)
(* the polyhedron of a combinatorial 3-manifold is again one (in particular *)
(* any retriangulation, e.g. the barycentric subdivision).                   *)
(* ========================================================================= *)

needs "src/pc_moi_tridef.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_bary.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. A family of PL charts on a subset X of real^N covering X is a PL      *)
(* atlas: the inverse of a PL homeomorphism is PL, so the transition maps   *)
(* are compositions of PL maps on open subsets of real^M.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_STA_PL_ATLAS_FROM_CHARTS = prove
 (`!(X:real^N->bool) (atlas:((real^N->bool)#(real^N->real^M))->bool).
        (!U p. (U,p) IN atlas
               ==> open_in (subtopology euclidean X) U /\ open (IMAGE p U) /\
                   homeomorphic_map (subtopology euclidean U,
                                     subtopology euclidean (IMAGE p U)) p /\
                   pl_map_on U p) /\
        (!x. x IN X ==> ?U p. (U,p) IN atlas /\ x IN U)
        ==> pl_manifold_atlas (subtopology euclidean X) atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_manifold_atlas] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `p:real^N->real^M`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `p:real^N->real^M`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `X INTER U:real^N->bool = U` (fun th -> ASM_REWRITE_TAC[th])
    THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[];
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `p:real^N->real^M`;
                       `V:real^N->bool`; `q:real^N->real^M`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean X) (U:real^N->bool) /\
    open (IMAGE (p:real^N->real^M) U) /\
    homeomorphic_map (subtopology euclidean U,
                      subtopology euclidean (IMAGE p U)) p /\
    pl_map_on U p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean X) (V:real^N->bool) /\
    pl_map_on V (q:real^N->real^M)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?g. homeomorphism (U,IMAGE (p:real^N->real^M) U) (p,g)`
  (X_CHOOSE_TAC `g:real^M->real^N`) THENL
   [UNDISCH_TAC
     `homeomorphic_map (subtopology euclidean U,
                        subtopology euclidean (IMAGE (p:real^N->real^M) U)) p`
    THEN
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY]
    THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (IMAGE (p:real^N->real^M) U) (g:real^M->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `p:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^M) (U INTER V))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^N->real^M) U` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^N->real^M`; `subtopology euclidean (U:real^N->bool)`;
                   `subtopology euclidean (IMAGE (p:real^N->real^M) U)`;
                   `U INTER V:real^N->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; INTER_SUBSET] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN EXISTS_TAC `euclidean:(real^N)topology`
    THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(q:real^N->real^M) o (g:real^M->real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (p:real^N->real^M) U` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; IMAGE_SUBSET; INTER_SUBSET];
      UNDISCH_TAC `homeomorphism (U,IMAGE (p:real^N->real^M) U) (p,g)` THEN
      REWRITE_TAC[homeomorphism] THEN SET_TAC[]];
    UNDISCH_TAC `homeomorphism (U,IMAGE (p:real^N->real^M) U) (p,g)` THEN
    REWRITE_TAC[homeomorphism; IN_INTER; o_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Moving a 3-simplex of real^N to real^3: a translation and a linear    *)
(* isometry of real^3 onto the direction subspace give an affine            *)
(* bijection of relative frontiers.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_STA_SIMPLEX_RF_R3 = prove
 (`!k:real^N->bool.
        &3 simplex k
        ==> ?S:real^3->bool f g.
                &3 simplex S /\
                pl_homeomorphism (relative_frontier S,relative_frontier k) (f,g)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&3 simplex ({}:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  ABBREV_TAC `k0 = IMAGE (\x:real^N. --a + x) k` THEN
  SUBGOAL_THEN `(vec 0:real^N) IN k0` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (k0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN ASM_REWRITE_TAC[SIMPLEX_TRANSLATION_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `dim(span(k0:real^N->bool)) = 3` ASSUME_TAC THENL
   [REWRITE_TAC[DIM_SPAN] THEN
    MP_TAC(ISPEC `k0:real^N->bool` AFF_DIM_DIM_0) THEN
    ANTS_TAC THENL [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k0:real^N->bool`; `&3:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `span(k0:real^N->bool)`] ISOMETRY_SUBSPACES) THEN
  REWRITE_TAC[SUBSPACE_UNIV; SUBSPACE_SPAN; DIM_UNIV; DIMINDEX_3; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y:real^3. (m:real^3->real^N) x = m y ==> x = y`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
    ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:real^3->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':real^N->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^3. (m':real^N->real^3) ((m:real^3->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN k0 ==> (m:real^3->real^N) ((m':real^N->real^3) y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (m:real^3->real^N) (:real^3)` MP_TAC
    THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (m:real^3->real^N) (IMAGE (m':real^N->real^3) k0) = k0`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `!y:real^N. y IN k0 ==> (m:real^3->real^N) ((m':real^N->real^3) y) = y`
    THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (IMAGE (m':real^N->real^3) k0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:real^3->real^N`; `IMAGE (m':real^N->real^3) k0`;
                   `&3:int`] SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier k =
    IMAGE (\z:real^3. (m:real^3->real^N) z + a)
          (relative_frontier (IMAGE (m':real^N->real^3) k0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `k = IMAGE (\x:real^N. a + x) k0` SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (\x:real^N. --a + x) k = k0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; IMAGE_ID];
      ALL_TAC] THEN
    REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN
    SUBGOAL_THEN
     `relative_frontier k0 =
      IMAGE (m:real^3->real^N)
            (relative_frontier (IMAGE (m':real^N->real^3) k0))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `relative_frontier (IMAGE (m:real^3->real^N)
                    (IMAGE (m':real^N->real^3) k0))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (m':real^N->real^3) k0`;
    `\z:real^3. (m:real^3->real^N) z + a`;
    `\x:real^N. (m':real^N->real^3) x - m' a`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `!z:real^3. (m':real^N->real^3) ((m:real^3->real^N) z + a) - m' a = z`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; LINEAR_CONTINUOUS_ON;
                 CONTINUOUS_ON_CONST; ETA_AX];
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

(* The interior of a 3-simplex of real^3 is the simplex minus its relative  *)
(* frontier.                                                                 *)

let MOI_STA_SIMPLEX_INTERIOR = prove
 (`!S:real^3->bool.
        &3 simplex S ==> S DIFF relative_frontier S = interior S`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `relative_interior S:real^3->bool = interior S`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `S:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. The closed star of a vertex v is the cone from v over its link, and    *)
(* the cone is PL homeomorphic to a 3-simplex S of real^3 with the link      *)
(* going onto the relative frontier of S.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_STA_SEGMENT_PARAM = prove
 (`!v x y:real^N.
        y IN segment[v,x] <=> ?u. &0 <= u /\ u <= &1 /\ y = v + u % (x - v)`,
  REWRITE_TAC[IN_SEGMENT] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % v + u % x:real^N = v + u % (x - v)`]);;

let MOI_STA_LINK_FACTS = prove
 (`!c (v:real^N).
        lf_simplicial_complex c
        ==> ~(v IN UNIONS (simplicial_link c v)) /\
            (!x y. x IN UNIONS (simplicial_link c v) /\
                   y IN UNIONS (simplicial_link c v) /\ y IN segment[v,x]
                   ==> y = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((v:real^N) IN UNIONS (simplicial_link c v))` ASSUME_TAC
  THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `v:real^N`]
      MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `u = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LZERO; VECTOR_ADD_RID]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                 `v + u % (x - v):real^N`; `x:real^N`; `&1`; `u:real`]
    MOI_CMB_CONE_UNIQUE) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]; SIMP_TAC[]]);;

let MOI_STA_STAR_PLH = prove
 (`!c (v:real^N).
        combinatorial_manifold 3 c /\ {v} IN c
        ==> ?S:real^3->bool p q.
                &3 simplex S /\
                pl_homeomorphism
                  (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                   S)
                  (p,q) /\
                IMAGE p (UNIONS (simplicial_link c v)) = relative_frontier S /\
                ~(UNIONS (simplicial_link c v) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
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
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^3) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(relative_frontier S:real^3->bool = {})` THEN
    UNDISCH_TAC
     `IMAGE ((f0:real^N->real^N) o (f1:real^3->real^N)) (relative_frontier S) =
      UNIONS (simplicial_link c (v:real^N))` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The open star of a vertex: the points all of whose simplices contain   *)
(* the vertex.  It is open in the polyhedron (local finiteness), equals the *)
(* closed star minus the link, and the open stars of the vertices cover the *)
(* polyhedron.                                                               *)
(* ------------------------------------------------------------------------- *)

let moi_sta_open_star = new_definition
 `moi_sta_open_star (c:(real^N->bool)->bool) (v:real^N) =
    {x | x IN UNIONS c /\ !t. t IN c /\ x IN t ==> v IN t}`;;

let MOI_STA_IMAGE_DIFF = prove
 (`!(p:A->B) q s t l.
        (!x. x IN s ==> q(p x) = x) /\ IMAGE p s = t /\ l SUBSET s
        ==> IMAGE p (s DIFF l) = t DIFF IMAGE p l`,
  SET_TAC[]);;

let MOI_STA_OPEN_STAR_EQ = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        ~(UNIONS (simplicial_link c v) = {})
        ==> moi_sta_open_star c v =
            UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)} DIFF
            UNIONS (simplicial_link c v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  REWRITE_TAC[moi_sta_open_star; EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_CON_IN_CONE] THEN
      SUBGOAL_THEN `?t:real^N->bool. t IN c /\ x IN t` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^N) IN t` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `x:real^N = v` THENL
       [UNDISCH_TAC `~(UNIONS (simplicial_link c (v:real^N)) = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
        MAP_EVERY EXISTS_TAC [`y:real^N`; `&0`] THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LZERO;
                        VECTOR_ADD_RID];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                       `x:real^N`] MOI_CMB_STAR_CONE) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
          STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`y:real^N`; `r:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_CON_IN_CONE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))
   ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
    MOI_CMB_LINK_IN_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(v:real^N) IN t'` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((x:real^N) IN UNIONS (simplicial_link c v))` THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  EXISTS_TAC `t' INTER t:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  SUBGOAL_THEN `(t' INTER t:real^N->bool) face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_STA_OPEN_STAR_OPEN = prove
 (`!c (v:real^N).
        lf_simplicial_complex c
        ==> open_in (subtopology euclidean (UNIONS c)) (moi_sta_open_star c v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{s | s IN c /\ ~(s INTER u = {})}:(real^N->bool)->bool`;
                 `x:real^N`; `u:real^N->bool`] MOI_CMB_FINITE_CLOSED_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN t` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]);;

let MOI_STA_OPEN_STAR_COVER = prove
 (`!c (x:real^N).
        lf_simplicial_complex c /\ x IN UNIONS c
        ==> ?v. {v} IN c /\ x IN moi_sta_open_star c v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN c /\ x IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (t:real^N->bool) /\ compact t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (f:real^N->bool) /\ compact f /\ ~(f = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
      ASM_MESON_TAC[FACE_OF_IMP_COMPACT];
      MP_TAC(ISPEC `f:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  EXISTS_TAC `v:real^N` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{v:real^N} face_of f` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FACE_OF_SING]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t' INTER f:real^N->bool) face_of f` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->bool`; `t' INTER f:real^N->bool`;
                 `f:real^N->bool`] SUBSET_OF_FACE_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `f:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(v:real^N) extreme_point_of f` THEN
  REWRITE_TAC[extreme_point_of] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The vertex chart: the cone homeomorphism restricted to the open star  *)
(* maps it PL homeomorphically onto the interior of S, an open set.         *)
(* ------------------------------------------------------------------------- *)

let MOI_STA_VERTEX_CHART = prove
 (`!c (v:real^N).
        combinatorial_manifold 3 c /\ {v} IN c
        ==> ?p:real^N->real^3.
                open (IMAGE p (moi_sta_open_star c v)) /\
                homeomorphic_map
                  (subtopology euclidean (moi_sta_open_star c v),
                   subtopology euclidean (IMAGE p (moi_sta_open_star c v))) p /\
                pl_map_on (moi_sta_open_star c v) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_STAR_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_OPEN)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `homeomorphism
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)},S)
      ((p:real^N->real^3),(q:real^3->real^N)) /\
    pl_map_on
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))})
      p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}
         ==> (q:real^3->real^N) ((p:real^N->real^3) x) = x) /\
    IMAGE p
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}) =
    S`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphism
        (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)},S)
        ((p:real^N->real^3),(q:real^3->real^N))` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link c (v:real^N)) SUBSET
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_CON_IN_CONE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y:real^N`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sta_open_star c (v:real^N) SUBSET
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ)
    THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^3) (moi_sta_open_star c v) = interior S`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ)
    THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `S:real^3->bool` MOI_STA_SIMPLEX_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `IMAGE (p:real^N->real^3) (UNIONS (simplicial_link c (v:real^N))) =
      relative_frontier S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_STA_IMAGE_DIFF THEN EXISTS_TAC `q:real^3->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `p:real^N->real^3` THEN ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY]
    THEN EXISTS_TAC `q:real^3->real^N` THEN
    UNDISCH_TAC
     `IMAGE (p:real^N->real^3) (moi_sta_open_star c v) = interior S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}`;
      `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC
     `UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `open_in (subtopology euclidean (UNIONS c))
              (moi_sta_open_star c (v:real^N))` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX]]);;

(* ------------------------------------------------------------------------- *)
(* 6. COMBINATORIAL_STAR_ATLAS: the PL charts of a combinatorial 3-manifold  *)
(* (all PL homeomorphisms of open subsets of the polyhedron onto open        *)
(* subsets of real^3) form a PL atlas; the open vertex stars already cover.  *)
(* ------------------------------------------------------------------------- *)

let COMBINATORIAL_STAR_ATLAS = prove
 (`!c:(real^N->bool)->bool.
     3 <= dimindex(:N) /\ combinatorial_manifold 3 c
     ==> ?atlas:((real^N->bool)#(real^N->real^3))->bool.
           pl_manifold_atlas (subtopology euclidean (UNIONS c)) atlas /\
           !U phi. (U,phi) IN atlas ==> pl_map_on U phi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  EXISTS_TAC
   `{(U,p) | open_in (subtopology euclidean (UNIONS c)) (U:real^N->bool) /\
             open (IMAGE (p:real^N->real^3) U) /\
             homeomorphic_map (subtopology euclidean U,
                               subtopology euclidean (IMAGE p U)) p /\
             pl_map_on U p}` THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC MOI_STA_PL_ATLAS_FROM_CHARTS THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`]
    MOI_STA_OPEN_STAR_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_VERTEX_CHART)
  THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`moi_sta_open_star c (v:real^N)`; `p:real^N->real^3`]
  THEN ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* 7. COMBINATORIAL_OPEN_SUBSET, COMBINATORIAL_RETRIANGULATION and           *)
(* COMBINATORIAL_BARYCENTRIC_SUBDIVISION: a locally finite complex whose     *)
(* polyhedron is an open subset of the polyhedron of a combinatorial         *)
(* 3-manifold is a PL triangulation of that open subset (identity map),      *)
(* hence combinatorial.                                                      *)
(* ------------------------------------------------------------------------- *)

let COMBINATORIAL_OPEN_SUBSET = prove
 (`!(c:(real^N->bool)->bool) d.
     3 <= dimindex(:N) /\ combinatorial_manifold 3 c /\
     lf_simplicial_complex d /\
     open_in (subtopology euclidean (UNIONS c)) (UNIONS d)
     ==> combinatorial_manifold 3 d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` COMBINATORIAL_STAR_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `atlas:((real^N->bool)#(real^N->real^3))->bool`
    STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPECL
   [`subtopology euclidean (UNIONS c):(real^N)topology`;
    `atlas:((real^N->bool)#(real^N->real^3))->bool`;
    `d:(real^N->bool)->bool`; `\x:real^N. x`; `UNIONS d:real^N->bool`]
   PL_TRIANGULATION_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[pl_triangulation] THEN
  SUBGOAL_THEN `UNIONS d SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; HOMEOMORPHIC_MAP_ID] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> t INTER s = s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `p:real^N->real^3`] THEN DISCH_TAC THEN
  EXISTS_TAC `p:real^N->real^3` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (U:real^N->bool)`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_manifold_atlas]) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p:real^N->real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{x:real^N | x IN UNIONS d /\ x IN U} = UNIONS d INTER W`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX]);;

let COMBINATORIAL_RETRIANGULATION = prove
 (`!c d:(real^N->bool)->bool.
     3 <= dimindex(:N) /\ combinatorial_manifold 3 c /\
     lf_simplicial_complex d /\ UNIONS d = UNIONS c
     ==> combinatorial_manifold 3 d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMBINATORIAL_OPEN_SUBSET THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let COMBINATORIAL_BARYCENTRIC_SUBDIVISION = prove
 (`!c:(real^N->bool)->bool.
     3 <= dimindex(:N) /\ combinatorial_manifold 3 c
     ==> combinatorial_manifold 3 (barycentric_subdivision c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMBINATORIAL_RETRIANGULATION THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION]);;

