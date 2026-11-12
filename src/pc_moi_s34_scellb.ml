needs "src/pc_moi_s34_recogb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_scellb: the source cells of the Sec 34 cell diagram form a     *)
(* cell diagram on |kk| UNION N (Moise, Geometric Topology in Dimensions 2   *)
(* and 3, GTM 47, Sec 34, p.245, stages (1)-(7), source side).  Main         *)
(* theorem (pc_moi_s34_stmt.ml):                                             *)
(*   SCELL_B = MOI_S34_SCELL_B                                              *)
(* Route.                                                                    *)
(* (1) Labels and dimensions from pc_moi_s34_recoga (MOI_S4G_); the proper  *)
(* faces of a source cell union to the boundary named by scell_facts or by  *)
(* GRAPH_TUBE_DUAL_CELLS.  At an interior vertex the stars in tt and kk     *)
(* agree (a PL 2-sphere inside a PL 2-sphere is all of it, by invariance of *)
(* domain), so the vertex ball of an interior vertex lies in |kk|.           *)
(* (2) Source open cells and point profiles give the meeting property;      *)
(* local finiteness from tt; the union of the cells is |kk| UNION N.        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A PL 2-sphere inside a PL 2-sphere is all of it (any N).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4B_SPHERE_HOMEO = prove
 (`!P:real^N->bool. pl_sphere 2 P ==> sphere(vec 0:real^3,&1) homeomorphic P`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `relative_frontier(k:real^N->bool)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`cball(vec 0:real^3,&1)`; `k:real^N->bool`]
      HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL; AFF_DIM_CBALL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]]);;

let MOI_S4B_PUNCTURED = prove
 (`!(Q:real^N->bool) q. pl_sphere 2 Q /\ q IN Q ==> (Q DELETE q) homeomorphic (:real^2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN
    `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `relative_frontier(k:real^N->bool) DELETE (g:real^N->real^N) q` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `f:real^N->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`Q:real^N->bool`; `relative_frontier(k:real^N->bool)`] THEN
    UNDISCH_TAC `homeomorphism (relative_frontier k,Q) (f:real^N->real^N,g)` THEN
    REWRITE_TAC[GSYM HOMEOMORPHISM_SYM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (Q,relative_frontier k) (g:real^N->real^N,f)` THEN
    REWRITE_TAC[homeomorphism] THEN UNDISCH_TAC `(q:real^N) IN Q` THEN SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN THEN
    REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
      UNDISCH_TAC `homeomorphism (relative_frontier k,Q) (f:real^N->real^N,g)` THEN
      REWRITE_TAC[homeomorphism] THEN UNDISCH_TAC `(q:real^N) IN Q` THEN SET_TAC[];
      ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_ARITH `&3:int = &2 + &1`]]]);;

let MOI_S4B_SPHERE_IN_SPHERE = prove
 (`!P Q:real^N->bool. pl_sphere 2 P /\ pl_sphere 2 Q /\ P SUBSET Q ==> P = Q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Q:real^N->bool`; `q:real^N`] MOI_S4B_PUNCTURED) THEN
  ASM_REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^N->real^2` (X_CHOOSE_TAC `phi':real^2->real^N`)) THEN
  MP_TAC(ISPEC `P:real^N->bool` MOI_S4B_SPHERE_HOMEO) THEN
  ASM_REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^3->real^N` (X_CHOOSE_TAC `th':real^N->real^3`)) THEN
  SUBGOAL_THEN `IMAGE (th:real^3->real^N) (sphere(vec 0,&1)) SUBSET Q DELETE q`
  ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (sphere(vec 0:real^3,&1),P) (th:real^3->real^N,th')` THEN
    REWRITE_TAC[homeomorphism] THEN
    UNDISCH_TAC `(P:real^N->bool) SUBSET Q` THEN UNDISCH_TAC `~((q:real^N) IN P)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:real^N->real^2) o (th:real^3->real^N)) continuous_on
                sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[homeomorphism];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Q DELETE (q:real^N)` THEN
      ASM_MESON_TAC[homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE ((phi:real^N->real^2) o (th:real^3->real^N))
                           (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `&1`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2; DIMINDEX_3;
                    OPEN_IN_REFL] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(th:real^3->real^N) x IN Q DELETE q /\ th y IN Q DELETE q`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (th:real^3->real^N) (sphere(vec 0,&1)) SUBSET Q DELETE q` THEN
      UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(th:real^3->real^N) x = th y` ASSUME_TAC THENL
     [UNDISCH_TAC `homeomorphism (Q DELETE q,(:real^2)) (phi:real^N->real^2,phi')` THEN
      REWRITE_TAC[homeomorphism] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(fun th ->
        ONCE_REWRITE_TAC[GSYM(MATCH_MP th
          (ASSUME `(th:real^3->real^N) x IN Q DELETE q`))] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[MATCH_MP th (ASSUME `(th:real^3->real^N) y IN Q DELETE q`)]);
      UNDISCH_TAC `homeomorphism (sphere(vec 0:real^3,&1),P) (th:real^3->real^N,th')` THEN
      REWRITE_TAC[homeomorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE ((phi:real^N->real^2) o (th:real^3->real^N))
                              (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE ((phi:real^N->real^2) o (th:real^3->real^N)) (sphere(vec 0,&1))`
         CLOPEN) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  UNDISCH_TAC `compact(IMAGE ((phi:real^N->real^2) o (th:real^3->real^N))
                             (sphere(vec 0,&1)))` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Stars at interior vertices and edges lie in kk; vertex balls              *)
(* miss the simplices of tt without the vertex.                               *)
(* ------------------------------------------------------------------------- *)

(* At an interior vertex every simplex of tt containing it is in kk. *)

let MOI_S4B_STAR_IN = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(v IN complex_boundary kk)
     ==> !r. r IN tt /\ v IN r ==> r IN kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (simplicial_link kk (v:real^N)) = UNIONS (simplicial_link tt v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4B_SPHERE_IN_SPHERE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[simplicial_link] THEN
      UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `r = {v:real^N}` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?V:real^N->bool. ~affine_dependent V /\ r = convex hull V /\ FINITE V`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FM3_LF_SIMPLEX) THEN
    ASM_REWRITE_TAC[simplex] THEN MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    UNDISCH_TAC `r = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sg = convex hull (V DELETE (v:real^N))` THEN
  SUBGOAL_THEN `(sg:real^N->bool) face_of r` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[DELETE_SUBSET] THEN
    TRY(FIRST_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `sg:real^N->bool`
                              then ACCEPT_TAC(SYM th) else NO_TAC));
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN sg)` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN DISCH_TAC THEN
    UNDISCH_TAC `~affine_dependent (V:real^N->bool)` THEN REWRITE_TAC[affine_dependent] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `V DELETE (v:real^N)` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    UNDISCH_TAC `(v:real^N) IN convex hull (V DELETE v)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sg:real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(r = {v:real^N})` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `V = {v:real^N}` SUBST1_TAC THENL
     [UNDISCH_TAC `V DELETE (v:real^N) = {}` THEN UNDISCH_TAC `(v:real^N) IN V` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN tt` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(sg:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
  MP_TAC(ISPEC `sg:real^N->bool` RELATIVE_INTERIOR_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^N`) THEN
  SUBGOAL_THEN `(p:real^N) IN UNIONS (simplicial_link kk v)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    EXISTS_TAC `sg:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `sg:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(p:real^N) IN relative_interior sg` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)))
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(sg:real^N->bool) SUBSET ta` ASSUME_TAC THENL
   [SUBGOAL_THEN `(sg INTER ta:real^N->bool) face_of sg` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sg:real^N->bool`; `ta:real^N->bool`]
                    MOI_FM3_LF_INTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
        UNDISCH_TAC `(ta:real^N->bool) IN kk` THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(sg INTER ta:real^N->bool) = sg` THENL
     [UNDISCH_TAC `(sg INTER ta:real^N->bool) = sg` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sg INTER ta:real^N->bool`; `sg:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sg:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^N) IN relative_interior sg` THEN
    UNDISCH_TAC `(p:real^N) IN ta` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `r = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `V DELETE (v:real^N) SUBSET sg` MP_TAC THENL
       [EXPAND_TAC "sg" THEN REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `ta:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^N) IN t` THEN
      UNDISCH_TAC `(sg:real^N->bool) SUBSET ta` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4H_KK_CONVEX THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER t:real^N->bool) face_of t` MP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `r:real^N->bool`; `t:real^N->bool`]
                  MOI_FM3_LF_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(t:real^N->bool) IN kk` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r INTER t:real^N->bool = r` SUBST1_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) SUBSET t` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk` (fun th -> MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `t:real^N->bool`; `r:real^N->bool`]
                MOI_FM3_LF_FACE) THEN
  ASM_SIMP_TAC[]);;

(* Vertex balls miss the simplices of tt without the vertex (the tt form of *)
(* MOI_S4G_VB_OUT, same proof).                                            *)

let MOI_S4B_VB_OUT_TT = prove
 (`!(tt:(real^N->bool)->bool) kk u q.
     moi_s34_tube tt kk /\ {u} IN kk /\ q IN tt /\ ~(u IN q)
     ==> moi_s34_vb tt kk u INTER q = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN skeleton 1 kk` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN tt` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN tt /\ u IN sg /\ x IN sg` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_vb tt kk u SUBSET UNIONS {s | s IN tt /\ (u:real^N) IN s}` THEN
    UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Vs:real^N->bool. ~affine_dependent Vs /\ sg = convex hull Vs`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; simplex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN Vs` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN UNIONS {s | s IN barycentric_subdivision tt /\ (u:real^N) IN s}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u` THEN
    REWRITE_TAC[moi_s34_vb; derived_dual_cell; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN Vs ==> moi_s4a_bc Vs a x <= moi_s4a_bc Vs u x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sg:real^N->bool`; `u:real^N`]
                  MOI_S4A_STAR_IN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sg:real^N->bool = convex hull Vs` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[MOI_S4A_BC_STAR] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q INTER sg:real^N->bool) face_of sg` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  UNDISCH_TAC `sg:real^N->bool = convex hull Vs` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull E` ASSUME_TAC THENL
   [UNDISCH_TAC `q INTER convex hull Vs:real^N->bool = convex hull E` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N) IN E)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N) IN convex hull E` MP_TAC THENL
     [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
    UNDISCH_TAC `q INTER convex hull Vs:real^N->bool = convex hull E` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4a_bc Vs (u:real^N) x = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Vs:real^N->bool`; `E:real^N->bool`] MOI_S4A_BC_SUBHULL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Vs:real^N->bool`; `x:real^N`] MOI_S4A_BC_HULL_EXPAND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `Vs:real^N->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &0 ==> s = &1 ==> F`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum (Vs:real^N->bool) (\a. &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `moi_s4a_bc Vs (u:real^N) x` THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    REWRITE_TAC[SUM_0; REAL_LE_REFL]]);;

(* The vertex ball of an interior vertex lies in |kk|. *)

let MOI_S4B_VB_KK = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(v IN complex_boundary kk)
     ==> moi_s34_vb tt kk v SUBSET UNIONS kk`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                MOI_S4B_STAR_IN) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* A splitting disk lies in the simplices of tt containing its edge. *)

let MOI_S4B_SD_STAR = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> moi_s34_sd tt kk g SUBSET UNIONS {q | q IN tt /\ g SUBSET q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_vb tt kk a /\ y IN moi_s34_vb tt kk b`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`; `a:real^N`] MOI_S4G_SD_SUB_VB) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`; `b:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk (segment[a,b])` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN tt /\ a IN sg /\ y IN sg` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_vb tt kk a SUBSET UNIONS {s | s IN tt /\ (a:real^N) IN s}` THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk a` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N) IN sg` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `b:real^N`;
                   `sg:real^N->bool`] MOI_S4B_VB_OUT_TT) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk b` THEN UNDISCH_TAC `(y:real^N) IN sg` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `sg:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex(sg:real^N->bool)` MP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sg:real^N->bool`] MOI_FDN_LF_SIMPLEX) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4A_TUBE]; SIMP_TAC[]];
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]]);;

(* The splitting disk of an interior edge lies in |kk|. *)

let MOI_S4B_SD_KK = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ ~(g SUBSET complex_boundary kk)
     ==> moi_s34_sd tt kk g SUBSET UNIONS kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4B_SD_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `a:real^N`;
                 `b:real^N`] MOI_S4O_EDGE_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(a:real^N = b)` THEN MESON_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  UNDISCH_TAC `moi_s34_sd tt kk (segment[a,b]) SUBSET
               UNIONS {q | q IN tt /\ segment[a:real^N,b] SUBSET q}` THEN
  UNDISCH_TAC `!q. q IN tt /\ segment[a:real^N,b] SUBSET q ==> q IN kk` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The union of the proper faces of a source cell, by labels.                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4B_BDRY_MEM = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x y.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x
     ==> (y IN UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)} <=>
          ?m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\
                       moi_s4g_face kk k' q' x' k q x /\
                       ~(k' = k /\ q' = q /\ x' = x) /\ y IN m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(m:real^N->bool) IN moi_s34_scells tt kk` THEN
    REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `q':real^N->bool`
      (X_CHOOSE_TAC `x':real^N->bool`))) THEN
    MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                   `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_PROPER_FACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                   `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_PROPER_FACE) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4B_BS_RULE = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x (H:real^N->bool).
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\
     (!m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\ moi_s4g_face kk k' q' x' k q x /\
                   ~(k' = k /\ q' = q /\ x' = x)
                   ==> m SUBSET H) /\
     (!y. y IN H
          ==> ?m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\
                           moi_s4g_face kk k' q' x' k q x /\
                           ~(k' = k /\ q' = q /\ x' = x) /\ y IN m)
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)} = H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN ASSUME_TAC (el 1 cs) THEN
    LABEL_TAC "A" (el 2 cs) THEN LABEL_TAC "B" (el 3 cs)) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`; `y:real^N`] MOI_S4B_BDRY_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    STRIP_TAC THEN
    USE_THEN "A" (MP_TAC o SPECL [`m:real^N->bool`; `k':num`; `q':real^N->bool`;
                                  `x':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Tactic: the common start of the inclusion part (proper faces by kind). *)

let MOI_S4B_SUB_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let lab,rest = CONJ_PAIR th in
    MP_TAC(MATCH_MP MOI_S4G_LAB_PARAMS lab) THEN
    SUBST1_TAC(MATCH_MP MOI_S4G_LAB_CELL lab) THEN MP_TAC rest) THEN
  REWRITE_TAC[moi_s4g_face; ARITH_EQ; SING_SUBSET] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ; MOI_S4G_CHOICE_SING; moi_s4g_cell] THEN REPEAT STRIP_TAC;;

(* The splitting disk of an edge at v is the meet of two vertex balls. *)

let MOI_S4B_SD_PAIR = prove
 (`!(tt:(real^N->bool)->bool) kk g v.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ v IN g /\ {v} IN kk
     ==> ?w. ~(w = v) /\ segment[v,w] IN skeleton 1 kk /\
             moi_s34_sd tt kk g = moi_s34_vb tt kk v INTER moi_s34_vb tt kk w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (segment[a,b]) =
                moi_s34_vb tt kk a INTER moi_s34_vb tt kk (b:real^N)` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] IN skeleton 1 kk` ASSUME_TAC THENL
   [REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v:real^N = a \/ v = b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) IN segment[a,b]` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `{a:real^N,b}`;
                   `v:real^N`] MOI_S4A_VTX) THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; AFFINE_INDEPENDENT_2; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[INTER_COMM] THEN ASM_MESON_TAC[]]);;

(* A PL 2-ball is nonempty; a vertex of kk lies in a larger simplex of kk.   *)

let MOI_S4B_BALL2_NE = prove
 (`!S:real^N->bool. pl_ball 2 S ==> ~(S = {})`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) k = S` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN DISCH_TAC THEN
  UNDISCH_TAC `&(CARD(c:real^N->bool)):int = &2 + &1` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES] THEN INT_ARITH_TAC);;

let MOI_S4B_VERTEX_UP = prove
 (`!(tt:(real^N->bool)->bool) kk u.
     moi_s34_tube tt kk /\ {u} IN kk ==> ?t. t IN kk /\ u IN t /\ ~(t = {u})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `u:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link kk (u:real^N)) = {})` MP_TAC THENL
   [ASM_CASES_TAC `(u:real^N) IN complex_boundary kk` THEN
    ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY; MOI_S4B_BALL2_NE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` (X_CHOOSE_THEN `f:real^N->bool`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC))) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`{u:real^N}`; `f:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN f` THEN UNDISCH_TAC `~((u:real^N) IN f)` THEN
  SET_TAC[]);;

(* Every point of |kk| lies in a 3-simplex of kk. *)

let MOI_S4B_KK_TETRA = prove
 (`!(tt:(real^N->bool)->bool) kk y.
     moi_s34_tube tt kk /\ y IN UNIONS kk
     ==> ?r. r IN moi_s34_simp kk (&3) /\ y IN r`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNIONS]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?u:real^N. u IN V` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(y:real^N) IN q` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                   `u:real^N`] MOI_S4A_VTX_KK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `q = convex hull (V:real^N->bool)` THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN q` ASSUME_TAC THENL
   [UNDISCH_TAC `q = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s. s IN kk /\ (u:real^N) IN s /\ q SUBSET s /\ ~(s = {u})`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `q = {u:real^N}` THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N`]
                    MOI_S4B_VERTEX_UP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
      STRIP_TAC THEN UNDISCH_TAC `q = {u:real^N}` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET];
      EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N`;
                 `s:real^N->bool`] MOI_S4O_KK_PURE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
  UNDISCH_TAC `(y:real^N) IN q` THEN UNDISCH_TAC `(q:real^N->bool) SUBSET s` THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The source boundary identities SBS1-SBS10: the union of the              *)
(* proper faces of a source cell is the boundary named by scell_facts or by *)
(* GRAPH_TUBE_DUAL_CELLS.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4B_UNM_TAC : tactic =
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN ASM_MESON_TAC[SING_SUBSET];;

let MOI_S4B_UNION_L = SET_RULE
 `!a b c:real^N->bool. b SUBSET a ==> b SUBSET a UNION c`;;

let MOI_S4B_UNION_R = SET_RULE
 `!a b c:real^N->bool. b SUBSET c ==> b SUBSET a UNION c`;;

(* SBS1: vertex balls. *)

let MOI_S4B_SBS1 = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_vb tt kk v /\
                     ~(m = moi_s34_vb tt kk v)} =
         (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {moi_s34_vb tt kk v INTER moi_s34_vb tt kk w | w |
                 ~(w = v) /\ segment[v,w] IN skeleton 1 kk}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`1`; `{v:real^N}`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab] THEN ASM_MESON_TAC[];
    MOI_S4B_SUB_TAC THENL
     [(* 2 *) MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                             `q':real^N->bool`; `v:real^N`] MOI_S4B_SD_PAIR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4B_UNION_R THEN MOI_S4B_UNM_TAC;
      ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4B_UNION_L THENL
     [(* 5 *) SET_TAC[];
      (* 6 *) SET_TAC[];
      (* 7 *) MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                             `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      (* 8 *) MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                             `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      (* 9 *) USE_THEN "o1" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      (* 10 *) USE_THEN "o2" (MP_TAC o SPEC `q':real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `q':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [ASM_CASES_TAC `(y:real^N) IN UNIONS kk` THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `y:real^N`]
                      MOI_S4B_KK_TETRA) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(v:real^N) IN r` ASSUME_TAC THENL
         [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                         `r:real^N->bool`] MOI_S4G_VB_OUT) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
          UNDISCH_TAC `(y:real^N) IN r` THEN
          UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
          SET_TAC[];
          ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [`r INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                              `5`; `r:real^N->bool`; `{v:real^N}`] THEN
        REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
        UNDISCH_TAC `(y:real^N) IN r` THEN SET_TAC[];
        SUBGOAL_THEN `(v:real^N) IN complex_boundary kk` ASSUME_TAC THENL
         [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                        MOI_S4B_VB_KK) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `~((y:real^N) IN UNIONS kk)` THEN
          UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
          SET_TAC[];
          ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [`closure((moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk)
                                       DIFF UNIONS kk)`; `9`; `{v:real^N}`;
                              `{}:real^N->bool`] THEN
        REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
        UNDISCH_TAC `~((y:real^N) IN UNIONS kk)` THEN
        UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
        SET_TAC[]];
      SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `segment[v:real^N,w] IN moi_s34_simp kk (&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `segment[v:real^N,w] IN skeleton 1 kk` THEN
        REWRITE_TAC[skeleton; moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[] THEN
        ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`moi_s34_sd tt kk (segment[v:real^N,w])`; `2`;
                            `segment[v:real^N,w]`; `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ; SING_SUBSET; ENDS_IN_SEGMENT] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_s34_sd tt kk (segment[v,w]) =
                    moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)` SUBST1_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v:real^N,w] IN moi_s34_simp kk (&1)` THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MESON_TAC[MOI_S4H_SIMP_KK];
        ASM_REWRITE_TAC[]]]]);;

(* Helpers: a point of Bd N in a simplex q of kk lies in a vertex ball of a *)
(* vertex of q; a splitting disk meeting a simplex of kk has its edge in it. *)

let MOI_S4B_BD_VB = prove
 (`!(tt:(real^N->bool)->bool) kk q y.
     moi_s34_tube tt kk /\ q IN kk /\ y IN q /\ y IN moi_s34_bd tt kk
     ==> ?v. v IN q /\ {v} IN kk /\ y IN moi_s34_vb tt kk v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4G_BD_NB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_NB_UNIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `q:real^N->bool`] MOI_S4G_VB_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN q` THEN UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v` THEN
  SET_TAC[]);;

let MOI_S4B_SD_IN = prove
 (`!(tt:(real^N->bool)->bool) kk g q.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ q IN kk /\
     ~(moi_s34_sd tt kk g INTER q = {})
     ==> g SUBSET q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (segment[a,b]) =
                moi_s34_vb tt kk a INTER moi_s34_vb tt kk (b:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN q /\ b IN q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `a:real^N`;
                     `q:real^N->bool`] MOI_S4G_VB_OUT);
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `b:real^N`;
                     `q:real^N->bool`] MOI_S4G_VB_OUT)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    UNDISCH_TAC `~(moi_s34_sd tt kk (segment[a:real^N,b]) INTER q = {})` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(q:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_KK_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* SBS2: splitting disks. *)

let MOI_S4B_SBS2 = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_sd tt kk g /\
                     ~(m = moi_s34_sd tt kk g)} =
         moi_s34_sd tt kk g INTER moi_s34_bd tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`2`; `g:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC THENL
     [SET_TAC[];
      SET_TAC[];
      USE_THEN "o2" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN UNIONS kk` THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `y:real^N`]
                    MOI_S4B_KK_TETRA) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(g:real^N->bool) SUBSET r` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S4B_SD_IN THEN
        MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
        UNDISCH_TAC `(y:real^N) IN r` THEN
        UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk g INTER moi_s34_bd tt kk` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`r INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                            `7`; `r:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN r` THEN
      UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk g INTER moi_s34_bd tt kk` THEN
      SET_TAC[];
      SUBGOAL_THEN `(g:real^N->bool) SUBSET complex_boundary kk` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
                      MOI_S4B_SD_KK) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `~((y:real^N) IN UNIONS kk)` THEN
        UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk g INTER moi_s34_bd tt kk` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`closure((moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk)
                                     DIFF UNIONS kk)`; `10`; `g:real^N->bool`;
                            `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      UNDISCH_TAC `~((y:real^N) IN UNIONS kk)` THEN
      UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk g INTER moi_s34_bd tt kk` THEN
      SET_TAC[]]]);;

(* SBS3: face disks. *)

let MOI_S4B_SBS3 = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET closure (s DIFF moi_s34_nb tt kk) /\
                     ~(m = closure (s DIFF moi_s34_nb tt kk))} =
         s INTER moi_s34_bd tt kk`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`3`; `s:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC THEN SET_TAC[];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`;
                   `y:real^N`] MOI_S4B_BD_VB) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                          `6`; `s:real^N->bool`; `{v:real^N}`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]);;

(* SBS4: tetra balls. *)

let MOI_S4B_SBS4 = prove
 (`!(tt:(real^N->bool)->bool) kk r.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3)
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET closure (r DIFF moi_s34_nb tt kk) /\
                     ~(m = closure (r DIFF moi_s34_nb tt kk))} =
         UNIONS {closure (s DIFF moi_s34_nb tt kk) | s |
                 s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
         (r INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`4`; `r:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC THENL
     [MOI_S4B_UNM_TAC;
      MATCH_MP_TAC MOI_S4B_UNION_R THEN UNDISCH_TAC `(q':real^N->bool) SUBSET r` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4B_UNION_R THEN UNDISCH_TAC `(q':real^N->bool) SUBSET r` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4B_UNION_R THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4B_UNION_R THEN SET_TAC[]];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`closure (s DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))`;
                            `3`; `s:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^N) IN r INTER moi_s34_bd tt kk` THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                     `y:real^N`] MOI_S4B_BD_VB) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`r INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                            `5`; `r:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]]);;

(* SBS5: patches X(r,v). *)

let MOI_S4B_SBS5 = prove
 (`!(tt:(real^N->bool)->bool) kk r v.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                     ~(m = r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)} =
         UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
         UNIONS {r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`5`; `r:real^N->bool`; `{v:real^N}`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab] THEN ASM_MESON_TAC[];
    MOI_S4B_SUB_TAC THENL
     [MOI_S4B_UNM_TAC;
      MOI_S4B_UNM_TAC;
      MATCH_MP_TAC MOI_S4B_UNION_R THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN EXISTS_TAC `x':real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET_TRANS]; ASM_MESON_TAC[SUBSET]]];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                            `6`; `s:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`r INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                            `7`; `r:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ; SING_SUBSET] THEN
      ASM_REWRITE_TAC[]]]);;

(* SBS6: face arcs X(s,v). *)

let MOI_S4B_SBS6 = prove
 (`!(tt:(real^N->bool)->bool) kk s v.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                     ~(m = s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)} =
         UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`6`; `s:real^N->bool`; `{v:real^N}`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab] THEN ASM_MESON_TAC[];
    MOI_S4B_SUB_TAC THEN MOI_S4B_UNM_TAC;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ; SING_SUBSET] THEN
    ASM_REWRITE_TAC[]]);;

(* SBS7: edge arcs X(r,g). *)

let MOI_S4B_SBS7 = prove
 (`!(tt:(real^N->bool)->bool) kk r g.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET r
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                     ~(m = r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)} =
         UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                 s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`7`; `r:real^N->bool`; `g:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC THEN MOI_S4B_UNM_TAC;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
    ASM_REWRITE_TAC[]]);;

(* SBS8: marked points have no proper faces. *)

let MOI_S4B_SBS8 = prove
 (`!(tt:(real^N->bool)->bool) kk s g.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET s
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                     ~(m = s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)} = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`8`; `s:real^N->bool`; `g:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC;
    REWRITE_TAC[NOT_IN_EMPTY]]);;

(* SBS9: outer patches. *)

let MOI_S4B_SBS9 = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                       UNIONS kk) /\
                     ~(m = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk))} =
         UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
         UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`9`; `{v:real^N}`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab] THEN ASM_MESON_TAC[];
    MOI_S4B_SUB_TAC THENL
     [MOI_S4B_UNM_TAC;
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MATCH_MP_TAC MOI_S4B_UNION_L THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN EXISTS_TAC `q':real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      MOI_S4B_UNM_TAC];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                            `6`; `s:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`closure ((moi_s34_sd tt kk (g:real^N->bool) INTER
                                       moi_s34_bd tt kk) DIFF UNIONS kk)`;
                            `10`; `g:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ; SING_SUBSET] THEN
      ASM_REWRITE_TAC[]]]);;

(* SBS10: outer arcs. *)

let MOI_S4B_SBS10 = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
     ==> UNIONS {m | m IN moi_s34_scells tt kk /\
                     m SUBSET closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                       UNIONS kk) /\
                     ~(m = closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk))} =
         UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                 s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET complex_boundary kk}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4B_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`10`; `g:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_s4g_lab];
    MOI_S4B_SUB_TAC THEN MOI_S4B_UNM_TAC;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; ARITH_EQ] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* (S1) every source cell is a PL cell of its dimension whose                *)
(* boundary is the union of its proper faces; (S2) proper faces have        *)
(* smaller dimension.                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4B_CELLB = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s34_tube tt kk /\ moi_s34_scell_facts tt kk /\ moi_s4g_lab tt kk l k q x
     ==> pl_cell_with_boundary (moi_s4g_kd k) l
           (UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_scell_facts (tt:(real^N->bool)->bool) kk` THEN
  REWRITE_TAC[moi_s34_scell_facts] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "c1" (el 0 cs) THEN LABEL_TAC "c2" (el 1 cs) THEN
    LABEL_TAC "c3" (el 2 cs) THEN LABEL_TAC "c4" (el 3 cs) THEN
    LABEL_TAC "c5" (el 4 cs) THEN LABEL_TAC "c6" (el 5 cs) THEN
    LABEL_TAC "c7" (el 6 cs) THEN LABEL_TAC "c8" (el 7 cs)) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb; GSYM moi_s34_bd] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "gv" (el 1 cs) THEN LABEL_TAC "ge" (el 2 cs)) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_kd] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [(* 1 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                  MOI_S4B_SBS1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "gv" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS)];
    (* 2 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                  MOI_S4B_SBS2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_s34_sd tt kk q = moi_s34_vb tt kk a INTER moi_s34_vb tt kk (b:real^N)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC MOI_S4A_SD_EDGE THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
      ALL_TAC] THEN
    REWRITE_TAC[INTER_ASSOC] THEN
    USE_THEN "ge" (MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL;
                      AFF_DIM_2] THEN
      UNDISCH_TAC `segment[a:real^N,b] IN kk` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SIMP_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    (* 3 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                  MOI_S4B_SBS3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c2" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 4 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                  MOI_S4B_SBS4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c1" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 5 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`;
                   `v:real^N`] MOI_S4B_SBS5) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c3" (MP_TAC o SPECL [`q:real^N->bool`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 6 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`;
                   `v:real^N`] MOI_S4B_SBS6) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c4" (MP_TAC o SPECL [`q:real^N->bool`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 7 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`;
                   `x:real^N->bool`] MOI_S4B_SBS7) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c5" (MP_TAC o SPECL [`q:real^N->bool`; `x:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 8 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`;
                   `x:real^N->bool`] MOI_S4B_SBS8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c6" (MP_TAC o SPECL [`q:real^N->bool`; `x:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` SUBST1_TAC) THEN
    REWRITE_TAC[MOI_S4G_POINT_CELL];
    (* 9 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                  MOI_S4B_SBS9) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c7" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* 10 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                  MOI_S4B_SBS10) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "c8" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

let MOI_S4B_S1 = prove
 (`!(tt:(real^N->bool)->bool) kk l.
     moi_s34_tube tt kk /\ moi_s34_scell_facts tt kk /\ l IN moi_s34_scells tt kk
     ==> moi_s34_dim l <= 3 /\
         pl_cell_with_boundary (moi_s34_dim l) l
           (UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(l:real^N->bool) IN moi_s34_scells tt kk` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
    (X_CHOOSE_TAC `x:real^N->bool`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_DIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_S4H_KD_LE] THEN MATCH_MP_TAC MOI_S4B_CELLB THEN
  MAP_EVERY EXISTS_TAC [`q:real^N->bool`; `x:real^N->bool`] THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Separation facts for the source cells: three vertex balls never           *)
(* meet; Bd N misses the 1-skeleton; Cl(q - N) meets N only in Bd N.         *)
(* ------------------------------------------------------------------------- *)

(* Source form: a point lies in at most two vertex balls (TUBE_TRIPLE of    *)
(* pc_moi_s35_triple), and two vertex balls meet only along an edge of kk.  *)

let MOI_S4B_VB3 = prove
 (`!(tt:(real^N->bool)->bool) kk u v w y.
     moi_s34_tube tt kk /\ {u} IN kk /\ {v} IN kk /\ {w} IN kk /\
     y IN moi_s34_vb tt kk u /\ y IN moi_s34_vb tt kk v /\ y IN moi_s34_vb tt kk w
     ==> u = v \/ u = w \/ v = w`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `u:real^N = v` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u:real^N = w` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v:real^N = w` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `u:real^N`; `v:real^N`; `w:real^N`] TUBE_TRIPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM moi_s34_vb] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk u` THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v` THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk w` THEN SET_TAC[]]);;

let MOI_S4B_VB2 = prove
 (`!(tt:(real^N->bool)->bool) kk u v y.
     moi_s34_tube tt kk /\ {u} IN kk /\ {v} IN kk /\ ~(u = v) /\
     y IN moi_s34_vb tt kk u /\ y IN moi_s34_vb tt kk v
     ==> segment[u,v] IN moi_s34_simp kk (&1) /\
         moi_s34_sd tt kk (segment[u,v]) =
         moi_s34_vb tt kk u INTER moi_s34_vb tt kk v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[u:real^N,v] IN kk` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                   `u:real^N`; `v:real^N`] MOI_FTA_CELLS_DISJOINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
      REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN
      CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM moi_s34_vb] THEN
      UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk u` THEN
      UNDISCH_TAC `(y:real^N) IN moi_s34_vb tt kk v` THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL]]);;

(* Bd N misses the simplices of kk of dimension at most 1. *)

let MOI_S4B_BD_SKEL = prove
 (`!(tt:(real^N->bool)->bool) kk q y.
     moi_s34_tube tt kk /\ q IN kk /\ aff_dim q <= &1 /\ y IN q
     ==> ~(y IN moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `q:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MOI_S4G_FLAT_THEN "h"] THEN
  UNDISCH_TAC `(y:real^N) IN moi_s34_bd tt kk` THEN
  MOI_S4G_USE_IFF "fbd" [`y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `{}:real^N->bool`; `(h:real^N->real^N) y`;
                 `&2 / &5`] MOI_S4A_BC_SUM_LE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[EMPTY_SUBSET; DIFF_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES; DIFF_EMPTY] THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) <= 2` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `aff_dim(convex hull V:real^N->bool) <= &1` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC]);;

(* Cl(q - N) meets N only in Bd N. *)

let MOI_S4B_CL_NB = prove
 (`!(tt:(real^N->bool)->bool) kk q y.
     moi_s34_tube tt kk /\ q IN kk /\ y IN closure (q DIFF moi_s34_nb tt kk) /\
     y IN moi_s34_nb tt kk
     ==> y IN moi_s34_bd tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `q:real^N->bool`)) THEN
  SUBGOAL_THEN `(y:real^N) IN convex hull V` ASSUME_TAC THENL
   [SUBGOAL_THEN `closure (convex hull V DIFF moi_s34_nb tt kk) SUBSET
                  convex hull (V:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[SUBSET_DIFF; COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL;
                   FINITE_IMP_COMPACT];
      UNDISCH_TAC `(y:real^N) IN closure (convex hull V DIFF moi_s34_nb tt kk)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MOI_S4G_FLAT_THEN "h"] THEN
  UNDISCH_TAC `(y:real^N) IN closure (convex hull V DIFF moi_s34_nb tt kk)` THEN
  MOI_S4G_USE_IFF "fcl" [`y:real^N`] THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_s34_nb tt kk` THEN
  MOI_S4G_USE_IFF "fnb" [`y:real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MOI_S4G_USE_IFF "fbd" [`y:real^N`] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y /\ y <= x ==> x = y`) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness facts for the source profiles.                                  *)
(* ------------------------------------------------------------------------- *)

(* Two simplices of kk through y, the first not inside the second: y lies   *)
(* in a lower-dimensional face of the first.                                 *)

let MOI_S4B_SIMP_MEET = prove
 (`!(tt:(real^N->bool)->bool) kk q1 q2 y.
     moi_s34_tube tt kk /\ q1 IN kk /\ q2 IN kk /\ y IN q1 /\ y IN q2 /\
     ~(q1 SUBSET q2)
     ==> ?f. f IN kk /\ y IN f /\ f SUBSET q1 /\ aff_dim f < aff_dim q1`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  EXISTS_TAC `q1 INTER q2:real^N->bool` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `q1:real^N->bool`; `q2:real^N->bool`]
                MOI_FM3_LF_INTER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    SET_TAC[];
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4H_KK_CONVEX];
      UNDISCH_TAC `~((q1:real^N->bool) SUBSET q2)` THEN SET_TAC[]]]);;

(* The 1-skeleton of kk lies in N and misses Bd N. *)

let MOI_S4B_SKEL_NB = prove
 (`!(tt:(real^N->bool)->bool) kk f y.
     moi_s34_tube tt kk /\ f IN kk /\ aff_dim f <= &1 /\ y IN f
     ==> y IN moi_s34_nb tt kk`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                MOI_FTA_GRAPH_IN_NBHD) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_nb] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; skeleton; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S4B_LOW = prove
 (`!(tt:(real^N->bool)->bool) kk f y.
     moi_s34_tube tt kk /\ f IN kk /\ aff_dim f <= &1 /\ y IN f /\
     (~(y IN moi_s34_nb tt kk) \/ y IN moi_s34_bd tt kk)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `~((y:real^N) IN moi_s34_nb tt kk)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4B_SKEL_NB THEN EXISTS_TAC `f:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f:real^N->bool`; `y:real^N`] MOI_S4B_BD_SKEL) THEN
    ASM_REWRITE_TAC[]]);;

(* A point of complex_boundary kk lies in a boundary triangle. *)

let MOI_S4B_CB_TRI = prove
 (`!(kk:(real^N->bool)->bool) y.
     y IN complex_boundary kk
     ==> ?s. s IN moi_s34_simp kk (&2) /\ s SUBSET complex_boundary kk /\ y IN s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[complex_boundary; IN_UNIONS; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
  REWRITE_TAC[complex_boundary] THEN GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Uniqueness of the triangle, tetrahedron and edge through a point. *)

let MOI_S4B_S2_UNIQ = prove
 (`!(tt:(real^N->bool)->bool) kk s s' y.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\
     y IN s /\ y IN s' /\ (~(y IN moi_s34_nb tt kk) \/ y IN moi_s34_bd tt kk)
     ==> s = s'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`; `s':real^N->bool`; `y:real^N`] MOI_S4B_SIMP_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4H_SIMP_KK];
      ASM_MESON_TAC[MOI_S4H_SIMP_KK];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `s:real^N->bool`; `s':real^N->bool`; `2`; `2`] MOI_S4G_NEST) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S4B_LOW THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `f:real^N->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(f:real^N->bool) < aff_dim(s:real^N->bool)` THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN INT_ARITH_TAC]);;

let MOI_S4B_S23 = prove
 (`!(tt:(real^N->bool)->bool) kk s r y.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ r IN kk /\
     y IN s /\ y IN r /\ (~(y IN moi_s34_nb tt kk) \/ y IN moi_s34_bd tt kk)
     ==> s SUBSET r`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`; `r:real^N->bool`; `y:real^N`] MOI_S4B_SIMP_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S4H_SIMP_KK];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S4B_LOW THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `f:real^N->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(f:real^N->bool) < aff_dim(s:real^N->bool)` THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN INT_ARITH_TAC]);;

let MOI_S4B_S3_UNIQ = prove
 (`!(tt:(real^N->bool)->bool) kk r r' y.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\
     y IN r /\ y IN r' /\ (~(y IN moi_s34_nb tt kk) \/ y IN moi_s34_bd tt kk) /\
     ~(?s. s IN moi_s34_simp kk (&2) /\ y IN s)
     ==> r = r'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `r:real^N->bool`; `r':real^N->bool`; `y:real^N`] MOI_S4B_SIMP_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4H_SIMP_KK];
      ASM_MESON_TAC[MOI_S4H_SIMP_KK];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `r:real^N->bool`; `r':real^N->bool`; `3`; `3`] MOI_S4G_NEST) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `aff_dim(f:real^N->bool) = &2` THENL
     [UNDISCH_TAC `~(?s. s IN moi_s34_simp kk (&2) /\ (y:real^N) IN s)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `f:real^N->bool` THEN
      ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
      MATCH_MP_TAC MOI_S4B_LOW THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `f:real^N->bool`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(aff_dim(f:real^N->bool) = &2)` THEN
      UNDISCH_TAC `aff_dim(f:real^N->bool) < aff_dim(r:real^N->bool)` THEN
      UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN INT_ARITH_TAC]]);;

let MOI_S4B_SD_UNIQ = prove
 (`!(tt:(real^N->bool)->bool) kk g g' y.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ g' IN moi_s34_simp kk (&1) /\
     y IN moi_s34_sd tt kk g /\ y IN moi_s34_sd tt kk g'
     ==> g = g'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g':real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real^N` (X_CHOOSE_THEN `b':real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g':real^N->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN `!c d:real^N. {c} IN kk /\ c IN segment[c,d] /\
                  y IN moi_s34_sd tt kk (segment[c,d]) ==> y IN moi_s34_vb tt kk c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[c:real^N,d]`; `c:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_vb tt kk a /\ y IN moi_s34_vb tt kk b /\
                y IN moi_s34_vb tt kk a' /\ y IN moi_s34_vb tt kk b'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `a':real^N`; `y:real^N`] MOI_S4B_VB3) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `b':real^N`; `y:real^N`] MOI_S4B_VB3) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[SEGMENT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The kind of a source point and the profiles of the open source            *)
(* cells (each open cell determines the kind and the index of its label).    *)
(* ------------------------------------------------------------------------- *)

let moi_s4b_two = new_definition
 `moi_s4b_two (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (y:real^N) <=>
    ?u v. ~(u = v) /\ {u} IN kk /\ {v} IN kk /\
          y IN moi_s34_vb tt kk u /\ y IN moi_s34_vb tt kk v`;;

let moi_s4b_tri = new_definition
 `moi_s4b_tri (kk:(real^N->bool)->bool) (y:real^N) <=>
    ?s. s IN moi_s34_simp kk (&2) /\ y IN s`;;

let moi_s4b_kind = new_definition
 `moi_s4b_kind (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (y:real^N) =
    if ~(y IN moi_s34_nb tt kk) then (if moi_s4b_tri kk y then 3 else 4)
    else if ~(y IN moi_s34_bd tt kk) then (if moi_s4b_two tt kk y then 2 else 1)
    else if y IN UNIONS kk then
      (if moi_s4b_tri kk y then (if moi_s4b_two tt kk y then 8 else 6)
       else (if moi_s4b_two tt kk y then 7 else 5))
    else (if moi_s4b_two tt kk y then 10 else 9)`;;

let MOI_S4B_SIMP1_SKEL = prove
 (`!(kk:(real^N->bool)->bool) g. g IN moi_s34_simp kk (&1) ==> g IN skeleton 1 kk`,
  REWRITE_TAC[moi_s34_simp; skeleton; IN_ELIM_THM] THEN SIMP_TAC[INT_LE_REFL]);;

let MOI_S4B_TWO_SD = prove
 (`!(tt:(real^N->bool)->bool) kk g y.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ y IN moi_s34_sd tt kk g
     ==> moi_s4b_two tt kk y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  REWRITE_TAC[moi_s4b_two] THEN MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `segment[a:real^N,b]`; `a:real^N`] MOI_S4G_SD_SUB_VB) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `segment[a:real^N,b]`; `b:real^N`] MOI_S4G_SD_SUB_VB) THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  UNDISCH_TAC `(y:real^N) IN moi_s34_sd tt kk (segment[a,b])` THEN SET_TAC[]);;

(* A point of a vertex ball in no other vertex ball. *)

let MOI_S4B_ONLY_V = prove
 (`!(tt:(real^N->bool)->bool) kk v y.
     moi_s34_tube tt kk /\ {v} IN kk /\ y IN moi_s34_vb tt kk v /\
     (!w. ~(w = v) /\ segment[v,w] IN moi_s34_simp kk (&1) ==>
          ~(y IN moi_s34_sd tt kk (segment[v,w])))
     ==> (!u. {u} IN kk /\ y IN moi_s34_vb tt kk u ==> u = v) /\
         ~(moi_s4b_two tt kk y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N. {u} IN kk /\ y IN moi_s34_vb tt kk u ==> u = v` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `u:real^N`; `y:real^N`] MOI_S4B_VB2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[moi_s4b_two] THEN ASM_MESON_TAC[]]);;

(* Profiles of the open source cells, kinds 1-4. *)

let MOI_S4B_PROF1 = prove
 (`!(tt:(real^N->bool)->bool) kk v y.
     moi_s34_tube tt kk /\ {v} IN kk /\ y IN moi_s34_vb tt kk v /\
     ~(y IN (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
            UNIONS {moi_s34_vb tt kk v INTER moi_s34_vb tt kk w | w |
                    ~(w = v) /\ segment[v,w] IN skeleton 1 kk})
     ==> moi_s4b_kind tt kk y = 1 /\
         (!m q' x'. moi_s4g_lab tt kk m 1 q' x' /\ y IN m ==> q' = {v} /\ x' = {})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM;
              TAUT `~(a \/ b) <=> ~a /\ ~b`; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `y:real^N`] MOI_S4B_ONLY_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_s34_sd tt kk (segment[v,w]) =
                  moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)` SUBST1_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[MOI_S4H_SIMP_KK];
      REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[MOI_S4B_SIMP1_SKEL]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "only") ASSUME_TAC)] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S4G_VB_NB; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^N) IN moi_s34_bd tt kk)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    USE_THEN "only" (MP_TAC o SPEC `v':real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4B_PROF2 = prove
 (`!(tt:(real^N->bool)->bool) kk g y.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ y IN moi_s34_sd tt kk g /\
     ~(y IN moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
     ==> moi_s4b_kind tt kk y = 2 /\
         (!m q' x'. moi_s4g_lab tt kk m 2 q' x' /\ y IN m ==> q' = g /\ x' = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S4G_SD_NB; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^N) IN moi_s34_bd tt kk)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_s4b_two tt kk (y:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_TWO_SD THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_MESON_TAC[]]);;

let MOI_S4B_PROF3 = prove
 (`!(tt:(real^N->bool)->bool) kk s y.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\
     y IN closure (s DIFF moi_s34_nb tt kk) /\ ~(y IN s INTER moi_s34_bd tt kk)
     ==> moi_s4b_kind tt kk y = 3 /\
         (!m q' x'. moi_s4g_lab tt kk m 3 q' x' /\ y IN m ==> q' = s /\ x' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_S4G_KK_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN closure (s DIFF moi_s34_nb tt kk)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN moi_s34_nb tt kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN s INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4B_CL_NB THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `moi_s4b_tri kk (y:real^N)` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s4b_tri] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^N) IN q'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `q':real^N->bool`] MOI_S4G_KK_CLOSED) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4B_S2_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4B_PROF4 = prove
 (`!(tt:(real^N->bool)->bool) kk r y.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\
     y IN closure (r DIFF moi_s34_nb tt kk) /\
     ~(y IN UNIONS {closure (s DIFF moi_s34_nb tt kk) | s |
                    s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
            (r INTER moi_s34_bd tt kk))
     ==> moi_s4b_kind tt kk y = 4 /\
         (!m q' x'. moi_s4g_lab tt kk m 4 q' x' /\ y IN m ==> q' = r /\ x' = {})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; TAUT `~(a \/ b) <=> ~a /\ ~b`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_S4G_KK_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN closure (r DIFF moi_s34_nb tt kk)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN moi_s34_nb tt kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN r INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4B_CL_NB THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s4b_tri kk (y:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4b_tri] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_S23 THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^N) IN UNIONS {closure (s DIFF moi_s34_nb tt kk) | s |
                    s IN moi_s34_simp kk (&2) /\ s SUBSET r})` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^N) IN q'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `q':real^N->bool`] MOI_S4G_KK_CLOSED) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4B_S3_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s4b_tri]]);;

(* Profiles, kinds 5-8 (cells on Bd N inside |kk|). *)

let MOI_S4B_PROF5 = prove
 (`!(tt:(real^N->bool)->bool) kk r v y.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk /\
     y IN r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
     ~(y IN UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
            UNIONS {r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})
     ==> moi_s4b_kind tt kk y = 5 /\
         (!m q' x'. moi_s4g_lab tt kk m 5 q' x' /\ y IN m ==> q' = r /\ x' = {v})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; TAUT `~(a \/ b) <=> ~a /\ ~b`; UNIONS_GSPEC; IN_ELIM_THM;
              NOT_EXISTS_THM] THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_BD_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s4b_tri kk (y:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4b_tri] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_S23 THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                     `s:real^N->bool`] MOI_S4G_VB_OUT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term ((=) `moi_s34_vb tt kk (v:real^N)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `y:real^N`] MOI_S4B_ONLY_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_SD_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th))) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "only") ASSUME_TAC)] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "only" (MP_TAC o SPEC `v':real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4B_S3_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s4b_tri]]);;

let MOI_S4B_PROF6 = prove
 (`!(tt:(real^N->bool)->bool) kk s v y.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk /\
     y IN s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
     ~(y IN UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})
     ==> moi_s4b_kind tt kk y = 6 /\
         (!m q' x'. moi_s4g_lab tt kk m 6 q' x' /\ y IN m ==> q' = s /\ x' = {v})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_BD_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4b_tri kk (y:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4b_tri] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `y:real^N`] MOI_S4B_ONLY_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_SD_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th))) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "only") ASSUME_TAC)] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "only" (MP_TAC o SPEC `v':real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4B_S2_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4B_PROF7 = prove
 (`!(tt:(real^N->bool)->bool) kk r g y.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET r /\
     y IN r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
     ~(y IN UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})
     ==> moi_s4b_kind tt kk y = 7 /\
         (!m q' x'. moi_s4g_lab tt kk m 7 q' x' /\ y IN m ==> q' = r /\ x' = g)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_BD_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4b_two tt kk (y:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4B_TWO_SD THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s4b_tri kk (y:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4b_tri] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_S23 THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_SD_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4B_S3_UNIQ THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s4b_tri];
      MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S4B_PROF8 = prove
 (`!(tt:(real^N->bool)->bool) kk s g y.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET s /\
     y IN s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk
     ==> moi_s4b_kind tt kk y = 8 /\
         (!m q' x'. moi_s4g_lab tt kk m 8 q' x' /\ y IN m ==> q' = s /\ x' = g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_BD_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4b_two tt kk (y:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4B_TWO_SD THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4b_tri kk (y:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4b_tri] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4B_S2_UNIQ THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                            `y:real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

(* Profiles, kinds 9-10 (the outer cells). *)

let MOI_S4B_PROF9 = prove
 (`!(tt:(real^N->bool)->bool) kk v y.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     y IN closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk) /\
     ~(y IN UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
            UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})
     ==> moi_s4b_kind tt kk y = 9 /\
         (!m q' x'. moi_s4g_lab tt kk m 9 q' x' /\ y IN m ==> q' = {v} /\ x' = {})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; TAUT `~(a \/ b) <=> ~a /\ ~b`; UNIONS_GSPEC; IN_ELIM_THM;
              NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_vb tt kk v /\ y IN moi_s34_bd tt kk`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "o1" (MP_TAC o SPEC `v:real^N`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^N) IN closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                          UNIONS kk)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_VB_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN UNIONS kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_IN_B) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `y:real^N`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC o MATCH_MP MOI_S4B_CB_TRI) THEN
    SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                     `s:real^N->bool`] MOI_S4G_VB_OUT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_neg(snd(dest_forall(concl th))) &&
      type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term ((=) `moi_s34_vb tt kk (v:real^N)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `y:real^N`] MOI_S4B_ONLY_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET complex_boundary kk` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `segment[v:real^N,w]`] MOI_S4B_SD_KK) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th ->
      is_forall(concl th) && is_neg(snd(dest_forall(concl th))) &&
      type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th))) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INTER];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "only") ASSUME_TAC)] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    USE_THEN "only" (MP_TAC o SPEC `v':real^N`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "o1" (MP_TAC o SPEC `v':real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4B_PROF10 = prove
 (`!(tt:(real^N->bool)->bool) kk g y.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk /\
     y IN closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk) /\
     ~(y IN UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET complex_boundary kk})
     ==> moi_s4b_kind tt kk y = 10 /\
         (!m q' x'. moi_s4g_lab tt kk m 10 q' x' /\ y IN m ==> q' = g /\ x' = {})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_sd tt kk g /\ y IN moi_s34_bd tt kk`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "o2" (MP_TAC o SPEC `g:real^N->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^N) IN closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                          UNIONS kk)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_SD_NB; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4b_two tt kk (y:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4B_TWO_SD THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN UNIONS kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_IN_B) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `y:real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC o MATCH_MP MOI_S4B_CB_TRI) THEN
    SUBGOAL_THEN `(g:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4B_SD_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_neg(snd(dest_forall(concl th))) &&
      type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s4b_kind];
    REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "o2" (MP_TAC o SPEC `q':real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^N) IN m` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Open source cells; (S3) source cells meet in the union of their           *)
(* common faces.                                                              *)
(* ------------------------------------------------------------------------- *)

let moi_s4b_oc = new_definition
 `moi_s4b_oc (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (l:real^N->bool) =
    l DIFF UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)}`;;

let MOI_S4B_CASE_TAC (sbs:thm) (prof:thm) (args:term list) : tactic =
  MP_TAC(ISPECL ([`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] @ args) sbs) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC prof THEN ASM_REWRITE_TAC[];;

let MOI_S4B_PROF_LAB = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x y.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\ y IN moi_s4b_oc tt kk l
     ==> moi_s4b_kind tt kk y = k /\
         (!m q' x'. moi_s4g_lab tt kk m k q' x' /\ y IN m ==> q' = q /\ x' = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_s4b_oc tt kk l` THEN
  REWRITE_TAC[moi_s4b_oc; IN_DIFF] THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  GEN_REWRITE_TAC LAND_CONV [moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [MOI_S4B_CASE_TAC MOI_S4B_SBS1 MOI_S4B_PROF1 [`v:real^N`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS2 MOI_S4B_PROF2 [`q:real^N->bool`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS3 MOI_S4B_PROF3 [`q:real^N->bool`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS4 MOI_S4B_PROF4 [`q:real^N->bool`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS5 MOI_S4B_PROF5 [`q:real^N->bool`; `v:real^N`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS6 MOI_S4B_PROF6 [`q:real^N->bool`; `v:real^N`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS7 MOI_S4B_PROF7 [`q:real^N->bool`; `x:real^N->bool`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS8 MOI_S4B_PROF8 [`q:real^N->bool`; `x:real^N->bool`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS9 MOI_S4B_PROF9 [`v:real^N`];
    MOI_S4B_CASE_TAC MOI_S4B_SBS10 MOI_S4B_PROF10 [`q:real^N->bool`]]);;

(* Open cells of distinct source cells are disjoint. *)

let MOI_S4B_OC_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk l m y.
     moi_s34_tube tt kk /\ l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk /\
     y IN moi_s4b_oc tt kk l /\ y IN moi_s4b_oc tt kk m
     ==> l = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_TAC `x:real^N->bool`)))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `q':real^N->bool` (X_CHOOSE_TAC `x':real^N->bool`)))
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`; `y:real^N`]
                MOI_S4B_PROF_LAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "idx")) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `m:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`; `y:real^N`]
                MOI_S4B_PROF_LAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `k':num = k` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "idx" (MP_TAC o SPECL [`m:real^N->bool`; `q':real^N->bool`; `x':real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s4b_oc tt kk m` THEN
    REWRITE_TAC[moi_s4b_oc; IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  MATCH_MP_TAC MOI_S4G_LAB_FUN THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                        `k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* Every source cell is the union of the open cells of its faces. *)

let MOI_S4B_OC_COVER = prove
 (`!(tt:(real^N->bool)->bool) kk l.
     moi_s34_tube tt kk /\ l IN moi_s34_scells tt kk
     ==> l = UNIONS {moi_s4b_oc tt kk n | n | n IN moi_s34_scells tt kk /\ n SUBSET l}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!d (l:real^N->bool). moi_s34_tube tt kk /\ l IN moi_s34_scells tt kk /\
          moi_s34_dim l = d
          ==> l = UNIONS {moi_s4b_oc tt kk n | n | n IN moi_s34_scells tt kk /\ n SUBSET l}`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `l:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    ASM_CASES_TAC
     `(y:real^N) IN UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)}` THENL
     [UNDISCH_TAC
       `(y:real^N) IN UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)}` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `moi_s34_dim (m:real^N->bool)`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `moi_s34_dim (l:real^N->bool) = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC MOI_S4H_DIM_LT THEN
        MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `m:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s:real^N->bool. (y:real^N) IN s`) THEN
      ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `l:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL; moi_s4b_oc; IN_DIFF]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `n:real^N->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[moi_s4b_oc] THEN ASM SET_TAC[]]);;

(* S3: source cells meet in the union of their common faces. *)

let MOI_S4B_S3 = prove
 (`!(tt:(real^N->bool)->bool) kk l m.
     moi_s34_tube tt kk /\ l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk
     ==> l INTER m =
         UNIONS {n | n IN moi_s34_scells tt kk /\ n SUBSET l /\ n SUBSET m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`]
                  MOI_S4B_OC_COVER) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `m:real^N->bool`]
                  MOI_S4B_OC_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\t:real^N->bool. (y:real^N) IN t`) THEN
    ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\t:real^N->bool. (y:real^N) IN t`) THEN
    ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `n1:real^N->bool`; `n2:real^N->bool`; `y:real^N`] MOI_S4B_OC_DISJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `n2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s4b_oc tt kk n2` THEN
    REWRITE_TAC[moi_s4b_oc; IN_DIFF] THEN SIMP_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM; SUBSET_INTER] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* (S5) the source cells cover |kk| UNION N; (S4) they are locally           *)
(* finite.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4B_S5 = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> UNIONS (moi_s34_scells tt kk) = UNIONS kk UNION moi_s34_nb tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN kk ==> q SUBSET UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `l:real^N->bool` THEN
    REWRITE_TAC[MOI_S4G_SCELLS_LAB; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                    MOI_S4G_VB_NB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                    MOI_S4G_SD_NB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
      USE_THEN "o1" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                    MOI_S4G_VB_NB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[];
      USE_THEN "o2" (MP_TAC o SPEC `q:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`]
                    MOI_S4G_SD_NB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^N->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `q:real^N->bool` THEN
    (CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN
                              ASM_MESON_TAC[MOI_S4H_SIMP_KK]]) THEN
    TRY(MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `q:real^N->bool`] MOI_S4G_KK_CLOSED) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; SIMP_TAC[]] THEN NO_TAC) THEN
    SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [ASM_CASES_TAC `(y:real^N) IN moi_s34_nb tt kk` THENL
       [ALL_TAC;
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `y:real^N`]
                      MOI_S4B_KK_TETRA) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `closure (r DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
          MAP_EVERY EXISTS_TAC [`4`; `r:real^N->bool`; `{}:real^N->bool`] THEN
          ASM_REWRITE_TAC[moi_s4g_lab];
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
          ASM_REWRITE_TAC[IN_DIFF]]];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^N) IN moi_s34_nb tt kk` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_NB_UNIONS) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN
    ASM_REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    MAP_EVERY EXISTS_TAC [`1`; `{v:real^N}`; `{}:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN EXISTS_TAC `v:real^N` THEN
    ASM_REWRITE_TAC[]]);;

(* The index of a source cell meeting u, in terms of the simplices FQ of tt *)
(* meeting u and the vertices FV of kk whose balls meet u.                  *)

let MOI_S4B_LF_INDEX = prove
 (`!(tt:(real^N->bool)->bool) kk u FQ FV l k q x.
     moi_s34_tube tt kk /\
     (!v. {v} IN kk /\ ~(moi_s34_vb tt kk v INTER u = {}) ==> v IN FV) /\
     (!q. q IN kk /\ ~(q INTER u = {}) ==> q IN FQ) /\
     moi_s4g_lab tt kk l k q x /\ ~(l INTER u = {})
     ==> (1 <= k /\ k <= 10) /\
         (q IN FQ \/ (?v. v IN FV /\ q = {v}) \/
          (?a b. a IN FV /\ b IN FV /\ q = segment[a,b]) \/ q = {}) /\
         (x IN FQ \/ (?v. v IN FV /\ x = {v}) \/
          (?a b. a IN FV /\ b IN FV /\ x = segment[a,b]) \/ x = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "vbf" (el 1 cs) THEN LABEL_TAC "kqf" (el 2 cs) THEN
    ASSUME_TAC (el 3 cs) THEN ASSUME_TAC (el 4 cs)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "o1") (LABEL_TAC "o2")) THEN
  SUBGOAL_THEN
   `!g:real^N->bool. g IN moi_s34_simp kk (&1) /\ ~(moi_s34_sd tt kk g INTER u = {})
                     ==> ?a b. a IN FV /\ b IN FV /\ g = segment[a,b]`
  (LABEL_TAC "sdf") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `g:real^N->bool`)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`; `a:real^N`] MOI_S4G_SD_SUB_VB) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `segment[a:real^N,b]`; `b:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THEN USE_THEN "vbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(moi_s34_sd tt kk (segment[a:real^N,b]) INTER u = {})` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q':real^N->bool. q' IN kk ==> closure (q' DIFF moi_s34_nb tt kk) SUBSET q'`
  (LABEL_TAC "cl") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q':real^N->bool`] MOI_S4G_KK_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `l:real^N->bool`)) THEN
  REPEAT CONJ_TAC THENL
   [(* 1 *)
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN
    USE_THEN "vbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* 2 *)
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN USE_THEN "sdf" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    (* 3 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    USE_THEN "cl" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~(closure (q DIFF moi_s34_nb tt kk) INTER (u:real^N->bool) = {})` THEN
    SET_TAC[];
    (* 4 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    USE_THEN "cl" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~(closure (q DIFF moi_s34_nb tt kk) INTER (u:real^N->bool) = {})` THEN
    SET_TAC[];
    (* 5 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~((q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN
    USE_THEN "vbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    (* 6 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~((q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN
    USE_THEN "vbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    (* 7 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~((q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN USE_THEN "sdf" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    (* 8 *)
    DISJ1_TAC THEN USE_THEN "kqf" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    UNDISCH_TAC `~((q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN USE_THEN "sdf" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) INTER
                   (u:real^N->bool) = {})` THEN SET_TAC[];
    (* 9 *)
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN
    USE_THEN "vbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "o1" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)
                   INTER (u:real^N->bool) = {})` THEN SET_TAC[];
    (* 10 *)
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN USE_THEN "sdf" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "o2" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(closure ((moi_s34_sd tt kk q INTER moi_s34_bd tt kk) DIFF UNIONS kk)
                   INTER (u:real^N->bool) = {})` THEN SET_TAC[]]);;

(* The vertices of tt in a simplex of tt are finitely many. *)

let MOI_S4B_VERTS_FINITE = prove
 (`!(tt:(real^N->bool)->bool) s.
     lf_simplicial_complex tt /\ s IN tt ==> FINITE {v | {v} IN tt /\ v IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. {v} IN tt /\ v IN s ==> v extreme_point_of s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `{v:real^N}`; `s:real^N->bool`]
                  MOI_FM3_LF_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{v:real^N} INTER s = {v}` (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `(v:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FM3_LF_SIMPLEX) THEN
  ASM_REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[EXTREME_POINT_OF_CONVEX_HULL]]);;

(* S4: the source cells are locally finite. *)

let MOI_S4B_S4 = prove
 (`!(tt:(real^N->bool)->bool) kk x.
     moi_s34_tube tt kk /\ x IN UNIONS (moi_s34_scells tt kk)
     ==> ?u. open u /\ x IN u /\
             FINITE {l | l IN moi_s34_scells tt kk /\ ~(l INTER u = {})}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `!v z:real^N. {v} IN kk /\ z IN moi_s34_vb tt kk v
                             ==> ?s. s IN tt /\ v IN s /\ z IN s`
  (LABEL_TAC "star") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                   `v:real^N`] MOI_FTA_CELL_IN_STAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
      REWRITE_TAC[GSYM moi_s34_vb; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS (moi_s34_scells tt kk)` THEN
    ASM_SIMP_TAC[MOI_S4B_S5; IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS kk` THEN REWRITE_TAC[IN_UNIONS] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(x:real^N) IN moi_s34_nb tt kk` THEN
      ASM_SIMP_TAC[MOI_S4G_NB_UNIONS; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIONS] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [lf_simplicial_complex] o
                check (fun th -> concl th = `lf_simplicial_complex (tt:(real^N->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `FQ = {s:real^N->bool | s IN tt /\ ~(s INTER u = {})}` THEN
  ABBREV_TAC `FV = {v:real^N | {v} IN kk /\ ?s. s IN FQ /\ v IN s}` THEN
  SUBGOAL_THEN `FINITE (FV:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS {{v:real^N | {v} IN tt /\ v IN s} | s | s IN FQ}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
       [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC MOI_S4B_VERTS_FINITE THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(s:real^N->bool) IN FQ` THEN EXPAND_TAC "FQ" THEN
        SIMP_TAC[IN_ELIM_THM]];
      EXPAND_TAC "FV" THEN GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
      STRIP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `PP = (FQ:(real^N->bool)->bool) UNION IMAGE (\v:real^N. {v}) FV UNION
                   IMAGE (\p:real^N#real^N. segment[FST p,SND p]) (FV CROSS FV) UNION
                   {{}}` THEN
  SUBGOAL_THEN `FINITE (PP:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "PP" THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_CROSS; FINITE_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\p:num#(real^N->bool)#(real^N->bool).
                       moi_s4g_cell tt kk (FST p) (FST(SND p)) (SND(SND p)))
                    ((1..10) CROSS (PP CROSS PP))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN kk /\ ~(moi_s34_vb tt kk v INTER u = {}) ==> v IN FV`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(moi_s34_vb tt kk (v:real^N) INTER u = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "star" (MP_TAC o SPECL [`v:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "FV" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "FQ" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN kk /\ ~(q INTER u = {}) ==> q IN FQ`
  ASSUME_TAC THENL
   [EXPAND_TAC "FQ" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `l:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `(l:real^N->bool) IN moi_s34_scells tt kk` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_S4G_SCELLS_LAB] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
    (X_CHOOSE_TAC `y:real^N->bool`))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `(k,q,y):num#(real^N->bool)#(real^N->bool)` THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND; IN_CROSS; IN_NUMSEG] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MOI_S4G_LAB_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "PP" THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_CROSS; IN_SING; EXISTS_PAIR_THM; FST; SND] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N->bool`;
                 `FQ:(real^N->bool)->bool`; `FV:real^N->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `y:real^N->bool`] MOI_S4B_LF_INDEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem SCELL_B.                                                  *)
(* ------------------------------------------------------------------------- *)

let SCELL_B = prove
 (MOI_S34_SCELL_B,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_src_ok] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `l:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4B_S1 THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4H_DIM_LT THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4B_S3 THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4B_S4 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4B_S5 THEN ASM_REWRITE_TAC[]]);;

