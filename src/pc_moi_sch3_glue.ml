(* ========================================================================= *)
(* pc_moi_sch3_glue: Moise, Geometric Topology in Dimensions 2 and 3,        *)
(* GTM 47, Sec 17, Thms 9-11, pp.121-122.  Main theorems: STAR_SIMPLE (a     *)
(* PL 2-sphere met at most once by every ray from an interior point is       *)
(* simply imbedded), CONE_DISK_SIMPLE (the cone over a PL 2-cell from a      *)
(* point seeing it injectively, glued to the cell, is simply imbedded) and   *)
(* THM11 (two simply imbedded spheres meeting in a plane 2-cell glue to a    *)
(* simply imbedded sphere).                                                  *)
(* The first section sets up cones from a point, rays and the tetrahedron    *)
(* over a triangle.                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_sch3_s2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Membership in the cone UNIONS (segments from v to the points of X).       *)
(* ------------------------------------------------------------------------- *)

let MOI_SGL_CONE_MEM = prove
 (`!(v:real^N) X x r.
     x IN X /\ &0 <= r /\ r <= &1
     ==> v + r % (x - v) IN UNIONS {segment[v,x] | x IN X}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_CON_IN_CONE] THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `r:real`] THEN ASM_REWRITE_TAC[]);;

let MOI_SGL_CONE_BASE = prove
 (`!(v:real^N) X x. x IN X ==> x IN UNIONS {segment[v,x] | x IN X}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `X:real^N->bool`; `x:real^N`; `&1`]
    MOI_SGL_CONE_MEM) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_ARITH `v + &1 % (x - v):real^N = x`]);;

let MOI_SGL_SUBSET_CONE = prove
 (`!(v:real^N) X. X SUBSET UNIONS {segment[v,x] | x IN X}`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_SGL_CONE_BASE THEN ASM_REWRITE_TAC[]);;

let MOI_SGL_CONE_APEX = prove
 (`!(v:real^N) X x. x IN X ==> v IN UNIONS {segment[v,x] | x IN X}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `X:real^N->bool`; `x:real^N`; `&0`]
    MOI_SGL_CONE_MEM) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_ARITH `v + &0 % (x - v):real^N = v`]);;

let MOI_SGL_CONE_MONO = prove
 (`!(v:real^N) X Y.
     X SUBSET Y
     ==> UNIONS {segment[v,x] | x IN X} SUBSET UNIONS {segment[v,x] | x IN Y}`,
  REWRITE_TAC[SUBSET; MOI_CON_IN_CONE] THEN MESON_TAC[]);;

let MOI_SGL_CONE_UNION = prove
 (`!(v:real^N) X Y.
     UNIONS {segment[v,x] | x IN X UNION Y} =
     UNIONS {segment[v,x] | x IN X} UNION UNIONS {segment[v,x] | x IN Y}`,
  REWRITE_TAC[EXTENSION; IN_UNION; MOI_CON_IN_CONE] THEN MESON_TAC[]);;

let MOI_SGL_SEGMENT_CONE = prove
 (`!(v:real^N) X x. x IN X ==> segment[v,x] SUBSET UNIONS {segment[v,x] | x IN X}`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Rays from v meeting d at most once.                                       *)

let MOI_SGL_RAY_EQ = prove
 (`!d (v:real^N) x y r.
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     x IN d /\ y IN d /\ &0 <= r /\ r <= &1 /\ y = v + r % (x - v)
     ==> y = x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  VECTOR_ARITH_TAC);;

let MOI_SGL_RAY_SAME = prove
 (`!d (v:real^N) x x' r r'.
     ~(v IN d) /\ (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     x IN d /\ x' IN d /\ &0 <= r /\ r <= &1 /\ &0 <= r' /\ r' <= &1 /\
     v + r % (x - v) = v + r' % (x' - v)
     ==> v + r % (x - v) = v \/ x = x'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `v:real^N`; `x:real^N`; `x':real^N`;
                 `r:real`; `r':real`] MOI_CON_RAY_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) DISJ_CASES_TAC) THENL
   [DISJ1_TAC THEN UNDISCH_TAC `r = &0` THEN DISCH_THEN SUBST1_TAC THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* A tactic for set algebra with cones: generalize every UNIONS subterm of   *)
(* the goal into a fresh variable, so that SET_TAC treats cones as atoms.   *)

let MOI_SGL_GEN_UNIONS_TAC : tactic = fun (asl,w as g) ->
  let rec tsize t =
    if is_comb t then tsize (rator t) + tsize (rand t)
    else if is_abs t then 1 + tsize (body t) else 1 in
  let tms = setify (find_terms (fun t -> is_comb t &&
              (try fst(dest_const(rator t)) = "UNIONS" with Failure _ -> false)) w) in
  let tms' = sort (fun a b -> tsize a > tsize b) tms in
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) tms' g;;

(* ========================================================================= *)
(* The tetrahedron spanned by a point v and a triangle c seen injectively    *)
(* from v (its boundary is c together with the cone over the boundary of c); *)
(* the base case of Moise Thm 10 (a single triangle).                        *)
(* ========================================================================= *)

let MOI_SGL_SIMPLEX_NONEMPTY = prove
 (`!(c:real^N->bool) n. n simplex c /\ &0 <= n ==> ~(c = {})`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_EMPTY] THEN ASM_INT_ARITH_TAC);;

let MOI_SGL_TETRA = prove
 (`!c (v:real^3).
     &2 simplex c /\ ~(v IN c) /\
     (!x y. x IN c /\ y IN c /\ y IN segment[v,x] ==> y = x)
     ==> &3 simplex (convex hull (v INSERT c)) /\
         convex hull (v INSERT c) = UNIONS {segment[v,x] | x IN c} /\
         relative_frontier (convex hull (v INSERT c)) =
           c UNION UNIONS {segment[v,x] | x IN relative_frontier c} /\
         c INTER UNIONS {segment[v,x] | x IN relative_frontier c} =
           relative_frontier c /\
         frontier (convex hull (v INSERT c)) =
           relative_frontier (convex hull (v INSERT c)) /\
         compact (convex hull (v INSERT c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (c:real^3->bool) /\ compact c /\ ~(c = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      MATCH_MP_TAC MOI_SGL_SIMPLEX_NONEMPTY THEN EXISTS_TAC `&2:int` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN affine hull c)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_NOT_IN_AFFINE_HULL THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (convex hull ((v:real^3) INSERT c))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`; `&2:int`] MOI_CON_CONE_SIMPLEX) THEN
    ASM_REWRITE_TAC[INT_ARITH `&2 + &1:int = &3`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier (convex hull ((v:real^3) INSERT c)) =
      c UNION UNIONS {segment[v,x] | x IN relative_frontier c} /\
    c INTER UNIONS {segment[v,x] | x IN relative_frontier c} =
      relative_frontier c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&2 simplex (c:real^3->bool)` THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
      (X_CHOOSE_THEN `e:real^3` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[GSYM HULL_INSERT] THEN
    MATCH_MP_TAC MOI_FSA_RF_TETRA THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT];
        ASM_MESON_TAC[AFFINE_HULL_CONVEX_HULL]];
      REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[HULL_INC; IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier (convex hull ((v:real^3) INSERT c)) =
    relative_frontier (convex hull (v INSERT c))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    MP_TAC(ISPEC `convex hull ((v:real^3) INSERT c)` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; DIMINDEX_3] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull ((v:real^3) INSERT c) = UNIONS {segment[v,x] | x IN c}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
    SUBGOAL_THEN `convex hull c = c:real^3->bool` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CONVEX_HULL_EQ]; REFL_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_SGL_BASE3 = prove
 (`!c (v:real^3).
     &2 simplex c /\ ~(v IN c) /\
     (!x y. x IN c /\ y IN c /\ y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple (c UNION UNIONS {segment[v,x] | x IN relative_frontier c})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`] MOI_SGL_TETRA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))] THEN
    MATCH_MP_TAC MOI_SCD_SIMPLE_SIMPLEX THEN REWRITE_TAC[CONJUNCT1 th]));;

(* ========================================================================= *)
(* Cones over PL circles and PL arcs are PL 2-cells; the cone sphere d UNION *)
(* (cone over the boundary j) of a PL 2-cell d.                              *)
(* ========================================================================= *)

let MOI_SGL_CONEMAP_SEGMENT = prove
 (`!a (u:real^M) (v:real^N) f x.
     ~(u IN a) /\ (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
     x IN a
     ==> IMAGE (moi_con_conemap a u v f) (segment[u,x]) = segment[v,f x]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. &0 <= r /\ r <= &1
        ==> moi_con_conemap a u v f (u + r % (x - u)) =
            v + r % ((f:real^M->real^N) x - v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&1 - r) % u + r % x:real^M = u + r % (x - u)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u + r % (x - u):real^M` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [VECTOR_ARITH_TAC;
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

let MOI_SGL_CONE_CIRCLE = prove
 (`!d j (v:real^N).
     pl_cell_with_boundary 2 d j /\ ~(v IN j) /\
     (!x y. x IN j /\ y IN j /\ y IN segment[v,x] ==> y = x)
     ==> pl_cell_with_boundary 2 (UNIONS {segment[v,x] | x IN j}) j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
     (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `j = IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[INT_ARITH `&1 <= &2:int`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k,IMAGE f (relative_frontier k))
                     (f:real^N->real^N,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `d:real^N->bool`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`;
                 `IMAGE (f:real^N->real^N) (relative_frontier k)`;
                 `simplex_barycentre (k:real^N->bool)`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k) (v:real^N)
                     (f:real^N->real^N)`;
    `moi_con_conemap (IMAGE (f:real^N->real^N) (relative_frontier k)) (v:real^N)
                     (simplex_barycentre k) (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let MOI_SGL_STD_SEGMENT = prove
 (`(!x:real^2. x IN segment[basis 1,basis 2] ==> x$1 + x$2 = &1) /\
   ~(vec 0:real^2 IN segment[basis 1,basis 2]) /\
   (!x y:real^2. x IN segment[basis 1,basis 2] /\ y IN segment[basis 1,basis 2] /\
                 y IN segment[vec 0,x] ==> y = x)`,
  SUBGOAL_THEN `!x:real^2. x IN segment[basis 1,basis 2] ==> x$1 + x$2 = &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^2) IN segment[vec 0,x]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t = &1` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `(x:real^2)$1 + x$2 = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^2)$1 + y$2 = &1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `y = (&1 - t) % vec 0 + t % (x:real^2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    UNDISCH_TAC `(x:real^2)$1 + x$2 = &1` THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_SGL_CONE_ARC = prove
 (`!(bb:real^1->real^3) v.
     arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\ ~(v IN path_image bb) /\
     (!x y. x IN path_image bb /\ y IN path_image bb /\ y IN segment[v,x]
            ==> y = x)
     ==> pl_cell_with_boundary 2 (UNIONS {segment[v,x] | x IN path_image bb})
           (path_image bb UNION segment[v,pathstart bb] UNION
            segment[v,pathfinish bb])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA; moi_fsa_disk] THEN
  MP_TAC(ISPEC `bb:real^1->real^3` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(basis 1:real^2 = basis 2)` ASSUME_TAC THENL
   [SIMP_TAC[BASIS_INJ_EQ; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPEC `linepath(basis 1:real^2,basis 2)` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_SIMP_TAC[ARC_LINEPATH_EQ; MOI_PL2_PL_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; PATH_IMAGE_LINEPATH;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (segment[basis 1:real^2,basis 2],path_image bb)
      ((bb:real^1->real^3) o (l:real^2->real^1),
       linepath(basis 1:real^2,basis 2) o (h:real^3->real^1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((bb:real^1->real^3) o (l:real^2->real^1)) (basis 1) = pathstart bb /\
    ((bb:real^1->real^3) o (l:real^2->real^1)) (basis 2) = pathfinish bb`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[o_THM; pathstart; pathfinish]; ALL_TAC] THEN
  STRIP_ASSUME_TAC MOI_SGL_STD_SEGMENT THEN
  MP_TAC(ISPECL [`segment[basis 1:real^2,basis 2]`; `path_image(bb:real^1->real^3)`;
                 `vec 0:real^2`; `v:real^3`;
                 `(bb:real^1->real^3) o (l:real^2->real^1)`;
                 `linepath(basis 1:real^2,basis 2) o (h:real^3->real^1)`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS {segment[vec 0,x] | x IN segment[basis 1:real^2,basis 2]} =
    convex hull {vec 0,basis 1,basis 2}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [CONVEX_HULL_INSERT_SEGMENTS] THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {vec 0:real^2,basis 1,basis 2}`;
    `moi_con_conemap (segment[basis 1:real^2,basis 2]) (vec 0) (v:real^3)
       ((bb:real^1->real^3) o (l:real^2->real^1))`;
    `moi_con_conemap (path_image(bb:real^1->real^3)) v (vec 0:real^2)
       (linepath(basis 1:real^2,basis 2) o (h:real^3->real^1))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] THEN
    REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP RELATIVE_FRONTIER_OF_TRIANGLE
    (CONJUNCT1 MOI_PL2_STD_TRIANGLES)] THEN
  SUBGOAL_THEN `segment[basis 2:real^2,vec 0] = segment[vec 0,basis 2]`
  SUBST1_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  SUBGOAL_THEN `!x:real^2. x IN segment[basis 1,basis 2]
       ==> IMAGE (moi_con_conemap (segment[basis 1,basis 2]) (vec 0) (v:real^3)
                   ((bb:real^1->real^3) o (l:real^2->real^1))) (segment[vec 0,x]) =
           segment[v,((bb:real^1->real^3) o (l:real^2->real^1)) x]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SGL_CONEMAP_SEGMENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `basis 1 IN segment[basis 1:real^2,basis 2] /\
                basis 2 IN segment[basis 1:real^2,basis 2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (moi_con_conemap (segment[basis 1,basis 2]) (vec 0) (v:real^3)
           ((bb:real^1->real^3) o (l:real^2->real^1))) (segment[basis 1,basis 2]) =
    path_image bb`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((bb:real^1->real^3) o (l:real^2->real^1))
                      (segment[basis 1,basis 2])` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]];
    ALL_TAC] THEN
  SET_TAC[]);;

let MOI_SGL_CONE_SPHERE = prove
 (`!d j (v:real^3).
     pl_cell_with_boundary 2 d j /\ ~(v IN d) /\
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x)
     ==> pl_sphere 2 (d UNION UNIONS {segment[v,x] | x IN j}) /\
         d INTER UNIONS {segment[v,x] | x IN j} = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SPU_CELL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `d INTER UNIONS {segment[v,x] | x IN j} = j:real^3->bool`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
      SUBGOAL_THEN `y:real^3 = x` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[MOI_SGL_CONE_BASE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DISK_UNION THEN
  EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SGL_CONE_CIRCLE THEN EXISTS_TAC `d:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]]);;

(* ========================================================================= *)
(* The deletion step of Moise Thm 10 (p.121): deleting the free tetrahedron  *)
(* over a free triangle c of the cell d (c meets the boundary j in an arc A, *)
(* the complementary arc of the boundary of c is B) by the push property of  *)
(* the tetrahedron at the disk c UNION v*A.                                  *)
(* ========================================================================= *)

(* Rays from v meet d at most once: intersections of cones over subsets.    *)

let MOI_SGL_CONE_INTER_BASE = prove
 (`!d X Y (v:real^N).
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     X SUBSET d /\ Y SUBSET d
     ==> UNIONS {segment[v,x] | x IN X} INTER Y SUBSET X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_INTER; MOI_CON_IN_CONE] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `y:real^N = x` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_SGL_RAY_EQ THEN
  MAP_EVERY EXISTS_TAC [`d:real^N->bool`; `v:real^N`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_SGL_CONE_INTER_CONE = prove
 (`!d X Y (v:real^N).
     ~(v IN d) /\ (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     X SUBSET d /\ Y SUBSET d
     ==> UNIONS {segment[v,x] | x IN X} INTER UNIONS {segment[v,x] | x IN Y}
         SUBSET v INSERT UNIONS {segment[v,x] | x IN X INTER Y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; MOI_CON_IN_CONE] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) (X_CHOOSE_THEN `x':real^N` (X_CHOOSE_THEN `r':real`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `v:real^N`; `x:real^N`; `x':real^N`;
                 `r:real`; `r':real`] MOI_SGL_RAY_SAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_SGL_CONE_PAIR = prove
 (`!(v:real^N) p q.
     UNIONS {segment[v,x] | x IN {p,q}} = segment[v,p] UNION segment[v,q]`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_INSERT;
              NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* The three set facts of the deletion step (a = the free arc of c in j,    *)
(* b = the complementary arc of the boundary of c, j = a UNION kj).          *)

let MOI_SGL_DEL_SETS = prove
 (`!d j c d' a b kj p q (v:real^3).
     ~(v IN d) /\ (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     j SUBSET d /\ d = c UNION d' /\ c INTER d' SUBSET b /\ c INTER j SUBSET a /\
     a SUBSET c /\ b SUBSET c /\ a INTER b = {p,q} /\ a UNION kj = j /\
     a INTER kj SUBSET b
     ==> (d UNION UNIONS {segment[v,x] | x IN j}) INTER
         UNIONS {segment[v,x] | x IN c}
           SUBSET c UNION UNIONS {segment[v,x] | x IN a} /\
         (c UNION UNIONS {segment[v,x] | x IN a}) INTER
         UNIONS {segment[v,x] | x IN b}
           SUBSET b UNION segment[v,p] UNION segment[v,q] /\
         ((d UNION UNIONS {segment[v,x] | x IN j}) DIFF
          (c UNION UNIONS {segment[v,x] | x IN a})) UNION
         UNIONS {segment[v,x] | x IN b} =
         d' UNION UNIONS {segment[v,x] | x IN kj UNION b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN a /\ q IN a /\ p IN b /\ q IN b` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET d /\ a SUBSET d /\ b SUBSET d /\
                kj SUBSET d /\ d' SUBSET d`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `cn = \X. UNIONS {segment[v:real^3,x] | x IN X}` THEN
  SUBGOAL_THEN `!X. UNIONS {segment[v:real^3,x] | x IN X} = cn X`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "cn" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!X Y. X SUBSET d /\ Y SUBSET d ==> cn X INTER Y SUBSET X) /\
    (!X Y. X SUBSET d /\ Y SUBSET d
           ==> cn X INTER cn Y SUBSET (v:real^3) INSERT cn (X INTER Y)) /\
    (!X Y. X SUBSET Y ==> cn X SUBSET cn Y) /\
    (!X Y. cn (X UNION Y) = cn X UNION cn Y) /\
    (!X. X SUBSET cn X) /\
    (!X x. x IN X ==> v IN cn X) /\
    cn {p,q} = segment[v,p] UNION segment[v,q]`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cn" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SGL_CONE_INTER_BASE THEN
      EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SGL_CONE_INTER_CONE THEN
      EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_SGL_CONE_MONO];
      REWRITE_TAC[MOI_SGL_CONE_UNION];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[MOI_SGL_CONE_BASE];
      MESON_TAC[MOI_SGL_CONE_APEX];
      REWRITE_TAC[MOI_SGL_CONE_PAIR]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `cn (c:real^3->bool) INTER d SUBSET c /\
                  cn c INTER cn j SUBSET (v:real^3) INSERT cn (c INTER j) /\
                  cn (c INTER j) SUBSET cn a /\ v IN cn (a:real^3->bool)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      SET_TAC[]];
    SUBGOAL_THEN `cn (b:real^3->bool) INTER c SUBSET b /\
                  cn a INTER cn b SUBSET (v:real^3) INSERT cn (a INTER b) /\
                  cn {p,q} = segment[v,p] UNION segment[v,q] /\
                  v IN segment[v,p]`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ENDS_IN_SEGMENT]];
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    SUBGOAL_THEN `cn (a:real^3->bool) INTER d' SUBSET a /\
                  cn kj INTER c SUBSET kj /\
                  cn kj INTER cn a SUBSET (v:real^3) INSERT cn (kj INTER a) /\
                  cn (kj INTER a) SUBSET cn b /\
                  cn j = cn a UNION cn kj /\
                  cn (kj UNION b) = cn kj UNION cn b /\
                  b SUBSET cn b /\ v IN cn b`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`d = c UNION d':real^3->bool`; `c INTER d' SUBSET b:real^3->bool`;
      `c INTER j SUBSET a:real^3->bool`; `a SUBSET c:real^3->bool`;
      `a UNION kj = j:real^3->bool`; `a INTER kj SUBSET b:real^3->bool`] THEN
    SET_TAC[]]);;

(* The final push step: if the cell D of the frontier of the 3-cell T is    *)
(* pushed across T, the sphere S becomes S'.                                *)

let MOI_SGL_PUSH_STEP = prove
 (`!t dd je s e s':real^3->bool.
     moi_sch3_push t dd je /\ compact t /\ je SUBSET dd /\ dd SUBSET s /\
     t SUBSET convex hull s /\ pl_polyhedron ((s DIFF dd) UNION je) /\
     s INTER t SUBSET dd /\ frontier t = dd UNION e /\ dd INTER e SUBSET je /\
     je SUBSET e /\ (s DIFF dd) UNION e = s' /\ moi_sch3_simple s'
     ==> moi_sch3_simple s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCD_PUSH_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `dd:real^3->bool`; `je:real^3->bool`] THEN
  SUBGOAL_THEN `(s DIFF dd) UNION (frontier t DIFF dd) UNION je = s':real^3->bool`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(s DIFF dd) UNION e = s':real^3->bool` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `frontier t = dd UNION e:real^3->bool` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `dd INTER e SUBSET je:real^3->bool` THEN
    UNDISCH_TAC `je SUBSET e:real^3->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  UNDISCH_TAC `s INTER t SUBSET dd:real^3->bool` THEN SET_TAC[]);;

(* ========================================================================= *)
(* The deletion step of Moise Thm 10 in real^3.  The free triangle c of the  *)
(* PL 2-cell d meets the boundary j in the arc A = (frontier c) INTER j; B   *)
(* (the arc bb) is the complementary arc of the boundary of c and kj the     *)
(* complementary arc of j; d' is the rest of d.  The tetrahedron T =         *)
(* hull(v,c) has the push property at the disk c UNION v*A (SIMPLEX_PUSH);   *)
(* pushing it carries the cone sphere of d onto the cone sphere of d'        *)
(* (MOI_SCD_PUSH_SIMPLE via MOI_SGL_PUSH_STEP).                              *)
(* ========================================================================= *)

let MOI_SGL_JE_FACTS = prove
 (`!(v:real^3) a b c p q.
     p IN a /\ q IN a /\ p IN b /\ q IN b /\ b SUBSET c
     ==> (b UNION segment[v,p] UNION segment[v,q]) SUBSET
         c UNION UNIONS {segment[v,x] | x IN a} /\
         (b UNION segment[v,p] UNION segment[v,q]) SUBSET
         UNIONS {segment[v,x] | x IN b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3`; `a:real^3->bool`; `p:real^3`] MOI_SGL_SEGMENT_CONE) THEN
  MP_TAC(ISPECL [`v:real^3`; `a:real^3->bool`; `q:real^3`] MOI_SGL_SEGMENT_CONE) THEN
  MP_TAC(ISPECL [`v:real^3`; `b:real^3->bool`; `p:real^3`] MOI_SGL_SEGMENT_CONE) THEN
  MP_TAC(ISPECL [`v:real^3`; `b:real^3->bool`; `q:real^3`] MOI_SGL_SEGMENT_CONE) THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET UNIONS {segment[v,x] | x IN b}` MP_TAC
  THENL [REWRITE_TAC[SUBSET] THEN MESON_TAC[MOI_SGL_CONE_BASE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(b:real^3->bool) SUBSET c` THEN
  MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[]);;

let MOI_SGL_DELETE3 = prove
 (`!d j c d' kj (bb:real^1->real^3) v.
     pl_cell_with_boundary 2 d j /\ ~(v IN d) /\
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x) /\
     &2 simplex c /\ c UNION d' = d /\
     c INTER d' SUBSET path_image bb /\
     c INTER j SUBSET relative_frontier c /\
     arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
     (relative_frontier c INTER j) UNION path_image bb = relative_frontier c /\
     (relative_frontier c INTER j) INTER path_image bb =
       {pathstart bb, pathfinish bb} /\
     (relative_frontier c INTER j) UNION kj = j /\
     (relative_frontier c INTER j) INTER kj SUBSET path_image bb /\
     moi_sch3_simple (d' UNION UNIONS {segment[v,x] | x IN kj UNION path_image bb})
     ==> moi_sch3_simple (d UNION UNIONS {segment[v,x] | x IN j})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SPU_CELL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `c UNION d' = d:real^3->bool` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier c SUBSET (c:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image bb SUBSET relative_frontier (c:real^3->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(relative_frontier c INTER j) UNION path_image bb =
                 relative_frontier (c:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart bb IN relative_frontier c INTER (j:real^3->bool) /\
    pathfinish bb IN relative_frontier c INTER j /\
    pathstart bb IN path_image (bb:real^1->real^3) /\
    pathfinish bb IN path_image bb`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(relative_frontier c INTER j) INTER path_image bb =
                 {pathstart bb, pathfinish (bb:real^1->real^3)}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN c) /\
                (!x y. x IN c /\ y IN c /\ y IN segment[v,x] ==> y = x)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (convex hull ((v:real^3) INSERT c)) /\
                compact (convex hull ((v:real^3) INSERT c))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`] MOI_SGL_TETRA) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bb:real^1->real^3`; `v:real^3`] MOI_SGL_CONE_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`; `c:real^3->bool`;
                 `d':real^3->bool`; `relative_frontier c INTER (j:real^3->bool)`;
                 `path_image (bb:real^1->real^3)`; `kj:real^3->bool`;
                 `pathstart (bb:real^1->real^3)`; `pathfinish (bb:real^1->real^3)`;
                 `v:real^3`] MOI_SGL_DEL_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `c INTER j SUBSET relative_frontier (c:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `relative_frontier c SUBSET (c:real^3->bool)` THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`relative_frontier c SUBSET (c:real^3->bool)`;
        `path_image bb SUBSET relative_frontier (c:real^3->bool)`] THEN
      SET_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`v:real^3`; `relative_frontier c INTER (j:real^3->bool)`;
                 `path_image (bb:real^1->real^3)`; `c:real^3->bool`;
                 `pathstart (bb:real^1->real^3)`; `pathfinish (bb:real^1->real^3)`]
    MOI_SGL_JE_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_frontier c SUBSET (c:real^3->bool)`;
      `path_image bb SUBSET relative_frontier (c:real^3->bool)`] THEN
    SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `frontier (convex hull ((v:real^3) INSERT c)) =
    (c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}) UNION
    UNIONS {segment[v,x] | x IN path_image bb} /\
    relative_frontier (convex hull ((v:real^3) INSERT c)) =
    (c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}) UNION
    UNIONS {segment[v,x] | x IN path_image bb}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`] MOI_SGL_TETRA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(relative_frontier c INTER j) UNION path_image bb =
                 relative_frontier (c:real^3->bool)` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM th]) THEN
    REWRITE_TAC[MOI_SGL_CONE_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(v:real^3) IN UNIONS {segment[v,x] | x IN j} /\
    UNIONS {segment[v,x] | x IN relative_frontier c INTER j} SUBSET
    UNIONS {segment[v,x] | x IN (j:real^3->bool)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SGL_CONE_APEX THEN
      EXISTS_TAC `pathstart (bb:real^1->real^3)` THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_SGL_CONE_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`; `v:real^3`] MOI_SGL_CONE_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_sphere 2 ((c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}) UNION
                 UNIONS {segment[v,x] | x IN path_image (bb:real^1->real^3)})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "relative_frontier"
       with Failure _ -> false))) THEN
    MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2
      (c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j})
      (path_image bb UNION segment[v,pathstart bb] UNION
       segment[v,pathfinish (bb:real^1->real^3)])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
      [`(c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}) UNION
        UNIONS {segment[v,x] | x IN path_image (bb:real^1->real^3)}`;
       `UNIONS {segment[v,x] | x IN path_image (bb:real^1->real^3)}`;
       `path_image bb UNION segment[v,pathstart bb] UNION
        segment[v,pathfinish (bb:real^1->real^3)]`] DISK_COMPLEMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}) INTER
       UNIONS {segment[v,x] | x IN path_image bb} SUBSET
       path_image bb UNION segment[v,pathstart bb] UNION
       segment[v,pathfinish (bb:real^1->real^3)]`;
      `(path_image bb UNION segment[v,pathstart bb] UNION
        segment[v,pathfinish (bb:real^1->real^3)])
        SUBSET c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER j}`] THEN
    MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SGL_PUSH_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull ((v:real^3) INSERT c)`;
    `c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER (j:real^3->bool)}`;
    `path_image bb UNION segment[v,pathstart bb] UNION
     segment[v,pathfinish (bb:real^1->real^3)]`;
    `UNIONS {segment[v,x] | x IN path_image (bb:real^1->real^3)}`;
    `d' UNION UNIONS {segment[v,x] | x IN kj UNION path_image (bb:real^1->real^3)}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLEX_PUSH THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `(c:real^3->bool) SUBSET d` THEN
    UNDISCH_TAC
     `UNIONS {segment[v,x] | x IN relative_frontier c INTER j} SUBSET
      UNIONS {segment[v,x] | x IN (j:real^3->bool)}` THEN
    MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `d UNION UNIONS {segment[v,x] | x IN (j:real^3->bool)}` THEN
    REWRITE_TAC[HULL_SUBSET] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET d` THEN
    UNDISCH_TAC `(v:real^3) IN UNIONS {segment[v,x] | x IN j}` THEN
    MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
    MP_TAC(ISPECL
      [`d UNION UNIONS {segment[v,x] | x IN (j:real^3->bool)}`;
       `c UNION UNIONS {segment[v,x] | x IN relative_frontier c INTER (j:real^3->bool)}`;
       `path_image bb UNION segment[v,pathstart bb] UNION
        segment[v,pathfinish (bb:real^1->real^3)]`] DISK_COMPLEMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(c:real^3->bool) SUBSET d` THEN
      UNDISCH_TAC
       `UNIONS {segment[v,x] | x IN relative_frontier c INTER j} SUBSET
        UNIONS {segment[v,x] | x IN (j:real^3->bool)}` THEN
      MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
      MESON_TAC[MOI_SPU_CELL_POLY]];
    MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`] MOI_SGL_TETRA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Planar models.  A PL 2-cell in real^3 has a triangulated planar model: a  *)
(* polygonal cell decomposition g of a 2-cell in real^2 by triangles and a   *)
(* PL homeomorphism onto the cell that is affine on every triangle (so       *)
(* FREE_CELL of pc_moi_sch3_free applies).                                   *)
(* ========================================================================= *)

(* Purity: the triangles of a triangulation of a convex body in the plane   *)
(* cover it.                                                                *)

let MOI_SGL_PURE2 = prove
 (`!t k:real^2->bool.
     simplicial_complex t /\ UNIONS t = k /\ convex k /\ ~(interior k = {})
     ==> UNIONS {c | c IN t /\ aff_dim c = &2} = k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS t = k:real^2->bool` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^2->bool. c IN t ==> closed c` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {c | c IN t /\ aff_dim c = &2}:real^2->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior (UNIONS {c | c IN t /\ ~(aff_dim c = &2)}:real^2->bool) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_RESTRICT; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^2->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFF_DIM THEN
    MP_TAC(ISPEC `c:real^2->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_2] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (k:real^2->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `k:real^2->bool`)) THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        ball(x:real^2,e) INTER UNIONS {c | c IN t /\ aff_dim c = &2} = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^2) DIFF UNIONS {c | c IN t /\ aff_dim c = &2}`
      OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN closure(interior k)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `ball(x:real^2,e) INTER interior k SUBSET
    interior (UNIONS {c | c IN t /\ ~(aff_dim c = &2)})`
  MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS t = k:real^2->bool` THEN
    UNDISCH_TAC `ball(x:real^2,e) INTER UNIONS {c | c IN t /\ aff_dim c = &2} = {}` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[SUBSET; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SGL_SIMPLEX2_FACTS = prove
 (`!k:real^2->bool.
     &2 simplex k ==> convex k /\ compact k /\ closed k /\ ~(interior k = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex (k:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `&2:int` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLEX_IMP_COMPACT THEN EXISTS_TAC `&2:int` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLEX_IMP_CLOSED THEN EXISTS_TAC `&2:int` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `k:real^2->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC AFF_DIM_SIMPLEX THEN ASM_REWRITE_TAC[]]);;

(* An affine map injective on a planar set with interior has an injective  *)
(* linear part; it maps a planar triangle onto a triangle in real^3, and    *)
(* the boundary onto the boundary.                                          *)

let MOI_SGL_LINEAR_INJ = prove
 (`!(l:real^2->real^3) c y (phi:real^2->real^3).
     linear l /\ ~(interior c = {}) /\ (!z. z IN c ==> phi z = l z + y) /\
     (!x x'. x IN c /\ x' IN c /\ phi x = phi x' ==> x = x')
     ==> !u w. l u = l w ==> u = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(interior (c:real^2->bool) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^2` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `w:real^2`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(l:real^2->real^3) (u - w) = vec 0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(u - w:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / (&2 * norm(u - w:real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((e / (&2 * norm(u - w:real^2))) % (u - w)) = e / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < norm(u - w:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(z0 + (e / (&2 * norm(u - w:real^2))) % (u - w)) IN c /\ (z0:real^2) IN c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; DIST_REFL] THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `z0 - (z0 + a % b):real^N = --(a % b)`; NORM_NEG] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `z0 + (e / (&2 * norm(u - w:real^2))) % (u - w) = z0`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                       MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    REWRITE_TAC[VECTOR_ARITH `z0 + a % b:real^N = z0 <=> a % b = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;

let MOI_SGL_AFFINE_SIMPLEX = prove
 (`!c (phi:real^2->real^3) l y.
     &2 simplex c /\ linear l /\ (!z. z IN c ==> phi z = l z + y) /\
     (!x x'. x IN c /\ x' IN c /\ phi x = phi x' ==> x = x')
     ==> &2 simplex (IMAGE phi c) /\
         relative_frontier (IMAGE phi c) = IMAGE phi (relative_frontier c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (c:real^2->bool) /\ closed c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (c:real^2->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_2] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^2->real^3`; `c:real^2->bool`; `y:real^3`;
                 `phi:real^2->real^3`] MOI_SGL_LINEAR_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. s SUBSET c ==> IMAGE (phi:real^2->real^3) s =
                IMAGE (\x. y + x) (IMAGE (l:real^2->real^3) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET; VECTOR_ADD_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier c SUBSET (c:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[SIMPLEX_TRANSLATION_EQ; RELATIVE_FRONTIER_TRANSLATION] THEN
  MP_TAC(ISPECL [`l:real^2->real^3`; `c:real^2->bool`; `&2:int`]
    SIMPLEX_LINEAR_IMAGE_EQ) THEN
  MP_TAC(ISPECL [`l:real^2->real^3`; `c:real^2->bool`]
    RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SGL_PLANAR_TRIANG = prove
 (`!d j:real^3->bool.
     pl_cell_with_boundary 2 d j
     ==> ?g j2 (phi:real^2->real^3) psi.
           moi_sfr_cplx g /\ (!c. c IN g ==> &2 simplex c) /\
           pl_cell_with_boundary 2 (UNIONS g) j2 /\
           pl_homeomorphism (UNIONS g,d) (phi,psi) /\
           (!c. c IN g ==> ?l y. linear l /\ !z. z IN c ==> phi z = l z + y) /\
           IMAGE phi j2 = j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA; moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^3`
    (X_CHOOSE_THEN `f':real^3->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_polyhedron (k:real^2->bool)` MP_TAC THENL
   [ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t0:(real^2->bool)->bool`; `f:real^2->real^3`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `UNIONS {c | c IN t /\ aff_dim c = &2} = k:real^2->bool`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SGL_PURE2 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^2->bool` MOI_SGL_SIMPLEX2_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{c | c IN t /\ aff_dim c = &2}:(real^2->bool)->bool`;
    `relative_frontier k:real^2->bool`; `f:real^2->real^3`; `f':real^3->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_sfr_cplx; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (c:real^2->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `n:int = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    REWRITE_TAC[MOI_SS2_CELL_EQ_FSA_2] THEN MATCH_MP_TAC MOI_FSA_DISK_TRI THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The free triangle in the plane (after FREE_CELL): its free arc A, the     *)
(* complementary arcs B (in the boundary of c) and kj (in the boundary j),   *)
(* and how c meets the rest of the decomposition.                            *)
(* ========================================================================= *)

let MOI_SGL_FREE_ARCS = prove
 (`!(gamc:real^1->real^N) gam h.
     simple_path gamc /\ pathfinish gamc = pathstart gamc /\
     pl_map_on (interval[vec 0,vec 1]) gamc /\
     simple_path gam /\ pathfinish gam = pathstart gam /\
     pl_map_on (interval[vec 0,vec 1]) gam /\
     arc h /\ path_image h SUBSET path_image gamc /\
     path_image h SUBSET path_image gam
     ==> ?bb kj. arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
                 path_image h UNION path_image bb = path_image gamc /\
                 path_image h INTER path_image bb = {pathstart bb, pathfinish bb} /\
                 path_image h UNION kj = path_image gam /\
                 path_image h INTER kj SUBSET path_image bb /\
                 closure ((path_image gam UNION path_image gamc) DIFF path_image h) =
                 kj UNION path_image bb`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`gamc:real^1->real^N`; `h:real^1->real^N`] MOI_PL2_ARC_IN_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`gam:real^1->real^N`; `h:real^1->real^N`] MOI_PL2_ARC_IN_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kg:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`kc:real^1->real^N`; `path_image (kg:real^1->real^N)`] THEN
  SUBGOAL_THEN `pathstart kc IN path_image (kc:real^1->real^N) /\
                pathfinish kc IN path_image kc`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `{pathstart kc, pathfinish kc} =
                {pathstart h, pathfinish (h:real^1->real^N)}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`{pathstart kc, pathfinish kc} = {pathstart h, pathfinish (h:real^1->real^N)}`;
      `pathstart kc IN path_image (kc:real^1->real^N)`;
      `pathfinish kc IN path_image (kc:real^1->real^N)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(path_image gam UNION path_image gamc) DIFF path_image h =
    (path_image kg DIFF {pathstart h, pathfinish h}) UNION
    (path_image kc DIFF {pathstart h, pathfinish (h:real^1->real^N)})`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image h INTER path_image kc =
       {pathstart h, pathfinish (h:real^1->real^N)}`;
      `path_image h UNION path_image kc = path_image (gamc:real^1->real^N)`;
      `path_image h INTER path_image kg =
       {pathstart h, pathfinish (h:real^1->real^N)}`;
      `path_image h UNION path_image kg = path_image (gam:real^1->real^N)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_UNION] THEN BINOP_TAC THEN
  MATCH_MP_TAC MOI_SFR_ARC_CLOSURE_DIFF THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]);;

let MOI_SGL_FREE_FACTS = prove
 (`!g j c:real^2->bool.
     moi_sfr_cplx g /\ pl_cell_with_boundary 2 (UNIONS g) j /\ c IN g /\
     pl_ball 1 (relative_frontier c INTER j) /\
     pl_cell_with_boundary 2 (UNIONS (g DELETE c))
       (closure ((j UNION relative_frontier c) DIFF (relative_frontier c INTER j)))
     ==> ?(bb:real^1->real^2) kj.
           arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
           (relative_frontier c INTER j) UNION path_image bb = relative_frontier c /\
           (relative_frontier c INTER j) INTER path_image bb =
             {pathstart bb, pathfinish bb} /\
           (relative_frontier c INTER j) UNION kj = j /\
           (relative_frontier c INTER j) INTER kj SUBSET path_image bb /\
           closure ((j UNION relative_frontier c) DIFF (relative_frontier c INTER j)) =
             kj UNION path_image bb /\
           c INTER UNIONS (g DELETE c) SUBSET path_image bb /\
           c INTER j SUBSET relative_frontier c /\
           c UNION UNIONS (g DELETE c) = UNIONS g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `relative_frontier (c:real^2->bool)`)) THEN
  MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MOI_SFR_CELL_FACTS o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_THEN `gamc:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS g:real^2->bool`; `j:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN
    ASSUME_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC o
    MATCH_MP MOI_PL2_PL_BALL_1_ARC) THEN
  MP_TAC(ISPECL [`gamc:real^1->real^2`; `gam:real^1->real^2`; `h:real^1->real^2`]
    MOI_SGL_FREE_ARCS) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^1->real^2` (X_CHOOSE_THEN `kj:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`bb:real^1->real^2`; `kj:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c INTER j SUBSET frontier (c:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^2->bool`; `UNIONS g:real^2->bool`] SUBSET_INTERIOR) THEN
    ANTS_TAC THENL [UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `frontier (UNIONS g) = j:real^2->bool` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `frontier (UNIONS g) INTER interior (UNIONS g) = {}:real^2->bool`
    MP_TAC THENL [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `frontier c UNION interior c = c:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[]] THEN
  MP_TAC(ISPECL [`UNIONS (g DELETE c):real^2->bool`;
                 `kj UNION path_image (bb:real^1->real^2)`] MOI_SFR_CELL_FACTS) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "closure" with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2)] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN frontier c` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN UNIONS (g DELETE c)` THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^2->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `c':real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN frontier (UNIONS (g DELETE c))` MP_TAC THENL
   [REWRITE_TAC[frontier; IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^2) IN closure(interior c)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^2) IN UNIONS (g DELETE c)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^2->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `c':real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^2) IN frontier c INTER j INTER kj` MP_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(frontier c INTER j) UNION kj = j:real^2->bool` THEN
    UNDISCH_TAC `(x:real^2) IN kj` THEN SET_TAC[];
    UNDISCH_TAC `(frontier c INTER j) INTER kj SUBSET path_image (bb:real^1->real^2)` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The deletion step with planar data: the facts about the free triangle in  *)
(* the plane (MOI_SGL_FREE_FACTS) are carried to real^3 by the planar model  *)
(* phi (injective, affine on each triangle) and MOI_SGL_DELETE3 is applied.  *)
(* ========================================================================= *)

let MOI_SGL_INJ_INTER = prove
 (`!(f:real^M->real^N) g k s t.
     (!x. x IN k ==> g (f x) = x) /\ s SUBSET k /\ t SUBSET k
     ==> IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t)`,
  MESON_TAC[MOI_SS2_INJ_IMAGE]);;

let MOI_SGL_DELETE_PL = prove
 (`!g j2 c kj (bb:real^1->real^2) (phi:real^2->real^3) psi v.
     pl_cell_with_boundary 2 (UNIONS g) j2 /\
     pl_homeomorphism (UNIONS g,IMAGE phi (UNIONS g)) (phi,psi) /\
     c IN g /\ &2 simplex c /\
     (?l y. linear l /\ !z. z IN c ==> phi z = l z + y) /\
     ~(v IN IMAGE phi (UNIONS g)) /\
     (!x y. x IN IMAGE phi (UNIONS g) /\ y IN IMAGE phi (UNIONS g) /\
            y IN segment[v,x] ==> y = x) /\
     arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
     (relative_frontier c INTER j2) UNION path_image bb = relative_frontier c /\
     (relative_frontier c INTER j2) INTER path_image bb =
       {pathstart bb, pathfinish bb} /\
     (relative_frontier c INTER j2) UNION kj = j2 /\
     (relative_frontier c INTER j2) INTER kj SUBSET path_image bb /\
     c INTER UNIONS (g DELETE c) SUBSET path_image bb /\
     c INTER j2 SUBSET relative_frontier c /\
     c UNION UNIONS (g DELETE c) = UNIONS g /\
     moi_sch3_simple (IMAGE phi (UNIONS (g DELETE c)) UNION
                      UNIONS {segment[v,x] | x IN IMAGE phi (kj UNION path_image bb)})
     ==> moi_sch3_simple (IMAGE phi (UNIONS g) UNION
                          UNIONS {segment[v,x] | x IN IMAGE phi j2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^2->bool) SUBSET UNIONS g /\
                UNIONS (g DELETE c) SUBSET UNIONS (g:(real^2->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c UNION UNIONS (g DELETE c) = UNIONS (g:(real^2->bool)->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier c SUBSET (c:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j2:real^2->bool) SUBSET UNIONS g` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SPU_CELL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image bb SUBSET relative_frontier (c:real^2->bool) /\
                (kj:real^2->bool) SUBSET j2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(relative_frontier c INTER j2) UNION path_image bb =
       relative_frontier (c:real^2->bool)`;
      `(relative_frontier c INTER j2) UNION kj = j2:real^2->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS g ==> (psi:real^3->real^2) ((phi:real^2->real^3) x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_LINV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. s SUBSET UNIONS g /\ t SUBSET UNIONS g
          ==> IMAGE (phi:real^2->real^3) s INTER IMAGE phi t = IMAGE phi (s INTER t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SGL_INJ_INTER THEN
    MAP_EVERY EXISTS_TAC [`psi:real^3->real^2`; `UNIONS g:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x x'. x IN c /\ x' IN c /\ (phi:real^2->real^3) x = phi x' ==> x = x'`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `phi:real^2->real^3`; `l:real^2->real^3`;
                 `y:real^3`] MOI_SGL_AFFINE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (phi:real^2->real^3) (UNIONS g)) (IMAGE phi j2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`UNIONS g:real^2->bool`;
                          `IMAGE (phi:real^2->real^3) (UNIONS g)`;
                          `psi:real^3->real^2`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; GSYM MOI_SS2_CELL_EQ_FSA_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^3) continuous_on UNIONS g /\
                pl_map_on (UNIONS g) (phi:real^2->real^3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_CONTINUOUS; pl_homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SGL_DELETE3 THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:real^2->real^3) c`;
    `IMAGE (phi:real^2->real^3) (UNIONS (g DELETE c))`;
    `IMAGE (phi:real^2->real^3) kj`;
    `(phi:real^2->real^3) o (bb:real^1->real^2)`] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  SUBGOAL_THEN `relative_frontier c INTER j2 SUBSET UNIONS (g:(real^2->bool)->bool)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image bb SUBSET UNIONS (g:(real^2->bool)->bool) /\
                relative_frontier c SUBSET UNIONS (g:(real^2->bool)->bool) /\
                kj SUBSET UNIONS (g:(real^2->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_UNION] THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS g:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS g:real^2->bool` THEN
    ASM_REWRITE_TAC[GSYM path_image];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Moise Thm 10 (p.121) by induction on the number of triangles of a planar  *)
(* model of the cell (free triangle: FREE_CELL of pc_moi_sch3_free;          *)
(* deletion: MOI_SGL_DELETE_PL; base: one tetrahedron).  The theorem         *)
(* CONE_DISK_SIMPLE.                                                         *)
(* ========================================================================= *)

let MOI_SGL_INDUCT = prove
 (`!n (g:(real^2->bool)->bool) j2 (phi:real^2->real^3) psi v.
     CARD g = n /\ moi_sfr_cplx g /\ (!c. c IN g ==> &2 simplex c) /\
     pl_cell_with_boundary 2 (UNIONS g) j2 /\
     pl_homeomorphism (UNIONS g,IMAGE phi (UNIONS g)) (phi,psi) /\
     (!c. c IN g ==> ?l y. linear l /\ !z. z IN c ==> phi z = l z + y) /\
     ~(v IN IMAGE phi (UNIONS g)) /\
     (!x y. x IN IMAGE phi (UNIONS g) /\ y IN IMAGE phi (UNIONS g) /\
            y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple (IMAGE phi (UNIONS g) UNION
                          UNIONS {segment[v,x] | x IN IMAGE phi j2})`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (g:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^2->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`UNIONS {}:real^2->bool`; `j2:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
    ASM_REWRITE_TAC[UNIONS_0] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `2 <= CARD (g:(real^2->bool)->bool)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^2->bool` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `g = {c:real^2->bool}` SUBST_ALL_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
      X_GEN_TAC `e:real^2->bool` THEN
      EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
      DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~(2 <= CARD (g:(real^2->bool)->bool))` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SFR_CARD2 THEN
      MAP_EVERY EXISTS_TAC [`c:real^2->bool`; `e:real^2->bool`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_1; IN_SING; FORALL_UNWIND_THM2]) THEN
    REWRITE_TAC[UNIONS_1] THEN
    SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `{c:real^2->bool}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `j2 = relative_frontier (c:real^2->bool)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`c:real^2->bool`; `j2:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:real^2->bool`; `phi:real^2->real^3`; `l:real^2->real^3`;
                   `y:real^3`] MOI_SGL_AFFINE_SIMPLEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_PL2_PL_HOMEO_LINV]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC MOI_SGL_BASE3 THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `{}:(real^2->bool)->bool`;
                 `j2:real^2->bool`] FREE_CELL) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[moi_sfr_cplx]) THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `j2:real^2->bool`; `c:real^2->bool`]
    MOI_SGL_FREE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^1->real^2` (X_CHOOSE_THEN `kj:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `CARD (g DELETE (c:real^2->bool))`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE] THEN UNDISCH_TAC `2 <= CARD (g:(real^2->bool)->bool)` THEN
    UNDISCH_TAC `CARD (g:(real^2->bool)->bool) = n` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`g DELETE (c:real^2->bool)`; `kj UNION path_image (bb:real^1->real^2)`;
     `phi:real^2->real^3`; `psi:real^3->real^2`; `v:real^3`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `UNIONS (g DELETE c) SUBSET UNIONS (g:(real^2->bool)->bool)`
    ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SFR_CPLX_SUBSET THEN
      EXISTS_TAC `g:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(lhs(concl th)) &&
        (try fst(dest_const(rator(lhs(concl th)))) = "closure"
         with Failure _ -> false))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`UNIONS g:real^2->bool`;
                            `IMAGE (phi:real^2->real^3) (UNIONS g)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `g DELETE (c:real^2->bool)` THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      ASM_MESON_TAC[MOI_SFR_CPLX_CELL];
      UNDISCH_TAC `~((v:real^3) IN IMAGE (phi:real^2->real^3) (UNIONS g))` THEN
      UNDISCH_TAC `UNIONS (g DELETE c) SUBSET UNIONS (g:(real^2->bool)->bool)` THEN
      SET_TAC[];
      ASM_MESON_TAC[IMAGE_SUBSET; SUBSET]];
    DISCH_TAC] THEN
  MATCH_MP_TAC MOI_SGL_DELETE_PL THEN
  MAP_EVERY EXISTS_TAC [`c:real^2->bool`; `kj:real^2->bool`; `bb:real^1->real^2`;
                        `psi:real^3->real^2`] THEN
  ASM_SIMP_TAC[]);;

let CONE_DISK_SIMPLE = prove
 (`!d j (v:real^3).
     pl_cell_with_boundary 2 d j /\ ~(v IN d) /\
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple (d UNION UNIONS {segment[v,x] | x IN j})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SGL_PLANAR_TRIANG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:(real^2->bool)->bool`; `j2:real^2->bool`;
                       `phi:real^2->real^3`; `psi:real^3->real^2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (phi:real^2->real^3) (UNIONS g) = d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (phi:real^2->real^3) j2 = j` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC MOI_SGL_INDUCT THEN
  MAP_EVERY EXISTS_TAC [`CARD (g:(real^2->bool)->bool)`; `psi:real^3->real^2`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Moise Thm 9 for a PL 2-sphere s met at most once by every ray from a      *)
(* point v of its inside (the theorem STAR_SIMPLE): a triangle tau of s      *)
(* spans with v a tetrahedron meeting s only in tau; pushing it across tau   *)
(* carries s onto the cone sphere over the disk (s - tau) UNION (boundary of *)
(* tau), which is simply imbedded by CONE_DISK_SIMPLE.                       *)
(* ========================================================================= *)

let MOI_SGL_SPHERE_TRIANGLE = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> ?tau. &2 simplex tau /\ tau SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `fc:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SPU_SIMPLEX_HAS_FACE) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `fc:real^3->bool`] MOI_SPU_FACE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (f:real^3->real^3) fc)
                            (IMAGE f (relative_frontier fc))`
  MP_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`fc:real^3->bool`; `f:real^3->real^3`;
                          `f':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k:real^3->bool`;
                          `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SGL_PLANAR_TRIANG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:(real^2->bool)->bool`; `j2:real^2->bool`;
                       `phi:real^2->real^3`; `psi:real^3->real^2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(g:(real^2->bool)->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`UNIONS {}:real^2->bool`; `j2:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
    ASM_REWRITE_TAC[UNIONS_0] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^2->bool`) THEN
  SUBGOAL_THEN `?l y. linear l /\ !z. z IN c ==> (phi:real^2->real^3) z = l z + y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (phi:real^2->real^3) c` THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `phi:real^2->real^3`; `l:real^2->real^3`;
                 `y:real^3`] MOI_SGL_AFFINE_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(c:real^2->bool) SUBSET UNIONS g` MP_TAC THENL
     [UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[MOI_PL2_PL_HOMEO_LINV; SUBSET];
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (phi:real^2->real^3) (UNIONS g)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN UNDISCH_TAC `(c:real^2->bool) IN g` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^2->real^3) (UNIONS g) = IMAGE (f:real^3->real^3) fc`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (relative_frontier k) = s` MP_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]; ALL_TAC] THEN
  UNDISCH_TAC `fc SUBSET relative_frontier (k:real^3->bool)` THEN SET_TAC[]);;

let STAR_SIMPLE = prove
 (`!s (v:real^3).
     pl_sphere 2 s /\ v IN inside s /\
     (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SGL_SPHERE_TRIANGLE) THEN
  SUBGOAL_THEN `~((v:real^3) IN s)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN tau) /\
                (!x y. x IN tau /\ y IN tau /\ y IN segment[v,x] ==> y = x)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 simplex (convex hull ((v:real^3) INSERT tau)) /\
    compact (convex hull ((v:real^3) INSERT tau)) /\
    frontier (convex hull ((v:real^3) INSERT tau)) =
      tau UNION UNIONS {segment[v,x] | x IN relative_frontier tau} /\
    relative_frontier (convex hull ((v:real^3) INSERT tau)) =
      tau UNION UNIONS {segment[v,x] | x IN relative_frontier tau} /\
    tau INTER UNIONS {segment[v,x] | x IN relative_frontier tau} =
      relative_frontier tau /\
    s INTER convex hull ((v:real^3) INSERT tau) SUBSET tau`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tau:real^3->bool`; `v:real^3`] MOI_SGL_TETRA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `tau:real^3->bool`; `s:real^3->bool`;
                   `v:real^3`] MOI_SGL_CONE_INTER_BASE) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 tau (relative_frontier tau:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN MATCH_MP_TAC MOI_FSA_DISK_TRI THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier tau SUBSET (tau:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `tau:real^3->bool`;
                 `relative_frontier tau:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_SGL_PUSH_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull ((v:real^3) INSERT tau)`; `tau:real^3->bool`;
    `relative_frontier tau:real^3->bool`;
    `UNIONS {segment[v,x] | x IN relative_frontier (tau:real^3->bool)}`;
    `((s DIFF tau) UNION relative_frontier tau) UNION
     UNIONS {segment[v,x] | x IN relative_frontier (tau:real^3->bool)}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLEX_PUSH THEN ASM_REWRITE_TAC[] THEN
    MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` INSIDE_SUBSET_CONVEX_HULL) THEN
      UNDISCH_TAC `(v:real^3) IN inside s` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[HULL_SUBSET]];
    ASM_MESON_TAC[MOI_SPU_CELL_POLY];
    REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[MOI_SGL_SUBSET_CONE];
    MP_TAC(ISPECL [`v:real^3`; `relative_frontier tau:real^3->bool`]
      MOI_SGL_SUBSET_CONE) THEN
    MOI_SGL_GEN_UNIONS_TAC THEN SET_TAC[];
    SUBGOAL_THEN `(s DIFF tau) UNION relative_frontier tau SUBSET (s:real^3->bool)`
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`relative_frontier tau SUBSET (tau:real^3->bool)`;
                             `tau SUBSET (s:real^3->bool)`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONE_DISK_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ========================================================================= *)
(* Moise Thm 11 (pp.121-122), the theorem THM11.  The two disks D1 = (s1 -   *)
(* d) UNION j and D2 = (s2 - d) UNION j form s; either the interior of D2    *)
(* misses the inside of s1 (push the filled s1 at D1 onto d, fixing D2: s    *)
(* becomes s2), or it lies inside s1, and then the interior of D1 misses the *)
(* inside of s2 (push the filled s2 at D2: s becomes s1).                    *)
(* ========================================================================= *)

let MOI_SGL_THM11_CASE = prove
 (`!s1 s2 d j:real^3->bool.
     moi_sch3_simple s1 /\ moi_sch3_simple s2 /\ pl_cell_with_boundary 2 d j /\
     d SUBSET convex hull j /\ s1 INTER s2 = d /\
     (s2 DIFF d) INTER inside s1 = {}
     ==> moi_sch3_simple ((s1 UNION s2) DIFF (d DIFF j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (s1:real^3->bool) /\ pl_sphere 2 (s2:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SCD_SIMPLE_IMP_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ d SUBSET s1 /\ d SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_SPU_CELL_POLY]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 ((s1 DIFF d) UNION j) (j:real^3->bool) /\
    pl_cell_with_boundary 2 ((s2 DIFF d) UNION j) (j:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (s1:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s1:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC MOI_SGL_PUSH_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`s1 UNION inside s1:real^3->bool`; `(s1 DIFF d) UNION j:real^3->bool`;
    `j:real^3->bool`; `d:real^3->bool`; `s2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(MATCH_MP MOI_SCD_SIMPLE_PUSH SIMPLEX_PUSH) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[COMPACT_WITH_INSIDE];
    SET_TAC[];
    ASM SET_TAC[];
    SUBGOAL_THEN
     `(s1:real^3->bool) SUBSET convex hull ((s1 UNION s2) DIFF (d DIFF j))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!a b c:real^3->bool. a SUBSET c /\ b SUBSET c /\ s = a UNION b
                             ==> s SUBSET c`) THEN
      MAP_EVERY EXISTS_TAC [`(s1 DIFF d) UNION j:real^3->bool`; `d:real^3->bool`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(s1 UNION s2) DIFF (d DIFF j):real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull j:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull s1:real^3->bool` THEN
    REWRITE_TAC[INSIDE_SUBSET_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
    SUBGOAL_THEN
     `(((s1 UNION s2) DIFF (d DIFF j)) DIFF ((s1 DIFF d) UNION j)) UNION j =
      (s2 DIFF d) UNION j:real^3->bool`
    SUBST1_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[MOI_SPU_CELL_POLY]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_SGL_NEST = prove
 (`!s1 s2 d:real^3->bool.
     pl_sphere 2 s1 /\ pl_sphere 2 s2 /\ s1 INTER s2 = d /\
     (s2 DIFF d) SUBSET inside s1
     ==> (s1 DIFF d) INTER inside s2 = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s1:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `outside s1 SUBSET outside (s2:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
    EXISTS_TAC `outside s1:real^3->bool` THEN ASM_REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPEC `s1:real^3->bool` OUTSIDE_INSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (inside s2:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC OPEN_INSIDE THEN
    ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT;
                  COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN closure(outside s1)` MP_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN frontier(outside s1)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `s2:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  SUBGOAL_THEN `(y:real^3) IN inside s2 /\ y IN outside s2` MP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> is_binary "SUBSET" (concl th) &&
                         rator(rand(concl th)) = `inside:(real^3->bool)->real^3->bool`)) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    SET_TAC[]]);;

let THM11 = prove
 (`!s1 s2 d j:real^3->bool.
     moi_sch3_simple s1 /\ moi_sch3_simple s2 /\ moi_sch3_plane_cell d j /\
     s1 INTER s2 = d
     ==> moi_sch3_simple ((s1 UNION s2) DIFF (d DIFF j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 d (j:real^3->bool) /\ d SUBSET convex hull j`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_plane_cell; PLANE_CELL_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (s1:real^3->bool) /\ pl_sphere 2 (s2:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SCD_SIMPLE_IMP_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ d SUBSET s1 /\ d SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_SPU_CELL_POLY]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(s2 DIFF d) INTER inside s1 = {}:real^3->bool` THENL
   [MATCH_MP_TAC MOI_SGL_THM11_CASE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s2 DIFF d) SUBSET inside (s1:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`(s2 DIFF d) UNION j:real^3->bool`; `j:real^3->bool`]
      MOI_SS2_CELL_FACTS) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `((s2 DIFF d) UNION j) DIFF j = s2 DIFF d:real^3->bool`
    SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s1:real^3->bool`; `s2 DIFF d:real^3->bool`]
      INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
    MP_TAC(ISPEC `s1:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
    UNDISCH_TAC `~((s2 DIFF d) INTER inside s1 = {}:real^3->bool)` THEN
    UNDISCH_TAC `s1 INTER s2 = d:real^3->bool` THEN
    UNDISCH_TAC `connected (s2 DIFF d:real^3->bool)` THEN
    REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN MATCH_MP_TAC MOI_SGL_THM11_CASE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SGL_NEST THEN ASM_REWRITE_TAC[]]);;

