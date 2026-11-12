(* ========================================================================= *)
(* pc_moi_s28_plane: planar facts transported along PL homeomorphisms       *)
(* (Moise GTM 47, p.198 (27.3) and Sec 3).  ANNULUS_COMPONENTS: a polygon in *)
(* the interior of a PL annulus cuts off a disk component or every component *)
(* of its complement reaches an end.  DISK_POLYGON: a polygon in a PL 2-cell *)
(* bounds a PL 2-cell inside it.  ANNULUS_FROM_HOLED, SQUARE_CELL: the       *)
(* models holed_disk_model 1 and 0 as pl_annulus_with_ends (either end       *)
(* inner) and pl_cell_with_boundary.  PRODUCT_ANNULUS: a product piece of a  *)
(* bicollar of a polygon is a PL annulus with the levels as ends.            *)
(* ANNULUS_COMPLEX: a PL annulus is triangulated by a combinatorial surface  *)
(* with chi 0 and boundary the two ends.  The PL product structure of the    *)
(* square annulus is moi_fps_psi of pc_moi_fnd_plst.                         *)
(* ========================================================================= *)

needs "src/pc_moi_s28_cut.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_fnd_plst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Transport along homeomorphisms.  Plane and half-plane charts move along   *)
(* homeomorphisms.  A PL 1-sphere j in the PL image a of a set X of the      *)
(* plane pulls back to a PL 1-sphere in X, and a PL 2-ball in X with         *)
(* frontier the pull-back of j pushes forward to a PL 2-cell bounded by j:   *)
(* MOI_S27_SPHERE_TO_PLANE and MOI_S27_CELL_FROM_PLANE (the case X = the     *)
(* square annulus) with the same proofs for any X.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_R2_TRANSPORT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g y.
     homeomorphism (s,t) (f,g) /\ moi_s28_locally_r2 s y
     ==> moi_s28_locally_r2 t (f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE (f:real^M->real^N) u) (f,g)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      concl th = `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) u` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `s:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`; `:M`,`:N`; `:2`,`:P`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S8PL_HALF_TRANSPORT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g y.
     homeomorphism (s,t) (f,g) /\ moi_s28_locally_half s y
     ==> moi_s28_locally_half t (f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real^M->bool` (X_CHOOSE_THEN `h:real^M->real^2`
      (X_CHOOSE_THEN `k:real^2->real^M` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `homeomorphism (IMAGE (f:real^M->real^N) u,u) (g,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      concl th = `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^M->real^N) u`;
                        `(h:real^M->real^2) o (g:real^N->real^M)`;
                        `(f:real^M->real^N) o (k:real^2->real^M)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `s:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      concl th = `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    UNDISCH_TAC `(y:real^M) IN u` THEN
    UNDISCH_TAC `(h:real^M->real^2) y = vec 0` THEN
    MESON_TAC[SUBSET]]);;

let MOI_S8PL_SPHERE_PULL = prove
 (`!(X:real^2->bool) (a:real^N->bool) (j:real^N->bool) f g.
     pl_homeomorphism
       (X,a) (f,g) /\
     pl_sphere 1 j /\ j SUBSET a
     ==> pl_sphere 1 (IMAGE g j) /\
         IMAGE g j SUBSET X /\
         IMAGE f (IMAGE g j) = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (IMAGE g j) = j` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^2) j SUBSET
    X`
  ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_sphere 1 (j:real^N->bool)` THEN
  REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k0,relative_frontier k)
                     ((h:real^2->real^N),(h':real^N->real^2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (h:real^2->real^N) (relative_frontier k0) = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S27_PLH_SIMPLEX_RF THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (j,IMAGE (g:real^N->real^2) j) (g,(f:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`a:real^N->bool`;
      `X:real^2->bool`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `j = IMAGE (F1:real^N->real^N) (relative_frontier k)`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  EXISTS_TAC `k0:real^2->bool` THEN
  EXISTS_TAC `(g:real^N->real^2) o (F1:real^N->real^N) o (h:real^2->real^N)` THEN
  EXISTS_TAC `((h':real^N->real^2) o (G1:real^N->real^N)) o (f:real^2->real^N)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S8PL_CELL_PUSH = prove
 (`!(X:real^2->bool) (a:real^N->bool) (j:real^N->bool) f g d.
     pl_homeomorphism
       (X,a) (f,g) /\
     pl_ball 2 d /\
     d SUBSET X /\
     frontier d = IMAGE g j /\ j SUBSET a /\ 2 <= dimindex(:N)
     ==> pl_cell_with_boundary 2 (IMAGE f d) j /\ IMAGE f d SUBSET a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `pl_ball 2 (d:real^2->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^2`
    (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k1:real^2->bool`; `d:real^2->bool`; `f1:real^2->real^2`;
                 `g1:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k1:real^2->bool` MOI_S27_SIMPLEX_TO_SPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^N->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (d,IMAGE (f:real^2->real^N) d) (f,(g:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`X:real^2->bool`; `a:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `d = IMAGE (f1:real^2->real^2) k1` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((f:real^2->real^N) o (f1:real^2->real^2) o (h':real^N->real^2))
          (relative_frontier kk) = j`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `relative_frontier k1 SUBSET (k1:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN (k1:real^2->bool) ==> (h':real^N->real^2) (h x) = x`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC
     `IMAGE (h:real^2->real^N) (relative_frontier k1) = relative_frontier kk` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `IMAGE (h':real^N->real^2) (IMAGE (h:real^2->real^N) (relative_frontier k1)) =
      relative_frontier k1`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `IMAGE (g:real^N->real^2) j = IMAGE (f1:real^2->real^2) (relative_frontier k1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  EXISTS_TAC `kk:real^N->bool` THEN
  EXISTS_TAC `(f:real^2->real^N) o (f1:real^2->real^2) o (h':real^N->real^2)` THEN
  EXISTS_TAC `((h:real^2->real^N) o (g1:real^2->real^2)) o (g:real^N->real^2)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SQUARE_CELL.  The square [-1,1]^2 is a PL 2-ball (PL_SCHOENFLIES_2 on its *)
(* boundary moi_fps_sq, whose inside is the open square), so is its affine   *)
(* image [0,4]^2 = holed_disk_model 0; MOI_S8PL_CELL_PUSH then gives the PL  *)
(* 2-cell bounded by the image of the frontier.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_SQUARE_BALL = prove
 (`pl_ball 2 (interval[--vec 1:real^2,vec 1])`,
  MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_fps_sq`) THEN REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `moi_fps_sq = frontier(interval[--vec 1:real^2,vec 1])` SUBST1_TAC THENL
   [REWRITE_TAC[moi_fps_sq] THEN MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; BOUNDED_INTERVAL; CONVEX_INTERVAL] THEN
  REWRITE_TAC[frontier] THEN SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL] THEN
  MP_TAC(ISPEC `interval[--vec 1:real^2,vec 1]` INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_S8PL_SQUARE04_BALL = prove
 (`pl_ball 2 (interval[vec 0:real^2,vector[&4;&4]])`,
  MATCH_MP_TAC PL_BALL_PL_HOMEOMORPHIC THEN
  EXISTS_TAC `interval[--vec 1:real^2,vec 1]` THEN
  MAP_EVERY EXISTS_TAC [`\z:real^2. &2 % z + vector[&2;&2]`;
                        `\w:real^2. inv(&2) % w + --vec 1`] THEN
  REWRITE_TAC[MOI_S8PL_SQUARE_BALL] THEN
  SUBGOAL_THEN `~(interval[--vec 1:real^2,vec 1] = {}) /\
                ~(interval[vec 0:real^2,vector[&4;&4]] = {})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT; VECTOR_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[homeomorphism; IMAGE_AFFINITY_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_2] THEN
      REAL_ARITH_TAC;
      AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_2;
                  PAIR_EQ; CONS_11] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_2] THEN
      REAL_ARITH_TAC;
      AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_2;
                  PAIR_EQ; CONS_11] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]];
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL; LINEAR_SCALING]]);;

let SQUARE_CELL = prove
 (MOI_S28_SQUARE_CELL,
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `f:real^2->real^N`; `g:real^N->real^2`] THEN
  REWRITE_TAC[MOI_FD_HOLED_DISK_MODEL_0] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `interval(vec 0:real^2,vector[&4;&4])`]
      INVARIANCE_OF_DIMENSION) THEN
    REWRITE_TAC[DIMINDEX_2; OPEN_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `interval(vec 0:real^2,vector[&4;&4]) SUBSET interval[vec 0,vector[&4;&4]]`
    ASSUME_TAC THENL [REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[vec 0:real^2,vector[&4;&4]]`; `a:real^N->bool`;
                 `IMAGE (f:real^2->real^N) (frontier(interval[vec 0:real^2,vector[&4;&4]]))`;
                 `f:real^2->real^N`; `g:real^N->real^2`;
                 `interval[vec 0:real^2,vector[&4;&4]]`] MOI_S8PL_CELL_PUSH) THEN
  SUBGOAL_THEN `frontier(interval[vec 0:real^2,vector[&4;&4]]) SUBSET
                interval[vec 0,vector[&4;&4]]` ASSUME_TAC THENL
   [SIMP_TAC[FRONTIER_SUBSET_CLOSED; CLOSED_INTERVAL]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S8PL_SQUARE04_BALL; SUBSET_REFL] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* DISK_POLYGON.  The 2-cell d is a PL image of a 2-simplex k0 of the plane  *)
(* (MOI_S27_SIMPLEX_FROM_PLANE); the polygon j pulls back to a PL 1-sphere J *)
(* in k0, J UNION inside J is a PL 2-ball inside the convex k0 with frontier *)
(* J (PL_SCHOENFLIES_2, INSIDE_SUBSET_CONVEX), and pushes forward to a PL    *)
(* 2-cell in d bounded by j.                                                 *)
(* ------------------------------------------------------------------------- *)

let DISK_POLYGON = prove
 (MOI_S28_DISK_POLYGON,
  MAP_EVERY X_GEN_TAC [`d:real^N->bool`; `b:real^N->bool`; `j:real^N->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_s28_bounds_disk] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    concl th = `pl_cell_with_boundary 2 (d:real^N->bool) b`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (k0,d) ((F1:real^N->real^N) o (h:real^2->real^N),
                             (h':real^N->real^2) o (G1:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `j:real^N->bool`;
                 `(F1:real^N->real^N) o (h:real^2->real^N)`;
                 `(h':real^N->real^2) o (G1:real^N->real^N)`] MOI_S8PL_SPHERE_PULL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = IMAGE ((h':real^N->real^2) o (G1:real^N->real^N)) j` THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_ball 2 (J UNION inside J:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `J UNION inside J SUBSET (k0:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(J UNION inside J:real^2->bool) = J` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^2->bool` PL_SPHERE_1_POLYGON) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC MOI_PL2_FRONTIER_JORDAN_REGION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `j:real^N->bool`;
                 `(F1:real^N->real^N) o (h:real^2->real^N)`;
                 `(h':real^N->real^2) o (G1:real^N->real^N)`;
                 `J UNION inside J:real^2->bool`] MOI_S8PL_CELL_PUSH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S27_SIMPLEX_DIMINDEX];
    STRIP_TAC] THEN
  EXISTS_TAC `IMAGE ((F1:real^N->real^N) o (h:real^2->real^N)) (J UNION inside J)` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ANNULUS_FROM_HOLED.  The frontier of the square annulus A = moi_fps_ann  *)
(* is the union of its two boundary squares, and the hd1 map of              *)
(* pc_moi_fnd_euler carries the frontier of holed_disk_model 1 onto it (a    *)
(* homeomorphism of closed sets of the plane preserves frontiers;            *)
(* MOI_FN2_HD1_FRONTIER of pc_moi_fnd_nb2, which is not loaded here, states  *)
(* the same).  The end swap of A is phi o (t |-> 3 - t) o psi with the       *)
(* product structure psi of pc_moi_fnd_plst.  Two disjoint connected         *)
(* nonempty sets with the same union as the two image squares are those      *)
(* squares in some order.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_RF_SQUARE = prove
 (`!r (x:real^2). &0 < r
     ==> (x IN relative_frontier(interval[--vector[r;r],vector[r;r]]) <=>
          max (abs(x$1)) (abs(x$2)) = r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]]) =
                frontier(interval[--vector[r;r]:real^2,vector[r;r]])` SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_NEG_COMPONENT; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_NEG_COMPONENT; VECTOR_2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S8PL_RF12 = prove
 (`relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
   {x:real^2 | max (abs(x$1)) (abs(x$2)) = &1} /\
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) =
   {x:real^2 | max (abs(x$1)) (abs(x$2)) = &2}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC MOI_S8PL_RF_SQUARE THEN REAL_ARITH_TAC);;

let MOI_S8PL_ANN_CLOSED = prove
 (`closed moi_fps_ann /\ compact moi_fps_ann`,
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_fps_ann] THEN MATCH_MP_TAC COMPACT_DIFF THEN
    REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL];
    REWRITE_TAC[COMPACT_IMP_CLOSED]]);;

let MOI_S8PL_ANN_FRONTIER = prove
 (`frontier moi_fps_ann =
   relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) UNION
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
  SIMP_TAC[frontier; CLOSURE_CLOSED; MOI_S8PL_ANN_CLOSED] THEN
  REWRITE_TAC[MOI_S8PL_RF12; EXTENSION; IN_DIFF; IN_UNION; IN_ELIM_THM;
              MOI_FPS_ANN; MOI_FPS_ANN_INTERIOR] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S8PL_HD1_FRONTIER = prove
 (`?gh. pl_homeomorphism (holed_disk_model 1,moi_fps_ann) (moi_feu_hd1_map,gh) /\
        IMAGE moi_feu_hd1_map (frontier (holed_disk_model 1)) =
        relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) UNION
        relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
  X_CHOOSE_TAC `gh:real^2->real^2`
    (REWRITE_RULE[GSYM moi_fps_ann] MOI_FEU_HD1_PL_HOMEOMORPHISM) THEN
  EXISTS_TAC `gh:real^2->real^2` THEN ASM_REWRITE_TAC[GSYM MOI_S8PL_ANN_FRONTIER] THEN
  MATCH_MP_TAC MOI_FPS_HOMEOMORPHISM_FRONTIER THEN EXISTS_TAC `gh:real^2->real^2` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism]) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FEU_EULER_HOLED_DISK_MODEL; MOI_S8PL_ANN_CLOSED]);;

(* The levels of psi.                                                        *)

let MOI_S8PL_PSI_LEVEL = prove
 (`!r. &1 <= r /\ r <= &2
       ==> IMAGE moi_fps_psi {x:real^2 | max (abs(x$1)) (abs(x$2)) = r} =
           moi_fps_sq PCROSS {lift r}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_TAC THEN MP_TAC(SPEC `x:real^2` MOI_FPS_PSI_COMPONENTS) THEN
    ANTS_TAC THENL [REWRITE_TAC[MOI_FPS_ANN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fps_psi x = pastecart (fstcart(moi_fps_psi x))
                                            (sndcart(moi_fps_psi x))` SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING; IN_IMAGE;
                IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `pastecart (u:real^2) (t:real^1)` MOI_FPS_PSI_ONTO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `x:real^2` MOI_FPS_PSI_COMPONENTS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN SIMP_TAC[]]);;

let MOI_S8PL_ANN_SWAP = prove
 (`?S S'. pl_homeomorphism (moi_fps_ann,moi_fps_ann) (S,S') /\
          IMAGE S (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) =
          relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) /\
          IMAGE S (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) =
          relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  X_CHOOSE_TAC `phi:real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  ABBREV_TAC `P = moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN
  ABBREV_TAC `sw = \z:real^(2,1)finite_sum.
                     pastecart (fstcart z) (lift(&3 - drop(sndcart z)))` THEN
  SUBGOAL_THEN `!z:real^(2,1)finite_sum. z IN P ==> sw z IN P /\ sw(sw z) = z`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN EXPAND_TAC "sw" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP; PASTECART_INJ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (P,P) (sw:real^(2,1)finite_sum->real^(2,1)finite_sum,sw)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      SUBGOAL_THEN `IMAGE (sw:real^(2,1)finite_sum->real^(2,1)finite_sum) P = P /\
                    sw continuous_on P` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_ANTISYM THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN ASM_MESON_TAC[];
          EXPAND_TAC "sw" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
          REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
        ASM_MESON_TAC[]];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\z:real^(2,1)finite_sum.
                    (\z. pastecart (fstcart z) (--(sndcart z))) z +
                    pastecart (vec 0:real^2) (lift(&3))` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "sw" THEN REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID] THEN
        GEN_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN CONJ_TAC THENL
         [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN EXPAND_TAC "P" THEN
          MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
          SIMP_TAC[MOI_FPS_SQ_PL_POLYHEDRON; POLYTOPE_IMP_PL_POLYHEDRON;
                   POLYTOPE_INTERVAL];
          MATCH_MP_TAC LINEAR_PASTECART THEN
          SIMP_TAC[LINEAR_FSTCART; LINEAR_COMPOSE_NEG; LINEAR_SNDCART]]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(phi:real^(2,1)finite_sum->real^2) o
     (sw:real^(2,1)finite_sum->real^(2,1)finite_sum) o moi_fps_psi`;
    `((phi:real^(2,1)finite_sum->real^2) o
      (sw:real^(2,1)finite_sum->real^(2,1)finite_sum)) o moi_fps_psi`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `P:real^(2,1)finite_sum->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `P:real^(2,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. (r = &1 \/ r = &2)
        ==> IMAGE (sw:real^(2,1)finite_sum->real^(2,1)finite_sum)
                  (moi_fps_sq PCROSS {lift r}) = moi_fps_sq PCROSS {lift(&3 - r)}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sw" THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
                PASTECART_IN_PCROSS; IN_SING; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_INJ] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    MESON_TAC[REAL_ARITH `&3 - (&3 - x) = x:real`; LIFT_DROP];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (moi_fps_ann,P) (moi_fps_psi,
                                    (phi:real^(2,1)finite_sum->real^2))`)) THEN
  SUBGOAL_THEN `!s:real^2->bool. s SUBSET moi_fps_ann
                ==> IMAGE (phi:real^(2,1)finite_sum->real^2) (IMAGE moi_fps_psi s) = s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^2) x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^2 | max (abs(x$1)) (abs(x$2)) = &1} SUBSET moi_fps_ann /\
                {x:real^2 | max (abs(x$1)) (abs(x$2)) = &2} SUBSET moi_fps_ann`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_FPS_ANN] THEN CONJ_TAC THEN GEN_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S8PL_RF12; IMAGE_o] THEN
  SIMP_TAC[MOI_S8PL_PSI_LEVEL; REAL_LE_REFL; REAL_ARITH `&1 <= &2`] THEN
  ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM(MATCH_MP MOI_S8PL_PSI_LEVEL (REAL_ARITH `&1 <= &1 /\ &1 <= &2`));
           GSYM(MATCH_MP MOI_S8PL_PSI_LEVEL (REAL_ARITH `&1 <= &2 /\ &2 <= &2`))] THEN
  ASM_SIMP_TAC[]);;

(* Matching the given ends with the two image squares.                       *)

let MOI_S8PL_CONNECTED_IN_TWO = prove
 (`!(s:real^N->bool) c0 c1.
     connected s /\ s SUBSET c0 UNION c1 /\ closed c0 /\ closed c1 /\ DISJOINT c0 c1
     ==> s SUBSET c0 \/ s SUBSET c1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOSED] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c0:real^N->bool`; `c1:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S8PL_TWO_PIECES = prove
 (`!(j0:real^N->bool) j1 c0 c1.
     j0 UNION j1 = c0 UNION c1 /\ DISJOINT j0 j1 /\ DISJOINT c0 c1 /\
     ~(j0 = {}) /\ ~(j1 = {}) /\ ~(c0 = {}) /\ ~(c1 = {}) /\
     (j0 SUBSET c0 \/ j0 SUBSET c1) /\ (j1 SUBSET c0 \/ j1 SUBSET c1)
     ==> (j0 = c0 /\ j1 = c1) \/ (j0 = c1 /\ j1 = c0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  ASM SET_TAC[]);;

(* The two boundary squares of A: compact, connected, nonempty.               *)

let MOI_S8PL_RF_FACTS = prove
 (`!r. &0 < r
       ==> compact (relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]])) /\
           connected (relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]])) /\
           ~(relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]]) = {})`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN REWRITE_TAC[BOUNDED_INTERVAL];
    MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_SPHERE_GEN THEN
    REWRITE_TAC[CONVEX_INTERVAL; BOUNDED_INTERVAL] THEN
    SUBGOAL_THEN `~(interior(interval[--vector[r;r]:real^2,vector[r;r]]) = {})`
      (fun th -> SIMP_TAC[th; AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2]) THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                  VECTOR_NEG_COMPONENT; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      INT_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vector[r; &0]:real^2` THEN
    ASM_SIMP_TAC[MOI_S8PL_RF_SQUARE; VECTOR_2] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The target.                                                               *)
(* ------------------------------------------------------------------------- *)

let ANNULUS_FROM_HOLED = prove
 (MOI_S28_ANNULUS_FROM_HOLED,
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `f:real^2->real^N`; `g:real^N->real^2`;
                       `j0:real^N->bool`; `j1:real^N->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  X_CHOOSE_THEN `gh:real^2->real^2` STRIP_ASSUME_TAC MOI_S8PL_HD1_FRONTIER THEN
  X_CHOOSE_THEN `S:real^2->real^2` (X_CHOOSE_THEN `S':real^2->real^2` STRIP_ASSUME_TAC)
    MOI_S8PL_ANN_SWAP THEN
  MP_TAC(SPEC `&1` MOI_S8PL_RF_FACTS) THEN MP_TAC(SPEC `&2` MOI_S8PL_RF_FACTS) THEN
  REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < &2`] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
                moi_fps_ann /\
                relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
                moi_fps_ann /\
                DISJOINT (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
                         (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S8PL_RF12; SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY; MOI_FPS_ANN] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R1 = relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  ABBREV_TAC `R2 = relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_fps_ann,a)
                  ((f:real^2->real^N) o (gh:real^2->real^2),
                   moi_feu_hd1_map o (g:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `holed_disk_model 1` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `F0 = (f:real^2->real^N) o (gh:real^2->real^2)` THEN
  ABBREV_TAC `G0 = moi_feu_hd1_map o (g:real^N->real^2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (moi_fps_ann,a:real^N->bool) (F0,G0)`)) THEN
  (* j0 UNION j1 is the union of the two image squares *)
  SUBGOAL_THEN `j0 UNION j1 = IMAGE (F0:real^2->real^N) R1 UNION IMAGE F0 R2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^2->real^N) (frontier (holed_disk_model 1)) = j0 UNION j1`)) THEN
    EXPAND_TAC "F0" THEN REWRITE_TAC[GSYM IMAGE_UNION; IMAGE_o] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE moi_feu_hd1_map (frontier (holed_disk_model 1)) = R1 UNION R2`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^2. x IN s ==> (f:real^2->real^2) x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        concl th = `pl_homeomorphism (holed_disk_model 1,moi_fps_ann)
                                     (moi_feu_hd1_map,gh)`)) THEN
    SUBGOAL_THEN `frontier (holed_disk_model 1) SUBSET holed_disk_model 1` MP_TAC THENL
     [SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED; MOI_FEU_EULER_HOLED_DISK_MODEL];
      ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN holed_disk_model 1 ==> (gh:real^2->real^2) (moi_feu_hd1_map x) = x` THEN
    MESON_TAC[SUBSET];
    ALL_TAC] THEN
  (* facts on the two image squares *)
  SUBGOAL_THEN
   `DISJOINT (IMAGE (F0:real^2->real^N) R1) (IMAGE F0 R2) /\
    ~(IMAGE (F0:real^2->real^N) R1 = {}) /\ ~(IMAGE (F0:real^2->real^N) R2 = {}) /\
    closed (IMAGE (F0:real^2->real^N) R1) /\ closed (IMAGE (F0:real^2->real^N) R2) /\
    connected (IMAGE (F0:real^2->real^N) R1) /\ connected (IMAGE (F0:real^2->real^N) R2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT (R1:real^2->bool) R2` THEN
      UNDISCH_TAC `(R1:real^2->bool) SUBSET moi_fps_ann` THEN
      UNDISCH_TAC `(R2:real^2->bool) SUBSET moi_fps_ann` THEN
      UNDISCH_TAC `!x. x IN moi_fps_ann ==> (G0:real^N->real^2) ((F0:real^2->real^N) x) = x` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j0:real^N->bool`; `j1:real^N->bool`;
                 `IMAGE (F0:real^2->real^N) R1`; `IMAGE (F0:real^2->real^N) R2`]
    MOI_S8PL_TWO_PIECES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S8PL_CONNECTED_IN_TWO THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j0 UNION j1 = IMAGE (F0:real^2->real^N) R1 UNION IMAGE F0 R2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`F0:real^2->real^N`; `G0:real^N->real^2`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(F0:real^2->real^N) o (S:real^2->real^2)`;
                          `(S':real^2->real^2) o (G0:real^N->real^2)`] THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* ANNULUS_COMPONENTS (Moise 27.3, component form).  Pull the polygon back   *)
(* to J in the square annulus A.  If 0 is not inside J, inside J is a        *)
(* component of A minus J missing the frontier of A whose closure is the PL  *)
(* ball J UNION inside J (MOI_S27_PLANE_CELL), and it pushes forward.  If 0  *)
(* is inside J, a component K of A minus J missing the frontier of A is open *)
(* in the plane and closed in the plane minus J, hence a component of the    *)
(* plane minus J (JORDAN_COMPONENTS): not the unbounded outside, and not the *)
(* inside, which contains 0, outside A.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_JORDAN = prove
 (`!J:real^2->bool.
     pl_sphere 1 J
     ==> compact J /\ ~(inside J = {}) /\ open (inside J) /\ connected (inside J) /\
         bounded (inside J) /\ ~bounded (outside J) /\ inside J INTER J = {} /\
         frontier (inside J) = J /\
         components ((:real^2) DIFF J) = {inside J, outside J}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `polygonal_path (pp:(real^2)list)` JORDAN_INSIDE_OUTSIDE) THEN
  MP_TAC(ISPEC `polygonal_path (pp:(real^2)list)` JORDAN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
  MATCH_MP_TAC COMPACT_PATH_IMAGE THEN ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH]);;

let MOI_S8PL_CLOSURE_IMAGE = prove
 (`!(f:real^M->real^N) s k.
     compact s /\ f continuous_on s /\ k SUBSET s
     ==> closure(IMAGE f k) = IMAGE f (closure k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closure k SUBSET (s:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[COMPACT_CLOSURE] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; COMPACT_IMP_BOUNDED]];
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let MOI_S8PL_COMPONENT_MONO = prove
 (`!(s:real^N->bool) t c.
     c IN components s /\ c SUBSET t /\ t SUBSET s ==> c IN components t`,
  REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN SET_TAC[]);;

let MOI_S8PL_ANN_INTERIOR_FRONTIER = prove
 (`interior moi_fps_ann = moi_fps_ann DIFF frontier moi_fps_ann /\
   bounded moi_fps_ann /\ ~(vec 0 IN moi_fps_ann)`,
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[frontier; CLOSURE_CLOSED; MOI_S8PL_ANN_CLOSED] THEN
    MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN SET_TAC[];
    SIMP_TAC[COMPACT_IMP_BOUNDED; MOI_S8PL_ANN_CLOSED];
    REWRITE_TAC[MOI_FPS_ANN; VEC_COMPONENT] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The target.                                                               *)
(* ------------------------------------------------------------------------- *)

let ANNULUS_COMPONENTS = prove
 (MOI_S28_ANNULUS_COMPONENTS,
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                       `j:real^N->bool`] THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^2->real^N`
    (X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (moi_fps_ann,a:real^N->bool) (f,g)`)) THEN
  MP_TAC(ISPECL [`moi_fps_ann`; `a:real^N->bool`; `j:real^N->bool`; `f:real^2->real^N`;
                 `g:real^N->real^2`] MOI_S8PL_SPHERE_PULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j SUBSET a DIFF (j0 UNION j1:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = IMAGE (g:real^N->real^2) j` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S8PL_JORDAN (ASSUME `pl_sphere 1 (J:real^2->bool)`)) THEN STRIP_TAC THEN
  MP_TAC MOI_S8PL_ANN_INTERIOR_FRONTIER THEN STRIP_TAC THEN
  MP_TAC MOI_S8PL_ANN_FRONTIER THEN
  ABBREV_TAC `R1 = relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  ABBREV_TAC `R2 = relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `frontier moi_fps_ann SUBSET moi_fps_ann` ASSUME_TAC THENL
   [SIMP_TAC[FRONTIER_SUBSET_CLOSED; MOI_S8PL_ANN_CLOSED]; ALL_TAC] THEN
  (* the polygon misses the frontier of A *)
  SUBGOAL_THEN `(J:real^2->bool) INTER frontier moi_fps_ann = {}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SUBST1_TAC(SYM(ASSUME `IMAGE (g:real^N->real^2) j = J`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN a /\ ~(y IN j0) /\ ~(y IN j1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `j SUBSET a DIFF (j0 UNION j1:real^N->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN j` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) x = y` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^N) IN j0)` THEN UNDISCH_TAC `~((y:real^N) IN j1)` THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `interior moi_fps_ann`] INVARIANCE_OF_DIMENSION) THEN
    REWRITE_TAC[DIMINDEX_2; OPEN_INTERIOR] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vector[&3 / &2; &0]:real^2` THEN
      REWRITE_TAC[MOI_FPS_ANN_INTERIOR; VECTOR_2] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(vec 0:real^2) IN inside J` THENL
   [DISJ2_TAC THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `homeomorphism (a DIFF j,moi_fps_ann DIFF J)
                    ((g:real^N->real^2),(f:real^2->real^N))` ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `moi_fps_ann`] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[homeomorphism] THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (g:real^N->real^2) j = J`)) THEN
      UNDISCH_TAC `j SUBSET a DIFF (j0 UNION j1:real^N->bool)` THEN
      UNDISCH_TAC `!y. y IN a ==> (f:real^2->real^N) (g y) = y` THEN
      UNDISCH_TAC `!x. x IN moi_fps_ann ==> (g:real^N->real^2) (f x) = x` THEN
      UNDISCH_TAC `IMAGE (g:real^N->real^2) a = moi_fps_ann` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `K = IMAGE (g:real^N->real^2) k` THEN
    SUBGOAL_THEN `(K:real^2->bool) IN components (moi_fps_ann DIFF J)` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHISM_COMPONENTS) THEN
      EXPAND_TAC "K" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(K:real^2->bool) SUBSET interior moi_fps_ann DIFF J` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`moi_fps_ann DIFF J:real^2->bool`; `K:real^2->bool`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
      UNDISCH_TAC `k INTER (j0 UNION j1:real^N->bool) = {}` THEN
      UNDISCH_TAC `(k:real^N->bool) IN components (a DIFF j)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      UNDISCH_TAC `j0 = IMAGE (f:real^2->real^N) R1` THEN
      UNDISCH_TAC `j1 = IMAGE (f:real^2->real^N) R2` THEN
      UNDISCH_TAC `!y. y IN a ==> (f:real^2->real^N) (g y) = y` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (K:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_COMPONENTS THEN
      EXISTS_TAC `interior moi_fps_ann DIFF J:real^2->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED];
        MATCH_MP_TAC MOI_S8PL_COMPONENT_MONO THEN
        EXISTS_TAC `moi_fps_ann DIFF J:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(K:real^2->bool) IN components ((:real^2) DIFF J)` MP_TAC THENL
     [MATCH_MP_TAC CLOPEN_IN_COMPONENTS THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`moi_fps_ann DIFF J:real^2->bool`; `K:real^2->bool`]
          CLOSED_IN_COMPONENT) THEN
        ASM_REWRITE_TAC[CLOSED_IN_CLOSED] THEN
        DISCH_THEN(X_CHOOSE_THEN `f0:real^2->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `moi_fps_ann INTER f0:real^2->bool` THEN
        ASM_SIMP_TAC[CLOSED_INTER; MOI_S8PL_ANN_CLOSED] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
        ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(vec 0:real^2) IN inside J` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(K:real^2->bool) SUBSET interior moi_fps_ann DIFF J` THEN
      MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `~((vec 0:real^2) IN moi_fps_ann)` THEN SET_TAC[];
      UNDISCH_TAC `~bounded(outside(J:real^2->bool))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_fps_ann` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* 0 is not inside J: the disk component *)
  DISJ1_TAC THEN
  MP_TAC(REWRITE_RULE[GSYM moi_fps_ann] (SPEC `J:real^2->bool` MOI_S27_PLANE_CELL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `inside J SUBSET interior moi_fps_ann DIFF (J:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(s:real^2->bool) SUBSET t /\ s INTER u = {} ==> s SUBSET t DIFF u`) THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    UNDISCH_TAC `J UNION inside J SUBSET moi_fps_ann` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(inside J) = J UNION inside (J:real^2->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^2->real^N) (inside J)` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `homeomorphism (moi_fps_ann DIFF J,a DIFF j)
                    ((f:real^2->real^N),(g:real^N->real^2))` ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`moi_fps_ann`; `a:real^N->bool`] THEN
      ASM_REWRITE_TAC[homeomorphism] THEN SUBST1_TAC(SYM(ASSUME `IMAGE (g:real^N->real^2) j = J`)) THEN
      UNDISCH_TAC `j SUBSET a DIFF (j0 UNION j1:real^N->bool)` THEN
      UNDISCH_TAC `!y. y IN a ==> (f:real^2->real^N) (g y) = y` THEN
      UNDISCH_TAC `!x. x IN moi_fps_ann ==> (g:real^N->real^2) (f x) = x` THEN
      UNDISCH_TAC `IMAGE (g:real^N->real^2) a = moi_fps_ann` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHISM_COMPONENTS) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC CLOPEN_IN_COMPONENTS THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `inside J = (moi_fps_ann DIFF J) INTER closure(inside(J:real^2->bool))`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `inside J SUBSET interior moi_fps_ann DIFF (J:real^2->bool)` THEN
        MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_CLOSURE]];
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `inside J SUBSET interior moi_fps_ann DIFF (J:real^2->bool)` THEN
      MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN SET_TAC[]];
    UNDISCH_TAC `inside J SUBSET interior moi_fps_ann DIFF (J:real^2->bool)` THEN
    UNDISCH_TAC `interior moi_fps_ann = moi_fps_ann DIFF frontier moi_fps_ann` THEN
    UNDISCH_TAC `frontier moi_fps_ann = R1 UNION (R2:real^2->bool)` THEN
    UNDISCH_TAC `frontier moi_fps_ann SUBSET moi_fps_ann` THEN
    UNDISCH_TAC `j0 = IMAGE (f:real^2->real^N) R1` THEN
    UNDISCH_TAC `j1 = IMAGE (f:real^2->real^N) R2` THEN
    UNDISCH_TAC `!x. x IN moi_fps_ann ==> (g:real^N->real^2) (f x) = x` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`f:real^2->real^N`; `moi_fps_ann`; `inside J:real^2->bool`]
      MOI_S8PL_CLOSURE_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_S8PL_ANN_CLOSED] THEN
      UNDISCH_TAC `inside J SUBSET interior moi_fps_ann DIFF (J:real^2->bool)` THEN
      MP_TAC(ISPEC `moi_fps_ann` INTERIOR_SUBSET) THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^N->bool`; `j:real^N->bool`; `f:real^2->real^N`;
                   `g:real^N->real^2`; `J UNION inside J:real^2->bool`]
      (REWRITE_RULE[GSYM moi_fps_ann] MOI_S27_CELL_FROM_PLANE)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j SUBSET a DIFF (j0 UNION j1:real^N->bool)` THEN SET_TAC[];
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Product charts.  If m has line charts, then m x [c1,c2] has plane charts  *)
(* at the points with c1 < t < c2, (h x, t) with a line chart h, and         *)
(* half-plane charts at the end levels, (h x - h x0, sg (c - t)) with        *)
(* c = c1, sg = -1 or c = c2, sg = 1 (as MOI_S8CU_COLLAR_HALF, without the   *)
(* bicollar).                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_PROD_R2 = prove
 (`!(m:real^N->bool) c1 c2 (x0:real^N) t0.
     moi_s4l_line_charts m /\ x0 IN m /\ c1 < drop t0 /\ drop t0 < c2
     ==> moi_s28_locally_r2 (m PCROSS interval[lift c1,lift c2]) (pastecart x0 t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x0:real^N` (GEN_REWRITE_RULE I [moi_s4l_line_charts]
    (ASSUME `moi_s4l_line_charts (m:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `V = IMAGE (h:real^N->real^1) (m INTER u)` THEN
  ABBREV_TAC `J = {t:real^1 | c1 < drop t /\ drop t < c2}` THEN
  ABBREV_TAC `N = (m INTER u:real^N->bool) PCROSS (J:real^1->bool)` THEN
  ABBREV_TAC `psi = \y:real^(N,1)finite_sum.
                      drop((h:real^N->real^1) (fstcart y)) % basis 1 +
                      drop(sndcart y) % basis 2:real^2` THEN
  ABBREV_TAC `phi = \v:real^2. pastecart ((h':real^1->real^N) (lift(v$1))) (lift(v$2))` THEN
  SUBGOAL_THEN `!y:real^(N,1)finite_sum. (psi:real^(N,1)finite_sum->real^2) y$1 =
                                         drop(h(fstcart y)) /\
                                         psi y$2 = drop(sndcart y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "psi" THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^(N,1)finite_sum. y IN N ==> (phi:real^2->real^(N,1)finite_sum) (psi y) = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `t1:real^1`] THEN STRIP_TAC THEN
    EXPAND_TAC "phi" THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[PASTECART_INJ] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (psi:real^(N,1)finite_sum->real^2) N =
    {v:real^2 | (\v:real^2. lift(v$1)) v IN V} INTER
    {v | (\v:real^2. lift(v$2)) v IN interval(lift c1,lift c2)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `v:real^2` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(N,1)finite_sum` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      EXPAND_TAC "N" THEN REWRITE_TAC[PCROSS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      UNDISCH_TAC `(t1:real^1) IN J` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN ASM SET_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `?x1:real^N. x1 IN m INTER u /\ (h:real^N->real^1) x1 = lift((v:real^2)$1)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `lift((v:real^2)$1) IN V` THEN EXPAND_TAC "V" THEN SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `pastecart (x1:real^N) (lift((v:real^2)$2))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
        ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
        EXPAND_TAC "N" THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_R2_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`N:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real^2`;
                        `phi:real^2->real^(N,1)finite_sum`] THEN
  REPEAT CONJ_TAC THENL
   [(* N open in the product *)
    SUBGOAL_THEN `N = (m PCROSS interval[lift c1,lift c2]) INTER
                      ((u:real^N->bool) PCROSS interval(lift c1,lift c2))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["N"; "J"] THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTER; IN_ELIM_THM;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]];
    (* the point *)
    EXPAND_TAC "N" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    (* homeomorphism *)
    REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THENL
       [SUBGOAL_THEN `(\y:real^(N,1)finite_sum. (h:real^N->real^1) (fstcart y)) =
                      h o fstcart` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m INTER u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART] THEN SIMP_TAC[];
        SIMP_TAC[ETA_AX; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
      REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `v:real^2` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^(N,1)finite_sum` THEN
        DISCH_TAC THEN EXISTS_TAC `(psi:real^(N,1)finite_sum->real^2) y` THEN
        ASM_SIMP_TAC[] THEN EXISTS_TAC `y:real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "phi" THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\v:real^2. (h':real^1->real^N) (lift(v$1))) =
                      h' o (\v. lift(v$1))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^1->bool` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
        SIMP_TAC[];
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]]];
    (* the image is open *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN GEN_TAC THEN
    SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_2; ARITH]]);;

let MOI_S8PL_PROD_HALF = prove
 (`!(m:real^N->bool) c1 c2 (x0:real^N) c sg.
     moi_s4l_line_charts m /\ x0 IN m /\ c1 < c2 /\
     ((c = c1 /\ sg = -- &1) \/ (c = c2 /\ sg = &1))
     ==> moi_s28_locally_half (m PCROSS interval[lift c1,lift c2]) (pastecart x0 (lift c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `sg * sg = &1 /\
                (!t. &0 <= sg * (c - t) /\ sg * (c - t) < c2 - c1 <=>
                     c1 <= t /\ t <= c2 /\ c - (c2 - c1) < t /\ t < c + (c2 - c1))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x0:real^N` (GEN_REWRITE_RULE I [moi_s4l_line_charts]
    (ASSUME `moi_s4l_line_charts (m:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `V = IMAGE (h:real^N->real^1) (m INTER u)` THEN
  ABBREV_TAC `s0 = drop((h:real^N->real^1) x0)` THEN
  ABBREV_TAC `J = {t:real^1 | &0 <= sg * (c - drop t) /\ sg * (c - drop t) < c2 - c1}` THEN
  ABBREV_TAC `N = (m INTER u:real^N->bool) PCROSS (J:real^1->bool)` THEN
  ABBREV_TAC `psi = \y:real^(N,1)finite_sum.
                      (drop((h:real^N->real^1) (fstcart y)) - s0) % basis 1 +
                      (sg * (c - drop(sndcart y))) % basis 2:real^2` THEN
  ABBREV_TAC `phi = \v:real^2. pastecart ((h':real^1->real^N) (lift(v$1 + s0)))
                                         (lift(c - sg * v$2))` THEN
  SUBGOAL_THEN `!y:real^(N,1)finite_sum. (psi:real^(N,1)finite_sum->real^2) y$1 =
                                         drop(h(fstcart y)) - s0 /\
                                         psi y$2 = sg * (c - drop(sndcart y))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "psi" THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^(N,1)finite_sum. y IN N ==> (phi:real^2->real^(N,1)finite_sum) (psi y) = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `t1:real^1`] THEN STRIP_TAC THEN
    EXPAND_TAC "phi" THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[REAL_ARITH `(x - s) + s = x:real`; LIFT_DROP] THEN
    SUBGOAL_THEN `c - sg * sg * (c - drop(t1:real^1)) = drop t1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_INJ] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (psi:real^(N,1)finite_sum->real^2) N =
    {z:real^2 | &0 <= z$2} INTER
    ({v:real^2 | (\v:real^2. lift(v$1 + s0)) v IN V} INTER
     {v | (\v:real^2. lift(v$2)) v IN interval(lift(--(&1)),lift(c2 - c1))})`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `v:real^2` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(N,1)finite_sum` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      EXPAND_TAC "N" THEN REWRITE_TAC[PCROSS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      REWRITE_TAC[REAL_ARITH `(x - s) + s = x:real`; LIFT_DROP] THEN
      UNDISCH_TAC `(t1:real^1) IN J` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [EXPAND_TAC "V" THEN ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN
      SUBGOAL_THEN `?x1:real^N. x1 IN m INTER u /\
                                (h:real^N->real^1) x1 = lift((v:real^2)$1 + s0)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `lift((v:real^2)$1 + s0) IN V` THEN EXPAND_TAC "V" THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `pastecart (x1:real^N) (lift(c - sg * (v:real^2)$2))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
        ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
        REWRITE_TAC[REAL_ARITH `c - (c - s * x) = s * x:real`; REAL_MUL_ASSOC] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC;
        EXPAND_TAC "N" THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
        REWRITE_TAC[REAL_ARITH `c - (c - s * x) = s * x:real`; REAL_MUL_ASSOC] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_HALF_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`N:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real^2`;
                        `phi:real^2->real^(N,1)finite_sum`] THEN
  REPEAT CONJ_TAC THENL
   [(* N open in the product *)
    SUBGOAL_THEN `N = (m PCROSS interval[lift c1,lift c2]) INTER
                      ((u:real^N->bool) PCROSS
                       interval(lift(c - (c2 - c1)),lift(c + (c2 - c1))))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["N"; "J"] THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTER; IN_ELIM_THM;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]];
    (* the point *)
    EXPAND_TAC "N" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    (* homeomorphism *)
    REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_CMUL; LIFT_DROP] THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        SUBGOAL_THEN `(\y:real^(N,1)finite_sum. (h:real^N->real^1) (fstcart y)) =
                      h o fstcart` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m INTER u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART] THEN SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        SIMP_TAC[CONTINUOUS_ON_CONST; ETA_AX; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
      REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `v:real^2` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^(N,1)finite_sum` THEN
        DISCH_TAC THEN EXISTS_TAC `(psi:real^(N,1)finite_sum->real^2) y` THEN
        ASM_SIMP_TAC[] THEN EXISTS_TAC `y:real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "phi" THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\v:real^2. (h':real^1->real^N) (lift(v$1 + s0))) =
                      h' o (\v. lift(v$1 + s0))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          SIMP_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^1->bool` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
          SIMP_TAC[]];
        REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]]];
    (* open in H *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN GEN_TAC THEN
    REWRITE_TAC[LIFT_ADD] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ADD) THEN
    SIMP_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_2; ARITH];
    (* the point maps to 0 *)
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; FSTCART_PASTECART;
                    SNDCART_PASTECART; LIFT_DROP] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* ANNULUS_COMPLEX.  G = f o phi carries P = moi_fps_sq x [1,2] onto the     *)
(* annulus a, the end levels onto the ends.  P has plane charts off the end *)
(* levels and half-plane charts on them (MOI_S8PL_PROD_R2, _PROD_HALF with   *)
(* the line charts of the PL 1-sphere moi_fps_sq); they move to a along G.   *)
(* A triangulation of the PL polyhedron a is then a combinatorial surface   *)
(* (SURF_LOCAL) whose boundary is the union of the ends, with chi 0          *)
(* (MOI_FEU_PL_HOMEOMORPHIC_EULER, MOI_FEU_EULER_ANNULUS_MODEL).             *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_PHI_LEVELS = prove
 (`!phi. pl_homeomorphism (moi_fps_ann,moi_fps_sq PCROSS interval[lift(&1),lift(&2)])
                          (moi_fps_psi,phi)
         ==> IMAGE (phi:real^(2,1)finite_sum->real^2) (moi_fps_sq PCROSS {lift(&1)}) =
             relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
             IMAGE phi (moi_fps_sq PCROSS {lift(&2)}) =
             relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
  GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_S8PL_RF12] THEN
  SIMP_TAC[GSYM(MATCH_MP MOI_S8PL_PSI_LEVEL (REAL_ARITH `&1 <= &1 /\ &1 <= &2`));
           GSYM(MATCH_MP MOI_S8PL_PSI_LEVEL (REAL_ARITH `&1 <= &2 /\ &2 <= &2`))] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN CONJ_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x:real^2. x IN s ==> (f:real^2->real^2) x = x) ==> IMAGE f s = s`) THEN
  REWRITE_TAC[o_THM; IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MOI_FPS_ANN] THEN ASM_REAL_ARITH_TAC);;

let ANNULUS_COMPLEX = prove
 (MOI_S28_ANNULUS_COMPLEX,
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`] THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_TAC `phi:real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  MP_TAC(MATCH_MP MOI_S8PL_PHI_LEVELS (ASSUME
    `pl_homeomorphism (moi_fps_ann,moi_fps_sq PCROSS interval[lift(&1),lift(&2)])
                      (moi_fps_psi,phi:real^(2,1)finite_sum->real^2)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fps_sq PCROSS interval[lift(&1),lift(&2)],a)
      ((f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2),
       moi_fps_psi o (g:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN
  SUBGOAL_THEN `j0 = IMAGE ((f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2))
                           (moi_fps_sq PCROSS {lift(&1)}) /\
                j1 = IMAGE ((f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2))
                           (moi_fps_sq PCROSS {lift(&2)})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `j0 = IMAGE (f:real^2->real^N)
                (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `j1 = IMAGE (f:real^2->real^N)
                (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`)) THEN
  ABBREV_TAC `G = (f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2)` THEN
  ABBREV_TAC `G' = moi_fps_psi o (g:real^N->real^2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (P:real^(2,1)finite_sum->bool,a:real^N->bool) (G:real^(2,1)finite_sum->real^N,G')`)) THEN
  SUBGOAL_THEN `homeomorphism (P:real^(2,1)finite_sum->bool,a:real^N->bool) (G:real^(2,1)finite_sum->real^N,G')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[homeomorphism]; ALL_TAC] THEN
  (* charts on P *)
  SUBGOAL_THEN
   `!z:real^(2,1)finite_sum.
      z IN P
      ==> (&1 < drop(sndcart z) /\ drop(sndcart z) < &2 ==> moi_s28_locally_r2 P z) /\
          (drop(sndcart z) = &1 \/ drop(sndcart z) = &2 ==> moi_s28_locally_half P z)`
  (LABEL_TAC "chP") THENL
   [SUBGOAL_THEN `moi_s4l_line_charts moi_fps_sq` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S8TA_SPHERE1_LINE_CHARTS THEN REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real^1`] THEN STRIP_TAC THEN
    CONJ_TAC THEN STRIP_TAC THENL
     [MATCH_MP_TAC MOI_S8PL_PROD_R2 THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `t:real^1 = lift(&1)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S8PL_PROD_HALF THEN EXISTS_TAC `-- &1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `t:real^1 = lift(&2)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S8PL_PROD_HALF THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(2,1)finite_sum. z IN P ==> &1 <= drop(sndcart z) /\
                                                     drop(sndcart z) <= &2`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the ends are the images of the end levels *)
  SUBGOAL_THEN `!z:real^(2,1)finite_sum.
                  z IN P ==> ((G:real^(2,1)finite_sum->real^N) z IN j0 UNION j1 <=>
                              drop(sndcart z) = &1 \/ drop(sndcart z) = &2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!s. s SUBSET P
                      ==> ((G:real^(2,1)finite_sum->real^N) z IN IMAGE G s <=> z IN s)`
    (fun th -> SUBGOAL_THEN `moi_fps_sq PCROSS {lift(&1)} SUBSET P /\
                             moi_fps_sq PCROSS {lift(&2)} SUBSET P`
      (fun th' -> ASM_SIMP_TAC[IN_UNION; th; th']))
    THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^(2,1)finite_sum` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(w:real^(2,1)finite_sum) IN P` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `z:real^(2,1)finite_sum = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
        FIRST_X_ASSUM(MP_TAC o AP_TERM `G':real^N->real^(2,1)finite_sum`) THEN
        ASM_SIMP_TAC[];
        DISCH_TAC THEN EXISTS_TAC `z:real^(2,1)finite_sum` THEN ASM_REWRITE_TAC[]];
      SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING; IN_INTERVAL_1;
                  LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(z:real^(2,1)finite_sum) IN P` THEN SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN
      SPEC_TAC(`z:real^(2,1)finite_sum`,`z:real^(2,1)finite_sum`) THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING; SNDCART_PASTECART] THEN
      REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* charts on a *)
  SUBGOAL_THEN
   `!y:real^N. y IN a
               ==> (~(y IN j0 UNION j1) ==> moi_s28_locally_r2 a y) /\
                   (y IN j0 UNION j1 ==> moi_s28_locally_half a y)`
  (LABEL_TAC "cha") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G':real^N->real^(2,1)finite_sum) y IN P /\
                  (G:real^(2,1)finite_sum->real^N) (G' y) = y`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
      (ASSUME `(G':real^N->real^(2,1)finite_sum) y IN P`) o check (fun th ->
      can (term_match []
        `!z:real^(2,1)finite_sum. z IN P ==>
           ((G:real^(2,1)finite_sum->real^N) z IN j0 UNION j1 <=> Q z)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "chP" (MP_TAC o C MATCH_MP
      (ASSUME `(G':real^N->real^(2,1)finite_sum) y IN P`)) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
      (ASSUME `(G':real^N->real^(2,1)finite_sum) y IN P`) o check (fun th ->
      can (term_match []
        `!z:real^(2,1)finite_sum. z IN P ==> &1 <= drop(sndcart z) /\ R z`) (concl th))) THEN
    STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(G:real^(2,1)finite_sum->real^N) (G' (y:real^N)) = y`)) THENL
     [MATCH_MP_TAC MOI_S8PL_R2_TRANSPORT THEN
      MAP_EVERY EXISTS_TAC [`P:real^(2,1)finite_sum->bool`;
                            `G':real^N->real^(2,1)finite_sum`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_S8PL_HALF_TRANSPORT THEN
      MAP_EVERY EXISTS_TAC [`P:real^(2,1)finite_sum->bool`;
                            `G':real^N->real^(2,1)finite_sum`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a triangulation *)
  SUBGOAL_THEN `pl_polyhedron (a:real^N->bool)` MP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
      check (fun th -> concl th = `pl_homeomorphism (moi_fps_ann,a:real^N->bool) (f,g)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^2->real^N) moi_fps_ann = a`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_FPS_ANN_PL_POLYHEDRON];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "cha" (MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^N) IN j0 UNION j1` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  EXISTS_TAC `d:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (G:real^(2,1)finite_sum->real^N) P = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN MATCH_MP_TAC CONNECTED_PCROSS THEN
    REWRITE_TAC[CONNECTED_INTERVAL; moi_fps_sq; MOI_FPS_VEC1_2] THEN
    REWRITE_TAC[VECTOR_ARITH `--vector[&1;&1]:real^2 = --vector[&1;&1]`] THEN
    MP_TAC(SPEC `&1` MOI_S8PL_RF_FACTS) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `surface_boundary (d:(real^N->bool)->bool)`)) THEN
    SUBST1_TAC(ASSUME `UNIONS d = (a:real^N->bool)`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~moi_s28_locally_r2 a (y:real^N)` THEN REWRITE_TAC[] THEN
      USE_THEN "cha" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN a`)) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN a` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN j0 UNION j1` THEN
        UNDISCH_TAC `j0 = IMAGE (G:real^(2,1)finite_sum->real^N) (moi_fps_sq PCROSS {lift(&1)})` THEN
        UNDISCH_TAC `j1 = IMAGE (G:real^(2,1)finite_sum->real^N) (moi_fps_sq PCROSS {lift(&2)})` THEN
        UNDISCH_TAC `IMAGE (G:real^(2,1)finite_sum->real^N) P = a` THEN
        SUBST1_TAC(SYM(ASSUME `moi_fps_sq PCROSS interval[lift(&1),lift(&2)] = P`)) THEN
        MP_TAC(SET_RULE `moi_fps_sq PCROSS {lift(&1)} SUBSET
                           moi_fps_sq PCROSS interval[lift(&1),lift(&2)] /\
                         moi_fps_sq PCROSS {lift(&2)} SUBSET
                           moi_fps_sq PCROSS interval[lift(&1),lift(&2)] ==>
                         !G:real^(2,1)finite_sum->real^N y j0 j1 a.
                           IMAGE G (moi_fps_sq PCROSS interval[lift(&1),lift(&2)]) = a ==>
                           j1 = IMAGE G (moi_fps_sq PCROSS {lift(&2)}) ==>
                           j0 = IMAGE G (moi_fps_sq PCROSS {lift(&1)}) ==>
                           y IN j0 UNION j1 ==> y IN a`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                      IN_INTERVAL_1] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
          MESON_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN
      USE_THEN "cha" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN a`)) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
  MAP_EVERY EXISTS_TAC [`moi_fps_ann`; `f:real^2->real^N`; `g:real^N->real^2`] THEN
  ASM_REWRITE_TAC[MOI_S8PL_ANN_CLOSED] THEN
  REWRITE_TAC[moi_fps_ann; MOI_FEU_EULER_ANNULUS_MODEL]);;

(* ------------------------------------------------------------------------- *)
(* PRODUCT_ANNULUS.  Any two PL 1-spheres are PL homeomorphic (both are PL   *)
(* images of the boundary of the standard triangle of the plane; the proof  *)
(* of MOI_S27_SIMPLEX_FROM_PLANE with the standard triangle kept).  With     *)
(* u: moi_fps_sq -> j and the affine map [1,2] -> [a,b], the product map    *)
(* composed with psi and the bicollar p carries the square annulus onto     *)
(* p(j x [a,b]), the inner square onto the level a and the outer one onto   *)
(* the level b.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S8PL_SIMPLEX_FROM_STD = prove
 (`!k:real^N->bool.
     &2 simplex k
     ==> ?h h'. pl_homeomorphism (convex hull {vec 0:real^2,basis 1,basis 2},k) (h,h') /\
                IMAGE h (relative_frontier (convex hull {vec 0:real^2,basis 1,basis 2})) =
                relative_frontier k`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `~collinear{vec 0:real^N,a - b,c - b}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(a:real^N) - b`; `(c:real^N) - b`] MOI_S27_PLANE_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. (x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)) + b)
          (convex hull {vec 0:real^2,basis 1,basis 2}) = convex hull {a,b,c}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^2. x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)`;
                   `b:real^N`; `{vec 0:real^2,basis 1,basis 2}`]
      MOI_REAL_AFFINE_IMAGE_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID;
                VECTOR_ADD_RID; VECTOR_SUB_ADD] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)`;
                 `b:real^N`; `&2:int`;
                 `convex hull {vec 0:real^2,basis 1,basis 2}`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_S27_STD_SIMPLEX_2]; ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. (x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)) + b`;
    `h':real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S8PL_SPHERE1_STD = prove
 (`!s:real^N->bool.
     pl_sphere 1 s
     ==> ?f g. pl_homeomorphism
                 (relative_frontier (convex hull {vec 0:real^2,basis 1,basis 2}),s) (f,g)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S8PL_SIMPLEX_FROM_STD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^N` (X_CHOOSE_THEN `h':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^2,basis 1,basis 2}`; `k:real^N->bool`;
                 `h:real^2->real^N`; `h':real^N->real^2`] MOI_S27_PLH_SIMPLEX_RF) THEN
  ASM_REWRITE_TAC[MOI_S27_STD_SIMPLEX_2] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(F1:real^N->real^N) o (h:real^2->real^N)`;
                        `(h':real^N->real^2) o (G1:real^N->real^N)`] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S8PL_SPHERE1_PLH = prove
 (`!(s:real^M->bool) (t:real^N->bool).
     pl_sphere 1 s /\ pl_sphere 1 t ==> ?f g. pl_homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^M->bool` MOI_S8PL_SPHERE1_STD) THEN
  MP_TAC(ISPEC `t:real^N->bool` MOI_S8PL_SPHERE1_STD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` (X_CHOOSE_THEN `g2:real^N->real^2`
    ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^M` (X_CHOOSE_THEN `g1:real^M->real^2`
    ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f2:real^2->real^N) o (g1:real^M->real^2)`;
                        `(f1:real^2->real^M) o (g2:real^N->real^2)`] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier (convex hull {vec 0:real^2,basis 1,basis 2})` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

(* Products of PL homeomorphisms of polyhedra.                               *)

let MOI_S8PL_PLH_PCROSS = prove
 (`!(s:real^M->bool) (s':real^P->bool) (t:real^N->bool) (t':real^Q->bool) f f' g g'.
     pl_homeomorphism (s,s') (f,f') /\ pl_homeomorphism (t,t') (g,g') /\
     pl_polyhedron s /\ pl_polyhedron t
     ==> pl_homeomorphism (s PCROSS t,s' PCROSS t')
           ((\z. pastecart (f(fstcart z)) (g(sndcart z))),
            (\z. pastecart (f'(fstcart z)) (g'(sndcart z))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; HOMEOMORPHISM; SUBSET; FORALL_IN_IMAGE])
    (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; HOMEOMORPHISM; SUBSET; FORALL_IN_IMAGE])
      STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `locally_polyhedral ((s:real^M->bool) PCROSS (t:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[HOMEOMORPHISM] THEN
    ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                 SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_FSTCART; LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THENL
     [EXISTS_TAC `s:real^M->bool`; EXISTS_TAC `t:real^N->bool`] THEN
    ASM_SIMP_TAC[MOI_PTR_PL_MAP_ON_LINEAR; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN SIMP_TAC[]]);;

let MOI_S8PL_IMAGE_PCROSS_MAP = prove
 (`!(f:real^M->real^P) (g:real^N->real^Q) s t.
     IMAGE (\z. pastecart (f(fstcart z)) (g(sndcart z))) (s PCROSS t) =
     IMAGE f s PCROSS IMAGE g t`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ] THEN
  MESON_TAC[]);;

(* The affine map of [1,2] onto [a,b].                                       *)

let MOI_S8PL_INTERVAL_PLH = prove
 (`!a b. a < b
         ==> ?lam'. pl_homeomorphism (interval[lift(&1),lift(&2)],interval[lift a,lift b])
                                     ((\t:real^1. (b - a) % t + lift(&2 * a - b)),lam')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[lift(&1),lift(&2)]`; `\t:real^1. (b - a) % t + lift(&2 * a - b)`;
                 `interval[lift a,lift b]`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_ARITH `a < b ==> ~(b - a < &0) /\ &0 <= b - a`;
                   REAL_ARITH `~(&2 < &1)`] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ; LIFT_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `c % x + y:real^1 = c % z + y <=> c % (x - z) = vec 0`;
                  VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `lam':real^1->real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL; LINEAR_SCALING]]);;

(* The theorem PRODUCT_ANNULUS.                                              *)

let PRODUCT_ANNULUS = prove
 (MOI_S28_PRODUCT_ANNULUS,
  MAP_EVERY X_GEN_TAC [`j:real^N->bool`; `w:real^N->bool`;
                       `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                       `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann; moi_s26_level; MOI_S8CU_SLAB_INTERVAL] THEN
  X_CHOOSE_TAC `phi:real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `j:real^N->bool`] MOI_S8PL_SPHERE1_PLH) THEN
  ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->real^N` (X_CHOOSE_THEN `u':real^N->real^2`
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] MOI_S8PL_INTERVAL_PLH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `lam':real^1->real^1`) THEN
  ABBREV_TAC `lam = \t:real^1. (b - a) % t + lift(&2 * a - b)` THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `j:real^N->bool`; `interval[lift(&1),lift(&2)]`;
                 `interval[lift a,lift b]`; `u:real^2->real^N`; `u':real^N->real^2`;
                 `lam:real^1->real^1`; `lam':real^1->real^1`] MOI_S8PL_PLH_PCROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON] THEN
    SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
    DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (u:real^2->real^N) moi_fps_sq = j` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  ABBREV_TAC `Lam = \z:real^(2,1)finite_sum.
                      pastecart ((u:real^2->real^N) (fstcart z)) ((lam:real^1->real^1) (sndcart z))` THEN
  ABBREV_TAC `Lam' = \z:real^(N,1)finite_sum.
                       pastecart ((u':real^N->real^2) (fstcart z)) ((lam':real^1->real^1) (sndcart z))` THEN
  (* the bicollar restricted to the slab *)
  SUBGOAL_THEN `pl_homeomorphism (j PCROSS interval[lift a,lift b],
                   IMAGE (p:real^(N,1)finite_sum->real^N) (j PCROSS interval[lift a,lift b]))
                 (p,q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(j:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]`;
                          `w:real^N->bool`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[moi_s26_bicollar];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG;
                  DROP_VEC; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
      SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL] THEN
      ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(p:real^(N,1)finite_sum->real^N) o
     (Lam:real^(2,1)finite_sum->real^(N,1)finite_sum) o moi_fps_psi`;
    `((phi:real^(2,1)finite_sum->real^2) o
      (Lam':real^(N,1)finite_sum->real^(2,1)finite_sum)) o
     (q:real^N->real^(N,1)finite_sum)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(j:real^N->bool) PCROSS interval[lift a,lift b]` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the ends *)
  SUBGOAL_THEN
   `IMAGE moi_fps_psi (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) =
    moi_fps_sq PCROSS {lift(&1)} /\
    IMAGE moi_fps_psi (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) =
    moi_fps_sq PCROSS {lift(&2)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S8PL_RF12] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S8PL_PSI_LEVEL THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. IMAGE (Lam:real^(2,1)finite_sum->real^(N,1)finite_sum) (moi_fps_sq PCROSS {lift r}) =
        j PCROSS {(b - a) % lift r + lift(&2 * a - b)}`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Lam" THEN REWRITE_TAC[MOI_S8PL_IMAGE_PCROSS_MAP] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN EXPAND_TAC "lam" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) % lift(&1) + lift(&2 * a - b) = lift a /\
                (b - a) % lift(&2) + lift(&2 * a - b) = lift b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]);;

