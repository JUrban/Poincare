(* ========================================================================= *)
(* pc_moi_s28_torus: the frontier of a PL solid torus in real^3 is a closed  *)
(* connected orientable combinatorial surface with chi 0 (Moise GTM 47, 28.1 *)
(* for the frontier, p.200).  Main theorem                                   *)
(* TORUS_SETUP : |- MOI_S28_TORUS_SETUP (pc_moi_s2628_stmt.ml; the           *)
(* antecedents PL_SOLID_TORUS_BASIC at real^3, SIDES_ORIENT_R3 and           *)
(* SURF_LOCAL at real^3 are kept).  Route: the frontier is the PL image of   *)
(* pl_torus_model (BASIC), hence a polyhedron (PL_POLYHEDRON_PL_IMAGE) with  *)
(* a triangulation t, whose simplices have dimension at most 2 since the     *)
(* frontier of a closed set has no interior; every point of the model, so of *)
(* the frontier, has a neighbourhood homeomorphic to the plane (a punctured  *)
(* square boundary is a line), so t is combinatorial by SURF_LOCAL; the      *)
(* sides interior s and the complement of s give orientability by            *)
(* SIDES_ORIENT_R3 (invariance of domain on the model of pl_solid_torus);    *)
(* chi 0 by COMPLEX_EULER_VALUES.                                            *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_s28_trib.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The models.  The square annulus of pl_solid_torus is the                 *)
(* closure of its interior (segments towards the middle square), hence so   *)
(* is the model M = moi_fps_m; a punctured square boundary is a line, so    *)
(* every point of pl_torus_model has a neighbourhood homeomorphic to the    *)
(* plane; pl_torus_model is a connected compact polyhedron.                 *)
(* ========================================================================= *)

let MOI_S8TO_ANN_INTERIOR = prove
 (`!x:real^2. x IN interior moi_fps_ann <=> &1 < infnorm x /\ infnorm x < &2`,
  REWRITE_TAC[MOI_FPS_ANN_INTERIOR; INFNORM_2]);;

let MOI_S8TO_ANN_CLOSURE = prove
 (`moi_fps_ann SUBSET closure(interior moi_fps_ann)`,
  REWRITE_TAC[SUBSET; MOI_FPS_ANN; GSYM INFNORM_2] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  ABBREV_TAC `r = infnorm(x:real^2)` THEN
  ABBREV_TAC `p:real^2 = (&3 / (&2 * r)) % x` THEN
  SUBGOAL_THEN
   `!u. &0 <= u /\ u <= &1
        ==> infnorm((&1 - u) % x + u % (p:real^2)) = (&1 - u) * r + u * &3 / &2`
  (LABEL_TAC "fm") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB; INFNORM_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (&1 - u) + u * &3 / (&2 * r)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[real_abs] THEN
    SUBGOAL_THEN `~(r = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN interior moi_fps_ann` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S8TO_ANN_INTERIOR] THEN
    USE_THEN "fm" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_POS; REAL_SUB_REFL; VECTOR_MUL_LZERO;
                VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment(x:real^2,p) SUBSET interior moi_fps_ann` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SEGMENT; MOI_S8TO_ANN_INTERIOR] THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
    USE_THEN "fm" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(&1 - u) * &1 <= (&1 - u) * r /\ (&1 - u) * r <= (&1 - u) * &2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^2 = p` THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment(x:real^2,p)`; `interior moi_fps_ann`] SUBSET_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]);;

let MOI_S8TO_M_CLOSURE = prove
 (`moi_fps_m SUBSET closure(interior moi_fps_m)`,
  REWRITE_TAC[moi_fps_m; INTERIOR_PCROSS; CLOSURE_PCROSS] THEN
  MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[MOI_S8TO_ANN_CLOSURE] THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
  SUBGOAL_THEN `~(interval(--vec 1:real^1,vec 1) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY_1; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[CLOSURE_OPEN_INTERVAL; SUBSET_REFL]]);;

let MOI_S8TO_SQ_FACTS = prove
 (`convex(interval[--vec 1:real^2,vec 1]) /\ bounded(interval[--vec 1:real^2,vec 1]) /\
   aff_dim(interval[--vec 1:real^2,vec 1]) = &2`,
  REWRITE_TAC[CONVEX_INTERVAL; BOUNDED_INTERVAL] THEN
  MP_TAC(ISPEC `interval[--vec 1:real^2,vec 1]` AFF_DIM_NONEMPTY_INTERIOR) THEN
  REWRITE_TAC[DIMINDEX_2; INTERIOR_CLOSED_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S8TO_SQ_NEG = prove
 (`!a:real^2. a IN moi_fps_sq ==> --a IN moi_fps_sq /\ ~(a = --a)`,
  GEN_TAC THEN
  REWRITE_TAC[MOI_FPS_SQ; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S8TO_SQ_PUNCT = prove
 (`!a:real^2. a IN moi_fps_sq ==> (moi_fps_sq DELETE a) homeomorphic (:real^1)`,
  GEN_TAC THEN REWRITE_TAC[moi_fps_sq] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN THEN
  ASM_REWRITE_TAC[MOI_S8TO_SQ_FACTS; AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1] THEN
  INT_ARITH_TAC);;

let MOI_S8TO_R2_PCROSS = prove
 (`(:real^1) PCROSS (:real^1) homeomorphic (:real^2)`,
  REWRITE_TAC[UNIV_PCROSS_UNIV] THEN MATCH_MP_TAC HOMEOMORPHIC_SUBSPACES THEN
  REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2] THEN
  ARITH_TAC);;

let MOI_S8TO_MODEL_R2 = prove
 (`!x. x IN pl_torus_model ==> moi_s28_locally_r2 pl_torus_model x`,
  REWRITE_TAC[pl_torus_model; GSYM moi_fps_sq; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  EXISTS_TAC `(moi_fps_sq DELETE --(a:real^2)) PCROSS (moi_fps_sq DELETE --(b:real^2))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_PCROSS THEN CONJ_TAC THEN
    MATCH_MP_TAC OPEN_IN_DELETE THEN REWRITE_TAC[OPEN_IN_REFL];
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_DELETE] THEN
    ASM_MESON_TAC[MOI_S8TO_SQ_NEG];
    MATCH_MP_TAC(INST_TYPE [`:(1,1)finite_sum`,`:N`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `(:real^1) PCROSS (:real^1)` THEN REWRITE_TAC[MOI_S8TO_R2_PCROSS] THEN
    MATCH_MP_TAC HOMEOMORPHIC_PCROSS THEN
    ASM_MESON_TAC[MOI_S8TO_SQ_NEG; MOI_S8TO_SQ_PUNCT]]);;

let MOI_S8TO_MODEL_FACTS = prove
 (`connected pl_torus_model /\ pl_polyhedron pl_torus_model /\ compact pl_torus_model`,
  REWRITE_TAC[pl_torus_model; GSYM moi_fps_sq] THEN
  SUBGOAL_THEN `connected moi_fps_sq` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fps_sq] THEN MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    REWRITE_TAC[MOI_S8TO_SQ_FACTS] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_PCROSS; COMPACT_PCROSS; MOI_FPS_SQ_COMPACT] THEN
  MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON]);;

(* ========================================================================= *)
(* The two sides of the frontier of a PL solid torus s in                   *)
(* real^3.  s is compact; by invariance of domain the image of the interior *)
(* of the model M lies in the interior of s, and M is the closure of its    *)
(* interior, so s is the closure of its interior.  Hence interior s and the *)
(* complement of s are disjoint open sets covering the complement of the    *)
(* frontier, each with frontier equal to frontier s.                        *)
(* ========================================================================= *)

let MOI_S8TO_SIDES = prove
 (`!s:real^3->bool.
     pl_solid_torus s
     ==> compact s /\
         ?i e. open i /\ open e /\ DISJOINT i e /\
               i UNION e = (:real^3) DIFF frontier s /\
               frontier i = frontier s /\ frontier e = frontier s`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact(s:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `s = IMAGE (f:real^(2,1)finite_sum->real^3) moi_fps_m` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_FPS_M_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^(2,1)finite_sum->real^3) (interior moi_fps_m) SUBSET interior s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^(2,1)finite_sum->real^3`; `moi_fps_m`]
                  CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interior moi_fps_m) SUBSET moi_fps_m` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    SIMP_TAC[INTERIOR_SUBSET; COMPACT_IMP_CLOSED; MOI_FPS_M_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET closure(interior s)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^(2,1)finite_sum->real^3) (closure(interior moi_fps_m))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^(2,1)finite_sum->real^3) moi_fps_m = s` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[MOI_S8TO_M_CLOSURE];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior(s:real^3->bool)` THEN
        ASM_REWRITE_TAC[CLOSURE_SUBSET]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interior s) = (s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[INTERIOR_SUBSET; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`interior s:real^3->bool`; `(:real^3) DIFF s`] THEN
  REWRITE_TAC[OPEN_INTERIOR; FRONTIER_COMPLEMENT; GSYM closed] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[frontier; INTERIOR_INTERIOR] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ========================================================================= *)
(* A set PL homeomorphic to pl_torus_model is locally the                   *)
(* plane at each point (transport by MOI_S8TB_TRANSPORT), and in real^3     *)
(* such a set with empty interior has a triangulation by simplices of       *)
(* dimension at most 2 (it is a polyhedron by PL_POLYHEDRON_PL_IMAGE; a     *)
(* 3-simplex of real^3 has interior points).                                *)
(* ========================================================================= *)

let MOI_S8TO_PL_TORUS_R2 = prove
 (`!(x:real^N->bool) (f:real^(2,2)finite_sum->real^N) g.
     homeomorphism (pl_torus_model,x) (f,g)
     ==> !y. y IN x ==> moi_s28_locally_r2 x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`pl_torus_model`; `x:real^N->bool`; `f:real^(2,2)finite_sum->real^N`;
                 `g:real^N->real^(2,2)finite_sum`; `(g:real^N->real^(2,2)finite_sum) y`]
                MOI_S8TB_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [MATCH_MP_TAC MOI_S8TO_MODEL_R2 THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^(2,2)finite_sum->real^N)(g y) = y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let MOI_S8TO_TRIANG = prove
 (`!(x:real^3->bool) (f:real^(2,2)finite_sum->real^3) g.
     interior x = {} /\ pl_homeomorphism (pl_torus_model,x) (f,g)
     ==> ?t. simplicial_complex t /\ UNIONS t = x /\
             !k. k IN t ==> aff_dim k <= &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (x:real^3->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^(2,2)finite_sum->real^3) pl_torus_model = x` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S8TO_MODEL_FACTS];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex(k:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(aff_dim(k:real^3->bool) = &3)` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM DIMINDEX_3; AFF_DIM_NONEMPTY_INTERIOR_EQ] THEN
    MATCH_MP_TAC(SET_RULE `!a b:real^3->bool. a SUBSET b /\ b = {} ==> a = {}`) THEN
    EXISTS_TAC `interior(x:real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^3->bool` AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[DIMINDEX_3] THEN INT_ARITH_TAC);;

(* ========================================================================= *)
(* The main theorem TORUS_SETUP.  The triangulation t of frontier s above is *)
(* combinatorial by SURF_LOCAL (every point is locally the plane, so the     *)
(* boundary is empty), orientable by SIDES_ORIENT_R3 with the two sides      *)
(* above, connected as a continuous image of the model, and has chi 0 by     *)
(* COMPLEX_EULER_VALUES.                                                     *)
(* ========================================================================= *)

let TORUS_SETUP = prove
 (MOI_S28_TORUS_SETUP,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bas")
    (CONJUNCTS_THEN2 (LABEL_TAC "ori") (LABEL_TAC "loc"))) THEN
  X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  USE_THEN "bas" (MP_TAC o C MP (ASSUME `pl_solid_torus (s:real^3->bool)`) o
                  SPEC `s:real^3->bool` o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) THEN
  MP_TAC(MATCH_MP MOI_S8TO_SIDES (ASSUME `pl_solid_torus (s:real^3->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sides")) THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `f:real^(2,2)finite_sum->real^3`;
                 `g:real^3->real^(2,2)finite_sum`] MOI_S8TO_TRIANG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_FRONTIER_EMPTY; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN frontier s ==> moi_s28_locally_r2 (frontier s) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TO_PL_TORUS_R2 THEN
    MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`;
                          `g:real^3->real^(2,2)finite_sum`] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "loc" (MP_TAC o SPEC `t:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!y:real^3. y IN frontier s ==> moi_s28_locally_r2 (frontier s) y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^(2,2)finite_sum->real^3) pl_torus_model = frontier s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S8TO_MODEL_FACTS];
    USE_THEN "ori" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `t:(real^3->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o el 5 o CONJUNCTS) THEN
    MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`;
                          `g:real^3->real^(2,2)finite_sum`] THEN
    ASM_REWRITE_TAC[]]);;

