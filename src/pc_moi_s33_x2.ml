needs "src/pc_moi_s33_frame.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_chain.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_s30_tame.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s33_x2: Lemma 2 of 33.1 (Moise GTM 47, p.231): a polyhedral tube  *)
(* neighbourhood in general position.  Main theorem                         *)
(*   X2 : |- MOI_S33_X2   (pc_moi_s33_stmt.ml)                              *)
(* Route: a compact combinatorial 3-manifold-with-boundary neighbourhood X0 *)
(* of K' = h|l| in U = int h(N) (the derived neighbourhood of the           *)
(* simplices meeting K' in an lf triangulation of U, MOI_S3X2_X0); the      *)
(* pseudo-cell surfaces E INTER (U - K') = (E - rim) - centre,              *)
(* locally polyhedral 2-manifolds, are triangulated near Bd X0 by a         *)
(* combinatorial 2-manifold (MOI_S3X2_SURF_TRIANG);                         *)
(* GENERAL_POSITION_SURFACES_3 moves Bd X0 to cross them                    *)
(* (MOI_S3X2_GP_STEP); X = the image of X0, CMWB 3 by                       *)
(* COMBINATORIAL_WB_PL_INVARIANT.                                           *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Helpers: intersections of locally polyhedral sets; compact polyhedral    *)
(* neighbourhoods (finitely many cubes); the symmetry of pl_crossing_at;    *)
(* lf triangulations of open subsets of real^3 are combinatorial.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3X2_LP_INTER = prove
 (`!s t:real^N->bool.
     locally_polyhedral s /\ locally_polyhedral t ==> locally_polyhedral (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s") (LABEL_TAC "t")) THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  REMOVE_THEN "s" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^N->bool)->bool`
    (X_CHOOSE_THEN `u1:real^N->bool` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "t" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(real^N->bool)->bool`
    (X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `FINITE {k1 INTER k2 | (k1:real^N->bool) IN c1 /\ (k2:real^N->bool) IN c2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `{k1 INTER k2 | (k1:real^N->bool) IN c1 /\ (k2:real^N->bool) IN c2}` THEN
  EXISTS_TAC `u1 INTER u2:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?k1:real^N->bool. k1 IN c1 /\ y IN k1` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?k2:real^N->bool. k2 IN c2 /\ y IN k2` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`k1:real^N->bool`; `k2:real^N->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER THEN ASM_MESON_TAC[];
      ASM SET_TAC[]]]);;

let MOI_S3X2_POLY_NBHD = prove
 (`!k u:real^N->bool.
     compact k /\ open u /\ k SUBSET u
     ==> ?q. pl_polyhedron q /\ k SUBSET interior q /\ q SUBSET u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `{interval(a,b) | a,b | interval[a:real^N,b] SUBSET u}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[FORALL_IN_GSPEC; OPEN_INTERVAL]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^N` (GEN_REWRITE_RULE I [OPEN_CONTAINS_INTERVAL]
      (ASSUME `open(u:real^N->bool)`))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN f
      ==> open t /\ polytope (closure t) /\ t SUBSET closure t /\ closure t SUBSET u`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?a b:real^N. t = interval(a,b) /\ interval[a,b] SUBSET u`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET
                   {interval(a,b) | a,b | interval[a:real^N,b] SUBSET u}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL; CLOSURE_SUBSET] THEN
    REWRITE_TAC[CLOSURE_INTERVAL] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[POLYTOPE_EMPTY; POLYTOPE_INTERVAL; EMPTY_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (IMAGE closure f):real^N->bool` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `IMAGE closure (f:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS f:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_UNIONS; SUBSET; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
      DISCH_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET];
      MATCH_MP_TAC OPEN_UNIONS THEN ASM_MESON_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let MOI_S3X2_CROSSING_SYM = prove
 (`!s t (x:real^3). pl_crossing_at s t x ==> pl_crossing_at t s x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `sw = \y:real^3. vector[y$2; y$1; y$3]:real^3` THEN
  SUBGOAL_THEN `linear (sw:real^3->real^3) /\ (!y. sw(sw y) = y) /\
                (!y. (sw y)$1 = y$2) /\ (!y. (sw y)$2 = y$1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x y:real^3. sw x = sw y ==> x = y) /\ (!y:real^3. ?x. sw x = y)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `(sw:real^3->real^3) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (sw:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  SUBGOAL_THEN `open (IMAGE (sw:real^3->real^3) (IMAGE (f:real^3->real^3) u))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sw:real^3->real^3`; `IMAGE (f:real^3->real^3) u`]
      OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) u`; `sw:real^3->real^3`; `vec 0:real^3`]
        PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[VECTOR_ADD_RID; ETA_AX; LOCALLY_POLYHEDRAL_OPEN]];
    ASM_MESON_TAC[LINEAR_0];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_S3X2_CM_IMP_CMWB = prove
 (`!n c:(real^N->bool)->bool.
     combinatorial_manifold n c ==> combinatorial_manifold_with_boundary n c`,
  REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
  MESON_TAC[]);;

let MOI_S3X2_OPEN_CM3 = prove
 (`!c:(real^3->bool)->bool.
     lf_simplicial_complex c /\ open (UNIONS c) ==> combinatorial_manifold 3 c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(v:real^3) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `UNIONS c:real^3->bool`;
                 `\x:real^3. x`] MOI_CMB_LOCAL_LINK_SPHERE) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; LE_REFL];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_REFL];
    ASM_REWRITE_TAC[];
    EXISTS_TAC `&1` THEN SIMP_TAC[REAL_LT_01];
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN ASM_REWRITE_TAC[];
    SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e r` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN EXISTS_TAC `q:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(v:real^3,r) SUBSET UNIONS c` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* A compact subset K of an open set U of real^3 has a compact              *)
(* combinatorial 3-manifold-with-boundary neighbourhood inside U: the       *)
(* derived neighbourhood of the faces of the simplices meeting K in an lf   *)
(* triangulation of U INTER ball (which is a combinatorial 3-manifold).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3X2_X0 = prove
 (`!(K:real^3->bool) U.
     compact K /\ open U /\ K SUBSET U
     ==> ?x0. FINITE x0 /\ combinatorial_manifold_with_boundary 3 x0 /\
              K SUBSET interior (UNIONS x0) /\ UNIONS x0 SUBSET U`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (U INTER ball(vec 0:real^3,B + &1)) /\
                (K:real^3->bool) SUBSET U INTER ball(vec 0,B + &1) /\
                U INTER ball(vec 0:real^3,B + &1) SUBSET U` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET; SUBSET_INTER] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    ASM_MESON_TAC[REAL_ARITH `x <= b ==> x < b + &1`];
    ALL_TAC] THEN
  ABBREV_TAC `V = U INTER ball(vec 0:real^3,B + &1)` THEN
  ABBREV_TAC `Q = interval[--((B + &1) % vec 1):real^3,(B + &1) % vec 1]` THEN
  SUBGOAL_THEN `(V:real^3->bool) SUBSET Q` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "Q"] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL_0; IN_INTERVAL; VECTOR_NEG_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `i:num`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (Q:real^3->bool)` MP_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{Q:real^3->bool}` THEN
    EXPAND_TAC "Q" THEN
    REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; POLYTOPE_INTERVAL; UNIONS_1];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^3->bool)->bool`; `V:real^3->bool`]
    LF_TRIANGULATION_OPEN_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (tr:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3X2_CM_IMP_CMWB THEN MATCH_MP_TAC MOI_S3X2_OPEN_CM3 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = UNIONS (IMAGE (\s:real^3->bool. {f | f face_of s})
                               {s | s IN tr /\ ~(s INTER K = {})})` THEN
  SUBGOAL_THEN `!f:real^3->bool. f IN L <=> ?s. s IN tr /\ ~(s INTER K = {}) /\ f face_of s`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `s:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
      MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN EXISTS_TAC `tr:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (L:(real^3->bool)->bool) tr` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `f:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(CONJUNCT1(CONJUNCT2(GEN_REWRITE_RULE I [lf_simplicial_complex]
        (ASSUME `lf_simplicial_complex (tr:(real^3->bool)->bool)`)))) THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      MESON_TAC[FACE_OF_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?s:real^3->bool. s IN tr /\ x IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
      MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN EXISTS_TAC `tr:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tr:(real^3->bool)->bool`; `L:(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tr:(real^3->bool)->bool`; `L:(real^3->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `derived_nbhd_complex tr (L:(real^3->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS L:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS tr)) interior_of
                derived_nbhd tr (L:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INTERIOR_OF_SUBTOPOLOGY_OPEN; GSYM OPEN_IN; EUCLIDEAN_INTERIOR_OF] THEN
    SET_TAC[];
    ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Triangulating the surface pieces: finitely many pairwise disjoint closed *)
(* sets E, each locally polyhedral inside a compact polyhedron q and a      *)
(* 2-manifold inside int q, give a combinatorial 2-manifold triangulating   *)
(* (UNIONS E) INTER int q (LF_TRIANGULATION_OPEN_SUBSET of the polyhedron   *)
(* (UNIONS E) INTER q, then SURFACE_TRIANG with SURF_LOCAL).                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3X2_SURF_LF = MP SURFACE_TRIANG SURF_LOCAL;;

let MOI_S3X2_SURF_TRIANG = prove
 (`!(ff:(real^3->bool)->bool) (q:real^3->bool).
     FINITE ff /\ pl_polyhedron q /\
     (!E. E IN ff
          ==> closed E /\ locally_polyhedral (E INTER q) /\
              !y. y IN E INTER interior q
                  ==> moi_s28_locally_r2 (E INTER interior q) y) /\
     (!E E'. E IN ff /\ E' IN ff /\ ~(E = E') ==> DISJOINT E E')
     ==> ?t. combinatorial_manifold 2 t /\ UNIONS t = UNIONS ff INTER interior q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS ff INTER q:real^3->bool)` MP_TAC THENL
   [SUBGOAL_THEN `UNIONS ff INTER q:real^3->bool =
                  UNIONS (IMAGE (\E. E INTER q) ff)` SUBST1_TAC THENL
     [REWRITE_TAC[INTER_UNIONS] THEN AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `E:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `UNIONS ff INTER interior q:real^3->bool`]
    LF_TRIANGULATION_OPEN_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `UNIONS ff INTER interior q:real^3->bool =
                  (UNIONS ff INTER q) INTER interior q` SUBST1_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN UNIONS t ==> moi_s28_locally_r2 (UNIONS t) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `E:real^3->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN
    EXISTS_TAC `E INTER interior q:real^3->bool` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(E:real^3->bool) IN ff`)) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `E INTER interior q:real^3->bool =
      (UNIONS ff INTER interior q) INTER ((:real^3) DIFF UNIONS (ff DELETE E))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `!E E':real^3->bool. E IN ff /\ E' IN ff /\ ~(E = E') ==> DISJOINT E E'` THEN
      UNDISCH_TAC `(E:real^3->bool) IN ff` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_DIFF; IN_UNIV; IN_DELETE; DISJOINT] THEN
      MESON_TAC[IN_INTER; NOT_IN_EMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^3->bool)->bool` MOI_S3X2_SURF_LF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The general position step: a compact CMWB 3 neighbourhood x0 of K inside *)
(* U is moved (GENERAL_POSITION_SURFACES_3, support in a polyhedral         *)
(* neighbourhood of Bd x0 inside U - K) so that its frontier crosses the    *)
(* surfaces E INTER (U - K) at every common point.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3X2_PLH_UNIV_FACTS = prove
 (`!(f:real^3->real^3) g kk.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
     (!x. ~(x IN kk) ==> f x = x)
     ==> (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
         (!s. IMAGE f s SUBSET s UNION kk) /\
         (!s. kk SUBSET s ==> IMAGE f s SUBSET s) /\
         (!s. open s ==> open (IMAGE f s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(!x:real^3. g((f:real^3->real^3) x) = x) /\
                (!y:real^3. f((g:real^3->real^3) y) = y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN kk ==> (f:real^3->real^3) x IN kk` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3)(f x) = f x` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `g:real^3->real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                   `s:real^3->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]]);;

let MOI_S3X2_GP_STEP = prove
 (`!(K:real^3->bool) U (ff:(real^3->bool)->bool) x0.
     compact K /\ open U /\ K SUBSET U /\
     FINITE x0 /\ combinatorial_manifold_with_boundary 3 x0 /\
     K SUBSET interior (UNIONS x0) /\ UNIONS x0 SUBSET U /\
     FINITE ff /\
     (!E. E IN ff
          ==> closed E /\ locally_polyhedral (E INTER (U DIFF K)) /\
              !y. y IN E INTER (U DIFF K)
                  ==> moi_s28_locally_r2 (E INTER (U DIFF K)) y) /\
     (!E E'. E IN ff /\ E' IN ff /\ ~(E = E') ==> DISJOINT E E')
     ==> ?x. FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
             K SUBSET interior (UNIONS x) /\ UNIONS x SUBSET U /\
             frontier (UNIONS x) SUBSET U DIFF K /\
             !E y. E IN ff /\ y IN E INTER frontier (UNIONS x)
                   ==> pl_crossing_at (E INTER (U DIFF K)) (frontier (UNIONS x)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
  (* basic facts on x0 *)
  SUBGOAL_THEN `compact (UNIONS x0:real^3->bool) /\ pl_polyhedron (UNIONS x0:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
      REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `x0:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `x0:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPEC `x0:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `B0 = frontier (UNIONS x0:real^3->bool)` THEN
  SUBGOAL_THEN `compact (B0:real^3->bool) /\ B0 SUBSET U DIFF K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN ASM_SIMP_TAC[COMPACT_FRONTIER] THEN
    MP_TAC(ISPEC `UNIONS x0:real^3->bool` FRONTIER_SUBSET_COMPACT) THEN
    MP_TAC(ISPEC `UNIONS x0:real^3->bool` frontier) THEN
    MAP_EVERY UNDISCH_TAC
     [`K SUBSET interior (UNIONS x0:real^3->bool)`; `UNIONS x0 SUBSET (U:real^3->bool)`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (U DIFF K:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B0:real^3->bool`; `U DIFF K:real^3->bool`] MOI_S3X2_POLY_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the surfaces inside int q *)
  MP_TAC(ISPECL [`ff:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S3X2_SURF_TRIANG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `E:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(E:real^3->bool) IN ff`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `E INTER q:real^3->bool = (E INTER (U DIFF K)) INTER q` SUBST1_TAC THENL
       [UNDISCH_TAC `(q:real^3->bool) SUBSET U DIFF K` THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S3X2_LP_INTER THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`E INTER (U DIFF K):real^3->bool`;
                            `E INTER interior q:real^3->bool`] THEN
      MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY UNDISCH_TAC [`(y:real^3) IN E INTER interior q`;
          `(q:real^3->bool) SUBSET U DIFF K`; `interior q SUBSET (q:real^3->bool)`] THEN
        SET_TAC[];
        SUBGOAL_THEN `E INTER interior q:real^3->bool =
                      (E INTER (U DIFF K)) INTER interior q` SUBST1_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`(q:real^3->bool) SUBSET U DIFF K`;
                                 `interior q SUBSET (q:real^3->bool)`] THEN SET_TAC[];
          MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR]];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET_REFL];
        MAP_EVERY UNDISCH_TAC [`(q:real^3->bool) SUBSET U DIFF K`;
                               `interior q SUBSET (q:real^3->bool)`] THEN SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* general position *)
  MP_TAC(ISPECL [`boundary_complex x0:(real^3->bool)->bool`; `tt:(real^3->bool)->bool`;
                 `interior q:real^3->bool`; `&1`] GENERAL_POSITION_SURFACES_3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERIOR; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `x0:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[boundary_complex] THEN SET_TAC[];
      SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `kk:real^3->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `kk:real^3->bool`]
    MOI_S3X2_PLH_UNIV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the moved neighbourhood and a triangulation of it *)
  SUBGOAL_THEN `pl_map_on (UNIONS x0) (f:real^3->real^3) /\
                pl_polyhedron (IMAGE (f:real^3->real^3) (UNIONS x0))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
      ASM_MESON_TAC[pl_homeomorphism];
      DISCH_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] o
    check (fun th -> concl th =
      `pl_polyhedron (IMAGE (f:real^3->real^3) (UNIONS x0))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (x:(real^3->bool)->bool) /\ lf_simplicial_complex x`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x0:(real^3->bool)->bool`; `x:(real^3->bool)->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`] COMBINATORIAL_WB_PL_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    ASM_MESON_TAC[pl_homeomorphism; SUBSET_UNIV];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `frontier (IMAGE (f:real^3->real^3) (UNIONS x0)) = IMAGE f B0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `complex_boundary (x:(real^3->bool)->bool)` &&
      rand (concl th) = `frontier (IMAGE (f:real^3->real^3) (UNIONS x0))`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `complex_boundary (x:(real^3->bool)->bool)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(kk:real^3->bool) SUBSET U DIFF K` ASSUME_TAC THENL
   [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`(q:real^3->bool) SUBSET U DIFF K`;
                           `(kk:real^3->bool) SUBSET interior q`] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* K inside the interior *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) (interior (UNIONS x0))` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN
      SUBGOAL_THEN `~((z:real^3) IN kk)` (fun th -> ASM_SIMP_TAC[th]) THENL
       [UNDISCH_TAC `(kk:real^3->bool) SUBSET U DIFF K` THEN
        UNDISCH_TAC `(z:real^3) IN K` THEN SET_TAC[];
        ASM SET_TAC[]];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTERIOR_SUBSET]];
    (* inside U *)
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:real^3->real^3) U` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    (* the frontier inside U - K *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) (U DIFF K)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  (* the crossings *)
  MAP_EVERY X_GEN_TAC [`E:real^3->bool`; `y:real^3`] THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) B0 SUBSET interior q` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) (interior q)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN interior q` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_crossing_at (IMAGE (f:real^3->real^3) B0) (UNIONS ff INTER interior q) y`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (term_match [`f:real^3->real^3`] `!x:real^3. x IN IMAGE (f:real^3->real^3) s INTER u ==> P x`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER; IN_UNIONS] THEN EXISTS_TAC `E:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3X2_CROSSING_SYM) THEN
  DISCH_TAC THEN MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS ff INTER interior q:real^3->bool`; `IMAGE (f:real^3->real^3) B0`;
    `interior q INTER ((:real^3) DIFF UNIONS (ff DELETE (E:real^3->bool)))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; IN_DELETE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `E':real^3->bool` THEN
    REWRITE_TAC[TAUT `~((a /\ b) /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
    UNDISCH_TAC `!E E':real^3->bool. E IN ff /\ E' IN ff /\ ~(E = E') ==> DISJOINT E E'` THEN
    DISCH_THEN(MP_TAC o SPECL [`E:real^3->bool`; `E':real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN E` THEN SET_TAC[];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN U /\ ~(z IN K)` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(q:real^3->bool) SUBSET U DIFF K` THEN
      UNDISCH_TAC `(z:real^3) IN interior q` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((z:real^3) IN UNIONS (ff DELETE E))` THEN
    UNDISCH_TAC `(E:real^3->bool) IN ff` THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN MESON_TAC[];
    REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The pseudo-cells of the handle decomposition: each edge is a segment     *)
(* [u,v], u ~= v; E = e[u,v] is closed, lies in h(N), and E INTER W is the  *)
(* locally polyhedral 2-manifold (E - rim) - centre.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3X2_TUBE_EDGE = prove
 (`!(t:(real^3->bool)->bool) l h s.
     moi_s33_tube t l h /\ s IN l /\ aff_dim s = &1
     ==> ?u v. ~(u = v) /\ s = segment[u,v]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(GEN_REWRITE_RULE I [lf_simplicial_complex]
      (ASSUME `lf_simplicial_complex (t:(real^3->bool)->bool)`))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a b:real^3. s = segment[a,b]` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3FR_SIMPLEX_SEGMENT THEN EXISTS_TAC `n:int` THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(s:real^3->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^3->bool) = &1` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; AFF_DIM_SING] THEN INT_ARITH_TAC);;

let MOI_S3X2_HD_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> closed (e(segment[u,v])) /\
         e(segment[u,v]) INTER
           (interior (IMAGE h (derived_nbhd t l)) DIFF IMAGE h (UNIONS l)) =
         (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v)) /\
         locally_polyhedral
           ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v))) /\
         (!y. y IN (e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE h(midpoint(u,v))
              ==> moi_s28_locally_r2
                    ((e(segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE
                     h(midpoint(u,v))) y) /\
         h(midpoint(u,v)) IN IMAGE h (UNIONS l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S3FR_IMAGE_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `~(u:real^3 = v)`)
    (ASSUME `segment[u:real^3,v] IN l`))) THEN
  ABBREV_TAC `E = (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
  ABBREV_TAC `j = moi_s33_rim t l (h:real^3->real^3) u v` THEN
  ABBREV_TAC `p = (h:real^3->real^3) (midpoint(u,v))` THEN
  REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  (* the end points are vertices of l *)
  SUBGOAL_THEN `{u:real^3} IN l /\ {v:real^3} IN l` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `segment[u:real^3,v]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->bool) SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
      can (term_match [] `!v w:real^3. {v} IN l /\ {w} IN l /\ ~(v = w) ==> P v w`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET s ==> a INTER b SUBSET s`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `IMAGE (h:real^3->real^3) (derived_nbhd t l)`)) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (E:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `closure (E DIFF j:real^3->bool)`)) THEN
    REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
                IMAGE h (derived_nbhd t l) DIFF interior (IMAGE h (derived_nbhd t l))`
  ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    (* the trace of W *)
    MAP_EVERY UNDISCH_TAC
     [`E INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) = j`;
      `E INTER IMAGE (h:real^3->real^3) (UNIONS l) = {p}`;
      `(E:real^3->bool) SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)`;
      `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
       IMAGE h (derived_nbhd t l) DIFF interior (IMAGE h (derived_nbhd t l))`] THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    (* plane charts *)
    SUBGOAL_THEN `!y:real^3. y IN E DIFF j ==> moi_s28_locally_r2 (E DIFF j) y`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `phi:real^3->real^2` (X_CHOOSE_THEN `psi:real^2->real^3`
        ASSUME_TAC) o GEN_REWRITE_RULE I [homeomorphic] o check (fun th ->
          concl th = `(E DIFF j:real^3->bool) homeomorphic ball(vec 0:real^2,&1)`)) THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `E DIFF j:real^3->bool`;
                     `psi:real^2->real^3`; `phi:real^3->real^2`;
                     `(phi:real^3->real^2) y`] MOI_S8PL_R2_TRANSPORT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
        REWRITE_TAC[moi_s28_locally_r2] THEN
        EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
        REWRITE_TAC[OPEN_IN_REFL] THEN
        SIMP_TAC[HOMEOMORPHIC_BALL_UNIV; REAL_LT_01] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`E DIFF j:real^3->bool`; `(E DIFF j) DELETE (p:real^3)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_DELETE THEN REWRITE_TAC[OPEN_IN_REFL];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET_REFL];
      SET_TAC[]];
    (* the centre is on K' *)
    UNDISCH_TAC `E INTER IMAGE (h:real^3->real^3) (UNIONS l) = {p}` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The theorem X2.                                                           *)
(* ------------------------------------------------------------------------- *)

let X2 = prove
 (MOI_S33_X2,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s33_x2] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool) /\
                compact (IMAGE (h:real^3->real^3) (UNIONS l)) /\
                IMAGE h (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[TUBE_FACTS]; ALL_TAC] THEN
  ABBREV_TAC `ff = IMAGE (e:(real^3->bool)->real^3->bool)
                         {s | s IN l /\ aff_dim s = &1}` THEN
  SUBGOAL_THEN `!E:real^3->bool. E IN ff
                  ==> ?u v:real^3. ~(u = v) /\ segment[u,v] IN l /\ E = e(segment[u,v])`
  ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `h:real^3->real^3`; `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (UNIONS l)`;
                 `interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`] MOI_S3X2_X0) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (UNIONS l)`;
                 `interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`;
                 `ff:(real^3->bool)->bool`; `x0:(real^3->bool)->bool`]
    MOI_S3X2_GP_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ff" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      X_GEN_TAC `E:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(E:real^3->bool) IN ff`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                     `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
        MOI_S3X2_HD_EDGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "ff" THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `s':real^3->bool` THEN REPEAT DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        GEN_REWRITE_RULE I [moi_s33_hd]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                 `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                 `c:real^3->real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(e:(real^3->bool)->real^3->bool) (segment[u,v])`;
                                `y:real^3`] o check (fun th ->
    can (find_term ((=) `pl_crossing_at`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `segment[u:real^3,v]` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
  MAP_EVERY EXISTS_TAC
   [`((e:(real^3->bool)->real^3->bool) (segment[u,v]) DIFF moi_s33_rim t l h u v) DELETE
     (h:real^3->real^3) (midpoint(u,v))`;
    `frontier (UNIONS x:real^3->bool)`;
    `(:real^3) DELETE (h:real^3->real^3) (midpoint(u,v))`] THEN
  ASM_REWRITE_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    DISCH_TAC THEN
    UNDISCH_TAC `frontier (UNIONS x) SUBSET
                 interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)) DIFF
                 IMAGE h (UNIONS l)` THEN
    UNDISCH_TAC `(y:real^3) IN
                 (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER frontier (UNIONS x)` THEN
    UNDISCH_TAC `(h:real^3->real^3) (midpoint(u,v)) IN IMAGE h (UNIONS l)` THEN
    UNDISCH_TAC `(y:real^3) = (h:real^3->real^3) (midpoint(u,v))` THEN
    SET_TAC[];
    MESON_TAC[]]);;

