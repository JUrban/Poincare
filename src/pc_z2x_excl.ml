(* ========================================================================= *)
(* pc_z2x_excl: the Z/2 cylinder exclusion, used in piece (b) of COR_9_94_L  *)
(* (MT Lemma 9.84 / Prop 9.85, pp. 238-239). At a soul base point the limit  *)
(* could a priori be the two-to-one model (S^2 x R)/Z2, which is orientable  *)
(* and has separating neck spheres, so orientability alone does not exclude  *)
(* it; here it is excluded by a covering argument. The main theorem          *)
(* Z2X_EXCLUSION proves the statement z2x_statement_tm: under                *)
(* P2B_SOUL_TOPOLOGY_STATEMENT, a time-0 limit of slices with soul points s  *)
(* k (lying over a compact K) cannot be the two-to-one model (S^2 x R)/Z2.   *)
(* Route: an exact static neck of the model (pc_z2x_neck) passes to the      *)
(* slices (P2B9_OPEN_NECK with the time-0 closeness Z2X_LIMIT_CLOSE); the    *)
(* image of the model shell is the component of s k off the neck sphere      *)
(* (Z2X_TRANSPORT), so the soul topology gives a ball chart b with           *)
(* b(ball(0,1)) equal to it; b^-1 o phi k o p is then a proper local         *)
(* homeomorphism of the shell onto ball(0,1), a covering, injective by       *)
(* simple connectivity, against p o rfs_twist = p (Z2X_COVER_CONTRA,         *)
(* Z2X_SLICE_COVER).                                                         *)
(* ========================================================================= *)

needs "src/pc_z2x_neck.ml";;
needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2b_ltr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The time-0 closeness of a p2c limit with                                   *)
(* its own phi (a p2c_flow_limit_with form of P2BL_FLOW_LIMIT_CLOSE, at the  *)
(* time-0 slice with t = 0 and Q = 1): on an open U inside a compact K, for  *)
(* large k, phi k is a diffeomorphism of U into the time-0 slice of V k and  *)
(* R g(0) is rfs_mclose to R (phi k)^* g_k (P2BL_LCK_CHART_CONVERT).         *)
(* ========================================================================= *)

let Z2X_LIMIT_CLOSE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x J (top:B topology) atlas g xl W phi K U delta R.
     p2c_flow_limit_with V x (\k. &0) (\k. &1) J (top,atlas) g xl W phi /\
     (!k. smooth_manifold_atlas (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0)) /\
          riemannian_metric (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))) /\
     riemannian_metric atlas (g (&0)) /\
     compact_in top K /\ open_in top U /\ U SUBSET K /\ &0 < delta /\ &0 < R
     ==> ?k0. !k. k0 <= k
            ==> K SUBSET W k /\
                (?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0))
                                  (IMAGE (phi k) (W k)) (phi k) psi) /\
                (?psi. mfd_diffeo top atlas U (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0))
                                  (IMAGE (phi k) U) (phi k) psi) /\
                rfs_mclose (rfs_kreg delta) delta atlas U (\y. R %% g (&0) y)
                  (\y. R %% mfd_pullback_metric atlas (rfs_vatlas (V k) (&0)) (phi k)
                                (rfs_vmetric (V k) (&0)) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "slices") STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "close" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ABBREV_TAC `m = rfs_kreg delta` THEN
  SUBGOAL_THEN `&0 < (&1 + inv R) pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `R:real` REAL_LT_INV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "close" (MP_TAC o SPECL [`&0`; `&0`; `K:B->bool`; `m:num`;
                                       `delta pow 2 / (&2 * (&1 + inv R) pow m)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `&0`) (LABEL_TAC "pt"))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) U
      (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) k) (&0))
      (rfs_vatlas (V k) (&0)) (IMAGE ((phi:num->B->A) k) U) (phi k) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "slices" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `delta pow 2 / &2` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < delta pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) k) (&0)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (&0)`;
                 `U:B->bool`; `IMAGE ((phi:num->B->A) k) U`; `(phi:num->B->A) k`; `psi:A->B`;
                 `(g:real->B->real^3^3) (&0)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (&0)`;
                 `R:real`; `&1`; `m:num`; `y:B`] P2BL_LCK_CHART_CONVERT) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_RID] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b <= c ==> a <= c`) th)) THEN
  USE_THEN "pt" (MP_TAC o SPECL [`&0`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv R) pow m * delta pow 2 / (&2 * (&1 + inv R) pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < (&1 + inv R) pow m` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* Two general tools.  A connected open set c                                *)
(* missing S whose closure adds only points of S is the connected component *)
(* of each of its points in the complement of S.  A map Fm from the shell    *)
(* inv rho < |y| < rho onto ball(0,1), continuous on the closed shell with  *)
(* the boundary spheres going to sphere(0,1), a local homeomorphism on the  *)
(* open shell and invariant under rfs_twist, cannot exist: it would be a    *)
(* covering (PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP), injective on the *)
(* path-connected shell over the simply connected ball (COVERING_SPACE_     *)
(* INJECTIVE), but rfs_twist y differs from y when |y| differs from 1.      *)
(* ========================================================================= *)

let Z2X_CLOPEN_COMPONENT = prove
 (`!top (S:A->bool) c x.
     c SUBSET topspace top DIFF S /\ x IN c /\ connected_in top c /\ open_in top c /\
     top closure_of c SUBSET c UNION S
     ==> connected_component_of (subtopology top (topspace top DIFF S)) x = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_UNIQUE THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  X_GEN_TAC `d:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`; `d:A->bool`; `c:A->bool`]
    CONNECTED_IN_CLOPEN_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EXISTS_TAC `top closure_of (c:A->bool)` THEN
      REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] CLOSURE_OF_SUBSET) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `top closure_of c SUBSET (c:A->bool) UNION S` THEN
      UNDISCH_TAC `(c:A->bool) SUBSET topspace top DIFF S` THEN SET_TAC[];
      REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `c:A->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:A->bool) SUBSET topspace top DIFF S` THEN
      SET_TAC[]];
    UNDISCH_TAC `(x:A) IN c` THEN UNDISCH_TAC `(x:A) IN d` THEN SET_TAC[]]);;

let Z2X_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  SIMP_TAC[P2AZQ_TWIST_FACTS]);;

let Z2X_COVER_CONTRA = prove
 (`!(Fm:real^3->real^3) rho.
     &1 < rho /\
     Fm continuous_on {y | inv rho <= norm y /\ norm y <= rho} /\
     IMAGE Fm {y | inv rho < norm y /\ norm y < rho} = ball(vec 0,&1) /\
     (!y. norm y = rho \/ norm y = inv rho ==> Fm y IN sphere(vec 0,&1)) /\
     (!y. inv rho < norm y /\ norm y < rho
          ==> ?t u G. y IN t /\ open t /\ t SUBSET {y | inv rho < norm y /\ norm y < rho} /\
                      open u /\ homeomorphism (t,u) (Fm,G)) /\
     (!y. inv rho < norm y /\ norm y < rho ==> Fm(rfs_twist y) = Fm y)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bd")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "tw")))))) THEN
  ABBREV_TAC `Osh = {y:real^3 | inv rho < norm y /\ norm y < rho}` THEN
  SUBGOAL_THEN `&0 < inv rho /\ inv rho < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `covering_space (Osh,(Fm:real^3->real^3)) (ball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `{x | x IN Osh /\ (Fm:real^3->real^3) x IN k} =
                    {x | x IN {y | inv rho <= norm y /\ norm y <= rho} /\ Fm x IN k}`
      SUBST1_TAC THENL
       [EXPAND_TAC "Osh" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
        X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `norm(z:real^3) = rho \/ norm z = inv rho` THENL
         [USE_THEN "bd" (MP_TAC o C MP (ASSUME `norm(z:real^3) = rho \/ norm z = inv rho`) o
                          SPEC `z:real^3`) THEN
          UNDISCH_TAC `(Fm:real^3->real^3) z IN k` THEN
          UNDISCH_TAC `(k:real^3->bool) SUBSET ball(vec 0,&1)` THEN
          REWRITE_TAC[SUBSET; IN_BALL_0; IN_SPHERE_0] THEN
          DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^3,rho)` THEN
        REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        SUBGOAL_THEN `{y:real^3 | inv rho <= norm y /\ norm y <= rho} =
                      cball(vec 0,rho) DIFF ball(vec 0,inv rho)` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_CBALL; OPEN_BALL]]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `(y:real^3) IN Osh` THEN EXPAND_TAC "Osh" THEN
                      REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `u:real^3->bool`
        (X_CHOOSE_THEN `G:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `u:real^3->bool`; `G:real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `homeomorphism (t,u) ((Fm:real^3->real^3),(G:real^3->real^3))` THEN
        REWRITE_TAC[homeomorphism] THEN
        DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
        UNDISCH_TAC `IMAGE (Fm:real^3->real^3) Osh = ball(vec 0,&1)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* injective by simple connectivity of the ball *)
  MP_TAC(ISPECL [`Fm:real^3->real^3`; `Osh:real^3->bool`; `ball(vec 0:real^3,&1)`]
    COVERING_SPACE_INJECTIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Osh" THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `inv rho`; `rho:real`]
        (CONJUNCT1 PATH_CONNECTED_ANNULUS)) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
      MATCH_MP_TAC CONVEX_IMP_SIMPLY_CONNECTED THEN REWRITE_TAC[CONVEX_BALL]];
    ALL_TAC] THEN
  (* a point and its twist *)
  ABBREV_TAC `y = ((&1 + rho) / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(y:real^3) = (&1 + rho) / &2` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(y:real^3) = (&1 + rho) / &2` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv rho < inv(norm(y:real^3)) /\ inv(norm y) < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `rfs_twist y:real^3`]) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "Osh" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[MATCH_MP Z2X_TWIST_NORM (ASSUME `~(y:real^3 = vec 0)`)] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "tw" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
  REWRITE_TAC[MATCH_MP Z2X_TWIST_NORM (ASSUME `~(y:real^3 = vec 0)`)] THEN
  UNDISCH_TAC `inv(norm(y:real^3)) < &1` THEN UNDISCH_TAC `norm(y:real^3) = (&1 + rho) / &2` THEN
  UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The two-to-one model as a space, and the                                  *)
(* transport of a clopen connected piece by a diffeomorphism.  p is         *)
(* continuous on real^3 minus 0, open on open sets missing 0, and maps      *)
(* compact sets missing 0 to compact sets; p o rfs_twist = p.  The shell U  *)
(* = p(inv rho < |y| < rho) with Sg = p(sphere(0,rho)) is open and          *)
(* connected, misses Sg, and p of the closed shell is U UNION Sg (compact). *)
(* ========================================================================= *)

let Z2X_EUCL_ATLAS = prove
 (`smooth_manifold_atlas (euclidean:(real^3)topology) (open_set_atlas (:real^3))`,
  MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let Z2X_MODEL_LOCAL = prove
 (`!top atlas (g:B->real^3^3) p lam y.
     p2azq_model (top,atlas) g p lam /\ ~(y = vec 0)
     ==> ?r p'. &0 < r /\ r < norm y /\
                mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(y,r)) top atlas
                           (IMAGE p (ball(y,r))) p p'`,
  REWRITE_TAC[p2azq_model; mfd_param] THEN MESON_TAC[]);;

let Z2X_BALL_NZ = prove
 (`!y:real^3 r. r < norm y ==> ball(y,r) SUBSET (:real^3) DELETE vec 0`,
  REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC `dist(y:real^3,vec 0) < r` THEN
  REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC);;

let Z2X_MODEL_CONT = prove
 (`!top atlas (g:B->real^3^3) p lam.
     p2azq_model (top,atlas) g p lam
     ==> continuous_map (subtopology euclidean ((:real^3) DELETE vec 0),top) p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `lam:real`; `y:real^3`] Z2X_MODEL_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `p':B->real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `ball(y:real^3,r)` THEN
  MP_TAC(ISPECL [`y:real^3`; `r:real`] Z2X_BALL_NZ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_REFL; CENTRE_IN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE `!s t:real^3->bool. s SUBSET t ==> t INTER s = s`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN SIMP_TAC[]);;

let Z2X_MODEL_OPEN = prove
 (`!top atlas (g:B->real^3^3) p lam s.
     p2azq_model (top,atlas) g p lam /\ open s /\ ~(vec 0 IN s)
     ==> open_in top (IMAGE p s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `lam:real`; `y:real^3`] Z2X_MODEL_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `p':B->real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (p:real^3->B) (ball(y,r) INTER s)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `ball(y:real^3,r)`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `IMAGE (p:real^3->B) (ball(y,r))`; `p:real^3->B`; `p':B->real^3`;
                   `ball(y:real^3,r) INTER s`] MFD_DIFFEO_RESTRICT) THEN
    ASM_SIMP_TAC[OPEN_IN_EUCLIDEAN; OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
    SIMP_TAC[mfd_diffeo];
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]]);;

let Z2X_MODEL_COMPACT = prove
 (`!top atlas (g:B->real^3^3) p lam c.
     p2azq_model (top,atlas) g p lam /\ compact c /\ ~(vec 0 IN c)
     ==> compact_in top (IMAGE p c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean ((:real^3) DELETE vec 0)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC Z2X_MODEL_CONT THEN MAP_EVERY EXISTS_TAC
     [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `lam:real`] THEN
    ASM_REWRITE_TAC[]]);;

let Z2X_MODEL_TWIST = prove
 (`!top atlas (g:B->real^3^3) p lam y.
     p2azq_model (top,atlas) g p lam /\ ~(y = vec 0) ==> p(rfs_twist y) = p y`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `p2azq_model (top,atlas) (g:B->real^3^3) p lam` THEN
  REWRITE_TAC[p2azq_model] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(rfs_twist y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2AZQ_TWIST_FACTS]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> t = `rfs_twist`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "=")) (concl th)
    then MP_TAC(SPECL [`y:real^3`; `rfs_twist y:real^3`] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

let Z2X_SHELL = prove
 (`!top atlas (g:B->real^3^3) p lam rho.
     p2azq_model (top,atlas) g p lam /\ &1 < rho /\ hausdorff_space top
     ==> open_in top (IMAGE p {y | inv rho < norm y /\ norm y < rho}) /\
         connected_in top (IMAGE p {y | inv rho < norm y /\ norm y < rho}) /\
         DISJOINT (IMAGE p {y | inv rho < norm y /\ norm y < rho})
                  (IMAGE p (sphere(vec 0,rho))) /\
         IMAGE p {y | inv rho <= norm y /\ norm y <= rho} =
         IMAGE p {y | inv rho < norm y /\ norm y < rho} UNION IMAGE p (sphere(vec 0,rho)) /\
         compact_in top (IMAGE p {y | inv rho <= norm y /\ norm y <= rho}) /\
         top closure_of (IMAGE p {y | inv rho < norm y /\ norm y < rho}) SUBSET
         IMAGE p {y | inv rho < norm y /\ norm y < rho} UNION IMAGE p (sphere(vec 0,rho)) /\
         (!z. ~(z = vec 0) /\ (rho < norm z \/ norm z < inv rho)
              ==> ~(p z IN IMAGE p {y | inv rho <= norm y /\ norm y <= rho}))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv rho /\ inv rho < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
                    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "m" (MP_TAC o REWRITE_RULE[p2azq_model]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "img")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "pb"))))))) THEN
  (* norms of twisted points *)
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> ~(rfs_twist y = vec 0) /\
                           norm(rfs_twist y) = inv(norm y) /\ rfs_twist(rfs_twist y) = y`
  (LABEL_TAC "tw") THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[P2AZQ_TWIST_FACTS] THEN
    REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_RNEG; VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* p y = p z exactly for z = y or z = twist y *)
  SUBGOAL_THEN `!y z:real^3. ~(y = vec 0) /\ ~(z = vec 0) /\ (p:real^3->B) y = p z
                             ==> norm z = norm y \/ norm z = inv(norm y)` (LABEL_TAC "pn") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o C MP (CONJ (ASSUME `~(y:real^3 = vec 0)`)
                                        (ASSUME `~(z:real^3 = vec 0)`)) o
                    SPECL [`y:real^3`; `z:real^3`]) THEN
    REWRITE_TAC[ASSUME `(p:real^3->B) y = p z`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. inv rho <= norm y ==> ~(y = vec 0)` (LABEL_TAC "nz") THENL
   [GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `inv rho <= norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the image of the closed shell *)
  SUBGOAL_THEN `IMAGE (p:real^3->B) {y | inv rho <= norm y /\ norm y <= rho} =
                IMAGE p {y | inv rho < norm y /\ norm y < rho} UNION IMAGE p (sphere(vec 0,rho))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(y:real^3) = rho` THENL
       [DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(y:real^3) = inv rho` THENL
       [DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `rfs_twist y:real^3` THEN
        SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
         [USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC Z2X_MODEL_TWIST THEN
          MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                `g:B->real^3^3`; `lam:real`] THEN
          ASM_REWRITE_TAC[] THEN USE_THEN "m" ACCEPT_TAC;
          REWRITE_TAC[IN_SPHERE_0] THEN
          USE_THEN "tw" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(MATCH_MP th
            (ASSUME `~(y:real^3 = vec 0)`)))]) THEN
          ASM_REWRITE_TAC[REAL_INV_INV]];
        DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->B) {y | inv rho <= norm y /\ norm y <= rho})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC Z2X_MODEL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `lam:real`] THEN
    CONJ_TAC THENL [USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | inv rho <= norm y /\ norm y <= rho} =
                    cball(vec 0,rho) DIFF ball(vec 0,inv rho)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      REWRITE_TAC[IN_ELIM_THM; NORM_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* open *)
    MATCH_MP_TAC Z2X_MODEL_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `lam:real`] THEN
    CONJ_TAC THENL [USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; NORM_0] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `{y:real^3 | inv rho < norm y /\ norm y < rho} =
                  ball(vec 0,rho) DIFF cball(vec 0,inv rho)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL]];
    (* connected *)
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean ((:real^3) DELETE vec 0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC Z2X_MODEL_CONT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `lam:real`] THEN
      USE_THEN "m" ACCEPT_TAC;
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`vec 0:real^3`; `inv rho`; `rho:real`]
          (CONJUNCT1 PATH_CONNECTED_ANNULUS)) THEN
        REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH; PATH_CONNECTED_IMP_CONNECTED];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `inv rho < norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
        ASM_REAL_ARITH_TAC]];
    (* disjoint *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM;
                IN_SPHERE_0] THEN
    X_GEN_TAC `w:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "pn" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "nz" MATCH_MP_TAC THEN UNDISCH_TAC `inv rho < norm(y:real^3)` THEN
        REAL_ARITH_TAC;
        USE_THEN "nz" MATCH_MP_TAC THEN UNDISCH_TAC `norm(z:real^3) = rho` THEN
        UNDISCH_TAC `inv rho < &1` THEN UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(y:real^3)) < rho` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      UNDISCH_TAC `inv rho < norm(y:real^3)` THEN UNDISCH_TAC `&0 < inv rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `inv(norm(y:real^3)) < rho` THEN UNDISCH_TAC `norm(y:real^3) < rho` THEN
    UNDISCH_TAC `norm(z:real^3) = rho` THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    (* closure *)
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && can (find_term (fun t -> t = `sphere(vec 0:real^3,rho)`)) (concl th))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    (* points outside the closed shell *)
    X_GEN_TAC `z:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "pn" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [UNDISCH_TAC `inv rho <= norm(y:real^3)` THEN UNDISCH_TAC `&0 < inv rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv rho <= inv(norm(y:real^3)) /\ inv(norm y) <= rho` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `inv rho <= norm(y:real^3)` THEN UNDISCH_TAC `norm(y:real^3) <= rho` THEN
    UNDISCH_TAC `rho < norm(z:real^3) \/ norm z < inv rho` THEN REAL_ARITH_TAC]);;

(* A compact subset of the model lies in the image of a shell. *)

let Z2X_COMPACT_SHELL = prove
 (`!top atlas (g:B->real^3^3) p lam K.
     p2azq_model (top,atlas) g p lam /\ compact_in top K
     ==> ?R. &1 < R /\ K SUBSET IMAGE p {y:real^3 | inv R < norm y /\ norm y < R}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `sh = \n:num. {y:real^3 | inv(&n + &1) < norm y /\ norm y < &n + &1}` THEN
  SUBGOAL_THEN `!n y. y IN (sh:num->real^3->bool) n <=> inv(&n + &1) < norm y /\ norm y < &n + &1`
  (LABEL_TAC "shd") THENL
   [EXPAND_TAC "sh" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (sh:num->real^3->bool) m SUBSET sh n` (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "shd" (fun th -> REWRITE_TAC[SUBSET; th]) THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&m + &1 <= &n + &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `compact_in top (K:B->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE (\n. IMAGE (p:real^3->B) ((sh:num->real^3->bool) n)) (:num)`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
      MATCH_MP_TAC Z2X_MODEL_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                            `lam:real`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "shd" (fun th -> REWRITE_TAC[th; NORM_0]) THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(sh:num->real^3->bool) n =
                      ball(vec 0,&n + &1) DIFF cball(vec 0,inv(&n + &1))` SUBST1_TAC THENL
         [USE_THEN "shd" (fun th -> REWRITE_TAC[EXTENSION; th]) THEN
          REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL]];
        REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x < &0)`) THEN MATCH_MP_TAC REAL_LT_INV THEN
        REAL_ARITH_TAC];
      UNDISCH_TAC `K SUBSET topspace (top:B topology)` THEN
      UNDISCH_TAC `p2azq_model (top,atlas) (g:B->real^3^3) p lam` THEN
      REWRITE_TAC[p2azq_model] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && can (find_term (fun t -> t = `topspace (top:B topology)`)) (concl th))) THEN
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:B` THEN DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      MP_TAC(SPEC `norm(y:real^3) + inv(norm y)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "shd" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `&0 < inv(norm(y:real^3))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\n. IMAGE (p:real^3->B) ((sh:num->real^3->bool) n)`; `(:num)`; `V:(B->bool)->bool`]
    FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `t:num->bool` num_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `&N + &2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (V:(B->bool)->bool)` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `V:(B->bool)->bool`)) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(sh:num->real^3->bool) N` THEN CONJ_TAC THENL
   [USE_THEN "mono" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "shd" (fun th -> REWRITE_TAC[SUBSET; th; IN_ELIM_THM]) THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv(&N + &2) <= inv(&N + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Transport of a clopen piece.  If phi is a                                 *)
(* diffeomorphism of W onto an open set of a Hausdorff manifold and U is     *)
(* open and connected with U UNION Sg compact in W and U missing Sg, then   *)
(* phi(U) is the connected component of each of its points in the           *)
(* complement of phi(Sg), and phi keeps the other points of W off phi(U)    *)
(* UNION phi(Sg).                                                           *)
(* ========================================================================= *)

let Z2X_TRANSPORT = prove
 (`!(top:C topology) (atlas:((C->bool)#(C->real^N))->bool)
    (topk:D topology) (atlask:((D->bool)#(D->real^M))->bool) W (phi:C->D) psi U Sg.
     hausdorff_space topk /\
     mfd_diffeo top atlas W topk atlask (IMAGE phi W) phi psi /\
     open_in top U /\ connected_in top U /\ DISJOINT U Sg /\ compact_in top (U UNION Sg) /\
     U UNION Sg SUBSET W
     ==> open_in topk (IMAGE phi U) /\ connected_in topk (IMAGE phi U) /\
         DISJOINT (IMAGE phi U) (IMAGE phi Sg) /\
         topk closure_of (IMAGE phi U) SUBSET IMAGE phi U UNION IMAGE phi Sg /\
         (!z. z IN W /\ ~(z IN U UNION Sg) ==> ~(phi z IN IMAGE phi U UNION IMAGE phi Sg)) /\
         (!x. x IN IMAGE phi U
              ==> connected_component_of
                    (subtopology topk (topspace topk DIFF IMAGE phi Sg)) x = IMAGE phi U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(U:C->bool) SUBSET W /\ (Sg:C->bool) SUBSET W` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(U:C->bool) UNION Sg SUBSET W` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in topk (IMAGE (phi:C->D) U)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:C topology`; `atlas:((C->bool)#(C->real^N))->bool`; `W:C->bool`;
                   `topk:D topology`; `atlask:((D->bool)#(D->real^M))->bool`;
                   `IMAGE (phi:C->D) W`; `phi:C->D`; `psi:D->C`; `U:C->bool`]
                  MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topk (IMAGE (phi:C->D) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology top (W:C->bool)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN W /\ y IN W /\ (phi:C->D) x = phi y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "inj" o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
    can (find_term (fun t -> t = `phi:C->D`)) (concl th))) THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (phi:C->D) U) (IMAGE phi Sg)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `w:D` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:C` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `b:C` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:C) = b` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `DISJOINT (U:C->bool) Sg` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `topk closure_of (IMAGE (phi:C->D) U) SUBSET IMAGE phi U UNION IMAGE phi Sg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (W:C->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:C` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `a:C` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:C) = a` ASSUME_TAC THEN
    TRY(USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]) THEN ASM SET_TAC[];
    X_GEN_TAC `x:D` THEN DISCH_TAC THEN MATCH_MP_TAC Z2X_CLOPEN_COMPONENT THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in topk (IMAGE (phi:C->D) U)`)) THEN
    UNDISCH_TAC `DISJOINT (IMAGE (phi:C->D) U) (IMAGE phi Sg)` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Fibres of the model and the neck region.                                 *)
(* p y = p z forces norm z = norm y or norm z = inv(norm y); hence the image *)
(* of a shell inv R1 < |y| < R1 misses the neck image p(rho neck domain)     *)
(* once rho exp(-a) >= R1.                                                   *)
(* ========================================================================= *)

let Z2X_NORM_FIBRE = prove
 (`!top atlas (g:B->real^3^3) p lam y z.
     p2azq_model (top,atlas) g p lam /\ ~(y = vec 0) /\ ~(z = vec 0) /\ p y = p z
     ==> norm z = norm y \/ norm z = inv(norm y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2azq_model] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `~(y:real^3 = vec 0)`) (ASSUME `~(z:real^3 = vec 0)`)) o
    SPECL [`y:real^3`; `z:real^3`] o check (fun th ->
      can (find_term (fun t -> t = `rfs_twist`)) (concl th))) THEN
  REWRITE_TAC[ASSUME `(p:real^3->B) y = p z`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[Z2X_TWIST_NORM]);;

let Z2X_NECK_AVOID = prove
 (`!top atlas (g:B->real^3^3) p lam eps rho R1.
     p2azq_model (top,atlas) g p lam /\ &0 < eps /\ &1 < R1 /\ &0 < rho /\
     R1 <= rho * exp(--(inv(sqrt(&2) * eps)))
     ==> DISJOINT (IMAGE p {y:real^3 | inv R1 < norm y /\ norm y < R1})
                  (IMAGE (p o (\w:real^3. rho % w)) (rfs_neck_dom eps))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
  X_GEN_TAC `q:B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv R1 /\ inv R1 < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `&1 < R1` THEN REAL_ARITH_TAC;
                    MATCH_MP_TAC REAL_INV_LT_1 THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < norm(w:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R1 < norm(rho % w:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs rho = rho` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `rho * exp(--(inv(sqrt(&2) * eps)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(rho % w:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `inv R1 < norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
      UNDISCH_TAC `&0 < inv R1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `R1 < norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
      UNDISCH_TAC `&1 < R1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `lam:real`; `y:real^3`; `rho % w:real^3`] Z2X_NORM_FIBRE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(q:B) = p (y:real^3)` THEN
    UNDISCH_TAC `(q:B) = p (rho % w:real^3)` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(y:real^3)) < R1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `inv(norm(y:real^3)) < R1` THEN UNDISCH_TAC `norm(y:real^3) < R1` THEN
  UNDISCH_TAC `R1 < norm(rho % w:real^3)` THEN REAL_ARITH_TAC);;

let Z2X_COMPONENT_IN = prove
 (`!X (a:B) c q. connected_component_of X a = c /\ connected_component_of X a q ==> q IN c`,
  REWRITE_TAC[IN] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* The covering contradiction in a slice.  If                                *)
(* phi is a diffeomorphism of an open W containing p of the closed shell     *)
(* into a manifold, and a ball chart b on ball(0,2) has b(ball(0,1)) = phi  *)
(* of the open shell and b(sphere(0,1)) = phi of p(sphere(0,rho)), then     *)
(* Fm = b' o phi o p satisfies the hypotheses of Z2X_COVER_CONTRA.           *)
(* ========================================================================= *)

let Z2X_DIFFEO_HOMEO = prove
 (`!s t (f:real^M->real^N) g.
     diffeomorphism_on s t f g ==> open s /\ open t /\ homeomorphism (s,t) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; homeomorphism] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let Z2X_SPHERE_SCALE = prove
 (`!rho. &0 < rho
         ==> IMAGE (\w:real^3. rho % w) (sphere(vec 0,&1)) = sphere(vec 0,rho)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `inv rho % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]);;

let Z2X_SLICE_COVER = prove
 (`!top atlas (g:B->real^3^3) p lam rho (topk:D topology)
    (atlask:((D->bool)#(D->real^3))->bool) W (phi:B->D) psi (b:real^3->D) b'.
     p2azq_model (top,atlas) g p lam /\ &1 < rho /\ hausdorff_space top /\
     smooth_manifold_atlas topk atlask /\
     mfd_diffeo top atlas W topk atlask (IMAGE phi W) phi psi /\
     IMAGE p {y:real^3 | inv rho <= norm y /\ norm y <= rho} SUBSET W /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&2)) topk atlask
                (IMAGE b (ball(vec 0,&2))) b b' /\
     IMAGE phi (IMAGE p {y:real^3 | inv rho < norm y /\ norm y < rho}) =
     IMAGE b (ball(vec 0,&1)) /\
     IMAGE phi (IMAGE p (sphere(vec 0,rho))) = IMAGE b (sphere(vec 0,&1))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dphi")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "db")
    (CONJUNCTS_THEN2 (LABEL_TAC "eqU") (LABEL_TAC "eqS"))))))))) THEN
  SUBGOAL_THEN `&0 < inv rho /\ inv rho < &1 /\ &0 < rho` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [USE_THEN "m" (MP_TAC o REWRITE_RULE[p2azq_model]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `lam:real`; `rho:real`] Z2X_SHELL) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "m" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Uopen") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Ceq") STRIP_ASSUME_TAC)))) THEN
  USE_THEN "dphi" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  USE_THEN "db" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                sphere(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* p of the closed shell goes into the chart domain *)
  SUBGOAL_THEN `IMAGE (phi:B->D) (IMAGE (p:real^3->B) {y:real^3 | inv rho <= norm y /\ norm y <= rho})
                SUBSET IMAGE (b:real^3->D) (ball(vec 0,&2))` ASSUME_TAC THENL
   [USE_THEN "Ceq" SUBST1_TAC THEN REWRITE_TAC[IMAGE_UNION] THEN
    USE_THEN "eqU" SUBST1_TAC THEN USE_THEN "eqS" SUBST1_TAC THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the boundary spheres go to sphere(0,1) *)
  SUBGOAL_THEN `!y:real^3. norm y = rho \/ norm y = inv rho
                           ==> (p:real^3->B) y IN IMAGE p (sphere(vec 0,rho))` (LABEL_TAC "bdp") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `rfs_twist y:real^3` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC Z2X_MODEL_TWIST THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `g:B->real^3^3`; `lam:real`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "m" ACCEPT_TAC;
      REWRITE_TAC[IN_SPHERE_0] THEN ASM_SIMP_TAC[Z2X_TWIST_NORM; REAL_INV_INV]];
    ALL_TAC] THEN
  MATCH_MP_TAC Z2X_COVER_CONTRA THEN
  MAP_EVERY EXISTS_TAC [`(b':D->real^3) o (phi:B->D) o (p:real^3->B)`; `rho:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* continuity on the closed shell *)
    REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology topk (IMAGE (b:real^3->D) (ball(vec 0,&2)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (W:B->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN CONJ_TAC THENL
         [MATCH_MP_TAC Z2X_MODEL_CONT THEN
          MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                                `lam:real`] THEN USE_THEN "m" ACCEPT_TAC;
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          UNDISCH_TAC `inv rho <= norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
          UNDISCH_TAC `&0 < inv rho` THEN REAL_ARITH_TAC];
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IMAGE_o] THEN FIRST_ASSUM ACCEPT_TAC];
    (* the image of the open shell *)
    REWRITE_TAC[IMAGE_o] THEN USE_THEN "eqU" SUBST1_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(b':D->real^3) ((b:real^3->D) z) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `b':D->real^3`)) (concl th) &&
        can (find_term (fun t -> t = `ball(vec 0:real^3,&2)`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
      ASM SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(b:real^3->D) z` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `b':D->real^3`)) (concl th) &&
          can (find_term (fun t -> t = `ball(vec 0:real^3,&2)`)) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
        ASM SET_TAC[];
        EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]];
    (* the boundary *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "bdp" (MP_TAC o C MATCH_MP (ASSUME `norm(y:real^3) = rho \/ norm y = inv rho`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `phi:B->D` FUN_IN_IMAGE)) THEN
    USE_THEN "eqS" SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(b':D->real^3) ((b:real^3->D) z) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `b':D->real^3`)) (concl th) &&
      can (find_term (fun t -> t = `ball(vec 0:real^3,&2)`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
    ASM SET_TAC[];
    (* local homeomorphisms *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `inv rho < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN UNDISCH_TAC `&0 < inv rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:real^3->B`; `lam:real`; `y:real^3`] Z2X_MODEL_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "m" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `p':B->real^3` STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC `r1 = min r (min (norm(y:real^3) - inv rho) (rho - norm y))` THEN
    SUBGOAL_THEN `&0 < r1 /\ r1 <= r` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r1" THEN UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `inv rho < norm(y:real^3)` THEN
      UNDISCH_TAC `norm(y:real^3) < rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball(y:real^3,r1) SUBSET ball(y,r) /\
                  ball(y:real^3,r1) SUBSET {y | inv rho < norm y /\ norm y < rho}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `r1 <= r` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`y:real^3`; `z:real^3`] NORM_TRIANGLE_SUB) THEN
      MP_TAC(ISPECL [`z:real^3`; `y:real^3`] NORM_TRIANGLE_SUB) THEN
      UNDISCH_TAC `dist(y:real^3,z) < r1` THEN EXPAND_TAC "r1" THEN
      REWRITE_TAC[dist; NORM_SUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `t = ball(y:real^3,r1)` THEN
    SUBGOAL_THEN `open (t:real^3->bool) /\ (y:real^3) IN t` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]; ALL_TAC] THEN
    (* the three diffeomorphisms *)
    SUBGOAL_THEN `mfd_diffeo euclidean (open_set_atlas (:real^3)) t (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                    (IMAGE (p:real^3->B) t) p p'` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`ball(y:real^3,r)`; `IMAGE (p:real^3->B) (ball(y,r))`] THEN
      ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (IMAGE (p:real^3->B) t) (topk:D topology) (atlask:((D->bool)#(D->real^3))->bool)
                    (IMAGE (phi:B->D) (IMAGE p t)) phi psi` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`W:B->bool`; `IMAGE (phi:B->D) W`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
          `mfd_diffeo euclidean (open_set_atlas (:real^3)) t (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
             (IMAGE (p:real^3->B) t) p p'`)) THEN SIMP_TAC[mfd_diffeo];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (p:real^3->B) {y:real^3 | inv rho <= norm y /\ norm y <= rho}` THEN
        CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `t SUBSET {y:real^3 | inv rho < norm y /\ norm y < rho}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_diffeo (topk:D topology) (atlask:((D->bool)#(D->real^3))->bool) (IMAGE (phi:B->D) (IMAGE (p:real^3->B) t))
                    euclidean (open_set_atlas (:real^3))
                    (IMAGE (b':D->real^3) (IMAGE phi (IMAGE p t))) b' b` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (b:real^3->D) (ball(vec 0,&2))`; `ball(vec 0:real^3,&2)`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "db" ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
          `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (IMAGE (p:real^3->B) t) (topk:D topology) (atlask:((D->bool)#(D->real^3))->bool)
             (IMAGE (phi:B->D) (IMAGE p t)) phi psi`)) THEN SIMP_TAC[mfd_diffeo];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (phi:B->D) (IMAGE (p:real^3->B) {y:real^3 | inv rho <= norm y /\ norm y <= rho})` THEN
        CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `t SUBSET {y:real^3 | inv rho < norm y /\ norm y < rho}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `diffeomorphism_on t (IMAGE (b':D->real^3) (IMAGE (phi:B->D) (IMAGE (p:real^3->B) t)))
                    (b' o phi o p) (((p':B->real^3) o (psi:D->B)) o (b:real^3->D))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MFD_DIFFEO_EUCLIDEAN] THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
      MAP_EVERY EXISTS_TAC [`topk:D topology`; `atlask:((D->bool)#(D->real^3))->bool`;
                            `IMAGE (phi:B->D) (IMAGE (p:real^3->B) t)`] THEN
      ASM_REWRITE_TAC[Z2X_EUCL_ATLAS] THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `IMAGE (p:real^3->B) t`] THEN
      ASM_REWRITE_TAC[Z2X_EUCL_ATLAS];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Z2X_DIFFEO_HOMEO) THEN
    MAP_EVERY EXISTS_TAC [`t:real^3->bool`;
                          `IMAGE (b':D->real^3) (IMAGE (phi:B->D) (IMAGE (p:real^3->B) t))`;
                          `((p':B->real^3) o (psi:D->B)) o (b:real^3->D)`] THEN
    ASM_REWRITE_TAC[];
    (* twist invariance *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC Z2X_MODEL_TWIST THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `lam:real`] THEN
    CONJ_TAC THENL [USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `inv rho < norm(vec 0:real^3)` THEN
    REWRITE_TAC[NORM_0] THEN UNDISCH_TAC `&0 < inv rho` THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The main theorem. The statement is the term z2x_statement_tm. Proof: a    *)
(* static eps-neck of the two-to-one model at radius rho (Z2X_MODEL_NECK)    *)
(* passes to the slices for large k (P2B9_OPEN_NECK, Z2X_LIMIT_CLOSE); the   *)
(* image of the model shell is the component of s k in the complement of the *)
(* neck sphere (Z2X_TRANSPORT), so P2B_SOUL_TOPOLOGY gives a ball chart b    *)
(* whose unit ball is that image; then b^-1 o phi k o p contradicts          *)
(* Z2X_SLICE_COVER.                                                          *)
(* ========================================================================= *)

let z2x_statement_tm =
 `!w:B->bool. P2B_SOUL_TOPOLOGY_STATEMENT w
  ==> !(V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
              (real->B->real^3^3))
       (x:num->B) J (top':B topology) atlas' (g':real->B->real^3^3) xl W phi
       (s:num->B) K (p:real^3->B) lam.
       p2c_flow_limit_with V x (\k. &0) (\k. &1) J (top',atlas') g' xl W phi /\
       (!k. hausdorff_space (rfs_vtop (V k) (&0)) /\
            connected_space (rfs_vtop (V k) (&0)) /\
            smooth_manifold_atlas (rfs_vtop (V k) (&0)) (rfs_vatlas (V k) (&0)) /\
            riemannian_metric (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) /\
            mfd_complete (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                         (rfs_vmetric (V k) (&0)) /\
            s k IN topspace (rfs_vtop (V k) (&0)) /\
            (!z. z IN topspace (rfs_vtop (V k) (&0)) /\ ~(z = s k)
                 ==> p2b_dist_regular (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                      (rfs_vmetric (V k) (&0)) (s k) z)) /\
       compact_in top' K /\
       (?k0. !k. k0 <= k ==> s k IN IMAGE (phi k) (K INTER W k)) /\
       riemannian_metric atlas' (g'(&0)) /\ &0 < lam /\
       IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top' /\
       (!y. ~(y = vec 0)
            ==> ?r. &0 < r /\ r < norm y /\ mfd_param top' atlas' (ball(y,r)) p) /\
       (!y z. ~(y = vec 0) /\ ~(z = vec 0)
              ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
       (!y. ~(y = vec 0) ==> rfs_pullback atlas' p (g'(&0)) y = lam %% cylinder_flow (&0) y)
       ==> F`;;
let Z2X_EXCLUSION = prove
 (z2x_statement_tm,
  GEN_TAC THEN REWRITE_TAC[P2B_SOUL_TOPOLOGY_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "soul"))) THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `x:num->B`; `J:real->bool`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:num->B`;
    `K:B->bool`; `p:real^3->B`; `lam:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sk") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `hausdorff_space (top':B topology) /\ smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2azq_model (top',atlas') ((g':real->B->real^3^3) (&0)) p lam` (LABEL_TAC "m")
  THENL [REWRITE_TAC[p2azq_model] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the neck size *)
  ABBREV_TAC `eps = min eps0 (&1 / &8)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps0 /\ eps < &1 / &4 /\ eps <= &1 / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 < eps0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) < &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
                      MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(&2) * eps /\ sqrt(&2) * eps < inv(&4)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(&2) * &1 / &8` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        UNDISCH_TAC `sqrt(&2) < &2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ea = exp(inv(sqrt(&2) * eps))` THEN
  SUBGOAL_THEN `&5 < ea /\ &0 < ea` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ea" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC(SPEC `inv(sqrt(&2) * eps)` REAL_EXP_LE_X) THEN
    UNDISCH_TAC `&4 < inv(sqrt(&2) * eps)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a shell containing K *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `K:B->bool`]
                Z2X_COMPACT_SHELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC) THEN
  (* the radius of the neck sphere *)
  ABBREV_TAC `rho = &2 * R1 * ea` THEN
  SUBGOAL_THEN `&1 < rho /\ ea < rho /\ R1 < rho /\ &0 < rho /\ rho * inv ea = &2 * R1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    SUBGOAL_THEN `&0 < (&2 * R1 - &1) * ea /\ &0 < R1 * (&2 * ea - &1)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      UNDISCH_TAC `&1 < R1` THEN UNDISCH_TAC `&5 < ea` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * R1 * ea) * inv ea = &2 * R1` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < ea` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `&1 < R1` THEN UNDISCH_TAC `&5 < ea` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the model neck at p(rho basis 1) *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `eps:real`;
                 `rho:real`; `basis 1:real^3`] Z2X_MODEL_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "m" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "neck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "out") (LABEL_TAC "pf"))))) THEN
  (* the open-neck transfer constant *)
  MP_TAC(INST_TYPE [`:B`,`:A`] P2B9_OPEN_NECK) THEN REWRITE_TAC[P2B_REQ_LRG_BASE] THEN
  DISCH_THEN(MP_TAC o SPECL [`eps:real`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
     `(g':real->B->real^3^3) (&0)`; `(p:real^3->B) (rho % basis 1)`;
     `(p:real^3->B) o (\w:real^3. rho % w)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "open"))) THEN
  (* the compact set Kp and the open neck image U0 *)
  ABBREV_TAC `R2 = rho * ea` THEN
  SUBGOAL_THEN `&1 < R2 /\ rho < R2 /\ &0 < inv R2 /\ inv R2 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R2" THEN
    SUBGOAL_THEN `&0 < rho * (ea - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&5 < ea` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 < rho * ea` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < rho * (ea - &1)` THEN UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `&0 < rho * (ea - &1)` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `&1 < rho * ea` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Kp = IMAGE (p:real^3->B) {y:real^3 | inv R2 <= norm y /\ norm y <= R2}` THEN
  SUBGOAL_THEN `compact_in top' (Kp:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN MATCH_MP_TAC Z2X_MODEL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3) (&0)`;
                          `lam:real`] THEN
    CONJ_TAC THENL [USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | inv R2 <= norm y /\ norm y <= R2} =
                    cball(vec 0,R2) DIFF ball(vec 0,inv R2)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      REWRITE_TAC[IN_ELIM_THM; NORM_0] THEN UNDISCH_TAC `&0 < inv R2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `U0 = IMAGE ((p:real^3->B) o (\w:real^3. rho % w)) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `open_in top' (U0:B->bool)` ASSUME_TAC THENL
   [USE_THEN "neck" (MP_TAC o REWRITE_RULE[rfs_neck]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':B->real^3`) THEN
    EXPAND_TAC "U0" THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `e':B->real^3`)) (concl th))) THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U0:B->bool) SUBSET Kp` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U0"; "Kp"] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < norm(w:real^3) /\ norm w < ea` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN rfs_neck_dom eps` THEN EXPAND_TAC "ea" THEN
      REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) = inv ea` SUBST_ALL_TAC THENL
     [EXPAND_TAC "ea" THEN REWRITE_TAC[REAL_EXP_NEG]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs rho = rho` SUBST1_TAC THENL [UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
                                                   ALL_TAC] THEN
    SUBGOAL_THEN `rho * inv ea < rho * norm(w:real^3) /\ rho * norm w < rho * ea` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "R2" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `inv R2 < &1` THEN UNDISCH_TAC `&1 < R1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the limit closeness at time 0 on U0 inside Kp *)
  MP_TAC(ISPECL [`(V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))`; `x:num->B`; `J:real->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `Kp:B->bool`; `U0:B->bool`; `delta:real`;
                 `inv lam`] Z2X_LIMIT_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    X_GEN_TAC `k:num` THEN USE_THEN "slices" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "close")) THEN
  USE_THEN "sk" (X_CHOOSE_THEN `k1:num` (LABEL_TAC "sk1")) THEN
  ABBREV_TAC `k = k0 + k1:num` THEN
  USE_THEN "close" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psiW:B->B`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psiU:B->B`) ASSUME_TAC))) THEN
  USE_THEN "sk1" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "slices" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  (* the neck of slice k *)
  USE_THEN "open" (MP_TAC o SPECL [`rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
    `rfs_vatlas ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `rfs_vmetric ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
    `(phi:num->B->B) k`; `psiU:B->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `psiU:B->B`)) (concl th) ||
      can (find_term (fun t -> t = `delta:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
    EXPAND_TAC "U0" THEN SIMP_TAC[];
    DISCH_TAC] THEN
  (* the model shell *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `rho:real`] Z2X_SHELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Ceq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "outC"))))))) THEN
  SUBGOAL_THEN `IMAGE (p:real^3->B) {y:real^3 | inv rho <= norm y /\ norm y <= rho} SUBSET
                (W:num->B->bool) k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Kp:B->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    EXPAND_TAC "Kp" THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv R2 <= inv rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `rho < R2` THEN UNDISCH_TAC `&0 < rho` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `inv rho <= norm(y:real^3)` THEN UNDISCH_TAC `norm(y:real^3) <= rho` THEN
    UNDISCH_TAC `rho < R2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* its transport to slice k *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `rfs_vatlas ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
                 `(W:num->B->bool) k`; `(phi:num->B->B) k`; `psiW:B->B`;
                 `IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho}`;
                 `IMAGE (p:real^3->B) (sphere(vec 0:real^3,rho))`] Z2X_TRANSPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "Ceq" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "offk") (LABEL_TAC "compk")))))) THEN
  (* K and the neck region *)
  SUBGOAL_THEN `K SUBSET IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->B) {y:real^3 | inv R1 < norm y /\ norm y < R1}` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv rho < inv R1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN UNDISCH_TAC `&1 < R1` THEN UNDISCH_TAC `R1 < rho` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `inv R1 < norm(y:real^3)` THEN UNDISCH_TAC `norm(y:real^3) < R1` THEN
    UNDISCH_TAC `R1 < rho` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `eps:real`;
                 `rho:real`; `R1:real`] Z2X_NECK_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "m" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) = inv ea` SUBST1_TAC THENL
     [EXPAND_TAC "ea" THEN REWRITE_TAC[REAL_EXP_NEG]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 < R1` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  (* s k in the transported shell, off the neck *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `z0:B` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE; IN_INTER] o
    check (fun th -> concl th = `(s:num->B) k IN IMAGE ((phi:num->B->B) k) (K INTER W k)`)) THEN
  SUBGOAL_THEN `(s:num->B) k IN IMAGE ((phi:num->B->B) k)
                  (IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho})`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a IN (W:num->B->bool) k /\ b IN W k /\ (phi:num->B->B) k a = phi k b
                      ==> a = b` (LABEL_TAC "injk") THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
      can (find_term (fun t -> t = `psiW:B->B`)) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s:num->B) k IN IMAGE ((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w))
                                      (rfs_neck_dom eps))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; o_THM; NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3->B) (rho % w) IN U0` ASSUME_TAC THENL
     [EXPAND_TAC "U0" THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z0:B) = (p:real^3->B) (rho % w)` ASSUME_TAC THENL
     [USE_THEN "injk" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (p:real^3->B) {y:real^3 | inv R1 < norm y /\ norm y < R1})
                          (IMAGE (p o (\w:real^3. rho % w)) (rfs_neck_dom eps))` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the neck sphere of slice k and the far point *)
  SUBGOAL_THEN `IMAGE ((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w)) (sphere(vec 0,&1)) =
                IMAGE (phi k) (IMAGE p (sphere(vec 0:real^3,rho)))` (LABEL_TAC "sph") THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_SIMP_TAC[Z2X_SPHERE_SCALE]; ALL_TAC] THEN
  ABBREV_TAC `yq = (rho * &4 / &3) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(yq:real^3) = rho * &4 / &3 /\ ~(yq = vec 0) /\
                rho % (&4 / &3 % basis 1) = yq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "yq" THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) yq IN Kp /\
                ~((p:real^3->B) yq IN IMAGE p {y:real^3 | inv rho < norm y /\ norm y < rho} UNION
                                     IMAGE p (sphere(vec 0,rho)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Kp" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `rho * &4 / &3 <= R2` MP_TAC THENL
       [EXPAND_TAC "R2" THEN MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 < rho` THEN
        UNDISCH_TAC `&5 < ea` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `inv R2 < &1` THEN UNDISCH_TAC `&1 < rho` THEN REAL_ARITH_TAC;
      USE_THEN "Ceq" (SUBST1_TAC o SYM) THEN USE_THEN "outC" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w)) (&4 / &3 % basis 1) =
                phi k (p yq)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  (* the far point in slice k *)
  SUBGOAL_THEN `IMAGE ((phi:num->B->B) k) (W k) SUBSET topspace (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `psiW:B->B`)) (concl th))) THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->B) k ((p:real^3->B) yq) IN topspace (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)) /\
                ~((phi:num->B->B) k ((p:real^3->B) yq) IN
                  IMAGE (phi k) (IMAGE p {y:real^3 | inv rho < norm y /\ norm y < rho}) UNION
                  IMAGE (phi k) (IMAGE p (sphere(vec 0:real^3,rho))))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(f:B->B) w t x. x IN w /\ IMAGE f w SUBSET t ==> f x IN t`) THEN
      EXISTS_TAC `(W:num->B->bool) k` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      USE_THEN "offk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the separation *)
  SUBGOAL_THEN `apx_separates (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0))
                  (IMAGE ((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w)) (sphere(vec 0,&1)))
                  ((s:num->B) k)
                  (((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w)) (&4 / &3 % basis 1))`
  ASSUME_TAC THENL
   [USE_THEN "sph" SUBST1_TAC THEN
    REWRITE_TAC[apx_separates; ASSUME `((phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w))
                                         (&4 / &3 % basis 1) = phi k (p yq)`] THEN
    SUBGOAL_THEN `IMAGE ((phi:num->B->B) k) (IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho})
                  SUBSET topspace (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`subtopology (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0))
                        (topspace (rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)) DIFF
                         IMAGE ((phi:num->B->B) k) (IMAGE (p:real^3->B) (sphere(vec 0:real^3,rho))))`;
                     `(s:num->B) k`;
                     `IMAGE ((phi:num->B->B) k) (IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho})`;
                     `(phi:num->B->B) k ((p:real^3->B) yq)`] Z2X_COMPONENT_IN) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "compk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        FIRST_ASSUM ACCEPT_TAC];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the ball chart from the soul topology *)
  USE_THEN "soul" (MP_TAC o SPECL [`eps:real`; `rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `rfs_vatlas ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
                                   `rfs_vmetric ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `(s:num->B) k`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(phi:num->B->B) k ((p:real^3->B) (rho % basis 1))`;
                             `(phi:num->B->B) k o (p:real^3->B) o (\w:real^3. rho % w)`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->B` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mfd_ball_chart; mfd_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball_chart")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `b':B->real^3`) THEN
  (* b(ball(0,1)) is the component of s k *)
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `rfs_vatlas ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
                 `ball(vec 0:real^3,&2)`; `b:real^3->B`; `b':B->real^3`;
                 `ball(vec 0:real^3,&1)`; `sphere(vec 0:real^3,&1)`] Z2X_TRANSPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL; CONNECTED_IN_EUCLIDEAN; CONNECTED_BALL;
                    COMPACT_IN_EUCLIDEAN] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL_0; IN_SPHERE_0; NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `ball(vec 0:real^3,&1) UNION sphere(vec 0,&1) = cball(vec 0,&1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_SPHERE_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
        REWRITE_TAC[COMPACT_CBALL]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(s:num->B) k` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->B) k) (IMAGE (p:real^3->B) {y:real^3 | inv rho < norm y /\ norm y < rho}) =
                IMAGE (b:real^3->B) (ball(vec 0,&1))` ASSUME_TAC THENL
   [USE_THEN "compk" (MP_TAC o SPEC `(s:num->B) k`) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && can (find_term (fun t -> t = `ball(vec 0:real^3,&1)`)) (rhs(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_component_of")) (concl th))) THEN
    USE_THEN "sph" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the contradiction *)
  MATCH_MP_TAC(INST_TYPE [`:B`,`:D`] Z2X_SLICE_COVER) THEN
  MAP_EVERY EXISTS_TAC
   [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3) (&0)`;
    `p:real^3->B`; `lam:real`; `rho:real`; `rfs_vtop ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`;
    `rfs_vatlas ((V:num->(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) k) (&0)`; `(W:num->B->bool) k`; `(phi:num->B->B) k`; `psiW:B->B`;
    `b:real^3->B`; `b':B->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [USE_THEN "m" ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `IMAGE (b:real^3->B) (sphere(vec 0,&1))`)) THEN
  USE_THEN "sph" ACCEPT_TAC);;

