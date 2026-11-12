(* ========================================================================= *)
(* pc_p2b_tubelim: the limit side of the bad tube in MT Thm 10.2 (MT Sec     *)
(* 10.3, the limit part of Prop 10.7 and Claims 10.10-10.11).  Proofs of two *)
(* of the five statements of pc_p2b_tubelimst: boxes under every point of    *)
(* the limit with approximant persistence and Rm bounds (P2BTL_LIM_BOXES,    *)
(* Claim 10.10 with corrected margins) and sec >= 0 on the box points        *)
(* (P2BTL_LIM_SEC, Claim 10.11).  The other three are in pc_p2b_tubelim2     *)
(* (ENECK) and pc_p2b_tubelim3 (CHAIN, SUMMABLE).                            *)
(* ========================================================================= *)

needs "src/pc_p2b_tubelimst.ml";;
needs "src/pc_p2b_tube3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basics.  Images of open sets under diffeos, compact neighbourhoods in     *)
(* manifolds, the facts of p2bt_lctx used below, and the uniform convergence *)
(* R_k o phi_k -> R on compact subsets of the limit.                         *)
(* ------------------------------------------------------------------------- *)

let P2BTL_DIFFEO_IMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W top' (atlas':((B->bool)#(B->real^M))->bool)
    W' (f:A->B) g X.
     mfd_diffeo top atlas W top' atlas' W' f g /\ open_in top X /\ X SUBSET W
     ==> open_in top' (IMAGE f X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W':B->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `homeomorphic_map (subtopology top W,subtopology top' W') (f:A->B)`
  ASSUME_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `subtopology top (W:A->bool)`; `subtopology top' (W':B->bool)`;
                 `X:A->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `X:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(X:A->bool) SUBSET W` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  EXISTS_TAC `X:A->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(X:A->bool) SUBSET W` THEN SET_TAC[]);;

let P2BTL_CPT_NBHD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top O /\ z IN O
     ==> ?X. open_in top X /\ z IN X /\ compact_in top (top closure_of X) /\
             top closure_of X SUBSET O`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `O:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:A) IN O` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `ph:A->real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`U:A->bool`; `ph:A->real^N`] o CONJUNCT1 o
              GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `ps:real^N->A` o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV]) THEN
  SUBGOAL_THEN `open_in top ((U:A->bool) INTER O)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (ph:A->real^N) (U INTER O))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `IMAGE (ph:A->real^N) U` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ph:A->real^N`; `subtopology top (U:A->bool)`;
                   `subtopology euclidean (IMAGE (ph:A->real^N) U)`; `U INTER O:A->bool`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U INTER O:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph:A->real^N) z IN IMAGE ph (U INTER O)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
                check (fun th -> is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "open")) THEN
  DISCH_THEN(MP_TAC o SPEC `(ph:A->real^N) z`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball((ph:A->real^N) z,r) SUBSET IMAGE ph U` ASSUME_TAC THENL
   [UNDISCH_TAC `cball((ph:A->real^N) z,r) SUBSET IMAGE ph (U INTER O)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN U ==> (ps:real^N->A)(ph x) = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `!x:A. x IN topspace top INTER U ==> (ps:real^N->A)(ph x) = x` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (ps:real^N->A) (cball(ph(z:A),r)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (subtopology top U) (IMAGE (ps:real^N->A) (cball(ph(z:A),r)))`
    MP_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (IMAGE (ph:A->real^N) U)` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
      SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (ps:real^N->A) (ball(ph(z:A),r))` THEN
  SUBGOAL_THEN `IMAGE (ps:real^N->A) (cball(ph(z:A),r)) SUBSET U INTER O` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN IMAGE (ph:A->real^N) (U INTER O)` MP_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN cball(ph(z:A),r)` THEN
      UNDISCH_TAC `cball((ph:A->real^N) z,r) SUBSET IMAGE ph (U INTER O)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `homeomorphic_map (subtopology euclidean (IMAGE (ph:A->real^N) U),
                                    subtopology top U) (ps:real^N->A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ps:real^N->A`; `subtopology euclidean (IMAGE (ph:A->real^N) U)`;
                   `subtopology top (U:A->bool)`; `ball(ph(z:A):real^N,r)`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`ph(z:A):real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
      UNDISCH_TAC `cball((ph:A->real^N) z,r) SUBSET IMAGE ph U` THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `ball(ph(z:A):real^N,r)` THEN
    REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL] THEN
    MP_TAC(ISPECL [`ph(z:A):real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
    UNDISCH_TAC `cball((ph:A->real^N) z,r) SUBSET IMAGE ph U` THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(ph:A->real^N) z` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE (ps:real^N->A) (cball(ph(z:A),r))` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (ps:real^N->A) (cball(ph(z:A),r))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      UNDISCH_TAC `IMAGE (ps:real^N->A) (cball(ph(z:A),r)) SUBSET U INTER O` THEN SET_TAC[]]]);;

let P2BTL_LCTX_BASIC = prove
 (`!eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    gamma s0 s1 EN A1 sub (top:B topology) atlas g zl W phi Vl.
     &0 < eps /\
     p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
     ==> &1 < C /\ &0 < A /\
         p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
         p2bt_cut eps C A V gamma s0 s1 A1 /\
         p2bt_lim V (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
                  (p2bt_zbase eps C V gamma s0) sub top atlas g zl W phi Vl /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         (!n. p2c_regular_view (V n) /\
              smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
              riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))) /\
         (!k. open_in top (W k) /\
              ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V ((sub:num->num) k)) (&0))
                               (rfs_vatlas (V ((sub:num->num) k)) (&0))
                               (IMAGE (phi k) (W k)) (phi k) psi) /\
         (!k w. w IN IMAGE (phi k) (W k)
                ==> ?e. rfs_strong_neck (V ((sub:num->num) k)) eps w (&0) e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_lctx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_lim]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) /\
        smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
        riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `p2bt_approx eps C A V0 t Q
                   (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `w:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:A) IN p2bt_tube eps ((EN:num->real->real^3->A) ((sub:num->num) k))
                                    ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bt_cutset")) (concl th) &&
      is_forall(concl th))) THEN
    BETA_TAC THEN REWRITE_TAC[p2bt_cutset] THEN
    UNDISCH_TAC `(w:A) IN IMAGE ((phi:num->B->A) k) (W k)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
                 `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) ((sub:num->num) k)`;
                 `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
                 `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) ((sub:num->num) k)`;
                 `(gamma:num->real->A) ((sub:num->num) k)`; `(s0:num->real) ((sub:num->num) k)`;
                 `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`]
                P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bt_approx eps C A V0 t Q
                   (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:A` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]);;

let P2BTL_R_UNIF = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z sub (top:B topology) atlas g zl W phi Vl K alpha.
     p2bt_lim V U z sub top atlas g zl W phi Vl /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
          riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))) /\
     compact_in top K /\ &0 < alpha
     ==> ?k0. !k. k0 <= k
                  ==> K SUBSET W k /\
                      !y. y IN K
                          ==> abs(mfd_scalar (rfs_vatlas (V ((sub:num->num) k)) (&0))
                                             (rfs_vmetric (V ((sub:num->num) k)) (&0)) (phi k y) -
                                  mfd_scalar atlas g y) <= alpha`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_lim] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `K:B->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN
  MP_TAC(ISPECL [`sqrt(abs B0 + &1)`; `alpha:real`]
                (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `2`; `eta pow 2`]) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN W (k:num)` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:B->bool) SUBSET W (k:num)` THEN UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th) &&
    is_forall(concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B` o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                 `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                 `(phi:num->B->A) k`; `psi:A->B`; `&1`; `sqrt(abs B0 + &1)`; `alpha:real`;
                 `eta:real`; `y:B`] LIM_POINT_CURV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_ARITH `&0 <= abs x + &1`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b + &1`) THEN ASM_SIMP_TAC[] ;
      SUBGOAL_THEN `(\z. &1 %% mfd_pullback_metric atlas
                         (rfs_vatlas ((V:num->(real->A topology)#
                            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0))
                         ((phi:num->B->A) k) (rfs_vmetric (V ((sub:num->num) k)) (&0)) z) =
                    mfd_pullback_metric atlas (rfs_vatlas (V ((sub:num->num) k)) (&0)) (phi k)
                                        (rfs_vmetric (V ((sub:num->num) k)) (&0))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_LID]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `rfs_vtop ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                     `rfs_vatlas ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                     `rfs_vmetric ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                     `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `y:B`; `2`]
                    P2BT_LIM_CLOSE_CONVERT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[REAL_DIV_1]]);;

(* ------------------------------------------------------------------------- *)
(* Boxes (MT Claim 10.10 with corrected margins).  Around a                  *)
(* compact set Kc of the limit with -1/R < s1' < 0 on Kc there is an open X  *)
(* with compact closure, and a < s1', such that for k large phi k (X) is a  *)
(* set of strong eps-neck centres with R_k <= -1/a, so it persists on       *)
(* (a,0] with |Rm| <= K1 (-1/a) (P2BN_NECK_SET_BACKWARD).                   *)
(* ------------------------------------------------------------------------- *)

let P2BTL_CPT_NBHD_SET = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) O Kc.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top O /\
     compact_in top Kc /\ Kc SUBSET O
     ==> ?X. open_in top X /\ Kc SUBSET X /\ compact_in top (top closure_of X) /\
             top closure_of X SUBSET O`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. ?X. (z:A) IN Kc
                        ==> open_in top X /\ z IN X /\ compact_in top (top closure_of X) /\
                            top closure_of X SUBSET O`
  MP_TAC THENL
   [X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN Kc` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BTL_CPT_NBHD THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(Kc:A->bool) SUBSET O` THEN
    UNDISCH_TAC `(z:A) IN Kc` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `XX:A->A->bool`) THEN
  MP_TAC(SPEC `IMAGE (XX:A->A->bool) Kc` (CONJUNCT2 (GEN_REWRITE_RULE I [compact_in]
    (ASSUME `compact_in top (Kc:A->bool)`)))) THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s:A->bool. s IN Fs
                            ==> open_in top s /\ compact_in top (top closure_of s) /\
                                top closure_of s SUBSET O`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:A->bool) IN IMAGE (XX:A->A->bool) Kc` MP_TAC THENL
     [UNDISCH_TAC `(Fs:(A->bool)->bool) SUBSET IMAGE (XX:A->A->bool) Kc` THEN
      UNDISCH_TAC `(s:A->bool) IN Fs` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS Fs:A->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM_MESON_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_SIMP_TAC[CLOSURE_OF_UNIONS] THEN MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE];
    ASM_SIMP_TAC[CLOSURE_OF_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

let P2BTL_BOX_COMPACT = prove
 (`?K1. &0 < K1 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      gamma s0 s1 EN A1 sub (top:B topology) atlas g zl W phi Vl Kc s1'.
       &0 < eps /\ eps <= &1 / &4 /\
       p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
       compact_in top Kc /\ ~(Kc = {}) /\ s1' < &0 /\
       (!y. y IN Kc ==> --inv(mfd_scalar atlas g y) < s1')
       ==> ?X a. open_in top X /\ compact_in top (top closure_of X) /\ Kc SUBSET X /\
                 a < s1' /\ a < &0 /\
                 (!z. z IN top closure_of X
                      ==> &0 < mfd_scalar atlas (g:B->real^3^3) z /\ --inv(mfd_scalar atlas (g:B->real^3^3) z) < a) /\
                 (?N. !k. N <= k
                          ==> top closure_of X SUBSET W k /\
                              rfs_persists (V ((sub:num->num) k)) (IMAGE (phi k) X) a (&0) /\
                              !s y'. a < s /\ s <= &0 /\ y' IN IMAGE (phi k) X
                                     ==> mfd_rm_norm (rfs_vatlas (V ((sub:num->num) k)) s)
                                                     (rfs_vmetric (V ((sub:num->num) k)) s) y'
                                         <= K1 * --inv a)`,
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nsb"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_SET_BACKWARD) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "eps eps4 lctx cpt ne s1n kc" THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  (* extreme values of R on Kc *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `Kc:B->bool`] P2B9S_COMPACT_SCALAR_RANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:B` (X_CHOOSE_THEN `y1:B` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!y:B. y IN Kc ==> &0 < mfd_scalar atlas (g:B->real^3^3) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "kc" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(r <= &0 ==> inv r <= &0) /\ s < &0 ==> --inv r < s ==> &0 < r`) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `Rmax = mfd_scalar atlas (g:B->real^3^3) y1` THEN
  ABBREV_TAC `Rmin = mfd_scalar atlas (g:B->real^3^3) y0` THEN
  SUBGOAL_THEN `&0 < Rmin /\ &0 < Rmax /\ --inv Rmax < s1'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Rmin"; "Rmax"] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = (s1' + --inv Rmax) / &2` THEN
  SUBGOAL_THEN `--inv Rmax < a /\ a < s1' /\ a < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Kt = --inv a` THEN
  SUBGOAL_THEN `Rmax < Kt /\ &0 < Kt /\ --inv Kt = a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kt" THEN REWRITE_TAC[REAL_INV_NEG; REAL_INV_INV; REAL_NEG_NEG] THEN
    SUBGOAL_THEN `&0 < --a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `inv(inv Rmax) < inv(--a)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_INV_INV; REAL_INV_NEG] THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_INV_NEG; REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K' = (Rmax + Kt) / &2` THEN
  SUBGOAL_THEN `Rmax < K' /\ K' < Kt` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the open set where Rmin/2 < R < K' *)
  ABBREV_TAC `O = {z:B | z IN topspace top /\ Rmin / &2 < mfd_scalar atlas (g:B->real^3^3) z /\
                         mfd_scalar atlas (g:B->real^3^3) z < K'}` THEN
  SUBGOAL_THEN `open_in top (O:B->bool) /\ Kc SUBSET O` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "O" THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`]
                    MFD_SCALAR_CONTINUOUS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `{z:B | z IN topspace top /\ Rmin / &2 < mfd_scalar atlas (g:B->real^3^3) z /\
                           mfd_scalar atlas (g:B->real^3^3) z < K'} =
                    {z | z IN topspace top /\ mfd_scalar atlas (g:B->real^3^3) z IN real_interval(Rmin / &2,K')}`
      SUBST1_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL; CONJ_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `euclideanreal` THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL; ETA_AX] THEN
      FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN
      DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `Kc:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:B) IN Kc` THEN SET_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Rmin:real` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; EXPAND_TAC "Rmin" THEN ASM_SIMP_TAC[]];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Rmax:real` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Rmax" THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `O:B->bool`;
                 `Kc:B->bool`] P2BTL_CPT_NBHD_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `X:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:B. z IN top closure_of X
                      ==> z IN topspace top /\ Rmin / &2 < mfd_scalar atlas (g:B->real^3^3) z /\
                          mfd_scalar atlas (g:B->real^3^3) z < K'`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN O` MP_TAC THENL
     [UNDISCH_TAC `top closure_of X SUBSET (O:B->bool)` THEN
      UNDISCH_TAC `(z:B) IN top closure_of X` THEN SET_TAC[];
      EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  (* uniform convergence of R on the closure *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `\n. p2bt_cutset eps ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n)
                        ((s0:num->real) n) ((s1:num->real) n) A1`;
                 `p2bt_zbase eps C (V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`;
                 `sub:num->num`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `zl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `top closure_of (X:B->bool)`; `Kt - K'`] P2BTL_R_UNIF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "lim" ACCEPT_TAC;
      GEN_TAC THEN USE_THEN "views" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "ru")) THEN
  MAP_EVERY EXISTS_TAC [`X:B->bool`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th ->
      can (find_term (fun t -> t = `Rmin / &2`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `--inv Kt = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_LT_NEG2] THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "ru" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rk")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  USE_THEN "views" (MP_TAC o SPEC `(sub:num->num) k`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") STRIP_ASSUME_TAC) THEN
  USE_THEN "nsb" (MP_TAC o SPECL
    [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`;
     `eps:real`; `IMAGE ((phi:num->B->A) k) X`; `Kt:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "reg" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
      MESON_TAC[];
      USE_THEN "reg" (MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view]) THEN
      MESON_TAC[];
      MATCH_MP_TAC (INST_TYPE [`:3`,`:N`; `:3`,`:M`] P2BTL_DIFFEO_IMAGE_OPEN) THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `(W:num->B->bool) k`;
                            `rfs_vatlas ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
                            `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      UNDISCH_TAC `~(Kc:B->bool = {})` THEN UNDISCH_TAC `(Kc:B->bool) SUBSET X` THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "necks" MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(X:B->bool) SUBSET W (k:num)` THEN UNDISCH_TAC `(z:B) IN X` THEN SET_TAC[];
        REWRITE_TAC[P2BN_RFS_VSCALAR] THEN
        SUBGOAL_THEN `(z:B) IN top closure_of X` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`top:B topology`; `X:B->bool`] CLOSURE_OF_SUBSET) THEN
          ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN UNDISCH_TAC `(z:B) IN X` THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "rk" (MP_TAC o SPEC `z:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th ->
          can (find_term (fun t -> t = `Rmin / &2`)) (concl th) && is_forall(concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2BTL_LIM_BOXES = prove
 (`!(u:A->bool) (w:B->bool). P2BT_LIM_BOXES_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_LIM_BOXES_STATEMENT] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "box"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_BOX_COMPACT) THEN
  EXISTS_TAC `&1 / &4` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "eps eps4 lctx" THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `s1':real`] THEN INTRO_TAC "y ry s1n" THEN
  USE_THEN "box" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `{y:B}`; `s1':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SING; NOT_INSERT_EMPTY; IN_SING] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->bool` (X_CHOOSE_THEN `a:real`
    (DESTRUCT_TAC "xo xc yx as an rx (@N. bx)"))) THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET top closure_of X` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`X:B->bool`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `{y:B} SUBSET X` THEN SET_TAC[];
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "rx" (MP_TAC o SPEC `z:B`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(X:B->bool) SUBSET top closure_of X` THEN
      UNDISCH_TAC `(z:B) IN X` THEN SET_TAC[];
      SIMP_TAC[]];
    MAP_EVERY EXISTS_TAC [`K1 * --inv a`; `N:num`] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "bx" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (X:B->bool)` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for sec >= 0 (MT Claim 10.11).  Collinear pairs, sec_min as a      *)
(* lower bound, the chart parametrizations through a diffeo, the rescaled   *)
(* Hamilton-Ivey pinching: if |Rm| <= Kb for Q g at x and Q is large, then  *)
(* sec >= -xi at x for Q g; and sec >= 0 passes to C2 limits at a point.    *)
(* ------------------------------------------------------------------------- *)

let P2BTL_LSECT_COLLINEAR = prove
 (`!(G:real^N->real^N^N) y u v. collinear {vec 0,u,v} ==> lsectional G y u v = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; lsectional; real_div] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(MESON[REAL_INV_0; REAL_MUL_RZERO] `!a b:real. b = &0 ==> a * inv b = &0`) THEN
  ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RMUL;
                  DOT_LMUL; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let P2BTL_SECMIN_LE = prove
 (`!top atlas (g:A->real^N^N) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     ~collinear {vec 0,u,v}
     ==> mfd_sec_min atlas g x <= mfd_sectional atlas g x u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`--(mfd_rm_norm atlas (g:A->real^N^N) x)`;
                        `mfd_sectional atlas (g:A->real^N^N) x u v`] THEN
  REWRITE_TAC[REAL_LE_REFL; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u':real^N`; `v':real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `u':real^N`; `v':real^N`] MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2BTL_CHART_PARAM = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ c IN atlas
     ==> mfd_param topX atlasX (IMAGE (SND c) (FST c INTER W)) (f o chart_inv c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `W:B->bool`; `W':A->bool`; `f':A->B`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) = (FST c,SND c)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[PAIR]; ALL_TAC] THEN
  ABBREV_TAC `U = FST(c:(B->bool)#(B->real^3))` THEN
  ABBREV_TAC `ph = SND(c:(B->bool)#(B->real^3))` THEN REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ open_in top (W:B->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)` THEN
      REWRITE_TAC[smooth_manifold_atlas] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) W
                              (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool) W'
                              (f:B->A) f'` THEN SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `IMAGE (ph:B->real^3) U` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `U:B->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `w:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `ph:B->real^3`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:B` o CONJUNCT1) THEN
    ASM_SIMP_TAC[]]);;

let P2BTL_PINCH_SEC = prove
 (`!top atl (g0:A->real^3^3) tau Q x Kb xi u v.
     smooth_manifold_atlas top atl /\ riemannian_metric atl g0 /\ x IN topspace top /\
     rfs_pinched_at atl g0 tau x /\ &0 <= tau /\ &0 < Q /\ &0 < xi /\
     mfd_rm_norm atl (\y. Q %% g0 y) x <= Kb /\
     exp(&3) / xi < Q /\ exp(&3 + &3 * Kb / xi) / xi < Q
     ==> --xi <= mfd_sectional atl (\y. Q %% g0 y) x u v`,
  REPEAT GEN_TAC THEN INTRO_TAC "sm riem x pin tau Q xi rmb q1 q2" THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,u,v}` THENL
   [ASM_SIMP_TAC[mfd_sectional; P2BTL_LSECT_COLLINEAR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atl (\y. Q %% (g0:A->real^3^3) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atl:((A->bool)#(A->real^3))->bool`; `g0:A->real^3^3`;
                 `Q:real`; `x:A`; `u:real^3`; `v:real^3`] P2BCS_SECT_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `mfd_sectional atl (g0:A->real^3^3) x u v < --xi * Q` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_sectional atl (g0:A->real^3^3) x u v / Q < --xi` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_sec_min atl (g0:A->real^3^3) x < --(xi * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_sectional atl (g0:A->real^3^3) x u v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BTL_SECMIN_LE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_sectional atl (g0:A->real^3^3) x u v < --xi * Q` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `X = --(mfd_sec_min atl (g0:A->real^3^3) x)` THEN
  SUBGOAL_THEN `&0 < xi * Q /\ xi * Q < X` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * X * (log X + log(&1 + tau) - &3) <= mfd_scalar atl (g0:A->real^3^3) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched_at atl (g0:A->real^3^3) tau x` THEN
    REWRITE_TAC[rfs_pinched_at] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atl (g0:A->real^3^3) x <= &6 * Kb * Q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atl:((A->bool)#(A->real^3))->bool`; `g0:A->real^3^3`;
                   `Q:real`; `x:A`] P2BCS_SCALAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atl:((A->bool)#(A->real^3))->bool`;
                   `\y. Q %% (g0:A->real^3^3) y`; `x:A`; `Kb:real`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atl:((A->bool)#(A->real^3))->bool`;
                     `\y. Q %% (g0:A->real^3^3) y`; `x:A`; `u':real^3`; `v':real^3`]
                    MFD_SECTIONAL_LE_RM_NORM) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC
        `mfd_rm_norm atl (\y. Q %% (g0:A->real^3^3) y) x <= Kb` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 < log(xi * Q) /\ log(xi * Q) <= log X /\ &0 <= log(&1 + tau)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `exp(&3) < xi * Q` ASSUME_TAC THENL
       [UNDISCH_TAC `exp(&3) / xi < Q` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`exp(&3)`; `xi * Q`] LOG_MONO_LT_IMP) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (xi * Q) * (log(xi * Q) - &3) <=
                &2 * X * (log X + log(&1 + tau) - &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(xi * Q) <= &3 + &3 * Kb / xi` ASSUME_TAC THENL
   [SUBGOAL_THEN `(log(xi * Q) - &3) * xi <= &3 * Kb` MP_TAC THENL
     [SUBGOAL_THEN `Q * (&2 * xi * (log(xi * Q) - &3)) <= Q * (&6 * Kb)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 * Kb / xi = (&3 * Kb) / xi` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `xi * Q <= exp(&3 + &3 * Kb / xi)` ASSUME_TAC THENL
   [MP_TAC(SPEC `xi * Q` EXP_LOG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `exp(&3 + &3 * Kb / xi) / xi < Q` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  UNDISCH_TAC `xi * Q <= exp(&3 + &3 * Kb / xi)` THEN REAL_ARITH_TAC);;

let P2BTL_SECT_LIMIT = prove
 (`!S (G0:real^3->real^3^3) p.
     metric_field S G0 /\ p IN S /\
     (!eta xi. &0 < eta /\ &0 < xi
               ==> ?G. metric_field S G /\ lck_dist2 2 G0 G p < eta /\
                       !u v. --xi <= lsectional G p u v)
     ==> !u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 p u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `d = --(lsectional (G0:real^3->real^3^3) p u v)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt(abs(lrm_deriv_norm2 0 (G0:real^3->real^3^3) p) + &1)`; `d / &3`]
                (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`eta pow 2`; `d / &3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->real^3^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "st" (MP_TAC o SPECL [`S:real^3->bool`; `G0:real^3->real^3^3`;
                                 `G:real^3->real^3^3`; `p:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SQRT_POW_2; REAL_ARITH `!x. &0 <= abs x + &1`;
             REAL_ARITH `!x. x <= abs x + &1`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* sec >= 0 on the box points (MT Claim 10.11): P2BTL_LIM_SEC.  At a        *)
(* point (s,y) with -1/R(y) < s <= 0 take a box as above below time s; the  *)
(* box clause of p2bt_lim gives C2 closeness at time s in the chart of y of *)
(* the limit to the pullbacks of the approximants, whose sectional          *)
(* curvatures are >= -xi for k large by the rescaled pinching of V0.        *)
(* ------------------------------------------------------------------------- *)

let P2BTL_PINCHED_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     rfs_pinched V /\ &0 <= t /\ x IN topspace(rfs_vtop V t)
     ==> rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_pinched; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

let P2BTL_TIME_DIFFEO = prove
 (`!(Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
    (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    X a s (f:B->A) f'.
     p2c_regular_view Vl /\ p2c_regular_view V' /\
     rfs_persists Vl X a (&0) /\ rfs_persists V' (IMAGE f X) a (&0) /\ a < s /\ s <= &0 /\
     mfd_diffeo (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) X
                (rfs_vtop V' (&0)) (rfs_vatlas V' (&0)) (IMAGE f X) f f'
     ==> mfd_diffeo (rfs_vtop Vl s) (rfs_vatlas Vl s) X
                    (rfs_vtop V' s) (rfs_vatlas V' s) (IMAGE f X) f f'`,
  REPEAT GEN_TAC THEN INTRO_TAC "rl r' pl p' as s0 df" THEN
  SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas
      (rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3)) s) (rfs_vatlas Vl s) /\
    smooth_manifold_atlas (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) /\
    smooth_manifold_atlas
      (rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s) (rfs_vatlas V' s) /\
    smooth_manifold_atlas (rfs_vtop V' (&0)) (rfs_vatlas V' (&0))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                      (real->B->real^3^3)`; `X:B->bool`; `a:real`; `&0`] P2BN_PERSISTS_ALT) THEN
    MP_TAC(ISPECL [`V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `IMAGE (f:B->A) X`; `a:real`; `&0`]
                  P2BN_PERSISTS_ALT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                             (real->B->real^3^3)) s) (rfs_vatlas Vl s) X
               (rfs_vtop Vl (&0)) (rfs_vatlas Vl (&0)) X (\y:B. y) (\y. y) /\
    mfd_diffeo (rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0)) (rfs_vatlas V' (&0)) (IMAGE (f:B->A) X)
               (rfs_vtop V' s) (rfs_vatlas V' s) (IMAGE f X) (\y:A. y) (\y. y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rl" (MP_TAC o SPECL [`X:B->bool`; `a:real`; `&0`; `s:real`] o
                     el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN
      USE_THEN "r'" (MP_TAC o SPECL [`IMAGE (f:B->A) X`; `a:real`; `&0`; `s:real`] o
                     el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                              (real->B->real^3^3)) s`;
                 `rfs_vatlas (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                (real->B->real^3^3)) s`; `X:B->bool`;
                 `rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                              (real->B->real^3^3)) (&0)`;
                 `rfs_vatlas (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                (real->B->real^3^3)) (&0)`; `X:B->bool`;
                 `rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`; `IMAGE (f:B->A) X`;
                 `\y:B. y`; `\y:B. y`; `f:B->A`; `f':A->B`] MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                              (real->B->real^3^3)) s`;
                 `rfs_vatlas (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                (real->B->real^3^3)) s`; `X:B->bool`;
                 `rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`; `IMAGE (f:B->A) X`;
                 `rfs_vtop (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `IMAGE (f:B->A) X`;
                 `(f:B->A) o (\y:B. y)`; `(\y:B. y) o (f':A->B)`; `\y:A. y`; `\y:A. y`]
                MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\y:A. y) o (f:B->A) o (\y:B. y) = f /\ ((\y:B. y) o (f':A->B)) o (\y:A. y) = f'`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let P2BTL_LIM_SEC = prove
 (`!(u:A->bool) (w:B->bool). P2BT_LIM_SEC_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_LIM_SEC_STATEMENT] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "box"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BTL_BOX_COMPACT) THEN
  EXISTS_TAC `&1 / &4` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "eps eps4 lctx" THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `w1:real^3`; `w2:real^3`] THEN
  INTRO_TAC "s0 y ry nc" THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`;
                 `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:num->real`; `Q:num->real`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
                 `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`]
                P2BTL_LCTX_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "c1 a0 approx cut lim haus smooth riem views diffs necks") THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bt_lim]) THEN
  ABBREV_TAC `Ry = mfd_scalar atlas (g:B->real^3^3) y` THEN
  SUBGOAL_THEN `&0 < Ry` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(Ry <= &0 ==> inv Ry <= &0) /\ --inv Ry < s /\ s <= &0
                             ==> &0 < Ry`) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `s1' = min s (--inv(&2 * Ry))` THEN
  SUBGOAL_THEN `--inv Ry < s1' /\ s1' < &0 /\ s1' <= s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1'" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&2 * Ry) /\ inv(&2 * Ry) < inv Ry` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "box" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`; `sub:num->num`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `zl:B`;
     `W:num->B->bool`; `phi:num->B->A`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `{y:B}`; `s1':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SING; NOT_INSERT_EMPTY; IN_SING] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->bool` (X_CHOOSE_THEN `a:real`
    (DESTRUCT_TAC "xo xc yx as an rx (@N0. bx)"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`X:B->bool`; `a:real`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vflow")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`K1 * --inv a`; `N0:num`] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "bx" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vf") (LABEL_TAC "bconv")) THEN
  SUBGOAL_THEN `a < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                (real->B->real^3^3)) X a (&0)`
  ASSUME_TAC THENL [USE_THEN "vf" (MP_TAC o REWRITE_RULE[p2c_vflow]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop Vl s) (rfs_vatlas Vl s) /\
                open_in (rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                     (real->B->real^3^3)) s) X`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                      (real->B->real^3^3)`; `X:B->bool`; `a:real`; `&0`] P2BN_PERSISTS_ALT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN X /\ (y:B) IN topspace (rfs_vtop Vl s)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                (real->B->real^3^3)) s`; `X:B->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `{y:B} SUBSET X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas Vl s)
                  (rfs_vmetric (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                   (real->B->real^3^3)) s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                     (real->B->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(y:B) IN topspace (rfs_vtop (Vl:(real->B topology)#
                     (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s)` THEN
      SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (rfs_vatlas (Vl:(real->B topology)#
                    (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s) (y:B)` THEN
  SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) IN rfs_vatlas Vl s /\ (y:B) IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `rfs_vtop (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                            (real->B->real^3^3)) s` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER X)`;
                 `metric_local (rfs_vatlas (Vl:(real->B topology)#
                    (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s) c
                    (rfs_vmetric Vl s)`;
                 `SND(c:(B->bool)#(B->real^3)) y`] P2BTL_SECT_LIMIT) THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(MP_TAC o SPECL [`w1:real^3`; `w2:real^3`]) THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER X))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) = (FST c,SND c)` SUBST1_TAC THENL
     [REWRITE_TAC[PAIR]; ALL_TAC] THEN
    REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (Vl:(real->B topology)#
                             (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                          `rfs_vatlas (Vl:(real->B topology)#
                             (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                          `FST(c:(B->bool)#(B->real^3))`] THEN
    ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `smooth_manifold_atlas (rfs_vtop Vl s)
                   (rfs_vatlas (Vl:(real->B topology)#
                      (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s)` THEN
    REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`] o
               CONJUNCT1) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (rfs_vatlas Vl s)
                     (rfs_vmetric (Vl:(real->B topology)#
                        (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eta:real`; `xi:real`] THEN STRIP_TAC THEN
  USE_THEN "bconv" (MP_TAC o SPECL [`{y:B}`; `2`; `eta:real`; `s:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SING; SING_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "kc")) THEN
  MP_TAC(SPEC `max (exp(&3) / xi) (exp(&3 + &3 * (K1 * --inv a) / xi) / xi)`
              REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `Nq:num`) THEN
  ABBREV_TAC `k = (k0:num) + N0 + Nq` THEN
  SUBGOAL_THEN `k0 <= k /\ N0 <= k /\ &Nq <= &k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k0:num) + N0 + Nq = k` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_regular_view ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) ((sub:num->num) k)) /\
    rfs_pinched (V0 ((sub:num->num) k)) /\
    (!s. s < &0 ==> rfs_vtop (V0 ((sub:num->num) k)) s = discrete_topology {}) /\
    &((sub:num->num) k) + &1 <= Q ((sub:num->num) k)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "approx" (MP_TAC o SPEC `(sub:num->num) k` o REWRITE_RULE[p2bt_approx]) THEN
    SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k <= &((sub:num->num) k)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&3) / xi < (Q:num->real) ((sub:num->num) k) /\
                exp(&3 + &3 * (K1 * --inv a) / xi) / xi < Q ((sub:num->num) k) /\ &0 < Q ((sub:num->num) k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `max (exp(&3) / xi) (exp(&3 + &3 * (K1 * --inv a) / xi) / xi) <= &Nq` THEN
    REWRITE_TAC[REAL_MAX_LE] THEN
    MP_TAC(SPEC `&3` REAL_EXP_POS_LT) THEN
    MP_TAC(SPEC `&3 + &3 * (K1 * --inv a) / xi` REAL_EXP_POS_LT) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < exp(&3) / xi` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* persistence of the image and the time-s diffeo *)
  USE_THEN "bx" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DESTRUCT_TAC "clw pk rmk") THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  USE_THEN "diffs" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop Vl s) (rfs_vatlas Vl s) X
               (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) ((sub:num->num) k)) s)
               (rfs_vatlas (V ((sub:num->num) k)) s) (IMAGE ((phi:num->B->A) k) X) (phi k) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_TIME_DIFFEO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas
      (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) ((sub:num->num) k)) s) (rfs_vatlas (V ((sub:num->num) k)) s) /\
    open_in (rfs_vtop (V ((sub:num->num) k)) s) (IMAGE ((phi:num->B->A) k) X)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) ((sub:num->num) k)`;
                   `IMAGE ((phi:num->B->A) k) X`; `a:real`; `&0`] P2BN_PERSISTS_ALT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:num->B->A) k) y IN
                topspace (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                      ((sub:num->num) k)) s`; `IMAGE ((phi:num->B->A) k) X`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:B) IN X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas ((V:num->(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s)
      (rfs_vmetric (V ((sub:num->num) k)) s)`
  ASSUME_TAC THENL
   [USE_THEN "views" (MP_TAC o CONJUNCT1 o SPEC `(sub:num->num) k`) THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `((phi:num->B->A) k) y IN
                   topspace (rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                     ((sub:num->num) k)) s)` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) ((sub:num->num) k)) s)
              (rfs_vatlas (V ((sub:num->num) k)) s)
              (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER X))
              ((phi:num->B->A) k o chart_inv c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BTL_CHART_PARAM THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (Vl:(real->B topology)#
                             (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                          `rfs_vatlas (Vl:(real->B topology)#
                             (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                          `IMAGE ((phi:num->B->A) k) X`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s)
               ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3)))
               (rfs_vmetric (V ((sub:num->num) k)) s)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s` THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "c" THEN USE_THEN "kc" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SING; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u1:real^3`; `u2:real^3`] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s`;
                 `rfs_vatlas ((V:num->(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s`;
                 `rfs_vmetric ((V:num->(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s`;
                 `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER X)`;
                 `(phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))`;
                 `SND(c:(B->bool)#(B->real^3)) y`; `u1:real^3`; `u2:real^3`]
                APX_PULLBACK_SECTIONAL_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))) (SND c y) = phi k y`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) = (FST c,SND c)` SUBST1_TAC THENL
     [REWRITE_TAC[PAIR]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (Vl:(real->B topology)#
                      (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                   `rfs_vatlas (Vl:(real->B topology)#
                      (real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) s`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`] CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the rescaled pinching *)
  UNDISCH_TAC `!s y'. a < s /\ s <= &0 /\ y' IN IMAGE ((phi:num->B->A) k) X
                      ==> mfd_rm_norm (rfs_vatlas ((V:num->(real->A topology)#
                            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                            ((sub:num->num) k)) s)
                            (rfs_vmetric (V ((sub:num->num) k)) s) y' <= K1 * --inv a` THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `(phi:num->B->A) k y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `((phi:num->B->A) k) y IN
                topspace (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) s)` THEN
  UNDISCH_TAC `smooth_manifold_atlas
      (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) ((sub:num->num) k)) s) (rfs_vatlas (V ((sub:num->num) k)) s)` THEN
  SUBGOAL_THEN
   `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      ((sub:num->num) k) =
    p2b_rescale_view ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) ((sub:num->num) k)) ((t:num->real) ((sub:num->num) k))
                     ((Q:num->real) ((sub:num->num) k))`
  SUBST1_TAC THENL
   [USE_THEN "approx" (MP_TAC o SPEC `(sub:num->num) k` o REWRITE_RULE[p2bt_approx]) THEN
    SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  REWRITE_TAC[P2BK_VS_PARTS] THEN
  ABBREV_TAC `tau = (t:num->real) ((sub:num->num) k) + s / (Q:num->real) ((sub:num->num) k)` THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC P2BTL_PINCH_SEC THEN
  EXISTS_TAC `rfs_vtop ((V0:num->(real->A topology)#
                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) tau` THEN
  EXISTS_TAC `tau:real` THEN EXISTS_TAC `K1 * --inv a` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(tau < &0) ==> &0 <= tau`) THEN DISCH_TAC THEN
    UNDISCH_TAC `((phi:num->B->A) k) y IN
                 topspace (rfs_vtop ((V0:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) tau)` THEN
    ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2c_regular_view ((V0:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `((phi:num->B->A) k) y IN
                   topspace (rfs_vtop ((V0:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) tau)` THEN
      SET_TAC[];
      SIMP_TAC[]];
    MATCH_MP_TAC P2BTL_PINCHED_AT THEN ASM_REWRITE_TAC[]]);;

