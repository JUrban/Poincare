(* ========================================================================= *)
(* Unit pc_p2c_e994c (Part 2C): the topology clause of the C-component (MT   *)
(* p. 241) and MT Thm 9.89 (2) with length L for compact kappa-solutions.  A *)
(* compact kappa-solution with ksep that is not round at time 0 is           *)
(* diffeomorphic to S^3 or has a twisted structure: at a time t where d^2 R  *)
(* is large (P2KC_LARGE_DR), Claim 9.90 for the shifted solution             *)
(* (P2KC_CLAIM_9_90) gives canonical neighbourhoods at every point;          *)
(* C-components and round components are excluded because their d^2 R is     *)
(* bounded (CANON_CCOMP_IN_BALL, CANON_ROUND_IN_BALL); so every point is a   *)
(* neck centre or a cap core and APX_A25 with SMT_TWISTED_SPHERE_ALL gives   *)
(* the topology.  From this and the two statements of pc_p2c_e994s, one      *)
(* compactness argument gives P2KC_KSOL_COMPACT_FROM_ROUTES.                 *)
(* ========================================================================= *)

needs "src/pc_p2c_e994a.ml";;
needs "src/pc_p2c_e994s.ml";;
needs "src/pc_canon_diam.ml";;
needs "src/pc_apx_a25top.ml";;
needs "src/pc_smt_straight.ml";;
needs "src/pc_p2a_kap0.ml";;
needs "src/pc_p2b_conelib.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* d(p,q)^2 R(z) is bounded on C-components and on round                    *)
(* components (the distance from z to any point is at most a constant      *)
(* times R(z)^(-1/2)).                                                       *)
(* ------------------------------------------------------------------------- *)

let P2KC_DR_BOUND = prove
 (`!d d1 d2 R M.
     &0 <= d /\ &0 <= M /\ d <= d1 + d2 /\
     d1 <= M * inv(sqrt R) /\ d2 <= M * inv(sqrt R)
     ==> d pow 2 * R <= (&2 * M) pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < R` THENL
   [ALL_TAC;
    SUBGOAL_THEN `&0 <= d pow 2 * --R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `&2 * M` REAL_LE_POW_2) THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `d * sqrt R <= &2 * M` ASSUME_TAC THENL
   [SUBGOAL_THEN `d <= (&2 * M) * inv(sqrt R)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 * R = (d * sqrt R) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let P2KC_DR_FROM_BALL = prove
 (`!top atlas (g:A->real^3^3) M p q z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 <= M /\
     mfd_joinable (top,atlas) z p /\ mfd_joinable (top,atlas) z q /\
     mfd_dist (top,atlas) g z p <= M * inv(sqrt(mfd_scalar atlas g z)) /\
     mfd_dist (top,atlas) g z q <= M * inv(sqrt(mfd_scalar atlas g z))
     ==> mfd_dist (top,atlas) g p q pow 2 * mfd_scalar atlas g z <= (&2 * M) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2KC_DR_BOUND THEN
  MAP_EVERY EXISTS_TAC [`mfd_dist (top,atlas) (g:A->real^3^3) p z`;
                        `mfd_dist (top,atlas) (g:A->real^3^3) z q`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) p z` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_MESON_TAC[MFD_JOINABLE_TRANS];
    MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MFD_DIST_SYM]]);;

let P2KC_CCOMP_DR = prove
 (`!top atlas (g:A->real^3^3) C U p q z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_c_component (top,atlas) g C U /\ &1 <= C /\ p IN U /\ q IN U /\ z IN U
     ==> mfd_dist (top,atlas) g p q pow 2 * mfd_scalar atlas g z <=
         (&2 * C * sqrt C) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `U:A->bool`; `z:A`; `p:A`] CANON_CCOMP_IN_BALL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `U:A->bool`; `z:A`; `q:A`] CANON_CCOMP_IN_BALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2KC_DR_FROM_BALL THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC]);;

let P2KC_ROUND_DR = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps U p q z.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\
       rfs_round_component (top,atlas) g eps U /\ &0 < eps /\ eps <= eps0 /\
       p IN U /\ q IN U /\ z IN U
       ==> mfd_dist (top,atlas) g p q pow 2 * mfd_scalar atlas g z <= (&2 * &12) pow 2`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb")) CANON_ROUND_IN_BALL THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "rb" (fun th ->
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `U:A->bool`; `z:A`; `p:A`] th) THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `U:A->bool`; `z:A`; `q:A`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2KC_DR_FROM_BALL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The topology clause (MT p. 241).  At a time t <= 0 with                   *)
(* d^2 R > D^2 (P2KC_LARGE_DR), Claim 9.90 for the shifted solution gives   *)
(* every point a canonical neighbourhood; D is so large that C0-components  *)
(* and round components are impossible (P2KC_CCOMP_DR, P2KC_ROUND_DR), so    *)
(* every point is a neck centre or a cap core at time t, and APX_A25 with    *)
(* SMT_TWISTED_SPHERE_ALL gives S^3 or a twisted structure.                  *)
(* ------------------------------------------------------------------------- *)

(* A connected component of a connected space is the whole space. *)

let P2KC_COMPONENT_TOPSPACE = prove
 (`!top (U:A->bool).
     connected_space top /\ U IN connected_components_of top ==> U = topspace top`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(U:A->bool) IN connected_components_of top` THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING]);;

let P2KC_TOPOLOGY = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3).
     P2KC_CLAIM_9_90_STATEMENT w /\ P2KC_LARGE_DR_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top /\
     ~p2b_round (top,atlas) (g (&0))
     ==> (mfd_diffeomorphic (subtopology top (topspace top))
                            (restrict_atlas atlas (topspace top))
                            (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
          rfs_has_twisted (subtopology top (topspace top))
                          (restrict_atlas atlas (topspace top)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2KC_CLAIM_9_90_STATEMENT; P2KC_LARGE_DR_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c990")))
    (CONJUNCTS_THEN2 (LABEL_TAC "ldr") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KAPPA_SOLUTION_P2C) THEN
  REWRITE_TAC[p2c_kappa_sol] THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_sphere_sep top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2b_ksep]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_TOPSPACE; RESTRICT_ATLAS_TOPSPACE] THEN
  MP_TAC(REWRITE_RULE[APX_A25_STATEMENT] (ISPEC `w:B->bool` APX_A25)) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a25"))) THEN
  MP_TAC(INST_TYPE [`:B`,`:A`] P2KC_ROUND_DR) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rdr"))) THEN
  ABBREV_TAC `eps = min eps4 (min epsA epsR)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps4 /\ eps <= epsA /\ eps <= epsR` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "c990" (MP_TAC o SPECL [`eps:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_THEN `D1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cn"))))) THEN
  SUBGOAL_THEN `&0 <= C0 * sqrt C0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = D1 + &2 * &12 + &2 * C0 * sqrt C0` THEN
  SUBGOAL_THEN `D1 pow 2 <= D pow 2 /\ (&2 * &12) pow 2 <= D pow 2 /\
                (&2 * C0 * sqrt C0) pow 2 <= D pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN EXPAND_TAC "D" THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ldr" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `D:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `p:B` (X_CHOOSE_THEN `q:B`
    (X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `gt = \s. (g:real->B->real^3^3) (s + t)` THEN
  SUBGOAL_THEN `p2b_kappa_solution kappa (top,atlas) (gt:real->B->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "gt" THEN MATCH_MP_TAC P2AK0_KSOL_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gt:real->B->real^3^3) (&0) = (g:real->B->real^3^3) t` ASSUME_TAC THENL
   [EXPAND_TAC "gt" THEN REWRITE_TAC[REAL_ADD_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top
                    ==> apx_neck_or_core (top,atlas) ((g:real->B->real^3^3) t) C0 eps x`
  (LABEL_TAC "nc") THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "cn" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `gt:real->B->real^3^3`; `x:B`; `p:B`; `q:B`;
      `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2b_canon_L] THEN SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[apx_neck_or_core] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `e:real^3->B` THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BK_EVOLVING_NECK_SLICE) THEN
      SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`U:B->bool`; `Y:B->bool`] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(U:B->bool) = topspace top` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC P2KC_COMPONENT_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `rfs_c_component (top,atlas) ((g:real->B->real^3^3) t) C0 U` THEN
        SIMP_TAC[rfs_c_component];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) t`; `C0:real`; `topspace top:B->bool`;
                     `p:B`; `q:B`; `z:B`] P2KC_CCOMP_DR) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(U:B->bool) = topspace top` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC P2KC_COMPONENT_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `rfs_round_component (top,atlas) ((g:real->B->real^3^3) t) eps U` THEN
        SIMP_TAC[rfs_round_component];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      REMOVE_THEN "rdr" (MP_TAC o SPECL [`top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) t`; `eps:real`;
        `topspace top:B->bool`; `p:B`; `q:B`; `z:B`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "a25" (MP_TAC o SPECL [`C0:real`; `eps:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) t`;
    `topspace top:B->bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING; GSYM compact_space] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_TOPSPACE; RESTRICT_ATLAS_TOPSPACE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  UNDISCH_TAC `apx_two_balls top (atlas:((B->bool)#(B->real^3))->bool)` THEN
  REWRITE_TAC[apx_two_balls] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[SMT_TWISTED_SPHERE_STATEMENT]
           (ISPEC `w:B->bool` SMT_TWISTED_SPHERE_ALL)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the main contradiction argument (MT Thm 9.89 (2), with Claim    *)
(* 9.90 and Prop 9.91 replaced by one compactness argument).  A bad point of *)
(* a compact kappa-solution stays bad after the normalisation R(x,0) = 1; a  *)
(* kappa-solution limit with ksep has canon_L at its base point for SOME     *)
(* constant (the noncompact case by P2B_KSOL_NONCOMPACT_CANON_L, a compact   *)
(* round slice by P2KC_ROUND_CANON, otherwise a C-component by the topology  *)
(* clause and P2KC_CCOMP_SOME); and a subsequence index passes any bound.    *)
(* ------------------------------------------------------------------------- *)

let P2KC_BAD_NORMALIZE = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) x C eps L.
     P2B_PROP_9_83K_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top /\
     x IN topspace top /\ ~p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)
     ==> ?q. &0 < q /\
             p2b_kappa_solution kappa (top,atlas) (\t y. q %% g (t / q) y) /\
             mfd_scalar atlas ((\t y. q %% g (t / q) y) (&0)) x = &1 /\
             ~p2b_canon_L (p2b_kview (top,atlas) (\t y. q %% g (t / q) y)) C eps L x (&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  ABBREV_TAC `Q = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `x:B`]
                  P2KC_COMPACT_R_POS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `Q:real`; `C:real`; `eps:real`; `L:real`; `x:B`]
                P2KC_CANON_L_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RFA_C971_KSOL_SCALE] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `Q:real`; `x:B`] P2BCS_SCALAR_CMUL) THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ]);;

let P2KC_LIMIT_CANON = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) pl C0 eps L.
     P2B_PROP_9_83K_STATEMENT w /\ P2B_COR_9_71_STATEMENT w /\
     P2KC_CLAIM_9_90_STATEMENT w /\ P2KC_LARGE_DR_STATEMENT w /\
     &1 < C0 /\ &0 < eps /\
     (!kappa top atlas (g:real->B->real^3^3) x.
        p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
        ~compact_space top /\ x IN topspace top
        ==> p2b_canon_L (p2b_kview (top,atlas) g) C0 eps (L + &1) x (&0)) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ pl IN topspace top
     ==> ?Cs. &1 < Cs /\ p2b_canon_L (p2b_kview (top,atlas) g) Cs eps (L + &1) pl (&0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(LABEL_TAC "dd" o check (is_forall o concl)) THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [ALL_TAC;
    EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN USE_THEN "dd" MATCH_MP_TAC THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` THENL
   [EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2KC_ROUND_CANON THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]
                P2KC_TOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]
                P2KC_CCOMP_SOME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cs:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Cs:real` THEN ASM_REWRITE_TAC[p2b_canon_L] THEN
  SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `topspace top:B->bool` THEN ASM_REWRITE_TAC[]);;

let P2KC_SUBSEQ_LARGE = prove
 (`!sub N (C:real). p3_subseq sub ==> ?n. N <= n /\ C <= &(sub n) + &2`,
  REWRITE_TAC[p3_subseq] THEN REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `m:num` (SPEC `C:real` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `N + m:num` THEN REWRITE_TAC[LE_ADD] THEN
  SUBGOAL_THEN `m <= (sub:num->num) (N + m)` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N + m:num` THEN REWRITE_TAC[LE_ADDR] THEN
    MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `N + m:num`);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Thm 9.89 (2) with length L (P2KC_COMPACT_FROM_PIECES) from its inputs  *)
(* and the two statements of pc_p2c_e994s.  For eps <= min eps2 eps0         *)
(* (P2B_KSOL_NONCOMPACT_CANON_L, P2B_LIMIT_TRANSFER_VIEW) and L >= 1 suppose *)
(* no C1 works.  For each n a compact kappa-solution with ksep has a point   *)
(* that is bad for C1 = n + 2; it is not round (P2KC_ROUND_CANON), so a      *)
(* kappa0-solution (PROP_9_58), normalised with R(x,0) = 1.  THM_9_64 gives  *)
(* a kappa0-solution limit with ksep; it has canon_L at length L + 1 at its  *)
(* base point for some Cs (P2KC_LIMIT_CANON), the transfer gives canon_L     *)
(* with Cs at length L at the bad points of a tail of the subsequence, and   *)
(* monotonicity in C contradicts badness once the index passes Cs            *)
(* (P2KC_SUBSEQ_LARGE).                                                      *)
(* ------------------------------------------------------------------------- *)

let P2KC_COMPACT_FROM_PIECES = prove
 (`!w:B->bool.
     P2B_PROP_9_83K_STATEMENT w /\ P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT w /\
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_COR_9_71_STATEMENT w /\
     P2KC_CLAIM_9_90_STATEMENT w /\ P2KC_LARGE_DR_STATEMENT w
     ==> P2B_KSOL_COMPACT_CANON_L_STATEMENT w`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[P2B_KSOL_COMPACT_CANON_L_STATEMENT] THEN
  UNDISCH_TAC `P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  MP_TAC(REWRITE_RULE[P2B_LIMIT_TRANSFER_VIEW_STATEMENT]
           (ISPECL [`w:B->bool`; `w:B->bool`] P2B_LIMIT_TRANSFER_VIEW)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  UNDISCH_TAC `P2B_PROP_9_58_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_PROP_9_58_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0"))) THEN
  EXISTS_TAC `min eps2 eps0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "nc" (MP_TAC o SPECL [`eps:real`; `L + &1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(LABEL_TAC "bad") THEN
  SUBGOAL_THEN
   `!n. ?top atlas (g:real->B->real^3^3) x.
          p2b_kappa_solution kappa0 (top,atlas) g /\ p2b_ksep top atlas /\
          compact_space top /\ x IN topspace top /\ mfd_scalar atlas (g (&0)) x = &1 /\
          ~p2b_canon_L (p2b_kview (top,atlas) g) (&n + &2) eps L x (&0)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&1 < &n + &2`
      (fun th -> USE_THEN "bad" (MP_TAC o REWRITE_RULE[th] o SPEC `&n + &2`)) THENL
     [MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `top:B topology`
      (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool`
      (X_CHOOSE_THEN `g:real->B->real^3^3` (X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `~p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~p2b_canon_L (p2b_kview (top,atlas) (g:real->B->real^3^3)) (&n + &2)
                                eps L x (&0)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC P2KC_ROUND_CANON THEN EXISTS_TAC `kappa:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2b_kappa_solution kappa0 (top,atlas) (g:real->B->real^3^3)` ASSUME_TAC
    THENL
     [USE_THEN "k0" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `x:B`;
                   `&n + &2`; `eps:real`; `L:real`] P2KC_BAD_NORMALIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `\t y. q %% (g:real->B->real^3^3) (t / q) y`; `x:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `TT:num->B topology`
    (X_CHOOSE_THEN `AA:num->((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `GG:num->real->B->real^3^3` (X_CHOOSE_THEN `XX:num->B` (LABEL_TAC "seq"))))) THEN
  UNDISCH_TAC `P2B_THM_9_64_STATEMENT (w:B->bool)` THEN REWRITE_TAC[P2B_THM_9_64_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa0:real`; `TT:num->B topology`;
    `AA:num->((B->bool)#(B->real^3))->bool`; `GG:num->real->B->real^3^3`; `XX:num->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `topl:B topology`
    (X_CHOOSE_THEN `atlasl:((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `gl:real->B->real^3^3` (X_CHOOSE_THEN `pl:B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl") STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `(pl:B) IN topspace topl` ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `topl:B topology`;
                 `atlasl:((B->bool)#(B->real^3))->bool`; `gl:real->B->real^3^3`; `pl:B`;
                 `C0:real`; `eps:real`; `L:real`] P2KC_LIMIT_CANON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cs:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "tr" (MP_TAC o SPECL [`Cs:real`; `eps:real`; `L:real`;
    `\k. p2b_kview (TT ((sub:num->num) k),AA (sub k)) ((GG:num->real->B->real^3^3) (sub k))`;
    `(XX:num->B) o (sub:num->num)`; `\k:num. &0`; `\k:num. &1`; `topl:B topology`;
    `atlasl:((B->bool)#(B->real^3))->bool`; `gl:real->B->real^3^3`; `pl:B`;
    `kappa0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
    MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MP_TAC(ISPECL [`sub:num->num`; `N:num`; `Cs:real`] P2KC_SUBSEQ_LARGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "N" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN
   `p2b_canon_L (p2b_kview (TT ((sub:num->num) n),AA (sub n))
                           ((GG:num->real->B->real^3^3) (sub n)))
                (&(sub n) + &2) eps L ((XX:num->B) (sub n)) (&0)`
  MP_TAC THENL
   [MATCH_MP_TAC P2KC_CANON_L_MONO_C THEN EXISTS_TAC `Cs:real` THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The route form P2KC_KSOL_COMPACT_FROM_ROUTES, from the route statements   *)
(* P2KC_CLAIM_9_90_ROUTE and P2KC_LARGE_DR_ROUTE of pc_p2c_e994s.            *)
(* ------------------------------------------------------------------------- *)

let P2KC_KSOL_COMPACT_FROM_ROUTES = prove
 (`!w:B->bool.
     P2KC_CLAIM_9_90_ROUTE_STATEMENT w /\ P2KC_LARGE_DR_ROUTE_STATEMENT w
     ==> P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2KC_CLAIM_9_90_ROUTE_STATEMENT; P2KC_LARGE_DR_ROUTE_STATEMENT;
              P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2KC_COMPACT_FROM_PIECES THEN
  ASM_MESON_TAC[]);;

