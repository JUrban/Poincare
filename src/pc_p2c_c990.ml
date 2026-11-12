(* ========================================================================= *)
(* Unit pc_p2c_c990 (piece 1 of piece (e) of COR_9_94_L): MT Claim 9.90      *)
(* (p. 240) in the uniform form P2KC_CLAIM_9_90_STATEMENT of pc_p2c_e994s,   *)
(* from the inputs PROP_9_83K, KSOL_NONCOMPACT_CANON_L (piece (d)), THM_9_64 *)
(* and PROP_9_58.  Main theorem: P2KD_CLAIM_9_90_ROUTE.                      *)
(*                                                                           *)
(* Route (contradiction).  C0 is the constant of (d) at length L + 1.  Bad   *)
(* points x_n with D1 = n + 1 are not round (P2KC_ROUND_CANON), so PROP_9_58 *)
(* gives a uniform kappa0; R(x_n,0) > 0 (P2KC_COMPACT_R_POS) and the         *)
(* parabolic rescaling by R(x_n,0) keeps badness and d^2 R.  THM_9_64 gives  *)
(* a kappa-solution limit with ksep.  A noncompact limit has canon_L at      *)
(* length L + 1 at its base point by (d), and P2B_LIMIT_TRANSFER_VIEW moves  *)
(* it back to x_n.  A compact limit is mapped onto M_n by the limit          *)
(* diffeomorphisms (P2BL_COMPONENT_IMAGE) with C^k-close metrics, so the     *)
(* C-component transfer kit of pc_p2b_979s bounds d_n and R_n on all of M_n  *)
(* and d^2 R stays bounded, against (n + 1)^2 < d^2 R.  Finally the          *)
(* constants and the main theorem.                                           *)
(* ========================================================================= *)

needs "src/pc_p2c_e994s.ml";;
needs "src/pc_p2c_e994a.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* Basic facts of kappa-solutions at time 0, the scale invariance of d^2 R,  *)
(* and the normalisation of a bad compact point (not round, kappa0 from      *)
(* PROP_9_58, rescaling by q = R(x,0) > 0).                                  *)
(* ------------------------------------------------------------------------- *)

let P2KD_KSOL_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> &0 < kappa /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         connected_space top /\ ~(topspace top = {}) /\
         riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ks") THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol]) THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

let P2KD_KVIEW_AT0 = prove
 (`!top atlas (g:real->B->real^3^3).
     rfs_vtop (p2b_kview (top,atlas) g) (&0) = top /\
     rfs_vatlas (p2b_kview (top,atlas) g) (&0) = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) g) (&0) = g (&0)`,
  SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL]);;

let P2KD_DR_SCALE = prove
 (`!top atlas (g:B->real^3^3) q p1 p2 z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     &0 < q /\ p1 IN topspace top /\ p2 IN topspace top /\ z IN topspace top
     ==> mfd_dist (top,atlas) (\y. q %% g y) p1 p2 pow 2 *
         mfd_scalar atlas (\y. q %% g y) z =
         mfd_dist (top,atlas) g p1 p2 pow 2 * mfd_scalar atlas g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:real`; `p1:B`; `p2:B`] MFD_DIST_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:real`; `z:B`] P2BCS_SCALAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD);;

let P2KD_NORMALIZE = prove
 (`!(w:B->bool) kappa0 kappa top atlas (g:real->B->real^3^3) x C eps L.
     P2B_PROP_9_83K_STATEMENT w /\
     (!kappa top atlas (g:real->B->real^3^3).
         p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
         ~p2b_round (top,atlas) (g(&0))
         ==> p2b_kappa_solution kappa0 (top,atlas) g) /\
     &0 < eps /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top /\
     x IN topspace top /\
     ~p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)
     ==> ?g':real->B->real^3^3.
           p2b_kappa_solution kappa0 (top,atlas) g' /\
           mfd_scalar atlas (g' (&0)) x = &1 /\
           ~p2b_canon_L (p2b_kview (top,atlas) g') C eps L x (&0) /\
           !p1 p2 z. p1 IN topspace top /\ p2 IN topspace top /\ z IN topspace top
                     ==> mfd_dist (top,atlas) (g' (&0)) p1 p2 pow 2 *
                         mfd_scalar atlas (g' (&0)) z =
                         mfd_dist (top,atlas) (g (&0)) p1 p2 pow 2 *
                         mfd_scalar atlas (g (&0)) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "k58") MP_TAC)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2KD_KSOL_BASIC) THEN
  SUBGOAL_THEN `~p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~p2b_canon_L (p2b_kview (top,atlas) (g:real->B->real^3^3)) C eps L x (&0)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC P2KC_ROUND_CANON THEN EXISTS_TAC `kappa:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_kappa_solution kappa0 (top,atlas) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "k58" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` ASSUME_TAC THENL
   [MATCH_MP_TAC P2KC_COMPACT_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` THEN
  EXISTS_TAC `\t y. q %% (g:real->B->real^3^3) (t / q) y` THEN
  SUBGOAL_THEN `(\t y. q %% (g:real->B->real^3^3) (t / q) y) (&0) = (\y. q %% g (&0) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:B` THEN BETA_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_C971_KSOL_SCALE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `q:real`; `x:B`] P2BCS_SCALAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
    MP_TAC(ISPECL [`kappa0:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `q:real`; `C:real`; `eps:real`; `L:real`; `x:B`]
                  P2KC_CANON_L_RESCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2KD_DR_SCALE THEN ASM_REWRITE_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* A compact limit bounds d^2 R on the approximants.  For a flow limit of    *)
(* kappa-solutions at time 0 with scale 1 (the THM_9_64 form) whose limit is *)
(* compact, the static limit diffeomorphisms phi_n are onto M_n              *)
(* (P2BL_COMPONENT_IMAGE, M_n connected), the metrics are C^k-close, so      *)
(* P2B9S_CCOMP_TARGET_POINT (stability: P2B9S_LRG_D) gives R_n <= R + 1 and  *)
(* the quadratic forms within 1 +/- delta, P2B9S_CCOMP_DIST gives d_n <=     *)
(* sqrt(1 + delta) d, and compactness bounds d and R on the limit.           *)
(* ------------------------------------------------------------------------- *)

let P2KD_CMUL1 = prove
 (`!G:B->real^3^3. (\z. &1 %% G z) = G`,
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX]);;

let P2KD_PROD_BOUND = prove
 (`!d D R Rm. d pow 2 <= D /\ R <= Rm ==> d pow 2 * R <= D * (abs Rm + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= R` THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let P2KD_SQ_BOUND = prove
 (`!dn d Bd delta. &0 <= dn /\ &0 <= d /\ d <= Bd /\ &0 <= delta /\ delta <= &1 /\
                   dn <= sqrt(&1 + delta) * d
                   ==> dn pow 2 <= &2 * Bd pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(&1 + delta) * d) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `sqrt(&1 + delta) pow 2 = &1 + delta` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]]]);;

let P2KD_COMPACT_BOUND = prove
 (`!kappa kappa' (top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B)
     (top':B topology) atlas' (g':real->B->real^3^3) pl.
     (!n. p2b_kappa_solution kappa (top n,atlas n) (g n) /\ x n IN topspace (top n)) /\
     (!Tl. &0 < Tl
           ==> p3_flow_limit (\n. p2b_kview (top n,atlas n) (g n)) x (\n. &0) (\n. &1)
                             (top',atlas') g' pl Tl) /\
     p2b_kappa_solution kappa' (top',atlas') g' /\ compact_space top'
     ==> ?B N. !n p q z. N <= n /\ p IN topspace (top n) /\ q IN topspace (top n) /\
                         z IN topspace (top n)
                         ==> mfd_dist (top n,atlas n) (g n (&0)) p q pow 2 *
                             mfd_scalar (atlas n) (g n (&0)) z <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq")
              (CONJUNCTS_THEN2 (LABEL_TAC "lim") STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`kappa':real`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`] P2KD_KSOL_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. &0 < kappa /\ hausdorff_space (top n:B topology) /\
        smooth_manifold_atlas (top n) (atlas n) /\
        connected_space (top n) /\ ~(topspace (top n) = {}) /\
        riemannian_metric (atlas n) ((g:num->real->B->real^3^3) n (&0)) /\
        mfd_complete (top n,atlas n) (g n (&0))`
  (LABEL_TAC "bas") THENL
   [GEN_TAC THEN
    MATCH_MP_TAC(ISPECL [`kappa:real`; `(top:num->B topology) n`;
                         `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                         `(g:num->real->B->real^3^3) n`] P2KD_KSOL_BASIC) THEN
    USE_THEN "seq" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top' (topspace (top':B topology))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace (top':B topology) IN connected_components_of top'` ASSUME_TAC THENL
   [SUBGOAL_THEN `connected_components_of (top':B topology) = {topspace top'}` SUBST1_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  (* curvature bounds of the compact limit *)
  SUBGOAL_THEN
   `?K0. !y. y IN topspace top'
             ==> rfa_rmd2 0 atlas' ((g':real->B->real^3^3) (&0)) y <= K0 /\
                 rfa_rmd2 1 atlas' (g' (&0)) y <= K0 /\
                 rfa_rmd2 2 atlas' (g' (&0)) y <= K0`
  (X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THENL
   [MP_TAC(ISPECL [`0`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `topspace (top':B topology)`]
                  P2B9S_RMD2_COMPACT_BOUND) THEN
    MP_TAC(ISPECL [`1`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `topspace (top':B topology)`]
                  P2B9S_RMD2_COMPACT_BOUND) THEN
    MP_TAC(ISPECL [`2`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `topspace (top':B topology)`]
                  P2B9S_RMD2_COMPACT_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "b2")) THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "b1")) THEN
    DISCH_THEN(X_CHOOSE_THEN `B0:real` (LABEL_TAC "b0")) THEN
    EXISTS_TAC `max B0 (max B1 B2)` THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "b0" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
    USE_THEN "b1" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
    USE_THEN "b2" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`K0:real`; `&1`] (MP P2B9S_LRG_D P2B_REQ_LRG_DERIV)) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  ABBREV_TAC `delta = min eta (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ &0 <= delta /\ delta <= eta /\ delta <= &1 / &4 /\
                delta < &1 /\ delta <= &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the static limit data at time 0 on the whole compact limit *)
  MP_TAC(BETA_RULE(ISPECL
   [`\n. p2b_kview (top n,atlas n) ((g:num->real->B->real^3^3) n)`; `x:num->B`;
    `\n:num. &0`; `\n:num. &1`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `pl:B`;
    `topspace (top':B topology)`; `topspace (top':B topology)`;
    `delta:real`; `&1`] P2BL_STATIC_DATA)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBSET_REFL; REAL_LT_01] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\n. p2b_kview (top n,atlas n) ((g:num->real->B->real^3^3) n)`; `x:num->B`;
      `\n:num. &0`] P2BL_REGULAR_VSLICES)) THEN
    ANTS_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[P2KD_KVIEW_AT0] THEN
      USE_THEN "seq" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "bas" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN
      USE_THEN "seq" (fun th -> REWRITE_TAC[th]);
      DISCH_THEN(ACCEPT_TAC o MATCH_MP (BETA_RULE(ISPECL
       [`\n. p2b_kview (top n,atlas n) ((g:num->real->B->real^3^3) n)`; `x:num->B`;
        `\n:num. &0`] P2BL_VSLICES_SLICES)))];
    ALL_TAC] THEN
  REWRITE_TAC[P2KD_KVIEW_AT0; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->B`
   (X_CHOOSE_THEN `k0:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "close")))) THEN
  (* bounds of d and R on the limit *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `topspace (top':B topology)`]
                P2B9S_DIST_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bd:real` (LABEL_TAC "Bd")) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `topspace (top':B topology)`]
                P2B9S_COMPACT_SCALAR_RANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:B` (X_CHOOSE_THEN `y1:B`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "Rr") (K ALL_TAC)))))) THEN
  EXISTS_TAC `(&2 * Bd pow 2) *
              (abs(mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) y1 + &1) + &1)` THEN
  EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `p:B`; `q:B`; `z:B`] THEN STRIP_TAC THEN
  USE_THEN "bas" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "close" (MP_TAC o C MP (ASSUME `k0:num <= n`) o SPEC `n:num`) THEN
  SUBST1_TAC(ISPEC `(g:num->real->B->real^3^3) n (&0)` P2KD_CMUL1) THEN
  SUBST1_TAC(ISPEC `mfd_pullback_metric atlas' ((atlas:num->((B->bool)#(B->real^3))->bool) n)
                      ((phi:num->B->B) n) ((g:num->real->B->real^3^3) n (&0))` P2KD_CMUL1) THEN
  SUBST1_TAC(ISPEC `(g':real->B->real^3^3) (&0)` P2KD_CMUL1) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:B->B`) MP_TAC) THEN
  REWRITE_TAC[rfs_mclose] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lck"))) THEN
  (* the image is a component of the connected M_n *)
  SUBGOAL_THEN `IMAGE ((phi:num->B->B) n) (topspace top') IN
                connected_components_of ((top:num->B topology) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(atlas:num->((B->bool)#(B->real^3))->bool) n`; `psi:B->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* pointwise comparison on the limit *)
  SUBGOAL_THEN
   `!y. y IN topspace (top':B topology)
        ==> abs(mfd_scalar (atlas n) ((g:num->real->B->real^3^3) n (&0)) ((phi:num->B->B) n y) -
                mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) y) <= &1 /\
            (!v. v dot (mfd_pullback_metric atlas' (atlas n) (phi n) (g n (&0)) y ** v) <=
                 (&1 + delta) * (v dot (g' (&0) y ** v))) /\
            (!v. (&1 - delta) * (v dot (g' (&0) y ** v)) <=
                 v dot (mfd_pullback_metric atlas' (atlas n) (phi n) (g n (&0)) y ** v))`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `(top:num->B topology) n`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                   `(g:num->real->B->real^3^3) n (&0)`;
                   `topspace (top':B topology)`; `IMAGE ((phi:num->B->B) n) (topspace top')`;
                   `(phi:num->B->B) n`; `psi:B->B`; `&1`; `K0:real`; `&1`; `eta:real`;
                   `d2:real`; `delta:real`; `y:B`] P2B9S_CCOMP_TARGET_POINT) THEN
    SUBST1_TAC(ISPEC `(g':real->B->real^3^3) (&0)` P2KD_CMUL1) THEN
    SUBST1_TAC(ISPEC `mfd_pullback_metric atlas' ((atlas:num->((B->bool)#(B->real^3))->bool) n)
                        ((phi:num->B->B) n) ((g:num->real->B->real^3^3) n (&0))` P2KD_CMUL1) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_POW_ONE; REAL_LT_01] THEN
    ANTS_TAC THENL
     [USE_THEN "K0" (STRIP_ASSUME_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
      USE_THEN "lck" (ASSUME_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y v. y IN topspace (top':B topology)
           ==> v dot (mfd_pullback_metric atlas' (atlas n) ((phi:num->B->B) n)
                        ((g:num->real->B->real^3^3) n (&0)) y ** v) <=
               (&1 + delta) * (v dot ((g':real->B->real^3^3) (&0) y ** v))) /\
    (!y v. y IN topspace top'
           ==> (&1 - delta) * (v dot (g' (&0) y ** v)) <=
               v dot (mfd_pullback_metric atlas' (atlas n) (phi n) (g n (&0)) y ** v))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:B`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top'`) o SPEC `y:B`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* distances on M_n *)
  SUBGOAL_THEN
   `!a b. a IN topspace (top':B topology) /\ b IN topspace top'
          ==> mfd_dist ((top:num->B topology) n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                       ((phi:num->B->B) n a) (phi n b) <=
              sqrt(&1 + delta) * mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) a b`
  (LABEL_TAC "dist") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `(top:num->B topology) n`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                   `(g:num->real->B->real^3^3) n (&0)`;
                   `topspace (top':B topology)`; `(phi:num->B->B) n`; `psi:B->B`;
                   `delta:real`; `a:B`; `b:B`] P2B9S_CCOMP_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  (* preimages under phi n, which is onto M_n *)
  SUBGOAL_THEN
   `(!a. a IN topspace (top':B topology)
         ==> (phi:num->B->B) n a IN topspace ((top:num->B topology) n)) /\
    (!p. p IN topspace (top n) ==> ?a. a IN topspace top' /\ p = phi n a)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE ((phi:num->B->B) n) (topspace top') = topspace ((top:num->B topology) n)`
    MP_TAC THENL
     [SUBGOAL_THEN `connected_components_of ((top:num->B topology) n) = {topspace (top n)}`
      MP_TAC THENL
       [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `IMAGE ((phi:num->B->B) n) (topspace top') IN
                     connected_components_of ((top:num->B topology) n)` THEN
        MESON_TAC[IN_SING]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b c. a IN topspace (top':B topology) /\ b IN topspace top' /\ c IN topspace top'
            ==> mfd_dist ((top:num->B topology) n,atlas n) ((g:num->real->B->real^3^3) n (&0))
                         ((phi:num->B->B) n a) (phi n b) pow 2 *
                mfd_scalar (atlas n) (g n (&0)) (phi n c) <=
                (&2 * Bd pow 2) *
                (abs(mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) y1 + &1) + &1)`
  (LABEL_TAC "fin") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2KD_PROD_BOUND THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2KD_SQ_BOUND THEN
      MAP_EVERY EXISTS_TAC [`mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) a b`;
                            `delta:real`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
        USE_THEN "Bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "dist" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "pt" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(c:B) IN topspace top'`) o SPEC `c:B`) THEN
      USE_THEN "Rr" (MP_TAC o CONJUNCT2 o C MP (ASSUME `(c:B) IN topspace top'`) o SPEC `c:B`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a b c. a IN topspace (top':B topology) /\ b IN topspace top' /\
                        c IN topspace top' /\
                        p = (phi:num->B->B) n a /\ q = phi n b /\ z = phi n c`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;



(* ------------------------------------------------------------------------- *)
(* No normalised bad sequence.  A sequence of kappa0-solutions with ksep,    *)
(* R(x_n,0) = 1, x_n not canon_L (C0, eps, L) and (n + 1)^2 < d_n(p_n,q_n)^2 *)
(* R_n(z_n) at time 0 is impossible: THM_9_64 gives a limit; if it is        *)
(* noncompact, (d) at length L + 1 and LIMIT_TRANSFER_VIEW give canon_L at   *)
(* x_(sub n); if it is compact, P2KD_COMPACT_BOUND bounds d^2 R along the    *)
(* subsequence.                                                              *)
(* ------------------------------------------------------------------------- *)

let P2KD_SQ_GT = prove
 (`!a. &0 <= a ==> a < (a + &1) pow 2`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `(a + &1) pow 2 = a pow 2 + &2 * a + &1` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ASM_REAL_ARITH_TAC]);;

let P2KD_NO_BAD_SEQ = prove
 (`!(w:B->bool) eps0 C0 eps L kappa0 (top:num->B topology) atlas
     (g:num->real->B->real^3^3) (x:num->B) (p:num->B) (q:num->B) (z:num->B).
     P2B_THM_9_64_STATEMENT w /\
     (!C eps L V x t Q top atlas g xl kappa.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ &1 <= L /\
         (!n. p2c_regular_view (V n:(real->B topology)#
                                    (real->((B->bool)#(B->real^3))->bool)#
                                    (real->B->real^3^3)) /\
              x n IN topspace(rfs_vtop (V n) (t n)) /\
              mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                           (rfs_vmetric (V n) (t n))) /\
         (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl) /\
         p2b_kappa_solution kappa (top,atlas) g /\
         p2b_canon_L (p2b_kview (top,atlas) g) C eps (L + &1) xl (&0)
         ==> ?N. !n. N <= n ==> p2b_canon_L (V n) C eps L (x n) (t n)) /\
     (!kappa top atlas (g:real->B->real^3^3) x.
         p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
         ~compact_space top /\ x IN topspace top
         ==> p2b_canon_L (p2b_kview (top,atlas) g) C0 eps (L + &1) x (&0)) /\
     &1 < C0 /\ &0 < eps /\ eps <= eps0 /\ &1 <= L /\ &0 < kappa0 /\
     (!n. p2b_kappa_solution kappa0 (top n,atlas n) (g n) /\ p2b_ksep (top n) (atlas n) /\
          x n IN topspace (top n) /\
          mfd_scalar (atlas n) (g n (&0)) (x n) = &1 /\
          ~p2b_canon_L (p2b_kview (top n,atlas n) (g n)) C0 eps L (x n) (&0) /\
          p n IN topspace (top n) /\ q n IN topspace (top n) /\ z n IN topspace (top n) /\
          (&n + &1) pow 2 < mfd_dist (top n,atlas n) (g n (&0)) (p n) (q n) pow 2 *
                            mfd_scalar (atlas n) (g n (&0)) (z n))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr")
   (CONJUNCTS_THEN2 (LABEL_TAC "nc") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bad"))))))))) THEN
  REWRITE_TAC[P2B_THM_9_64_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa0:real`; `top:num->B topology`;
                             `atlas:num->((B->bool)#(B->real^3))->bool`;
                             `g:num->real->B->real^3^3`; `x:num->B`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN USE_THEN "bad" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
   (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
     (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `pl:B`
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim") STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `(pl:B) IN topspace top'` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `compact_space (top':B topology)` THENL
   [(* compact limit: d^2 R is bounded along the subsequence *)
    MP_TAC(BETA_RULE(ISPECL
     [`kappa0:real`; `kappa0:real`; `\k:num. (top:num->B topology) ((sub:num->num) k)`;
      `\k:num. (atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k)`;
      `\k:num. (g:num->real->B->real^3^3) ((sub:num->num) k)`; `(x:num->B) o (sub:num->num)`;
      `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `pl:B`] P2KD_COMPACT_BOUND)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "bd"))) THEN
    MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    ABBREV_TAC `m = N + M:num` THEN
    SUBGOAL_THEN `m <= (sub:num->num) m` ASSUME_TAC THENL
     [ASM_MESON_TAC[P2BX0_SUBSEQ_GE]; ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o SPECL [`m:num`; `(p:num->B) (sub (m:num))`;
                                   `(q:num->B) (sub (m:num))`; `(z:num->B) (sub (m:num))`]) THEN
    USE_THEN "bad" (MP_TAC o SPEC `(sub:num->num) m`) THEN
    STRIP_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `&((sub:num->num) m)` P2KD_SQ_GT) THEN REWRITE_TAC[REAL_POS] THEN
    SUBGOAL_THEN `B <= &((sub:num->num) m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "m" THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* noncompact limit: (d) at length L + 1, then the transfer *)
    SUBGOAL_THEN `p2b_canon_L (p2b_kview (top',atlas') (g':real->B->real^3^3))
                              C0 eps (L + &1) pl (&0)` ASSUME_TAC THENL
     [USE_THEN "nc" MATCH_MP_TAC THEN EXISTS_TAC `kappa0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "tr" (MP_TAC o BETA_RULE o SPECL
     [`C0:real`; `eps:real`; `L:real`;
      `\k:num. p2b_kview ((top:num->B topology) ((sub:num->num) k),
                          (atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k))
                         ((g:num->real->B->real^3^3) ((sub:num->num) k))`;
      `(x:num->B) o (sub:num->num)`; `\k:num. &0`; `\k:num. &1`;
      `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
      `pl:B`; `kappa0:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[P2KD_KVIEW_AT0; o_THM] THEN X_GEN_TAC `n:num` THEN
      USE_THEN "bad" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
      MP_TAC(ISPECL [`kappa0:real`; `(top:num->B topology) (sub (n:num))`;
                     `(atlas:num->((B->bool)#(B->real^3))->bool) (sub (n:num))`;
                     `(g:num->real->B->real^3^3) (sub (n:num))`] P2KD_KSOL_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; o_THM] THEN
    USE_THEN "bad" (MP_TAC o SPEC `(sub:num->num) N`) THEN MESON_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* The constants and the main theorem.  eps4 = min of the eps of (d) and of  *)
(* LIMIT_TRANSFER_VIEW; C0 = the constant of (d) at L + 1; D1 by             *)
(* contradiction: bad data for D1 = n + 1 (Skolemised), normalised by        *)
(* P2KD_NORMALIZE, contradict P2KD_NO_BAD_SEQ.                               *)
(* ------------------------------------------------------------------------- *)

let P2KD_CLAIM_9_90_ROUTE = prove
 (`!w:B->bool. P2KC_CLAIM_9_90_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2KC_CLAIM_9_90_ROUTE_STATEMENT; P2KC_CLAIM_9_90_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[P2B_PROP_9_58_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k58"))) THEN
  REWRITE_TAC[P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
  MP_TAC(SPECL [`w:B->bool`; `w:B->bool`]
               (INST_TYPE [`:B`,`:A`] P2B_LIMIT_TRANSFER_VIEW)) THEN
  REWRITE_TAC[P2B_LIMIT_TRANSFER_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  EXISTS_TAC `min eps2 eps0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  USE_THEN "d" (MP_TAC o SPECL [`eps:real`; `L + &1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  EXISTS_TAC `C0:real` THEN REWRITE_TAC[ASSUME `&1 < C0`] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o
             REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN
   `!n:num. ?kappa top atlas (g:real->B->real^3^3) x p q z.
       (p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top /\
        x IN topspace top /\ p IN topspace top /\ q IN topspace top /\ z IN topspace top /\
        (&n + &1) pow 2 < mfd_dist (top,atlas) (g (&0)) p q pow 2 *
                          mfd_scalar atlas (g (&0)) z) /\
       ~p2b_canon_L (p2b_kview (top,atlas) g) C0 eps L x (&0)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "neg" (MP_TAC o SPEC `&n + &1`) THEN
    MATCH_MP_TAC(TAUT `~a ==> (a \/ b ==> b)`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:num->real` (X_CHOOSE_THEN `top:num->B topology`
   (X_CHOOSE_THEN `atlas:num->((B->bool)#(B->real^3))->bool`
     (X_CHOOSE_THEN `g:num->real->B->real^3^3` (X_CHOOSE_THEN `x:num->B`
       (X_CHOOSE_THEN `p:num->B` (X_CHOOSE_THEN `q:num->B`
         (X_CHOOSE_THEN `z:num->B` (LABEL_TAC "bad0"))))))))) THEN
  SUBGOAL_THEN
   `!n:num. ?g':real->B->real^3^3.
          p2b_kappa_solution kappa0 (top n,atlas n) g' /\
          mfd_scalar (atlas n) (g' (&0)) (x n) = &1 /\
          ~p2b_canon_L (p2b_kview (top n,atlas n) g') C0 eps L (x n) (&0) /\
          !p1 p2 z'. p1 IN topspace (top n) /\ p2 IN topspace (top n) /\
                     z' IN topspace (top n)
                     ==> mfd_dist (top n,atlas n) (g' (&0)) p1 p2 pow 2 *
                         mfd_scalar (atlas n) (g' (&0)) z' =
                         mfd_dist (top n,atlas n) (g n (&0)) p1 p2 pow 2 *
                         mfd_scalar (atlas n) (g n (&0)) z'`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `(kap:num->real) n`;
                         `(top:num->B topology) n`;
                         `(atlas:num->((B->bool)#(B->real^3))->bool) n`;
                         `(g:num->real->B->real^3^3) n`; `(x:num->B) n`;
                         `C0:real`; `eps:real`; `L:real`] P2KD_NORMALIZE) THEN
    USE_THEN "bad0" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `gn:num->real->B->real^3^3` (LABEL_TAC "nrm")) THEN
  MATCH_MP_TAC P2KD_NO_BAD_SEQ THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `eps0:real`; `C0:real`; `eps:real`; `L:real`;
                        `kappa0:real`; `top:num->B topology`;
                        `atlas:num->((B->bool)#(B->real^3))->bool`;
                        `gn:num->real->B->real^3^3`; `x:num->B`; `p:num->B`; `q:num->B`;
                        `z:num->B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  USE_THEN "bad0" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "nrm" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "nrm" (MP_TAC o SPECL [`(p:num->B) n`; `(q:num->B) n`; `(z:num->B) n`] o
                  CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

