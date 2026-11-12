(* ========================================================================= *)
(* Unit pc_rfa_c971: P2B_COR_9_71, MT (9.33)-(9.34), the uniform bounds      *)
(* |grad R| <= C R^(3/2) and |Lap R + 2|Ric|^2| <= C R^2 on 3-dimensional    *)
(* kappa-solutions with p2b_ksep, from P2B_LEMMA_9_65 and P2B_PROP_9_58 (Shi *)
(* route).  At (x,t), q = R(x,t) > 0 (strong maximum principle); if g(t) is  *)
(* round the derivatives of R vanish; otherwise the shifted and rescaled     *)
(* solution q g(t + s/q) is a kappa0-solution (Prop 9.58) with R = 1 at      *)
(* (x,0), Lemma 9.65 and the Harnack monotonicity bound abs Rm on B(x,1) x   *)
(* (-1,0], and Shi's estimate (RFA_C2_SHI_SCALED) with the trace bounds      *)
(* P2C_SCALAR_DERIV_TRACE gives the bounds at R = 1; then scale back.  The   *)
(* route form P2B_COR_9_71_ROUTE_STATEMENT is RFA_C971_MAIN stated as an     *)
(* implication.                                                              *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_rfa_c2base.ml";;
needs "src/pc_rfa_htrace.ml";;
needs "src/pc_rfa_split.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_p2a_l965.ml";;
needs "src/pc_p2b_chainstmts.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Parabolic rescaling.  The sectional curvature, the norm of                *)
(* Rm and the scalar curvature of q g are those of g divided by q, and a     *)
(* kappa-solution rescaled to q g(t/q) is a kappa-solution with the same     *)
(* kappa (RFA_C971_KSOL_SCALE; the structure follows P2AK0_KSOL_SHIFT of     *)
(* pc_p2a_kap0).                                                             *)
(* ------------------------------------------------------------------------- *)

let RFA_C971_SEC_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < q
     ==> mfd_sectional atlas (\z. q %% g z) x u v = mfd_sectional atlas g x u v / q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_sectional; METRIC_LOCAL_CMUL] THEN
  MATCH_MP_TAC APX_LSECTIONAL_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let RFA_C971_SCALAR_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < q
     ==> mfd_scalar atlas (\z. q %% g z) x = mfd_scalar atlas g x / q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar; METRIC_LOCAL_CMUL] THEN
  MATCH_MP_TAC LSCALAR_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let RFA_C971_RMNORM_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < q
     ==> mfd_rm_norm atlas (\z. q %% g z) x = mfd_rm_norm atlas g x / q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. q %% (g:A->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b:real`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[DIMINDEX_3; REAL_LE_REFL] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. q %% (g:A->real^3^3) z`; `inv q`; `x:A`;
                 `mfd_rm_norm atlas (\z. q %% (g:A->real^3^3) z) x`]
                RFA_MFD_RM_NORM_CMUL_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; REAL_LE_REFL; REAL_LT_INV_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. inv q %% (\z. q %% (g:A->real^3^3) z) z) = g` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_INV]);;

let RFA_C971_KSOL_SCALE = prove
 (`!kappa top atlas (g:real->B->real^3^3) q.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < q
     ==> p2b_kappa_solution kappa (top,atlas) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cpl")
   (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
   (CONJUNCTS_THEN2 (LABEL_TAC "nf") (LABEL_TAC "kn")))))))))))
   (LABEL_TAC "slab")) THEN
  (* the metrics at all times s <= 0 *)
  SUBGOAL_THEN `!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`
  (LABEL_TAC "rmet") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `s - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
    STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t <= &0 ==> t / q <= &0` (LABEL_TAC "tq") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* flow up to 0 *)
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a / q`; `&0`;
                   `g:real->B->real^3^3`; `q:real`] RFA_RFS_FLOW_UPTO_RESCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "upto" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_MUL_RZERO]];
    (* completeness *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t / q)`; `q:real`] MFD_COMPLETE_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN
      USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "cpl" MATCH_MP_TAC THEN USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* sectional curvature *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t / q <= &0` ASSUME_TAC THENL
     [USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t / q)`; `q:real`; `x:B`; `u:real^3`; `v:real^3`]
                  RFA_C971_SEC_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    (* bounded curvature on slices *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t / q <= &0` ASSUME_TAC THENL
     [USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o SPEC `t / q`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `K / q` THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t / q)`; `q:real`; `x:B`] RFA_C971_RMNORM_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    (* non-flat slices *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t / q <= &0` ASSUME_TAC THENL
     [USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "nf" (MP_TAC o SPEC `t / q`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `x:B` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t / q)`; `q:real`; `x:B`] RFA_C971_RMNORM_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    (* kappa-noncollapsing *)
    X_GEN_TAC `r0:real` THEN USE_THEN "kn" (MP_TAC o SPEC `r0 / sqrt q`) THEN
    REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_vball; rfs_parabolic_exists;
                rfs_persists; IN_ELIM_THM] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
    ASM_CASES_TAC `t <= &0` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par") (LABEL_TAC "curv"))))) THEN
    SUBGOAL_THEN `t / q <= &0 /\ &0 < sqrt q /\ riemannian_metric atlas ((g:real->B->real^3^3) (t / q))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        USE_THEN "rmet" MATCH_MP_TAC THEN USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_ball (top,atlas) (\x. q %% (g:real->B->real^3^3) (t / q) x) x r =
      mfd_ball (top,atlas) (g (t / q)) x (r / sqrt q)`
    (LABEL_TAC "ball") THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (t / q)`; `q:real`; `x:B`; `r:real`]
                    MFD_BALL_SCALE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t / q`; `x:B`; `r / sqrt q`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REMOVE_THEN "par" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_LE_REFL] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 < r2 ==> t - r2 < t`) THEN ASM_SIMP_TAC[REAL_POW_LT];
          USE_THEN "ball" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `s <= &0 /\ riemannian_metric atlas ((g:real->B->real^3^3) s)`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "rmet" MATCH_MP_TAC THEN
                          ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        REMOVE_THEN "curv" (MP_TAC o SPECL [`q * s`; `y:B`]) THEN
        SUBGOAL_THEN `(q * s) / q = s` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        USE_THEN "ball" (fun th -> REWRITE_TAC[th]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(r / sqrt q) pow 2 = r pow 2 / q` MP_TAC THENL
           [REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
            DISCH_THEN SUBST_ALL_TAC] THEN
          CONJ_TAC THENL
           [UNDISCH_TAC `t / q - r pow 2 / q < s` THEN
            SUBGOAL_THEN `t / q - r pow 2 / q = (t - r pow 2) / q` SUBST1_TAC THENL
             [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
            UNDISCH_TAC `s <= t / q` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
            REAL_ARITH_TAC];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `(g:real->B->real^3^3) s`; `q:real`; `y:B`] RFA_C971_RMNORM_SCALE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (t / q)) x (r / sqrt q)` THEN
          REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
          DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
        SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_INV_DIV] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sqrt(q pow 3) * v` THEN
    USE_THEN "ball" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (t / q)`;
                     `mfd_ball (top,atlas) ((g:real->B->real^3^3) (t / q)) x (r / sqrt q)`;
                     `v:real`; `q:real`] MFD_HAS_VOLUME_SCALE) THEN
      ASM_REWRITE_TAC[DIMINDEX_3];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(q pow 3) = sqrt q pow 3` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; REAL_POW_ADD; REAL_POW_1; SQRT_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `kappa * (r / sqrt q) pow 3 <= v` THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < sqrt q pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt q pow 3 * (kappa * r pow 3 / sqrt q pow 3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt q pow 3` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    (* curvature bounded on compact time intervals *)
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "slab" (MP_TAC o SPEC `a / q`) THEN
    ANTS_TAC THENL [USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `K / q` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a / q <= t / q /\ t / q <= &0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN USE_THEN "tq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t / q)`; `q:real`; `x:B`] RFA_C971_RMNORM_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;


(* ------------------------------------------------------------------------- *)
(* R > 0 on kappa-solutions.  At a non-flat point with sec >= 0              *)
(* some plane has sec > 0, so R > 0 there (RFA_FRAME3); the strong maximum   *)
(* principle RFA_SCALAR_STRONG_SEC (pc_rfa_split) from the non-flat point at *)
(* time t - 1 gives R > 0 on (t - 1, 0), and at t = 0 the Harnack           *)
(* monotonicity P2AL65_KSOL_SCALAR_LE0 carries R > 0 from time -1/2.         *)
(* ------------------------------------------------------------------------- *)

let RFA_C971_KSOL_METRICS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> smooth_manifold_atlas top atlas /\
         !s. s <= &0 ==> riemannian_metric atlas (g s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
  STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_C971_SCALAR_POS_PT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v) /\
     &0 < mfd_rm_norm atlas g x
     ==> &0 < mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
    SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u v. ~collinear {vec 0,u,v} /\ &0 < mfd_sectional atlas (g:A->real^3^3) x u v`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < mfd_rm_norm atlas (g:A->real^3^3) x` THEN
    REWRITE_TAC[REAL_NOT_LT; mfd_rm_norm] THEN MATCH_MP_TAC REAL_SUP_LE THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `abs(mfd_sectional atlas (g:A->real^3^3) x (basis 1) (basis 2))` THEN
      MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(?u v. ~collinear {vec 0,u,v} /\
                           &0 < mfd_sectional atlas (g:A->real^3^3) x u v)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
      UNDISCH_TAC `!u v. ~collinear {vec 0,u,v}
                         ==> &0 <= mfd_sectional atlas (g:A->real^3^3) x u v` THEN
      DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^3^3)) /\
    SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST(chart_at atlas x))`;
    `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g:A->real^3^3)`;
    `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`; `u:real^3`; `v:real^3`]
   RFA_FRAME3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "same") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")))))))) THEN
  REWRITE_TAC[mfd_scalar] THEN USE_THEN "sum" SUBST1_TAC THEN
  USE_THEN "same" SUBST1_TAC THEN
  SUBGOAL_THEN
   `&0 <= mfd_sectional atlas (g:A->real^3^3) x u1 w1 /\
    &0 <= mfd_sectional atlas g x v1 w1`
  MP_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `!u v. ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g:A->real^3^3) x u v` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < mfd_sectional atlas (g:A->real^3^3) x u v` THEN
  REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC);;

let RFA_C971_R_POS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) t x.
     P2B_KSOL_DRDT_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     t <= &0 /\ x IN topspace top
     ==> &0 < mfd_scalar atlas (g t) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] RFA_C971_KSOL_METRICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmet")) THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cpl")
   (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
   (CONJUNCTS_THEN2 (LABEL_TAC "nf") (LABEL_TAC "kn")))))))))))
   (LABEL_TAC "slab")) THEN
  (* a non-flat point at time t - 1 has R > 0 *)
  USE_THEN "nf" (MP_TAC o SPEC `t - &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (t - &1)) x0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_C971_SCALAR_POS_PT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the strong maximum principle on (t - 2, 0) *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `t - &2`; `&0`;
                 `g:real->B->real^3^3`; `t - &1`; `x0:B`] RFA_SCALAR_STRONG_SEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "upto" (MP_TAC o SPEC `t - &2`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  ASM_CASES_TAC `t < &0` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) (--(&1) / &2)) x` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2AL65_KSOL_SCALAR_LE0 THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* A round slice.  If every sectional curvature is k > 0, then               *)
(* k g has curvature 1 in every chart (P2C_COMPONENT_CONST_CURV), so nabla  *)
(* Rm = 0, R = 6 and abs(Ric)^2 = 12 there (P2C_ROUND_MODEL); the trace     *)
(* bounds P2C_SCALAR_DERIV_TRACE give grad R = 0 and Lap R = 0, and          *)
(* P2C_SCALE_QUANTITIES scales back: grad R = Lap R = 0, 3 abs(Ric)^2 = R^2. *)
(* ------------------------------------------------------------------------- *)

let RFA_C971_ROUND = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     p2b_round (top,atlas) g
     ==> rfs_scalar_grad2 atlas g x = &0 /\ rfs_scalar_lap atlas g x = &0 /\
         &3 * rfs_ric_norm2 atlas g x = mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_round] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. k %% (g:A->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
            ==> mfd_sectional atlas (\z. k %% (g:A->real^3^3) z) y u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `k:real`; `y:A`; `u:real^3`; `v:real^3`]
                  RFA_C971_SEC_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?V phi. chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A) =
                        (V:A->bool,phi:A->real^3)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2; mfd_scalar] THEN
  ASM_REWRITE_TAC[SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(V:A->bool,phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `G = metric_local atlas (V:A->bool,phi:A->real^3) (g:A->real^3^3)` THEN
  ABBREV_TAC `y0 = (phi:A->real^3) x` THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) V) G /\
                metric_field (IMAGE phi V) (\z. k %% G z) /\ y0 IN IMAGE phi V`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "G" THEN
      UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
      EXPAND_TAC "G" THEN REWRITE_TAC[GSYM METRIC_LOCAL_CMUL] THEN
      UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                     (\z. k %% (g:A->real^3^3) z)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
      EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the unit-curvature model k g in the chart *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. k %% (g:A->real^3^3) z`; `topspace top:A->bool`; `V:A->bool`;
                 `phi:A->real^3`] P2C_COMPONENT_CONST_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(V:A->bool) INTER topspace top = V` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) V`; `\z. k %% (G:real^3->real^3^3) z`]
                P2C_ROUND_MODEL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "par") (CONJUNCTS_THEN2 (LABEL_TAC "sc")
    (CONJUNCTS_THEN2 (LABEL_TAC "rn") (K ALL_TAC)))) THEN
  (* the derivatives of the model scalar curvature vanish at y0 *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) V`; `\z. k %% (G:real^3->real^3^3) z`; `y0:real^3`]
                P2C_SCALAR_DERIV_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ltnorm2 5 (\z. k %% (G:real^3->real^3^3) z)
            (lnabla 4 (\z. k %% G z) (lrm4 (\z. k %% G z))) y0 = &0 /\
    ltnorm2 6 (\z. k %% (G:real^3->real^3^3) z)
            (lnabla 5 (\z. k %% G z) (lnabla 4 (\z. k %% G z) (lrm4 (\z. k %% G z)))) y0 =
    &0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_LTNORM2_ZERO THEN GEN_TAC THENL
     [USE_THEN "par" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`5`; `IMAGE (phi:A->real^3) V`; `\z. k %% (G:real^3->real^3^3) z`;
                   `lnabla 4 (\z. k %% (G:real^3->real^3^3) z) (lrm4 (\z. k %% G z))`;
                   `\(x:real^3) (u:num->real^3). &0`] RFA_EQON_LNABLA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN
      USE_THEN "par" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[rfa_eqon] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN
      ASM_REWRITE_TAC[LRG_LNABLA_ZERO] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lgrad2 (\z. k %% (G:real^3->real^3^3) z) (lscalar (\z. k %% G z)) y0 = &0 /\
    llap (\z. k %% (G:real^3->real^3^3) z) (lscalar (\z. k %% G z)) y0 = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (phi:A->real^3) V`; `\z. k %% (G:real^3->real^3^3) z`;
                     `lscalar (\z. k %% (G:real^3->real^3^3) z)`; `y0:real^3`] LGRAD2_POS) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `llap (\z. k %% (G:real^3->real^3^3) z) (lscalar (\z. k %% G z)) y0`
                  REAL_LE_POW_2) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `llap (\z. k %% (G:real^3->real^3^3) z) (lscalar (\z. k %% G z)) y0 pow 2 = &0`
      MP_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ]]];
    ALL_TAC] THEN
  (* back to g *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) V`; `G:real^3->real^3^3`; `k:real`; `y0:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z u. lricci (G:real^3->real^3^3) z (u 1) (u 2)) = lric2 G` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lric2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  USE_THEN "sc" (fun th -> ASSUME_TAC(MATCH_MP th
    (ASSUME `(y0:real^3) IN IMAGE (phi:A->real^3) V`))) THEN
  USE_THEN "rn" (fun th -> ASSUME_TAC(MATCH_MP th
    (ASSUME `(y0:real^3) IN IMAGE (phi:A->real^3) V`))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The estimate at R = 1.  abs(Ric)^2 <= R^2 for sec >= 0                    *)
(* (Ricci eigenframe, RFA_P3_FRAME_SCALARS); roundness is scale invariant;  *)
(* for a non-round kappa-solution h with R(x,0) = 1, Prop 9.58 and Lemma    *)
(* 9.65 bound R on B(x,1) at time 0, KSOL_RM_LE0 bounds abs(Rm) on          *)
(* B(x,1) x (-1,0], and Shi (RFA_C2_SHI_SCALED) with the trace bounds        *)
(* P2C_SCALAR_DERIV_TRACE gives |grad R|^2 <= C1 and |Lap R + 2|Ric|^2| <= C1 *)
(* at (x,0) (RFA_C971_NORMALIZED).                                           *)
(* ------------------------------------------------------------------------- *)

let RFA_C971_RICNORM_LE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= rfs_ric_norm2 atlas g x /\
         rfs_ric_norm2 atlas g x <= mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_ric_norm2; mfd_scalar] THEN
  ABBREV_TAC `G = metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)` THEN
  ABBREV_TAC `y = SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x` THEN
  ABBREV_TAC `U = IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))` THEN
  SUBGOAL_THEN `metric_field U (G:real^3->real^3^3) /\ (y:real^3) IN U` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "y"; "U"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional (G:real^3->real^3^3) y u v`
  (LABEL_TAC "sec") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["G"; "y"] THEN
    REWRITE_TAC[GSYM mfd_sectional] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z u. lricci (G:real^3->real^3^3) z (u 1) (u 2)) = lric2 G` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lric2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_P3_FRAME_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
  SUBGOAL_THEN
   `!i j n. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= n /\ n <= 3 /\
            ~(i = j) /\ ~(i = n) /\ ~(j = n)
            ==> &0 <= lpcurv (G:real^3->real^3^3) y (\m. transp (S:real^3^3) ** basis i)`
  (LABEL_TAC "pnn") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> (transp (S:real^3^3) ** basis a) dot
                ((G:real^3->real^3^3) y ** (transp S ** basis b)) = if a = b then &1 else &0`
    (LABEL_TAC "on") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `a:num`; `b:num`]
                    RFA_GFRAME_ORTHO) THEN
      ASM_REWRITE_TAC[DIMINDEX_3];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `transp (S:real^3^3) ** basis j`; `transp (S:real^3^3) ** basis n`;
                   `transp (S:real^3^3) ** basis i`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL [USE_THEN "on" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "sec" MATCH_MP_TAC THEN
    MATCH_MP_TAC RFA_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    USE_THEN "on" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "pnn" (fun th -> MP_TAC(SPECL [`1`; `2`; `3`] th) THEN
    MP_TAC(SPECL [`2`; `1`; `3`] th) THEN MP_TAC(SPECL [`3`; `1`; `2`] th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y (\m. transp (S:real^3^3) ** basis 1)` THEN
  ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y (\m. transp (S:real^3^3) ** basis 2)` THEN
  ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y (\m. transp (S:real^3^3) ** basis 3)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= p1 * p2 /\ &0 <= p1 * p3 /\ &0 <= p2 * p3 /\
                &0 <= p1 pow 2 /\ &0 <= p2 pow 2 /\ &0 <= p3 pow 2`
  MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_C971_ROUND_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < q /\
     p2b_round (top,atlas) (\z. q %% g z)
     ==> p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_round] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `q * k` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `q:real`; `x:A`; `u:real^3`; `v:real^3`] RFA_C971_SEC_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC);;

let RFA_C971_LRM_TRACE = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U
     ==> lgrad2 G (lscalar G) y <= &9 * lrm_deriv_norm2 1 G y /\
         llap G (lscalar G) y pow 2 <= &27 * lrm_deriv_norm2 2 G y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lrm_deriv_norm2 1 (G:real^3->real^3^3) y = ltnorm2 5 G (lnabla 4 G (lrm4 G)) y /\
    lrm_deriv_norm2 2 (G:real^3->real^3^3) y =
    ltnorm2 6 G (lnabla 5 G (lnabla 4 G (lrm4 G))) y`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[lrm_deriv_norm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[TWO; ONE; lnabla_iter; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
                P2C_SCALAR_DERIV_TRACE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let RFA_C971_NORMALIZED = prove
 (`!(w:B->bool).
     P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w
     ==> ?C1. &0 < C1 /\
           !kappa top atlas (h:real->B->real^3^3) x.
             p2b_kappa_solution kappa (top,atlas) h /\ p2b_ksep top atlas /\
             ~p2b_round (top,atlas) (h(&0)) /\ x IN topspace top /\
             mfd_scalar atlas (h(&0)) x = &1
             ==> rfs_scalar_grad2 atlas (h(&0)) x <= C1 /\
                 abs(rfs_scalar_lap atlas (h(&0)) x + &2 * rfs_ric_norm2 atlas (h(&0)) x)
                 <= C1`,
  GEN_TAC THEN REWRITE_TAC[P2B_LEMMA_9_65_STATEMENT; P2B_PROP_9_58_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l965") (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p958")))
    ASSUME_TAC)) THEN
  USE_THEN "l965" (MP_TAC o SPECL [`kappa0:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (LABEL_TAC "cr")) THEN
  ABBREV_TAC `K = abs Cr / &2 + &1` THEN
  SUBGOAL_THEN `&0 < K /\ Cr / &2 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `K:real`; `&1`; `&1`] (INST_TYPE [`:B`,`:A`] RFA_C2_SHI_SCALED)) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi1"))) THEN
  MP_TAC(ISPECL [`2`; `K:real`; `&1`; `&1`] (INST_TYPE [`:B`,`:A`] RFA_C2_SHI_SCALED)) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `D2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi2"))) THEN
  EXISTS_TAC `max (&9 * D1) (sqrt(&27 * D2) + &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < max a (s + &2)`) THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `h:real->B->real^3^3`; `x:B`] THEN
  STRIP_TAC THEN
  USE_THEN "p958" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `h:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `h:real->B->real^3^3`] RFA_C971_KSOL_METRICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmet")) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `h:real->B->real^3^3`] P2B_KSOL_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (CONJUNCTS_THEN2 (LABEL_TAC "cpl") (CONJUNCTS_THEN2 (LABEL_TAC "sec") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((h:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [USE_THEN "rmet" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* R <= Cr on B(x,1) at time 0, abs(Rm) <= K on B(x,1) x (-1,0] *)
  SUBGOAL_THEN
   `!t y. --(&1) < t /\ t <= &0 /\ y IN mfd_ball (top,atlas) ((h:real->B->real^3^3) (&0)) x
                                                  (&1 / sqrt(&1))
          ==> mfd_rm_norm atlas (h t) y <= K * &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_1; REAL_DIV_1; REAL_MUL_RID] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((h:real->B->real^3^3) (&0)) x (&1)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas ((h:real->B->real^3^3) (&0)) y / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AL65_KSOL_RM_LE0 THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `r <= Cr /\ Cr / &2 <= k ==> r / &2 <= k`) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "cr" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `x:B`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top (top closure_of mfd_ball (top,atlas) ((h:real->B->real^3^3) (&0)) x
                                            (&1 / sqrt(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cpl" MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:B) IN mfd_ball (top,atlas) ((h:real->B->real^3^3) (&0)) x ((&1 / &2) / sqrt(&1))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL; SQRT_1; REAL_DIV_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_flow_upto (top,atlas) (--(&1)) (&0) (h:real->B->real^3^3) /\
    &1 <= &1 * (&0 - --(&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "upto" MATCH_MP_TAC THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "shi1" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `--(&1)`; `&0`; `h:real->B->real^3^3`; `x:B`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN(MP_TAC o SPEC `x:B`)] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "shi2" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `--(&1)`; `&0`; `h:real->B->real^3^3`; `x:B`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN(MP_TAC o SPEC `x:B`)] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_ONE; REAL_MUL_RID]) THEN
  (* the trace bounds and abs(Ric)^2 <= R^2 = 1 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                               ((h:real->B->real^3^3) (&0))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`]
                RFA_C971_LRM_TRACE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool)
                                     ((h:real->B->real^3^3) (&0))` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM rfs_scalar_grad2; GSYM rfs_scalar_lap] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(h:real->B->real^3^3) (&0)`; `x:B`] RFA_C971_RICNORM_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&9 * lrm_deriv_norm2 1
                 (metric_local atlas (chart_at atlas x) ((h:real->B->real^3^3) (&0)))
                 (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(rfs_scalar_lap atlas ((h:real->B->real^3^3) (&0)) x) <= sqrt(&27 * D2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&27 * lrm_deriv_norm2 2
                 (metric_local atlas (chart_at atlas x) ((h:real->B->real^3^3) (&0)))
                 (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main theorem RFA_C971_MAIN.  The derivative quantities of g are q^3,  *)
(* q^2 and q^2 times those of q g (RFA_C971_DERIV_SCALE,                     *)
(* P2C_SCALE_QUANTITIES).  At (x,t) with q = R(x,t) > 0: if g(t) is round    *)
(* the bounds hold with C >= 1 (RFA_C971_ROUND); otherwise                   *)
(* h(s) = q g(s/q + t) is a non-round kappa-solution with R(x,0) = 1         *)
(* (P2AK0_KSOL_SHIFT, RFA_C971_KSOL_SCALE) and RFA_C971_NORMALIZED scales    *)
(* back.                                                                     *)
(* ------------------------------------------------------------------------- *)

let RFA_C971_DERIV_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) q x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < q
     ==> rfs_scalar_grad2 atlas g x = q pow 3 * rfs_scalar_grad2 atlas (\z. q %% g z) x /\
         rfs_scalar_lap atlas g x = q pow 2 * rfs_scalar_lap atlas (\z. q %% g z) x /\
         rfs_ric_norm2 atlas g x = q pow 2 * rfs_ric_norm2 atlas (\z. q %% g z) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2; METRIC_LOCAL_CMUL] THEN
  ABBREV_TAC `G = metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `!H:real^3->real^3^3. (\z u. lricci H z (u 1) (u 2)) = lric2 H`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; lric2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`; `G:real^3->real^3^3`; `q:real`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
                P2C_SCALE_QUANTITIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "G" THEN
      UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let RFA_C971_MAIN = prove
 (`!w:B->bool. P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w
               ==> P2B_COR_9_71_STATEMENT w`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P2B_KSOL_DRDT_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_KSOL_DRDT_FROM_HARNACK THEN REWRITE_TAC[RFA_P2B_REQ_RFA_HARNACK];
    ALL_TAC] THEN
  MP_TAC(SPEC `w:B->bool` RFA_C971_NORMALIZED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "norm"))) THEN
  REWRITE_TAC[P2B_COR_9_71_STATEMENT] THEN
  EXISTS_TAC `max (&1) (max C1 (sqrt C1))` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x:B`; `t:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `C = max (&1) (max C1 (sqrt C1))` THEN
  SUBGOAL_THEN `&1 <= C /\ C1 <= C /\ sqrt C1 <= C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] RFA_C971_KSOL_METRICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmet")) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) t)` ASSUME_TAC THENL
   [USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) t) x` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_C971_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = mfd_scalar atlas ((g:real->B->real^3^3) t) x` THEN
  SUBGOAL_THEN `&0 <= sqrt q /\ &0 <= q * sqrt q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `p2b_round (top,atlas) ((g:real->B->real^3^3) t)` THENL
   [(* round: the derivatives vanish *)
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `x:B`] RFA_C971_ROUND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SQRT_0; REAL_ADD_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= q pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * q pow 2` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the shifted and rescaled solution *)
  SUBGOAL_THEN
   `p2b_kappa_solution kappa (top,atlas) (\s y. q %% (g:real->B->real^3^3) (s / q + t) y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\s. (g:real->B->real^3^3) (s + t)`; `q:real`] RFA_C971_KSOL_SCALE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AK0_KSOL_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "norm" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `\s y. q %% (g:real->B->real^3^3) (s / q + t) y`;
    `x:B`]) THEN
  REWRITE_TAC[REAL_ARITH `!q t:real. &0 / q + t = t`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~p2b_round (top,atlas) ((g:real->B->real^3^3) t)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC RFA_C971_ROUND_SCALE THEN EXISTS_TAC `q:real` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) t`; `q:real`; `x:B`] RFA_C971_SCALAR_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t`; `q:real`; `x:B`] RFA_C971_DERIV_SCALE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  ABBREV_TAC `G2 = rfs_scalar_grad2 atlas (\y. q %% (g:real->B->real^3^3) t y) x` THEN
  ABBREV_TAC `L2 = rfs_scalar_lap atlas (\y. q %% (g:real->B->real^3^3) t y) x` THEN
  ABBREV_TAC `N2 = rfs_ric_norm2 atlas (\y. q %% (g:real->B->real^3^3) t y) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(q pow 3 * C1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `sqrt(q pow 3) = q * sqrt q` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; REAL_POW_ADD; REAL_POW_1; SQRT_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(q * s) * a <= (q * s) * c ==> (q * s) * a <= c * q * s`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 * L2 + &2 * q pow 2 * N2 = q pow 2 * (L2 + &2 * N2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`] THEN
  MATCH_MP_TAC(REAL_ARITH `q2 * a <= q2 * c ==> q2 * a <= c * q2`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The route form: the route statement P2B_COR_9_71_ROUTE_STATEMENT of       *)
(* pc_p2b_chainstmts is RFA_C971_MAIN as an implication.                     *)
(* ------------------------------------------------------------------------- *)

let RFA_P2B_COR_9_71_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_71_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_COR_9_71_ROUTE_STATEMENT; RFA_C971_MAIN]);;

