(* ========================================================================= *)
(* Unit pc_p3_c172e: MT Lemma 17.2, part D continued (D5-D6):                *)
(* the exit argument for the evolving cap region, the transfer of curves     *)
(* through the cap parametrization, the exclusion of the neck alternatives   *)
(* of Thm 12.32 at the preimage of x, and the transfer of the standard        *)
(* solution's cap (P2B_PROP_9_79_CAP_FIX) to a (C,eps)-cap with x in its core *)
(* (MT pp. 400-401, Claim 17.4 replaced by the exit argument).                *)
(*                                                                         *)
(* The inner neck of the evolving cap region with its location (adapted      *)
(* from P3N_INNER_NECK of pc_p3_s16disc, with the location conjunct): the    *)
(* level set Phi{dist = d0} is the central sphere of an eps-neck of the       *)
(* slice whose image lies in Phi of the shell d0 - 1/eps < dist < d0 + 1/eps, *)
(* with R(x) h^2 (1 - s) <= 1 + eps/8 at its centre x.                        *)
(* ========================================================================= *)

needs "src/pc_p3_c172d.ml";;
needs "src/pc_p3_s16disc.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2b_capfix.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_INNER_NECK_LOC = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd.
             p3_std_initial g0 A0 /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2)
             ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                       IMAGE e (sphere(vec 0,&1)) = IMAGE Phi {x | p3_std_dist g0 x = d0} /\
                       IMAGE e (rfs_neck_dom eps) SUBSET
                       IMAGE Phi {x | d0 - inv eps < p3_std_dist g0 x /\
                                      p3_std_dist g0 x < d0 + inv eps} /\
                       mfd_scalar atlas g x * (h pow 2 * (&1 - s)) <= &1 + eps / &8`,
  GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (ISPECL [`K0:real`; `eps / &8`] LCK_CURVATURE_STABILITY)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "STAB"))) THEN
  MP_TAC(SPEC `rfs_kreg eps` P3N_CLOSE_COMBINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "COMB"))) THEN
  ABBREV_TAC `bt = min eta (eps / &8) / &2` THEN
  SUBGOAL_THEN `&0 < bt /\ bt < eta /\ bt <= eps / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bt" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + sqrt M` ASSUME_TAC THENL
   [MP_TAC(SPEC `M:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (bt / (&1 + sqrt M))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `dd pow 2 <= &1 / &4 /\ dd * (&1 + sqrt M) <= bt` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dd <= min (&1 / &2) (bt / (&1 + sqrt M))` THEN
    REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `Phi:real^3->A`; `m:real`;
                 `s:real`; `eps:real`; `d0:real`] P3N_INNER_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `a = sqrt(&1 - s)` THEN
  ABBREV_TAC `c = exp((A0 + &4 - d0) / sqrt(&2))` THEN
  ABBREV_TAC `V = {x:real^3 | sqrt(&2) * log c - sqrt(&2) * a * inv(sqrt(&2) * eps) <
                      A0 + &4 - p3_std_dist g0 x /\
                      A0 + &4 - p3_std_dist g0 x <
                      sqrt(&2) * log c + sqrt(&2) * a * inv(sqrt(&2) * eps)}` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log c = A0 + &4 - d0 /\
                sqrt(&2) * a * inv(sqrt(&2) * eps) = a / eps /\
                &0 < a / eps /\ a / eps <= inv eps /\ a <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `a <= &1` ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
                      REWRITE_TAC[SQRT_1; REAL_LE_REFL]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[LOG_EXP] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&2)`; `&0 < eps`] THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= rfs_kreg eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  ABBREV_TAC `H = \z:real^3. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) g z` THEN
  ABBREV_TAC `C = mpullback (p3_std_nc g0 A0) (cylinder_flow s)` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field V (H:real^3->real^3^3) /\ metric_field V (G0:real^3->real^3^3) /\
                metric_field V (C:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < m}` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "H" THEN MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; REAL_LT_INV_EQ; REAL_POW_LT; ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXPAND_TAC "C" THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC
       [`{y:real^3 | exp((sqrt(&2) * log c - sqrt(&2) * a * inv(sqrt(&2) * eps)) / sqrt(&2))
                     < norm y /\
                     norm y <
                     exp((sqrt(&2) * log c + sqrt(&2) * a * inv(sqrt(&2) * eps)) / sqrt(&2))}`;
        `p3s_ncinv g0 A0`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM annulus; OPEN_ANNULUS];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM NORM_POS_LT] THEN
          MESON_TAC[REAL_EXP_POS_LT; REAL_LT_TRANS]];
        EXPAND_TAC "V" THEN MATCH_MP_TAC P3S_NC_DIFFEO THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN V ==> lck_dist2 k C H w <= bt pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= lck_dist2 k (C:real^3->real^3^3) H w` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (C:real^3->real^3^3) H w) <= bt` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd * (&1 + sqrt M)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "COMB" MATCH_MP_TAC THEN
      EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `G0:real^3->real^3^3` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `lck_dist2 k (C:real^3->real^3^3) H w = sqrt(lck_dist2 k C H w) pow 2`
    SUBST1_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e = (Phi:real^3->A) o p3n_psi g0 A0 c a` THEN
  ABBREV_TAC `X = \z:real^3. (inv(&1 - s) * inv(h pow 2)) %% rfs_pullback atlas (e:real^3->A) g z` THEN
  SUBGOAL_THEN `open(rfs_neck_dom eps) /\
                rfs_neck_dom eps = annulus (exp(--(inv(sqrt(&2) * eps))))
                                           (exp(inv(sqrt(&2) * eps)))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (rfs_pullback atlas (e:real^3->A) g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (X:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (cylinder_flow (&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < inv(&1 - s) * inv(h pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "X" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) X y <= bt pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3n_psi g0 A0 c a y IN (V:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on; FUN_IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `V:real^3->bool`; `rfs_neck_dom eps`; `p3n_psi g0 A0 c a`;
                   `\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)`;
                   `C:real^3->real^3^3`; `H:real^3->real^3^3`; `y:real^3`]
                  LCK_DIST2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (p3n_psi g0 A0 c a) (rfs_neck_dom eps) = (V:real^3->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    SUBGOAL_THEN
       `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
          (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y =
        lck_dist2 k (mpullback (p3n_psi g0 A0 c a) C) (mpullback (p3n_psi g0 A0 c a) H) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN EXPAND_TAC "C" THEN MATCH_MP_TAC P3N_PSI_CYL THEN
        EXISTS_TAC `inv(sqrt(&2) * eps)` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
        EXPAND_TAC "H" THEN REWRITE_TAC[P3S_MPULLBACK_CMUL; ETA_AX] THEN AP_TERM_TAC THEN
        EXPAND_TAC "e" THEN MATCH_MP_TAC P3N_RFS_PULLBACK_O THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `{x:real^3 | p3_std_dist g0 x < m}`;
          `rfs_neck_dom eps`; `\x:real^3. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)`] THEN
        REWRITE_TAC[ASSUME `IMAGE (p3n_psi g0 A0 c a) (rfs_neck_dom eps) = (V:real^3->bool)`] THEN
        SUBGOAL_THEN `z IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
                   (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y <= bt pow 2`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!w:real^3. w IN (V:real^3->bool)
                             ==> lck_dist2 k (C:real^3->real^3^3) (H:real^3->real^3^3) w
                                 <= bt pow 2`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps`;
                   `\z:real^3. (&1 - s) %% cylinder_flow (&0) z`;
                   `\z:real^3. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z`;
                   `inv(&1 - s)`; `y:real^3`] P3N_LCK_SCALE_GE1) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]];
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z:real^3. inv(&1 - s) %% (&1 - s) %% cylinder_flow (&0) z) = cylinder_flow (&0) /\
                  (\z:real^3. inv(&1 - s) %% inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) = X`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN X_GEN_TAC `w:real^3` THEN
        SUBGOAL_THEN `inv(&1 - s) * (&1 - s) = &1` SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[MATRIX_CMUL_LID]];
        EXPAND_TAC "X" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC]];
      ALL_TAC] THEN
    UNDISCH_TAC `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
                   (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y <= bt pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN rfs_neck_dom eps /\ ~(basis 1:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; NORM_BASIS; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = lscalar (X:real^3->real^3^3) (basis 1)` THEN
  SUBGOAL_THEN `abs(lam - &1) <= eps / &8` ASSUME_TAC THENL
   [SUBGOAL_THEN `lscalar (cylinder_flow (&0)) (basis 1:real^3) = &1` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC P3N_CYL0_SCALAR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXPAND_TAC "lam" THEN
    USE_THEN "STAB" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                     `X:real^3->real^3^3`; `basis 1:real^3`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(ASSUME `!y:real^3. ~(y = vec 0)
                               ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) (basis 1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
          REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `bt pow 2` THEN CONJ_TAC THENL
           [MATCH_MP_TAC(ASSUME `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y <= bt pow 2`) THEN
            FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
            UNDISCH_TAC `&0 < bt` THEN UNDISCH_TAC `bt < eta` THEN REAL_ARITH_TAC]]];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1 + eps / &8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs(lam - &1) <= eps / &8` THEN UNDISCH_TAC `eps <= &1 / &4` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 * (&1 - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    UNDISCH_TAC `s < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) = lam / (h pow 2 * (&1 - s)) /\
    (\y. mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) %% rfs_pullback atlas e g y) =
    (\y. lam %% (X:real^3->real^3^3) y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_pullback atlas (e:real^3->A) g =
                  (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN
      X_GEN_TAC `w:real^3` THEN
      SUBGOAL_THEN `(h pow 2 * (&1 - s)) * inv(&1 - s) * inv(h pow 2) = &1` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(h pow 2 = &0) /\ ~(&1 - s = &0)` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_NZ THEN UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
            UNDISCH_TAC `s < &1` THEN REAL_ARITH_TAC];
          CONV_TAC REAL_FIELD];
        REWRITE_TAC[MATRIX_CMUL_LID]];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) = lam / (h pow 2 * (&1 - s))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `basis 1:real^3`]
                    APX_PULLBACK_SCALAR_GEN) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[ASSUME `rfs_pullback atlas (e:real^3->A) g =
                          (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)`] THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `X:real^3->real^3^3`; `h pow 2 * (&1 - s)`;
                     `basis 1:real^3`] LSCALAR_SCALE) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "lam" THEN REFL_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `rfs_pullback atlas (e:real^3->A) g =
                        (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)`] THEN
    REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN X_GEN_TAC `w:real^3` THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < h pow 2 * (&1 - s)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y
                      <= eps pow 2 / &4`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps`; `cylinder_flow (&0)`; `X:real^3->real^3^3`;
                   `lam:real`; `y:real^3`] LCK_DIST_RESCALE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) <= bt`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < bt` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(ASSUME `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y <= bt pow 2`) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y)
                  <= eps / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) +
                  abs(lam - &1) * sqrt(&3)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * (eps / &8) + (eps / &8) * &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `lam <= &1 + eps / &8` THEN UNDISCH_TAC `eps <= &1 / &4` THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
          EXISTS_TAC `rfs_neck_dom eps` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) <= bt` THEN
          UNDISCH_TAC `bt <= eps / &8` THEN REAL_ARITH_TAC;
          REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC];
        UNDISCH_TAC `&0 < eps` THEN UNDISCH_TAC `eps <= &1 / &4` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y)
                pow 2` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps / &2) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(e:real^3->A) (basis 1)` THEN EXISTS_TAC `e:real^3->A` THEN
  REWRITE_TAC[rfs_neck] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    REWRITE_TAC[ASSUME `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) =
                        lam / (h pow 2 * (&1 - s))`] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `(\y. mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) %%
                             rfs_pullback atlas e g y) =
                        (\y. lam %% (X:real^3->real^3^3) y)`;
                ASSUME `rfs_kreg eps = k`; rfs_close_on] THEN
    EXISTS_TAC `eps pow 2 / &4` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    EXPAND_TAC "e" THEN REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (p3n_psi g0 A0 c a) (rfs_neck_dom eps) = (V:real^3->bool)`
    SUBST1_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) =
                        lam / (h pow 2 * (&1 - s))`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

(* ========================================================================= *)
(* The exit argument (replaces MT Claim 17.4).  A C^1 curve in               *)
(* the slice from Phi{dist < d0} to outside Phi{dist < d0 + 1/eps} crosses   *)
(* the central sphere Phi{dist = d0} of the inner neck and then leaves the   *)
(* neck, so its length is at least h sqrt(1 - s) / (2 eps).                  *)
(* ========================================================================= *)

let P3H_UNIT_SPHERE_NECK_DOM = prove
 (`!eps u:real^3. &0 < eps /\ norm u = &1 ==> u IN rfs_neck_dom eps /\ apx_sval u = &0`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]]);;

let P3H_EXIT_ARITH = prove
 (`!R h s eps. &0 < R /\ &0 < h /\ &0 <= s /\ s < &1 /\ &0 < eps /\ eps <= &1 / &4 /\
               R * (h pow 2 * (&1 - s)) <= &1 + eps / &8
               ==> h * sqrt(&1 - s) / (&2 * eps) <=
                   sqrt(&1 - eps) * inv(sqrt R) * (inv eps - &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `h * sqrt(&1 - s) / &2 <= sqrt(&1 - eps) * inv(sqrt R)` MP_TAC THENL
   [SUBGOAL_THEN `h * sqrt(&1 - s) / &2 = sqrt(h pow 2 * (&1 - s) / &4) /\
                  sqrt(&1 - eps) * inv(sqrt R) = sqrt((&1 - eps) / R)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_div; SQRT_MUL; SQRT_INV] THEN
        SUBGOAL_THEN `sqrt(h pow 2) = h /\ sqrt(&4) = &2` (CONJUNCTS_THEN SUBST1_TAC) THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
            SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
            MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        REWRITE_TAC[real_div; SQRT_MUL; SQRT_INV]];
      ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `h pow 2 * (&1 - s) / &4 * R = (R * (h pow 2 * (&1 - s))) / &4`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `h * sqrt(&1 - s) / (&2 * eps) = (h * sqrt(&1 - s) / &2) * inv eps`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV) [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]);;

let P3H_CAP_EXIT01 = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd gamma.
             p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) IN IMAGE Phi {x | p3_std_dist g0 x < d0} /\
             ~(gamma(&1) IN IMAGE Phi {x | p3_std_dist g0 x < d0 + inv eps})
             ==> h * sqrt(&1 - s) / (&2 * eps) <= mfd_length atlas g gamma (&0) (&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_INNER_NECK_LOC) THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IN"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "IN" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m:real`;
     `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xn:A` (X_CHOOSE_THEN `en:real^3->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d0 /\ &0 < m` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 m` THEN
  ABBREV_TAC `r0 = p3s_rad_rinv g0 d0` THEN
  ABBREV_TAC `r1 = p3s_rad_rinv g0 (d0 + inv eps)` THEN
  SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < m} = ball(vec 0,R) /\
                {x:real^3 | p3_std_dist g0 x < d0} = ball(vec 0,r0) /\
                {x:real^3 | p3_std_dist g0 x = d0} = sphere(vec 0,r0) /\
                {x:real^3 | p3_std_dist g0 x < d0 + inv eps} = ball(vec 0,r1) /\
                &0 < r0 /\ r0 < r1 /\ r1 < R` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "r0"; "r1"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_STD_BALL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_STD_BALL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_STD_SPHERE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_STD_BALL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d0:real`] P3S_RINV_FACTS) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P3N_STD_RINV_LT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3N_STD_RINV_LT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,R)) (Phi:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(&0) IN IMAGE (Phi:real^3->A) (ball(vec 0,r0)) /\
                ~((gamma:real->A)(&1) IN IMAGE (Phi:real^3->A) (ball(vec 0,r1))) /\
                IMAGE (en:real^3->A) (sphere(vec 0,&1)) = IMAGE Phi (sphere(vec 0,r0)) /\
                IMAGE (en:real^3->A) (rfs_neck_dom eps) SUBSET IMAGE Phi (ball(vec 0,r1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (Phi:real^3->A) {x | d0 - inv eps < p3_std_dist g0 x /\
                                             p3_std_dist g0 x < d0 + inv eps}` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{x:real^3 | p3_std_dist g0 x < d0 + inv eps} = ball(vec 0,r1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Phi:real^3->A`;
                 `r0:real`; `R:real`] P3N_BALL_CORE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,R)`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Phi':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (Phi:real^3->A) (ball(vec 0,r0))`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~((gamma:real->A)(&1) IN IMAGE (Phi:real^3->A) (ball(vec 0,r1)))` THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> ~((x:A) IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (IMAGE (Phi:real^3->A) (cball(vec 0,r0)))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,R))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN IMAGE (Phi:real^3->A) (cball(vec 0,r0))` MP_TAC THENL
   [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) (ball(vec 0,r0))` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN IMAGE (en:real^3->A) (sphere(vec 0,&1))` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN IMAGE (Phi:real^3->A) (ball(vec 0,r0)))` THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,r0)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_CBALL_0; IN_SPHERE_0; IN_IMAGE; IN_BALL_0] THEN
    REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`eps:real`; `u:real^3`] P3H_UNIT_SPHERE_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `xn:A`; `en:real^3->A`; `u:real^3`; `gamma:real->A`;
                 `t1:real`; `&1`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~((gamma:real->A)(&1) IN IMAGE (Phi:real^3->A) (ball(vec 0,r1)))` THEN
      UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom eps) SUBSET
                   IMAGE (Phi:real^3->A) (ball(vec 0,r1))` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t1:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^3^3) gamma (&0) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) xn`; `h:real`; `s:real`; `eps:real`]
               P3H_EXIT_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_CAP_EXIT = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd gamma a b.
             p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
             mfd_c1_curve (top,atlas) gamma a b /\
             gamma a IN IMAGE Phi {x | p3_std_dist g0 x < d0} /\
             ~(gamma b IN IMAGE Phi {x | p3_std_dist g0 x < d0 + inv eps})
             ==> h * sqrt(&1 - s) / (&2 * eps) <= mfd_length atlas g gamma a b`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_CAP_EXIT01) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `b:real`] GRGD_AFFINE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`] GRGD_AFFINE_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "E" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
                        `Phi:real^3->A`; `m:real`; `G0:real^3->real^3^3`; `d0:real`;
                        `dd:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Short curves from Phi{dist < d0} stay in Phi{dist < d0 + 1/eps}. *)

let P3H_SHORT_CURVE_STAYS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd gamma.
             p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) IN IMAGE Phi {x | p3_std_dist g0 x < d0} /\
             mfd_length atlas g gamma (&0) (&1) < h * sqrt(&1 - s) / (&2 * eps)
             ==> !t. &0 <= t /\ t <= &1
                     ==> gamma t IN IMAGE Phi {x | p3_std_dist g0 x < d0 + inv eps}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_CAP_EXIT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < d0} SUBSET
                IMAGE Phi {x | p3_std_dist g0 x < d0 + inv eps}` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "E" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m:real`;
     `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `gamma:real->A`;
     `&0`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `t:real`; `&1`] APX_LENGTH_PREFIX_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The neck alternatives of Thm 12.32 at (q,t') (D6).  An                   *)
(* evolving neck of normalized length len at (x,t) in a flow view on [0,1)  *)
(* has len <= t R(x,t) (its region persists back to t - len/R(x,t) >= 0).   *)
(* ========================================================================= *)

let P3H_FLOWVIEW_NECK_TIME = prove
 (`!top atlas (G:real->A->real^3^3) eps x t len (e:real^3->A).
     rfs_evolving_neck (rfs_flow_view (top,atlas) {s | &0 <= s /\ s < &1} G)
                       eps x t len e
     ==> len <= t * mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (G t) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; rfs_persists] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  ABBREV_TAC `R = mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((G:real->A->real^3^3) t) x` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t - len / R < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `t * R < len` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_RDIV_EQ; REAL_ARITH `a - b < &0 <=> a < b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < len / R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "per" (MP_TAC o SPEC `min t ((t - len / R) / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(min t ((t - len / R) / &2) IN {s | &0 <= s /\ s < &1})`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
  MP_TAC(SPECL [`eps:real`; `basis 1:real^3`] P3H_UNIT_SPHERE_NECK_DOM) THEN
  ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN SET_TAC[]);;

(* The strong-neck alternative (length 1 + eps1) of Thm 12.32 at (q,t') is  *)
(* impossible: t' R_G(q,t') >= 1 + eps1 but R_G(q,t') is close to           *)
(* h^2 R(x,ts) = Q~ = 1/t'.                                                   *)

let P3H_CASE3_ARITH = prove
 (`!Rs Rh tp Kr dq len.
     &0 < tp /\ &1 <= Rh /\ Rh * tp = &1 /\ &0 <= Kr /\ &0 < dq /\ &0 < len /\
     &72 * sqrt Kr * dq <= &1 / &2 /\
     abs(Rh - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq /\
     len <= tp * Rs /\ &1 + &72 * dq < len * (&1 - &72 * sqrt Kr * dq)
     ==> F`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x = &72 * sqrt Kr * dq` THEN
  SUBGOAL_THEN `&0 < Rs` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `tp * Rs <= tp * &0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tp <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 * tp <= Rh * tp` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rs * (&1 - x) <= Rh + &72 * dq` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(Rh - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN EXPAND_TAC "x" THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tp * (Rs * (&1 - x)) <= tp * (Rh + &72 * dq)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `len * (&1 - x) <= (tp * Rs) * (&1 - x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tp * &72 * dq <= &72 * dq` ASSUME_TAC THENL
   [SUBGOAL_THEN `tp * (&72 * dq) <= &1 * (&72 * dq)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tp * (Rh + &72 * dq) = &1 + tp * &72 * dq` ASSUME_TAC THENL
   [UNDISCH_TAC `Rh * tp = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(tp * Rs) * (&1 - x) = tp * (Rs * (&1 - x))` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Transport of curves through the cap parametrization.  A C^1              *)
(* curve of the slice inside Phi(S) lifts to a C^1 curve of real^3 in S; if *)
(* h^-2 Phi^* g is C^0-close to G0 on S, its G0-length is at most           *)
(* sqrt 2 / h times the g-length.                                            *)
(* ========================================================================= *)

let P3H_CURVE_TRANSPORT = prove
 (`!top atlas (g:A->real^3^3) S (Phi:real^3->A) G0 h k gamma.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S Phi /\ metric_field S G0 /\ &0 < h /\
     (!y. y IN S
          ==> lck_dist2 k G0 (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= &1 / &4) /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     (!t. &0 <= t /\ t <= &1 ==> gamma t IN IMAGE Phi S)
     ==> ?c. mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
             (!t. &0 <= t /\ t <= &1 ==> c t IN S /\ gamma t = Phi(c t)) /\
             mfd_length (open_set_atlas (:real^3)) G0 c (&0) (&1) <=
             sqrt(&2) / h * mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`;
                 `Phi:real^3->A`; `gamma:real->A`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `P = rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field S (P:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S:real^3->bool`; `Phi:real^3->A`; `P:real^3->real^3^3`; `c:real->real^3`;
                 `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN REWRITE_TAC[rfs_pullback]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) =
                mfd_length atlas g ((Phi:real^3->A) o c) (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `(:real^3)`; `c:real->real^3`; `&0`; `&1`]
                P2BF_C1_CURVE_OPEN_MONO) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  EXISTS_TAC `c:real->real^3` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `mfd_length (open_set_atlas S) (G0:real^3->real^3^3) c (&0) (&1) <=
    sqrt(&2 * inv(h pow 2)) * mfd_length (open_set_atlas S) P c (&0) (&1)`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_METRIC_COMPARE THEN
    EXISTS_TAC `subtopology euclidean (S:real^3->bool)` THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; OPEN_SET_ATLAS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:real->real^3) t IN S` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field S (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `S:real^3->bool`; `G0:real^3->real^3^3`;
                   `\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z`;
                   `(c:real->real^3) t`; `v:real^3`] LCK_DIST_C0) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (G0:real^3->real^3^3)
                    (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) (c(t:real))) <= &1 / &2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 / &4)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN REWRITE_TAC[];
        SUBGOAL_THEN `&1 / &4 = (&1 / &2) pow 2` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[POW_2_SQRT; REAL_ARITH `&0 <= &1 / &2`; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= v dot ((G0:real^3->real^3^3) (c(t:real)) ** v)` ASSUME_TAC THENL
     [ASM_CASES_TAC `v:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `metric_field S (G0:real^3->real^3^3)` THEN REWRITE_TAC[metric_field] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ABBREV_TAC `a = v dot ((G0:real^3->real^3^3) (c(t:real)) ** v)` THEN
    ABBREV_TAC `b = v dot ((P:real^3->real^3^3) (c(t:real)) ** v)` THEN
    ABBREV_TAC `L = sqrt(lck_dist2 k (G0:real^3->real^3^3)
                     (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) (c(t:real)))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `L * a <= (&1 / &2) * a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * inv(h pow 2)) = sqrt(&2) / h` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL; SQRT_INV; real_div] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Reading the closeness of Prop 16.5.  At a normalized time s               *)
(* in the closeness set, Phi is a parametrization of the history slice at   *)
(* T + s h^2 on W, and h^-2 Phi^* g(T + s h^2) is lck-close to G s on W.     *)
(* ========================================================================= *)

let P3H_VIEW_CLOSE_AT = prove
 (`!(G:real->real^3->real^3^3) W (hs:(A)rfs_history) T1 h (Phi:real^3->A) J dq s.
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) T1 (inv(h pow 2)) Phi J dq /\
     &0 < h /\ s IN J /\ &0 <= s /\ s < &1
     ==> mfd_param (rfs_top_at hs (T1 + s * h pow 2)) (rfs_atlas_at hs (T1 + s * h pow 2))
                   W Phi /\
         ?d. d < dq pow 2 /\
             !y. y IN W
                 ==> lck_dist2 (rfs_kreg dq) (G s)
                       (\z. inv(h pow 2) %%
                            rfs_pullback (rfs_atlas_at hs (T1 + s * h pow 2)) Phi
                                         (rfs_metric_at hs (T1 + s * h pow 2)) z) y <= d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_view_close] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 + s / &1 = s /\ T1 + s / inv(h pow 2) = T1 + s * h pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1; real_div; REAL_INV_INV]; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS; GSYM rfs_vtop; GSYM rfs_vatlas; GSYM rfs_vmetric] THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rfs_mclose]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
  SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[SND; MATRIX_CMUL_LID; ETA_AX; P3H_PULLBACK_OPEN_UNIV]);;

(* ========================================================================= *)
(* Transfer of a cap of a metric on real^3 (the standard flow               *)
(* at t') through the cap parametrization Phi to the history slice          *)
(* (P2B_PROP_9_79_CAP_FIX, with the target h^-2 g, complete since the stage *)
(* is compact, and P2BCS_CAP_CMUL back to g).  The closeness is the one of  *)
(* Prop 16.5 (base G0), rescaled by R_G0(q) >= 1/2.                          *)
(* ========================================================================= *)

let P3H_CAP_TO_HIST = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
     !C eps C' eps' Kr.
       &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\ eps' <= eps0
       ==> ?delta. &0 < delta /\
             !(G0:real^3->real^3^3) q U Y (top:A topology) atlas g h W (Phi:real^3->A) d.
               metric_field (:real^3) G0 /\
               rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C eps U Y /\ q IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
               hausdorff_space top /\ smooth_manifold_atlas top atlas /\
               riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
               mfd_param top atlas W Phi /\ U SUBSET W /\
               &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
               &3 pow (rfs_kreg delta) * d < delta pow 2 /\
               (!y. y IN W
                    ==> lck_dist2 (rfs_kreg delta) G0
                          (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
               ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C' eps' U' Y' /\
                           Phi q IN Y'`,
  MP_TAC(ISPECL [`(:real^3)`; `(:A)`] P2B_PROP_9_79_CAP_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN
  SUBGOAL_THEN `open_in euclidean (U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo euclidean (open_set_atlas (:real^3)) U (top:A topology)
                           (atlas:((A->bool)#(A->real^3))->bool)
                           (IMAGE (Phi:real^3->A) U) Phi Phi'` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `W:real^3->bool` THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) W` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Rq = mfd_scalar (open_set_atlas (:real^3)) (G0:real^3->real^3^3) q` THEN
  ABBREV_TAC `P = rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G0:real^3->real^3^3`;
     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `\z:A. inv(h pow 2) %% (g:A->real^3^3) z`; `q:real^3`; `U:real^3->bool`;
     `Y:real^3->bool`; `Phi:real^3->A`; `Phi':A->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
      REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_COMPACT_IMP_COMPLETE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `&3 pow (rfs_kreg delta) * d` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
    SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
                      ALL_TAC] THEN
    SUBGOAL_THEN
     `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
      MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[SND; P2B9_PULLBACK_METRIC_CMUL] THEN REWRITE_TAC[P3H_PULLBACK_OPEN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field W (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) /\
                  metric_field W (G0:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[mfd_diffeo; OPEN_IN_EUCLIDEAN]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_kreg delta`; `W:real^3->bool`; `G0:real^3->real^3^3`;
                   `\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z`; `Rq:real`; `y:real^3`]
                  P2B9S_LCK_SCALE_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv Rq) pow rfs_kreg delta * d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN
        SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          SUBGOAL_THEN `inv Rq <= inv(&1 / &2)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G0:real^3->real^3^3)
                      (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `W:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U':A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Y':A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (\z:A. inv(h pow 2) %% (g:A->real^3^3) z) C' eps' U' Y'` THEN
  ASM_SIMP_TAC[P2BCS_CAP_CMUL]);;

(* ========================================================================= *)
(* The setting of subcase (ii).  The sub-neck W1 =                          *)
(* e(neck_dom(eps/p)) of a strong neck at (x,ts) persists over               *)
(* (ts - 1/Q, ts].                                                            *)
(* ========================================================================= *)

let P3H_SUBNECK_PERSISTS = prove
 (`!V eps x ts (e:real^3->A) p.
     p2c_regular_view V /\ rfs_strong_neck V eps x ts e /\ &0 < p /\ p <= &1
     ==> rfs_persists V (IMAGE e (rfs_neck_dom (eps / p)))
                      (ts - &1 / rfs_vscalar V ts x) ts`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT] o check
    (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
                   (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  SUBGOAL_THEN `rfs_neck_dom (eps / p) SUBSET rfs_neck_dom eps /\ open(rfs_neck_dom (eps / p))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_DOM_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        SUBGOAL_THEN `eps * p <= eps * &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ts x` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`;
                 `IMAGE (e:real^3->A) (rfs_neck_dom eps)`; `ts - &1 / Q`; `ts:real`;
                 `e:real^3->A`; `rfs_neck_dom (eps / p)`] P3H_VFLOW_NECK) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `&0 < &1 / Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      GEN_REWRITE_TAC I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) u`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`;
                 `rfs_neck_dom (eps / p)`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The setting of subcase (ii) in a history (D1 assembled).                  *)
(* At the first bad time ts >= p3_T i (i >= 1) a strong neck at x whose     *)
(* sub-neck W1 = e(neck_dom(eps/p1)) does not persist past T = ts - 1/Q     *)
(* starts at a surgery time T = T_k > 0 and meets the core of a new cap     *)
(* Phi of event k at a point e y0 of W1.                                     *)
(* ========================================================================= *)

let P3H_PARTD_SETUP = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) ts x e p1.
     1 <= i /\ &0 < eps /\ eps <= &1 / &8 /\ rs 0 = eps /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     p2c_regular_view (rfs_view hs) /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     inv(rs' (SUC i) pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
     rfs_strong_neck (rfs_view hs) eps x ts e /\ &0 < p1 /\ p1 < &1 /\
     ~(?eta0. &0 < eta0 /\
              rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom (eps / p1)))
                (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts)
     ==> ?k j Phi xi y0.
           1 <= k /\ k <= hs_count hs /\
           hs_time hs k = ts - &1 / rfs_vscalar (rfs_view hs) ts x /\ &0 < hs_time hs k /\
           j IN ev_index(hs_event hs k) /\
           p3_cap_param (md,g0,A0)
             (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd)) hs k j Phi xi /\
           y0 IN rfs_neck_dom (eps / p1) /\
           e y0 IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_struct")) (concl th))) THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `rs' (SUC i) <= eps /\ &0 < rs' (SUC i)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `rs' 0 = (eps:real)` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
      MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      ASM_MESON_TAC[p3_seq_ok]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / Q <= &1 / &64` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rs' (SUC i) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      SUBGOAL_THEN `rs' (SUC i) pow 2 = inv(inv(rs' (SUC i) pow 2))` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `eps pow 2 <= (&1 / &8) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &16 <= ts` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p3_T i` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`1`; `i:num`] P3_T_MONO) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p3_T] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 / Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`;
                 `e:real^3->A`; `p1:real`] P3H_SUBNECK_PERSISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `IMAGE (e:real^3->A) (rfs_neck_dom (eps / p1))`;
                 `ts - &1 / Q`; `ts:real`] P3H_EXPOSED_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p3_cap_ok] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_TAC `xi:real^3->real^3`)) THEN
  UNDISCH_TAC `~DISJOINT (IMAGE (e:real^3->A) (rfs_neck_dom (eps / p1)))
                 (IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j) (cball(vec 0,&1)))` THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `y0:real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Claim 17.3 in a history (D4).  With the closeness of Prop                 *)
(* 16.5 on [0, theta1) up to ts, R <= M h^-2 along the flow line of y =     *)
(* Phi qy, the bound R >= c/(1-s) of Prop 12.31 and the normalized curvature *)
(* bound at qy, the normalized time t' = (ts - T)/h^2 is below theta1.      *)
(* ========================================================================= *)

let P3H_CLAIM_17_3_HIST = prove
 (`!(G:real->real^3->real^3^3) W (hs:(A)rfs_history) T1 ts h (Phi:real^3->A) y qy c
    theta0 theta1 M dq Kr.
     rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) T1 (inv(h pow 2)) Phi
       {s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
            T1 + s * h pow 2 < rfs_horizon hs} dq /\
     &0 < h /\ T1 < ts /\ ts < rfs_horizon hs /\ theta1 <= &1 /\
     qy IN W /\ Phi qy = y /\
     (!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) (G s)) /\
     (!s z. &0 <= s /\ s < &1 ==> c / (&1 - s) <= lscalar (G s) z) /\
     (!tau. T1 < tau /\ tau <= ts ==> rfs_vscalar (rfs_view hs) tau y * h pow 2 <= M) /\
     (!s. &0 < s /\ s < &1 ==> lrm_deriv_norm2 0 (G s) qy <= Kr * lscalar (G s) qy pow 2) /\
     &0 <= theta0 /\ theta0 < theta1 /\ &0 <= M /\ &0 < dq /\ dq <= &1 / &10 /\
     &0 <= Kr /\ &72 * sqrt Kr * dq <= &1 / &2 /\
     (!s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq < c / (&1 - s))
     ==> (ts - T1) / h pow 2 < theta1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3H_CLAIM_17_3_CORE THEN
  MAP_EVERY EXISTS_TAC
   [`c:real`; `theta0:real`; `M:real`; `dq:real`; `Kr:real`; `G:real->real^3->real^3^3`;
    `\s z:real^3. inv(h pow 2) %%
                  rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) (T1 + s * h pow 2)) Phi
                               (rfs_metric_at hs (T1 + s * h pow 2)) z`;
    `W:real^3->bool`; `qy:real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `T1 + s * h pow 2 < ts` ASSUME_TAC THENL
   [UNDISCH_TAC `s < (ts - T1) / h pow 2` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * h pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `W:real^3->bool`; `hs:(A)rfs_history`;
                 `T1:real`; `h:real`; `Phi:real^3->A`;
                 `{s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
                       T1 + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)}`;
                 `dq:real`; `s:real`] P3H_VIEW_CLOSE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `qy:real^3`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `tau = T1 + s * h pow 2` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tau:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field W (rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) tau) (Phi:real^3->A)
                                              (rfs_metric_at hs tau))` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) tau` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[metric_field]];
    REWRITE_TAC[] THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W:real^3->bool`;
                   `rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) tau) (Phi:real^3->A)
                                 (rfs_metric_at hs tau)`;
                   `inv(h pow 2)`; `qy:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tau`; `rfs_atlas_at (hs:(A)rfs_history) tau`;
                   `rfs_metric_at (hs:(A)rfs_history) tau`; `W:real^3->bool`;
                   `Phi:real^3->A`; `qy:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vscalar")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS; real_div; REAL_INV_INV] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `d < dq pow 2` THEN UNDISCH_TAC
     `lck_dist2 (rfs_kreg dq) ((G:real->real^3->real^3^3) s)
        (\z. inv(h pow 2) %% rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) tau) (Phi:real^3->A)
                                         (rfs_metric_at hs tau) z) qy <= d` THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The preimage q of x (replaces MT Claim 17.4).  A short curve              *)
(* of the slice from y = Phi qy (dist qy < d1) to x stays in                *)
(* Phi{dist < d1 + 1/eps} by the exit argument and lifts through Phi to a   *)
(* curve of real^3 from qy to q, Phi q = x, of G0-length at most sqrt 2 / h  *)
(* times its length.  Short paths in a neck (APX_NECK_DIST).                 *)
(* ========================================================================= *)

let P3H_LIFT_SHORT_CURVE = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd gamma qy.
             p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\ dd <= &1 / &2 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             p3_std_dist g0 qy < d0 /\ gamma(&0) = Phi qy /\
             mfd_length atlas g gamma (&0) (&1) < h * sqrt(&1 - s) / (&2 * eps)
             ==> ?q c. p3_std_dist g0 q < d0 + inv eps /\ Phi q = gamma(&1) /\
                       mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
                       c(&0) = qy /\ c(&1) = q /\
                       (!t. &0 <= t /\ t <= &1 ==> p3_std_dist g0 (c t) < d0 + inv eps) /\
                       mfd_length (open_set_atlas (:real^3)) G0 c (&0) (&1) <=
                       sqrt(&2) / h * mfd_length atlas g gamma (&0) (&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_SHORT_CURVE_STAYS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "S" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m:real`;
     `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `gamma:real->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S1 = {x:real^3 | p3_std_dist g0 x < d0 + inv eps}` THEN
  SUBGOAL_THEN `S1 SUBSET {x:real^3 | p3_std_dist g0 x < m} /\ open(S1:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S1" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "S1" THEN
      SUBGOAL_THEN `&0 < d0 + inv eps` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d0 + inv eps`] P3N_STD_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S1:real^3->bool`; `Phi:real^3->A`; `G0:real^3->real^3^3`; `h:real`;
                 `rfs_kreg eps`; `gamma:real->A`] P3H_CURVE_TRANSPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < m}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dd pow 2` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(c:real->real^3) (&1)`; `c:real->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (c:real->real^3) t IN S1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN EXPAND_TAC "S1" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC;
    CONV_TAC SYM_CONV THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_POS];
    SUBGOAL_THEN `(c:real->real^3) (&0) IN {x:real^3 | p3_std_dist g0 x < m} /\
                  qy IN {x:real^3 | p3_std_dist g0 x < m} /\
                  (Phi:real^3->A) (c (&0)) = Phi qy` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM SET_TAC[REAL_LE_REFL; REAL_POS];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[REAL_LE_REFL; REAL_POS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `{x:real^3 | p3_std_dist g0 x < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S1" THEN
    REWRITE_TAC[IN_ELIM_THM]]);;

(* Short paths in a neck: from a point of the neck to its centre, length    *)
(* below (1 + alpha) R(x)^(-1/2) (1/eps + 5) (APX_NECK_DIST).              *)

let P3H_NECK_SHORT_PATH = prove
 (`!alpha. &0 < alpha
     ==> ?eps1. &0 < eps1 /\
           !top atlas (g:A->real^3^3) eps x (e:real^3->A) y0.
             &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
             rfs_neck (top,atlas) g eps x e /\ y0 IN rfs_neck_dom eps
             ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                         gamma(&0) = e y0 /\ gamma(&1) = x /\
                         mfd_length atlas g gamma (&0) (&1) <
                         (&1 + alpha) * inv(sqrt(mfd_scalar atlas g x)) * (inv eps + &5)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:A)` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps1:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`eps:real`; `u0:real^3`] P3H_UNIT_SPHERE_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "D" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y0:real^3`; `u0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `x:A`)) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(e:real^3->A) y0`; `(e:real^3->A) u0`;
                 `(&1 + alpha) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (e(u0:real^3)))) *
                  (inv eps + &5)`] APX_DIST_SHORT_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + alpha) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (e(u0:real^3)))) *
                (abs(apx_sval y0) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (&1 + alpha) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (e(u0:real^3))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MP_TAC(SPECL [`eps:real`; `y0:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&2) * pi < &5` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&3 / &2) * (&16 / &5)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
          SUBGOAL_THEN `&3 / &2 = sqrt((&3 / &2) pow 2)` SUBST1_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
          MP_TAC PI_POS THEN REAL_ARITH_TAC;
          MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The cap of Thm 12.32 at (q,t') lies in {dist < d0 + 1/eps}               *)
(* (replaces MT's use of Thm 12.5(5)): points of a (C,eps')-cap U are joined *)
(* to its core point q by curves inside U of length < C R(q)^(-1/2), and the *)
(* exit argument on the standard flow (Phi the identity) keeps such curves  *)
(* inside {dist < d0 + 1/eps}.                                               *)
(* ========================================================================= *)

let P3H_DIST_IN_SHORT_CURVE = prove
 (`!top atlas (g:A->real^3^3) S p q r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable_in (top,atlas) S p q /\ mfd_dist_in (top,atlas) g S p q < r
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = p /\ gamma(&1) = q /\
                 (!t. &0 <= t /\ t <= &1 ==> gamma t IN S) /\
                 mfd_length atlas g gamma (&0) (&1) < r`,
  REWRITE_TAC[mfd_dist_in; mfd_joinable_in] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (p:A) /\ gamma(&1) = q /\
                   (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}`; `r:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_IN_POS_LE]];
    REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN MESON_TAC[]]);;

let P3H_ID_PARAM = prove
 (`!S:real^3->bool. open S ==> mfd_param euclidean (open_set_atlas (:real^3)) S (\x. x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_param; IMAGE_ID] THEN
  EXISTS_TAC `\x:real^3. x` THEN MATCH_MP_TAC MFD_DIFFEO_ID THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
  MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let P3H_ID_PULLBACK = prove
 (`!(G:real^3->real^3^3). rfs_pullback (open_set_atlas (:real^3)) (\x. x) G = G`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; rfs_pullback] THEN X_GEN_TAC `y:real^3` THEN
  SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
  SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_local (open_set_atlas (:real^3)) ((:real^3),(\x:real^3. x)) G = G`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[SND; o_DEF; ETA_AX; P2B9_MPULLBACK_ID]);;

let P3H_CAP_IN_REGION = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 (Gt:real^3->real^3^3) s m d0 dd C epsc U Y q.
             p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
             rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C epsc U Y /\ q IN Y /\
             p3_std_dist g0 q < d0 /\
             &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
             C * sqrt(&2) <= sqrt(&1 - s) / (&2 * eps)
             ==> U SUBSET {x | p3_std_dist g0 x < d0 + inv eps}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:real^3`,`:A`] P3H_SHORT_CURVE_STAYS)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                 `Y:real^3->bool`; `q:real^3`] P2B_CAP_SUP_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist_in (euclidean,open_set_atlas (:real^3)) Gt U q z <
                C * inv(sqrt(sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) Gt) U)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                CONJUNCT2 o GEN_REWRITE_RULE I [rfs_cap] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
    REWRITE_TAC[rfs_sup_lt; FORALL_IN_GSPEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `dm:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dm:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * inv(sqrt(sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) Gt) U))) <=
                C * sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                     `Y:real^3->bool`] P2B_CAP_RATIO) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `q:real^3`)
        (X_CHOOSE_THEN `dr:real` (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPECL [`q:real^3`; `q:real^3`])))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) Gt q` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&2) = inv(sqrt(&1 / &2))` SUBST1_TAC THENL
     [REWRITE_TAC[SQRT_DIV; SQRT_1; real_div; REAL_MUL_LID; REAL_INV_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar (open_set_atlas (:real^3)) Gt q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `U:real^3->bool`; `q:real^3`; `z:real^3`;
                 `C * sqrt(&2)`] P3H_DIST_IN_SHORT_CURVE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                     `Y:real^3->bool`] APX_CAP_JOINABLE) THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < m}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3N_STD_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  REMOVE_THEN "S" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `euclidean:(real^3)topology`;
     `open_set_atlas (:real^3)`; `Gt:real^3->real^3^3`; `\x:real^3. x`; `m:real`; `&1`;
     `Gt:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `gamma:real->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; REAL_LT_01; P3H_ID_PULLBACK] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX; P2BL_LCK_DIST2_REFL] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC P3H_ID_PARAM THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* The neck alternative of Thm 12.32 that starts at time 0                  *)
(* (case (2)) is impossible at q: a curve of the slice from qy (dist <=      *)
(* A0 + 4) to q of length L with eps1 (2 R(q)^(1/2) L + 1) <= 1 puts qy in   *)
(* the neck (P3N_SET_IN_NECK), whose points are at distance >= A0 + 5.      *)
(* ========================================================================= *)

let P3H_CASE2_EXCL = prove
 (`!g0 A0 (Gt:real^3->real^3^3) eps1 q (e2:real^3->real^3) qy c L.
     p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) Gt eps1 q e2 /\ eps1 <= &1 / &2 /\
     (!z. z IN IMAGE e2 (rfs_neck_dom eps1) ==> A0 + &5 <= p3_std_dist g0 z) /\
     p3_std_dist g0 qy <= A0 + &4 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
     c(&0) = qy /\ c(&1) = q /\
     mfd_length (open_set_atlas (:real^3)) Gt c (&0) (&1) <= L /\ &0 <= L /\
     eps1 * (&2 * sqrt(mfd_scalar (open_set_atlas (:real^3)) Gt q) * L + &1) <= &1
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  UNDISCH_TAC `(q:real^3) IN IMAGE (e2:real^3->real^3) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
                riemannian_metric (open_set_atlas (:real^3)) (Gt:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  ABBREV_TAC `Rq = mfd_scalar (open_set_atlas (:real^3)) (Gt:real^3->real^3^3) q` THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `eps1:real`; `q:real^3`; `e2:real^3->real^3`;
                 `u:real^3`; `{qy:real^3}`; `&1`; `L:real`; `sqrt Rq`; `&1`] P3N_SET_IN_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; REAL_LT_01; REAL_LE_REFL; REAL_MUL_LID;
                    REAL_POW_ONE; REAL_MUL_RID] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL];
      REWRITE_TAC[IN_SING] THEN X_GEN_TAC `z:real^3` THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `\t. (c:real->real^3)(&0 + &1 - t)` THEN
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `Gt:real^3->real^3^3`; `c:real->real^3`; `&0`; `&1`] MFD_LENGTH_REVERSE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&0 + &1 - &0 = &1 /\ &0 + &1 - &1 = &0`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `qy:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The disappearance alternative of Prop 16.5 is impossible                 *)
(* in subcase (ii): the exposed point y of the cap region persists up to ts. *)
(* ========================================================================= *)

let P3H_NO_DISAPPEAR = prove
 (`!(hs:(A)rfs_history) k (Phi:real^3->A) W T1 ts y.
     rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k = T1 /\ T1 < ts /\
     y IN IMAGE Phi W /\
     (!tau. T1 < tau /\ tau <= ts ==> y IN topspace(rfs_top_at hs tau))
     ==> ~(?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= ts /\
                DISJOINT (IMAGE Phi W) (topspace(hs_top hs k')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k':num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `T1 < hs_time (hs:(A)rfs_history) k'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `T1:real`)) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_HS_TIME_LE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k'` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_top_at")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k':num`; `hs_time (hs:(A)rfs_history) k'`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `DISJOINT (IMAGE (Phi:real^3->A) W) (topspace(hs_top (hs:(A)rfs_history) k'))` THEN
  UNDISCH_TAC `(y:A) IN IMAGE (Phi:real^3->A) W` THEN SET_TAC[]);;
(* The C^2 bound of R14 at the base point of a canonical neighbourhood gives *)
(* abs(Rm)^2 <= Kr R^2 there.                                                 *)

let P3H_RM_FROM_C2 = prove
 (`!(G:real^3->real^3^3) U x Kr.
     metric_field (:real^3) G /\ x IN U /\
     &0 < mfd_scalar (open_set_atlas (:real^3)) G x /\
     (!y l. y IN U /\ l <= 2
            ==> lrm_deriv_norm2 l
                  (metric_local (open_set_atlas (:real^3)) (chart_at (open_set_atlas (:real^3)) y)
                     (\z. mfd_scalar (open_set_atlas (:real^3)) G x %% G z))
                  (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr)
     ==> lrm_deriv_norm2 0 G x <= Kr * lscalar G x pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `0`]) THEN ASM_REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) x = ((:real^3),(\x:real^3. x))`
  SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
  (fun th -> REWRITE_TAC[th; SND]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < mfd_scalar (open_set_atlas (:real^3)) (G:real^3->real^3^3) x` THEN
  SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; OPEN_UNIV; IN_UNIV] THEN
  ABBREV_TAC `R = lscalar (G:real^3->real^3^3) x` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `G:real^3->real^3^3`; `R:real`; `0`; `x:real^3`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ASM_REWRITE_TAC[IN_UNIV; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G:real^3->real^3^3) x =
                R pow 2 * (inv R pow 2 * lrm_deriv_norm2 0 G x)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* Scalar curvature through the cap parametrization: if                     *)
(* h^-2 Phi^* g is lck-close to G0 at q and abs(Rm_G0)^2 <= K0^2 there,     *)
(* then h^2 R_g(Phi q) is close to R_G0(q).                                  *)
(* ========================================================================= *)

let P3H_PHI_SCALAR_AT = prove
 (`!top atlas (g:A->real^3^3) W (Phi:real^3->A) (G0:real^3->real^3^3) h q K0 dq.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas W Phi /\ metric_field W G0 /\ q IN W /\ &0 < h /\
     lrm_deriv_norm2 0 G0 q <= K0 pow 2 /\ &0 < dq /\ dq <= &1 / &10 /\
     lck_dist2 (rfs_kreg dq) G0 (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) q <= dq pow 2
     ==> abs(h pow 2 * mfd_scalar atlas g (Phi q) - lscalar G0 q) <=
         &72 * (&1 + abs K0) * dq`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field W (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `G0:real^3->real^3^3`;
                 `\z:real^3. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) z`;
                 `q:real^3`; `K0:real`; `dq:real`] P3H_SCALAR_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)`;
                 `inv(h pow 2)`; `q:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:real^3->bool`; `Phi:real^3->A`; `q:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The far-field closeness of Prop 12.7 on a shell around the                *)
(* level d, at the regularity of eps_n and below ddx^2 (the cylinder         *)
(* pullback is a metric field on shells).                                    *)
(* ========================================================================= *)

let P3H_NC_CYL_FIELD = prove
 (`!g0 A0 a b t.
     p3_std_initial g0 A0 /\ a < b /\ b <= A0 + &4 /\ t < &1
     ==> metric_field {x:real^3 | a < A0 + &4 - p3_std_dist g0 x /\
                                  A0 + &4 - p3_std_dist g0 x < b}
                      (mpullback (p3_std_nc g0 A0) (cylinder_flow t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`{y:real^3 | exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))}`;
    `p3s_ncinv g0 A0`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM annulus; OPEN_ANNULUS];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM NORM_POS_LT] THEN
      MESON_TAC[REAL_EXP_POS_LT; REAL_LT_TRANS]];
    MATCH_MP_TAC P3S_NC_DIFFEO THEN ASM_REWRITE_TAC[]]);;

let P3H_SHELL_CLOSE = prove
 (`!g0 A0 (Gt:real^3->real^3^3) t A1 epsp eps_n ddx d.
     p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ t < &1 /\
     (!z. A1 < p3_std_dist g0 z
          ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) Gt z
              < epsp pow 2) /\
     &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx /\ &0 < eps_n /\ inv eps_n < d /\
     A1 + inv eps_n < d
     ==> !x. d - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n) (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) Gt x
                 < ddx pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `V = {x:real^3 | (A0 + &4 - d) - inv eps_n < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < (A0 + &4 - d) + inv eps_n}` THEN
  SUBGOAL_THEN `&0 < inv eps_n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field V (mpullback (p3_std_nc g0 A0) (cylinder_flow t))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P3H_NC_CYL_FIELD THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                (Gt:real^3->real^3^3) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `epsp pow 2` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The alternatives of Thm 12.32 at the preimage q of x at                  *)
(* the normalized time tp = t' (D6).  The strong-neck alternative           *)
(* contradicts tp R(q,tp) ~ 1, the neck from time 0 contradicts the short   *)
(* curve to qy, and the cap lies in the closeness region and transfers to a *)
(* (C,eps)-cap of the history slice with x in its core.                      *)
(* ========================================================================= *)

let P3H_D_CASES = prove
 (`!g0 A0 (G:real->real^3->real^3^3) tp q qy c L (top:A topology) atlas g h m
    (Phi:real^3->A) x C eps C_in eps_in Kr dq delta eps_n dd0n ddx d2 A1 epsp dq2 d.
     p3_std_initial g0 A0 /\ &0 < tp /\ tp < &1 /\
     (!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) (G t)) /\
     ((?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G tp) C_in eps_in U Y /\ q IN Y) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
           !z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps_in q tp (&1 + eps_in) e)) /\
     (!z U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G tp) C_in eps_in z U
            ==> !y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\w. mfd_scalar (open_set_atlas (:real^3)) (G tp) z %% G tp w))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
     (!z. A1 < p3_std_dist g0 z
          ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow tp)) (G tp) z
              < epsp pow 2) /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &0 < h /\
     mfd_param top atlas {z | p3_std_dist g0 z < m} Phi /\
     p3_std_dist g0 q < d2 /\ Phi q = x /\
     (!y. p3_std_dist g0 y < m
          ==> lck_dist2 (rfs_kreg dq2) (G tp)
                (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d) /\
     d < dq2 pow 2 /\
     (h pow 2 * mfd_scalar atlas g x) * tp = &1 /\ &1 <= h pow 2 * mfd_scalar atlas g x /\
     p3_std_dist g0 qy <= A0 + &4 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
     c(&0) = qy /\ c(&1) = q /\
     mfd_length (open_set_atlas (:real^3)) (G tp) c (&0) (&1) <= L /\ &0 <= L /\
     (!G0 q U Y (top:A topology) atlas g h W (Phi:real^3->A) d.
        metric_field (:real^3) G0 /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C_in eps_in U Y /\ q IN Y /\
        (!y l. y IN U /\ l <= 2
               ==> lrm_deriv_norm2 l
                     (metric_local (open_set_atlas (:real^3))
                        (chart_at (open_set_atlas (:real^3)) y)
                        (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                     (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
        mfd_param top atlas W Phi /\ U SUBSET W /\
        &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
        &3 pow (rfs_kreg delta) * d < delta pow 2 /\
        (!y. y IN W
             ==> lck_dist2 (rfs_kreg delta) G0
                   (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
        ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C eps U' Y' /\
                    Phi q IN Y') /\
     (!g0 A0 (Gt:real^3->real^3^3) s m d0 dd C epsc U Y q.
        p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
        inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0n /\
        (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n)
                   (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C epsc U Y /\ q IN Y /\
        p3_std_dist g0 q < d0 /\
        &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
        C * sqrt(&2) <= sqrt(&1 - s) / (&2 * eps_n)
        ==> U SUBSET {x | p3_std_dist g0 x < d0 + inv eps_n}) /\
     &0 < dq /\ dq <= &1 / &300 /\ &0 <= Kr /\ &72 * sqrt Kr * dq <= &1 / &2 /\
     &0 < eps_in /\ eps_in <= &1 / &2 /\
     &1 + &72 * dq < (&1 + eps_in) * (&1 - &72 * sqrt Kr * dq) /\
     eps_in * (&2 * sqrt(&2 * (h pow 2 * mfd_scalar atlas g x) + &1) * L + &1) <= &1 /\
     &0 < dq2 /\ dq2 <= dq /\ &0 < delta /\ dq2 <= delta / &3 pow (rfs_kreg delta) /\
     &0 < eps_n /\ eps_n <= &1 / &4 /\ &0 < ddx /\ ddx <= dd0n /\
     &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx /\
     inv eps_n < d2 /\ d2 + inv eps_n < m /\ A1 + inv eps_n < d2 /\
     C_in * sqrt(&2) <= sqrt(&1 - tp) / (&2 * eps_n)
     ==> ?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 < inv eps_n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Rh = h pow 2 * mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `Rs = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) tp)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lscalar ((G:real->real^3->real^3^3) tp) q = Rs` ASSUME_TAC THENL
   [EXPAND_TAC "Rs" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | p3_std_dist g0 z < m}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 q < m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the scalar comparison at q *)
  SUBGOAL_THEN
   `!U0. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                            C_in eps_in (q:real^3) U0 /\ q IN U0 /\ &0 < (Rs:real)
         ==> abs((Rh:real) - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq`
  ASSUME_TAC THENL
   [X_GEN_TAC `U0:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!y l. y IN U0 /\ l <= 2
            ==> lrm_deriv_norm2 l
                  (metric_local (open_set_atlas (:real^3)) (chart_at (open_set_atlas (:real^3)) y)
                     (\w. mfd_scalar (open_set_atlas (:real^3))
                            ((G:real->real^3->real^3^3) tp) q %% G tp w))
                  (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
            (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2"))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(G:real->real^3->real^3^3) tp`; `U0:real^3->bool`; `q:real^3`; `Kr:real`]
                  P3H_RM_FROM_C2) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`;
                   `(G:real->real^3->real^3^3) tp`; `h:real`; `q:real^3`;
                   `sqrt(Kr:real) * abs(Rs:real)`; `dq:real`] P3H_PHI_SCALAR_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        ASM_REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 (rfs_kreg dq2) ((G:real->real^3->real^3^3) tp)
                      (\z. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) z) q` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `{z:real^3 | p3_std_dist g0 z < m}` THEN
          ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
            ASM_REWRITE_TAC[SUBSET_UNIV];
            MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
             [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
              ASM_REWRITE_TAC[];
              MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
            MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dq2 pow 2` THEN
            CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN
                            ASM_REAL_ARITH_TAC]]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(sqrt(Kr:real) * abs(Rs:real)) = sqrt Kr * abs Rs` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &72 * sqrt Kr * dq /\ &0 < Rh` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the time-tp slice of an evolving neck of the flow view *)
  SUBGOAL_THEN
   `!len (e:real^3->real^3).
      rfs_evolving_neck
        (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
        eps_in q tp len e
      ==> rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                   eps_in q e`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^3->real^3. rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                                eps_in q e
                       ==> &0 < Rs /\ abs(Rh - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (Rs:real)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q`
      MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
          not (is_forall(concl th)) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
        SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Rh:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
          (concl th))) THEN
    EXISTS_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ1_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
        not (is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
      STRIP_TAC THEN
      MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:real^3) IN IMAGE (e:real^3->real^3) (sphere(vec 0,&1))` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC) o
    check (fun th -> is_disj(concl th))) THENL
   [
    FIRST_X_ASSUM(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `Y:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
     [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(G:real->real^3->real^3^3) tp`; `C_in:real`; `eps_in:real`; `U:real^3->bool`;
                   `Y:real^3->bool`] P2B_CAP_RATIO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3))
                    ((G:real->real^3->real^3^3) tp) C_in eps_in q U` ASSUME_TAC THENL
     [REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `U:real^3->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Rh:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 <= Rs` ASSUME_TAC THENL
     [SUBGOAL_THEN `&72 * sqrt Kr * dq * abs Rs <= abs Rs / &2` MP_TAC THENL
       [SUBGOAL_THEN `abs Rs / &2 = (&1 / &2) * abs Rs` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[REAL_ABS_POS; GSYM REAL_MUL_ASSOC];
        ALL_TAC] THEN
      UNDISCH_TAC `abs(Rh - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq` THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:real^3->bool) SUBSET {z | p3_std_dist g0 z < d2 + inv eps_n}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dd0n:real`)) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`A0:real`; `(G:real->real^3->real^3^3) tp`; `tp:real`; `m:real`;
                            `ddx:real`; `C_in:real`; `eps_in:real`; `Y:real^3->bool`;
                            `q:real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P3H_SHELL_CLOSE THEN
        MAP_EVERY EXISTS_TAC [`A1:real`; `epsp:real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`(G:real->real^3->real^3^3) tp`; `q:real^3`; `U:real^3->bool`; `Y:real^3->bool`;
       `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `h:real`;
       `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`; `d:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
      can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
              (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2"))
              (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(U:real^3->bool) SUBSET {z | p3_std_dist g0 z < d2 + inv eps_n}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_TRANS];
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3 pow (rfs_kreg delta) * dq2 pow 2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &3`];
          ALL_TAC] THEN
        SUBGOAL_THEN `&1 <= &3 pow (rfs_kreg delta)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `dq2 * &3 pow (rfs_kreg delta) <= delta` ASSUME_TAC THENL
         [UNDISCH_TAC `dq2 <= delta / &3 pow (rfs_kreg delta)` THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_IMP_LE; REAL_POW_LT; REAL_ARITH `&0 < &3`];
          ALL_TAC] THEN
        SUBGOAL_THEN `(dq2 * &3 pow (rfs_kreg delta)) pow 2 <= delta pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE;
                                                      REAL_ARITH `&0 <= &3`];
            ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_MUL] THEN
        SUBGOAL_THEN `&3 pow (rfs_kreg delta) <= (&3 pow (rfs_kreg delta)) pow 2` MP_TAC THENL
         [REWRITE_TAC[REAL_POW_2] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `&3 pow (rfs_kreg delta) * dq2 pow 2 <=
                      (&3 pow (rfs_kreg delta)) pow 2 * dq2 pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
          REAL_ARITH_TAC];
        X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 (rfs_kreg dq2) ((G:real->real^3->real^3^3) tp)
                      (\z. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) z) y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `{z:real^3 | p3_std_dist g0 z < m}` THEN
          ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
            ASM_REWRITE_TAC[SUBSET_UNIV];
            MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
             [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
              ASM_REWRITE_TAC[];
              MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
            MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta / &3 pow (rfs_kreg delta)` THEN
            ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT;
                                                REAL_ARITH `&0 < &3`] THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE_1; REAL_ARITH `&1 <= &3`]];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U':A->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Y':A->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                           eps_in q e` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC
        `tp * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Rh:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
               (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC P3H_CASE2_EXCL THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `(G:real->real^3->real^3^3) tp`;
                          `eps_in:real`; `q:real^3`; `e:real^3->real^3`; `qy:real^3`;
                          `c:real->real^3`; `L:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `eps_in * (&2 * sqrt(&2 * Rh + &1) * L + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> &2 * a + &1 <= &2 * b + &1`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `&72 * sqrt Kr * dq * abs Rs <= abs Rs / &2` MP_TAC THENL
     [SUBGOAL_THEN `abs Rs / &2 = (&1 / &2) * abs Rs` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; GSYM REAL_MUL_ASSOC];
      ALL_TAC] THEN
    UNDISCH_TAC `abs(Rh - Rs) <= &72 * (&1 + sqrt Kr * abs Rs) * dq` THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^3->real^3`) THEN
    SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                           eps_in q e` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `&1 + eps_in` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Rh:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
               (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `G:real->real^3->real^3^3`; `eps_in:real`; `q:real^3`; `tp:real`;
                   `&1 + eps_in`; `e:real^3->real^3`] P3H_FLOWVIEW_NECK_TIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC P3H_CASE3_ARITH THEN
    MAP_EVERY EXISTS_TAC [`Rs:real`; `Rh:real`; `tp:real`; `Kr:real`; `dq:real`;
                          `&1 + eps_in`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The history facts of part D before Prop 16.5 is applied:                 *)
(* the event k at T_k = ts - 1/R(x,ts), its cap parameterization, the       *)
(* exposed point e y0 = Phi qy in the cap core, the step bounds dl(T_k) <=  *)
(* dlt and rp(T_k) <= eps, the scale h(T_k) > 0, the canonical assumption   *)
(* at the threshold r' before ts, and the persistence of e y0 on (T_k,ts].  *)
(* ========================================================================= *)

let P3H_HIST_COMPACT_AT = prove
 (`!(hs:(A)rfs_history) t. rfs_history_ok hs ==> compact_space (rfs_top_at hs t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY]] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN
    ASM_REWRITE_TAC[rfs_live; rfs_horizon];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) t` o CONJUNCT1 o CONJUNCT2 o
                CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_SIMP_TAC[]);;

let P3H_D_HIST_FACTS = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt rs' ks' dd (hs:(A)rfs_history) ts x e p1.
     1 <= i /\ &0 < eps /\ eps <= &1 / &8 /\ rs 0 = eps /\ &0 < r' /\
     rs' (SUC i) = r' /\ p3_hfun C hf /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     p2c_regular_view (rfs_view hs) /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
     inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
     rfs_strong_neck (rfs_view hs) eps x ts e /\ &0 < p1 /\ p1 < &1 /\
     ~(?eta0. &0 < eta0 /\
              rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom (eps / p1)))
                (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts)
     ==> ?k j Phi xi y0 qy.
           1 <= k /\ k <= hs_count hs /\
           hs_time hs k = ts - &1 / rfs_vscalar (rfs_view hs) ts x /\
           &0 < hs_time hs k /\ hs_time hs k < ts /\
           j IN ev_index(hs_event hs k) /\
           p3_cap_param (md,g0,A0)
             (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd)) hs k j Phi xi /\
           y0 IN rfs_neck_dom eps /\ e y0 = Phi qy /\ p3_std_dist g0 qy <= A0 + &4 /\
           e y0 IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
           p3_stepf dd (hs_time hs k) <= dlt /\ p3_stepf rs' (hs_time hs k) <= eps /\
           &0 < p3_stepf dd (hs_time hs k) /\
           &0 < p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) /\
           (!t z. &0 <= t /\ t < ts /\ z IN topspace(rfs_top_at hs t) /\
                  inv(r' pow 2) <= rfs_vscalar (rfs_view hs) t z
                  ==> p3_canon_at (rfs_view hs) C eps z t) /\
           (!tau. hs_time hs k < tau /\ tau <= ts
                  ==> e y0 IN topspace(rfs_top_at hs tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `dlt:real`; `rs':num->real`; `ks':num->real`;
                 `dd:num->real`; `hs:(A)rfs_history`; `ts:real`; `x:A`; `e:real^3->A`;
                 `p1:real`] P3H_PARTD_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `Phi:real^3->A`
    (X_CHOOSE_THEN `xi:real^3->real^3` (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_struct")) (concl th))) THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < inv(r' pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 / Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the exposed point in the cap core *)
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p3_cap_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_param")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?qy. (e:real^3->A) y0 = Phi qy /\ p3_std_dist g0 qy <= A0 + &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->A) y0 IN IMAGE Phi {x | &0 <= A0 + &4 - p3_std_dist g0 x}`
    MP_TAC THENL
     [UNDISCH_TAC `(e:real^3->A) y0 IN IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j)
                                            (cball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `y0:real^3`;
                        `qy:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r' <= eps /\ &1 / Q <= &1 / &64` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r' <= eps` ASSUME_TAC THENL
     [SUBGOAL_THEN `rs' 0 = (eps:real)` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `rs' (SUC i) = (r':real)`)) THEN
      MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r' pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      SUBGOAL_THEN `r' pow 2 = inv(inv(r' pow 2))` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `eps pow 2 <= (&1 / &8) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_T (i - 1) <= ts - &1 / Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_T i = &2 * p3_T (i - 1) /\ &1 / &32 <= p3_T (i - 1)` MP_TAC THENL
     [SUBGOAL_THEN `i = SUC(i - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
                                                  [th]) THENL
       [UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3_T; real_pow] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> &1 / &32 <= a / &32`) THEN
        MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `i <= p3_step (ts - &1 / Q)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ts - &1 / Q`; `i - 1`] P3_STEP_GE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= i` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_stepf rs' (ts - &1 / Q) /\ &0 < p3_stepf dd (ts - &1 / Q)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `p3_stepf rs'`)) (concl th) &&
      not (can (find_term (fun t -> t = `s:real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`eps:real`; `eps / p1`] APX_NECK_DOM_MONO) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `eps * p1 <= eps * &1 ==> eps * p1 <= eps`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    REWRITE_TAC[p3_stepf] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dd:num->real) i` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `dd:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_stepf] THEN
    SUBGOAL_THEN `rs' 0 = (eps:real)` (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
     [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
    MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_hscale] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p3_hfun] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_hfun")) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`p3_stepf dd (ts - &1 / Q) * p3_stepf rs' (ts - &1 / Q)`;
                                `p3_stepf dd (ts - &1 / Q)`]) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts) C eps
                   (p3_stepf rs')` THEN
    REWRITE_TAC[P3H_TRUNC_CANON_BAD] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[p3h_bad; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a ==> ~(a /\ ~b) ==> b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[p3_stepf] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `rs' (SUC i) = (r':real)`)) THEN
    MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`;
                   `e:real^3->A`; `p1:real`] P3H_SUBNECK_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[rfs_view; rfs_persists] THEN
    DISCH_TAC THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.5 applied at the event k with the cutoff ts (its                 *)
(* disappearance alternative fails since the exposed point persists), and  *)
(* the alternatives of Thm 12.32 give a canonical neighbourhood of the     *)
(* point.                                                                   *)
(* ========================================================================= *)

let P3H_1232_CANON = prove
 (`!g0 A0 (G:real->real^3->real^3^3) C' eps x t.
     &0 <= t /\ t < &1 /\
     ((?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C' eps U Y /\ x IN Y) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps x t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x) e /\
           !z. z IN IMAGE e (rfs_neck_dom eps) ==> A0 + &5 <= p3_std_dist g0 z) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps x t (&1 + eps) e))
     ==> ?U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G t) C' eps x U /\
             x IN U`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN
   `!len (e:real^3->real^3).
      rfs_evolving_neck
        (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
        eps x t len e
      ==> ?U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3))
                ((G:real->real^3->real^3^3) t) C' eps x U /\ x IN U`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN CONJ_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 MP_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC) o check (fun th ->
    is_disj(concl th))) THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `Y:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U:real^3->bool` THEN REWRITE_TAC[rfs_canonical_nbhd] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` (ASSUME_TAC o CONJUNCT1)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    MAP_EVERY EXISTS_TAC
     [`t * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) x`;
      `e:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `e:real^3->real^3`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    MAP_EVERY EXISTS_TAC [`&1 + eps`; `e:real^3->real^3`] THEN ASM_REWRITE_TAC[]]);;

let P3H_D_165 = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) ts r' m dq2 theta1 d0
    k j (Phi:real^3->A) xi qy h.
     (!rp dl (hs:(A)rfs_history) k i Phi xi ts h tc.
        p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ tc <= rfs_horizon hs /\
        (!t x. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
               inv(r' pow 2) <= rfs_vscalar (rfs_view hs) t x
               ==> p3_canon_at (rfs_view hs) C eps x t) /\
        1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
        ts = hs_time hs k /\ ts < tc /\ h = p3_hscale hf rp dl ts /\
        p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
        dl ts <= d0 /\ rp ts <= eps
        ==> ?G. p3_std_flow g0 (&1) G /\
            (p3_view_close
              (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
              (&0) (&1) {x | p3_std_dist g0 x < m}
              (rfs_view hs) ts (inv(h pow 2)) Phi
              {s | &0 <= s /\ s < theta1 /\ ts + s * h pow 2 <= tc /\
                   ts + s * h pow 2 < rfs_horizon hs} dq2 \/
            ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
                 hs_time hs k' < ts + theta1 * h pow 2 /\
                 p3_view_close
                   (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                  {s | &0 <= s /\ s < &1} G)
                   (&0) (&1) {x | p3_std_dist g0 x < m}
                   (rfs_view hs) ts (inv(h pow 2)) Phi
                   {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dq2 /\
                 DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m}) (topspace(hs_top hs k')))) /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     dlt <= d0 /\ ts < rfs_horizon hs /\
     1 <= k /\ k <= hs_count hs /\ hs_time hs k < ts /\ j IN ev_index(hs_event hs k) /\
     p3_cap_param (md,g0,A0)
       (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd)) hs k j Phi xi /\
     h = p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) /\
     p3_std_dist g0 qy < m /\
     p3_stepf dd (hs_time hs k) <= dlt /\ p3_stepf rs' (hs_time hs k) <= eps /\
     (!t z. &0 <= t /\ t < ts /\ z IN topspace(rfs_top_at hs t) /\
            inv(r' pow 2) <= rfs_vscalar (rfs_view hs) t z
            ==> p3_canon_at (rfs_view hs) C eps z t) /\
     (!tau. hs_time hs k < tau /\ tau <= ts ==> Phi qy IN topspace(rfs_top_at hs tau))
     ==> ?G. p3_std_flow g0 (&1) G /\
             p3_view_close
               (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
               (&0) (&1) {x | p3_std_dist g0 x < m}
               (rfs_view hs) (hs_time hs k) (inv(h pow 2)) Phi
               {s | &0 <= s /\ s < theta1 /\ hs_time hs k + s * h pow 2 <= ts /\
                    hs_time hs k + s * h pow 2 < rfs_horizon hs} dq2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "165") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_struct]; ALL_TAC] THEN
  REMOVE_THEN "165" (MP_TAC o SPECL
   [`p3_stepf rs'`; `p3_stepf dd`; `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
    `xi:real^3->real^3`; `hs_time (hs:(A)rfs_history) k`; `h:real`; `ts:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `G:real->real^3->real^3^3` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th))) THEN
  MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `Phi:real^3->A`;
                 `{x:real^3 | p3_std_dist g0 x < m}`; `hs_time (hs:(A)rfs_history) k`;
                 `ts:real`; `(Phi:real^3->A) qy`] P3H_NO_DISAPPEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `qy:real^3` THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

(* ========================================================================= *)
(* Claim 17.3 at the exposed point (D4 assembled): the                     *)
(* normalized time t' = (ts - T_k) / h^2 of ts is below theta1.            *)
(* ========================================================================= *)

let P3H_STD_FLOW_FIELD = prove
 (`!g0 (G:real->real^3->real^3^3) s.
     p3_std_flow g0 (&1) G /\ &0 <= s /\ s < &1 ==> metric_field (:real^3) (G s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `&1`;
                 `G:real->real^3->real^3^3`; `s:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    SIMP_TAC[]]);;

let P3H_D_CLAIM = prove
 (`?eps3. &0 < eps3 /\
     !g0 A0 (G:real->real^3->real^3^3) (hs:(A)rfs_history) k j (Phi:real^3->A) xi md
      (dl:real->real) (hh:real->real) ts x eps (e:real^3->A) y0 qy C_in eps_in Kr c D M dq2
      theta0 theta1 m dd3.
       p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\ rfs_history_ok hs /\
       p2c_regular_view (rfs_view hs) /\
       p3_view_close
         (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
         (&0) (&1) {x | p3_std_dist g0 x < m}
         (rfs_view hs) (hs_time hs k) (inv(hh(hs_time hs k) pow 2)) Phi
         {s | &0 <= s /\ s < theta1 /\ hs_time hs k + s * hh(hs_time hs k) pow 2 <= ts /\
              hs_time hs k + s * hh(hs_time hs k) pow 2 < rfs_horizon hs} dq2 /\
       k <= hs_count hs /\ hs_time hs k = ts - &1 / rfs_vscalar (rfs_view hs) ts x /\
       hs_time hs k < ts /\ ts < rfs_horizon hs /\
       p3_cap_param (md,g0,A0) (dl,hh) hs k j Phi xi /\
       &0 < hh(hs_time hs k) /\ &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= md dd3 /\
       rfs_strong_neck (rfs_view hs) eps x ts e /\ eps <= eps3 /\ y0 IN rfs_neck_dom eps /\
       e y0 = Phi qy /\ p3_std_dist g0 qy < m /\
       e y0 IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
       &0 < c /\
       (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1
                ==> c / (&1 - t) <= mfd_scalar (open_set_atlas (:real^3)) (G t) x) /\
       (!G x t. p3_std_flow g0 (&1) G /\ &0 < t /\ t < &1
                ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in U Y /\
                           x IN Y) \/
                    (?e. rfs_evolving_neck
                           (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                          {s | &0 <= s /\ s < &1} G)
                           eps_in x t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x) e /\
                         !z. z IN IMAGE e (rfs_neck_dom eps_in)
                             ==> A0 + &5 <= p3_std_dist g0 z) \/
                    (?e. rfs_evolving_neck
                           (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                          {s | &0 <= s /\ s < &1} G)
                           eps_in x t (&1 + eps_in) e)) /\
       (!G t x U.
          p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1 /\
          rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in x U
          ==> !y l. y IN U /\ l <= 2
                    ==> lrm_deriv_norm2 l
                          (metric_local (open_set_atlas (:real^3))
                             (chart_at (open_set_atlas (:real^3)) y)
                             (\z. mfd_scalar (open_set_atlas (:real^3)) (G t) x %% G t z))
                          (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
       &0 < Kr /\ &1 <= D /\
       (!q. p3_std_dist g0 q <= A0 + &4
            ==> abs(lscalar g0 q) <= D /\ lrm_deriv_norm2 0 g0 q <= D pow 2) /\
       M = &6 * D /\ &0 < dd3 /\ dd3 <= &1 / &10 /\ A0 + &4 < inv dd3 /\
       &72 * (&1 + D) * dd3 <= D /\
       &0 <= theta0 /\ theta0 < theta1 /\ theta1 <= &1 /\ &0 < dq2 /\ dq2 <= &1 / &10 /\
       &72 * sqrt Kr * dq2 <= &1 / &2 /\
       (!s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq2 < c / (&1 - s))
       ==> (ts - hs_time hs k) / hh(hs_time hs k) pow 2 < theta1`,
  MP_TAC(SPEC `&1 / &10` P3H_NECK_Y_BOUNDS) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NY"))) THEN
  EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `hs_time (hs:(A)rfs_history) k = ts - &1 / Q`)) THEN
  ABBREV_TAC `h = (hh:real->real) (hs_time (hs:(A)rfs_history) k)` THEN
  SUBGOAL_THEN
   `!tau. hs_time (hs:(A)rfs_history) k < tau /\ tau <= ts
          ==> (&1 / &2 - &1 / &10) * Q <= rfs_vscalar (rfs_view hs) tau ((Phi:real^3->A) qy) /\
              rfs_vscalar (rfs_view hs) tau (Phi qy) <= (&1 + &1 / &10) * Q`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Phi:real^3->A) qy = (e:real^3->A) y0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "NY" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`;
                                   `e:real^3->A`; `y0:real^3`; `tau:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`;
                 `(e:real^3->A) y0`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
                 `dl:real->real`; `hh:real->real`; `Q:real`; `ts:real`; `dd3:real`; `D:real`;
                 `&1 / &10`] P3H_QT_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1 / &10`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE
    [ASSUME `(hh:real->real) (hs_time (hs:(A)rfs_history) k) = h`] th)) THEN
  SUBGOAL_THEN `abs(D:real) = D` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= D ==> abs D = D`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!tau. hs_time (hs:(A)rfs_history) k < tau /\ tau <= ts
                      ==> rfs_vscalar (rfs_view hs) tau ((Phi:real^3->A) qy) * h pow 2 <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1 / &10`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((&1 + &1 / &10) * Q) * h pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) ((G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_STD_FLOW_FIELD THEN
    EXISTS_TAC `g0:real^3->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s z. &0 <= s /\ s < &1
                      ==> c / (&1 - s) <= lscalar ((G:real->real^3->real^3^3) s) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `lscalar ((G:real->real^3->real^3^3) s) z =
                  mfd_scalar (open_set_atlas (:real^3)) (G s) z` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `theta0:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < &1
                    ==> lrm_deriv_norm2 0 ((G:real->real^3->real^3^3) s) qy <=
                        Kr * lscalar (G s) qy pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `qy:real^3`; `s:real`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `C_in:real`;
                   `eps_in:real`; `qy:real^3`; `s:real`] P3H_1232_CANON) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P3H_RM_FROM_C2 THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `c / (&1 - s)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `c:real`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th) &&
          not (can (find_term (fun t -> t = `theta0:real`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `s:real`; `qy:real^3`;
                                   `U:real^3->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
              (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < m}`;
                 `hs:(A)rfs_history`; `hs_time (hs:(A)rfs_history) k`; `ts:real`; `h:real`;
                 `Phi:real^3->A`; `(Phi:real^3->A) qy`; `qy:real^3`; `c:real`; `theta0:real`;
                 `theta1:real`; `M:real`; `dq2:real`; `Kr:real`] P3H_CLAIM_17_3_HIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Arithmetic for the end of part D: the neck path from e y0                *)
(* to x is short enough for the exit lemmas, and its lift satisfies the     *)
(* length condition of P3H_CASE2_EXCL.                                       *)
(* ========================================================================= *)

let P3H_FINISH_ARITH1 = prove
 (`!h Q len eps eps_in.
     &0 < h /\ &0 < Q /\ &1 <= h pow 2 * Q /\ &0 <= len /\
     len < (&1 + &1 / &10) * inv(sqrt Q) * (inv eps + &5) /\ &0 < eps /\ &0 < eps_in /\
     eps_in * (&7 * (inv eps + &5) + &1) <= &1
     ==> eps_in * (&2 * sqrt(&2 * (h pow 2 * Q) + &1) * (sqrt(&2) / h * len) + &1) <= &1`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `b = sqrt Q` THEN
  SUBGOAL_THEN `&0 < b /\ b pow 2 = Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps + &5` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * (h pow 2 * Q) + &1) <= &2 * h * b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `&1 <= h pow 2 * Q` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `b pow 2 = Q`)) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * (h pow 2 * Q) + &1) * (sqrt(&2) / h * len) <= &3 * b * len`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * h * b) * ((&3 / &2) / h * len)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; REAL_POS];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
      SUBGOAL_THEN `(&2 * h * b) * ((&3 / &2) / h * len) = &3 * b * len` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * b * len <= (&33 / &10) * (inv eps + &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(&3 * b) * ((&1 + &1 / &10) * inv b * (inv eps + &5))` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `len < (&1 + &1 / &10) * inv (sqrt Q) * (inv eps + &5)` THEN
      ASM_REWRITE_TAC[REAL_MUL_ASSOC];
      SUBGOAL_THEN `(&3 * b) * ((&1 + &1 / &10) * inv b * (inv eps + &5)) =
                    (&33 / &10) * (inv eps + &5)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `eps_in * (&7 * (inv eps + &5) + &1)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_FINISH_ARITH2 = prove
 (`!h Q len eps eps_n C_in tp theta1.
     &0 < h /\ &0 < Q /\ &1 <= h pow 2 * Q /\ &0 <= tp /\ tp < theta1 /\ theta1 < &1 /\
     &0 < eps /\ &0 < eps_n /\ &1 < C_in /\
     len < (&1 + &1 / &10) * inv(sqrt Q) * (inv eps + &5) /\
     &3 * eps_n * (inv eps + &5 + C_in) <= sqrt(&1 - theta1)
     ==> len < h * sqrt(&1 - tp) / (&2 * eps_n) /\
         C_in * sqrt(&2) <= sqrt(&1 - tp) / (&2 * eps_n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `b = sqrt Q` THEN ABBREV_TAC `w = inv eps + &5` THEN
  ABBREV_TAC `s1 = sqrt(&1 - tp)` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= h * b` ASSUME_TAC THENL
   [SUBGOAL_THEN `h * b = sqrt(h pow 2 * Q)` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN REWRITE_TAC[SQRT_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * eps_n * (w + C_in) <= s1` ASSUME_TAC THENL
   [SUBGOAL_THEN `w + C_in = inv eps + &5 + C_in` SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - theta1)` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "s1" THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps_n * w /\ &0 <= eps_n * C_in /\ &0 <= s1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "s1" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * s1 / (&2 * eps_n) = (h * s1) / (&2 * eps_n)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_RDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &2 * x`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `((&1 + &1 / &10) * inv b * w) * (&2 * eps_n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `((&1 + &1 / &10) * inv b * w) * (&2 * eps_n) =
                  inv b * ((&22 / &10) * eps_n * w) /\
                  h * s1 = inv b * ((h * b) * s1)` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * s1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C_in * &3 / &2) * (&2 * eps_n)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[GSYM real_div]];
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The end of part D at the first bad time ts (D5, D6): the                 *)
(* short neck path from the exposed point e y0 = Phi qy to x lifts through  *)
(* Phi (the exit lemmas, at the normalized time t' < theta1), and the       *)
(* alternatives of Thm 12.32 at the lifted point q give the cap at x.      *)
(* ========================================================================= *)

let P3H_D_FINISH = prove
 (`?eps1. &0 < eps1 /\
     !eps_n. &0 < eps_n /\ eps_n <= &1 / &4
       ==> ?dd0. &0 < dd0 /\
             !g0 A0 (G:real->real^3->real^3^3) (hs:(A)rfs_history) T1 ts h (Phi:real^3->A) x
              eps (e:real^3->A) y0 qy C C_in eps_in Kr dq delta ddx A1 epsp d1 m dq2 theta1.
               p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\ rfs_history_ok hs /\
               p2c_regular_view (rfs_view hs) /\
               p3_view_close
                 (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
                 (&0) (&1) {x | p3_std_dist g0 x < m} (rfs_view hs) T1 (inv(h pow 2)) Phi
                 {s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
                      T1 + s * h pow 2 < rfs_horizon hs} dq2 /\
               T1 = ts - &1 / rfs_vscalar (rfs_view hs) ts x /\ T1 < ts /\
               ts < rfs_horizon hs /\ &0 < h /\
               (ts - T1) / h pow 2 < theta1 /\ theta1 < &1 /\
               rfs_strong_neck (rfs_view hs) eps x ts e /\ &0 < eps /\ eps <= eps1 /\
               y0 IN rfs_neck_dom eps /\ e y0 = Phi qy /\ p3_std_dist g0 qy <= A0 + &4 /\
               (!G x t. p3_std_flow g0 (&1) G /\ &0 < t /\ t < &1
                        ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in
                                           U Y /\ x IN Y) \/
                            (?e. rfs_evolving_neck
                                   (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                  {s | &0 <= s /\ s < &1} G)
                                   eps_in x t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x)
                                   e /\
                                 !z. z IN IMAGE e (rfs_neck_dom eps_in)
                                     ==> A0 + &5 <= p3_std_dist g0 z) \/
                            (?e. rfs_evolving_neck
                                   (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                  {s | &0 <= s /\ s < &1} G)
                                   eps_in x t (&1 + eps_in) e)) /\
               (!G t x U.
                  p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1 /\
                  rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in x U
                  ==> !y l. y IN U /\ l <= 2
                            ==> lrm_deriv_norm2 l
                                  (metric_local (open_set_atlas (:real^3))
                                     (chart_at (open_set_atlas (:real^3)) y)
                                     (\z. mfd_scalar (open_set_atlas (:real^3)) (G t) x %% G t z))
                                  (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
               (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= theta1 /\
                        A1 < p3_std_dist g0 x
                        ==> lck_dist2 (rfs_kreg epsp)
                              (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                            < epsp pow 2) /\
               (!G0 q U Y (top:A topology) atlas g h W (Phi:real^3->A) d.
                  metric_field (:real^3) G0 /\
                  rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C_in eps_in U Y /\ q IN Y /\
                  (!y l. y IN U /\ l <= 2
                         ==> lrm_deriv_norm2 l
                               (metric_local (open_set_atlas (:real^3))
                                  (chart_at (open_set_atlas (:real^3)) y)
                                  (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                               (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
                  hausdorff_space top /\ smooth_manifold_atlas top atlas /\
                  riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
                  mfd_param top atlas W Phi /\ U SUBSET W /\
                  &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
                  &3 pow (rfs_kreg delta) * d < delta pow 2 /\
                  (!y. y IN W
                       ==> lck_dist2 (rfs_kreg delta) G0
                             (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
                  ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C eps U' Y' /\
                              Phi q IN Y') /\
               &1 < C_in /\
               &0 < dq /\ dq <= &1 / &300 /\ &0 <= Kr /\ &72 * sqrt Kr * dq <= &1 / &2 /\
               &0 < eps_in /\ eps_in <= &1 / &2 /\
               &1 + &72 * dq < (&1 + eps_in) * (&1 - &72 * sqrt Kr * dq) /\
               eps_in * (&7 * (inv eps + &5) + &1) <= &1 /\
               &0 < dq2 /\ dq2 <= dq /\ &0 < delta /\ dq2 <= delta / &3 pow (rfs_kreg delta) /\
               dq2 <= eps_n /\ dq2 <= ddx /\ &0 < ddx /\ ddx <= dd0 /\
               &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx /\
               A0 + &4 < d1 /\ inv eps_n < d1 /\ A1 + inv eps_n < d1 /\
               d1 + inv eps_n + inv eps_n < m /\
               &3 * eps_n * (inv eps + &5 + C_in) <= sqrt(&1 - theta1)
               ==> ?U Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts) (rfs_metric_at hs ts)
                                 C eps U Y /\ x IN Y`,
  MP_TAC(SPEC `&1 / &10` P3H_NECK_SHORT_PATH) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SP"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps_n:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps_n:real` P3H_CAP_IN_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CR"))) THEN
  MP_TAC(SPEC `eps_n:real` P3H_LIFT_SHORT_CURVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0l:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LF"))) THEN
  EXISTS_TAC `min (min dd0c dd0l) (&1 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 < inv eps_n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice at ts *)
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2C_RFS_VIEW_PARTS] THEN
  REWRITE_TAC[GSYM real_div] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT;
                                    P2C_RFS_VIEW_PARTS] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `compact_space (rfs_top_at (hs:(A)rfs_history) ts)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) ts) (rfs_metric_at hs ts) x =
                rfs_vscalar (rfs_view hs) ts x` ASSUME_TAC THENL
   [REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  ABBREV_TAC `tp = (ts - T1) / h pow 2` THEN
  SUBGOAL_THEN `&0 < tp /\ T1 + tp * h pow 2 = ts /\ (h pow 2 * Q) * tp = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tp" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `T1 = ts - &1 / Q` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= h pow 2 * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(h pow 2 * Q) * tp` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the closeness at t' = tp, read at time ts *)
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < m}`;
                 `hs:(A)rfs_history`; `T1:real`; `h:real`; `Phi:real^3->A`;
                 `{s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
                       T1 + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)}`;
                 `dq2:real`; `tp:real`] P3H_VIEW_CLOSE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open {z:real^3 | p3_std_dist g0 z < m}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) ts`; `rfs_atlas_at (hs:(A)rfs_history) ts`;
                   `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_STD_FLOW_FIELD THEN
    EXISTS_TAC `g0:real^3->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) tp)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. A1 < p3_std_dist g0 z
        ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow tp))
              ((G:real->real^3->real^3^3) tp) z < epsp pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `epsp:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `(G:real->real^3->real^3^3) tp`; `tp:real`;
                 `A1:real`; `epsp:real`; `eps_n:real`; `ddx:real`; `d1:real`]
                P3H_SHELL_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!y. p3_std_dist g0 y < m
        ==> lck_dist2 (rfs_kreg eps_n) ((G:real->real^3->real^3^3) tp)
              (\z. inv(h pow 2) %%
                   rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) ts) (Phi:real^3->A)
                                (rfs_metric_at hs ts) z) y < ddx pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dq2) ((G:real->real^3->real^3^3) tp)
                  (\z. inv(h pow 2) %%
                       rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) ts) (Phi:real^3->A)
                                    (rfs_metric_at hs ts) z) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `{z:real^3 | p3_std_dist g0 z < m}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
         [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
          EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) ts` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
        MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dq2 pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the short neck path from e y0 = Phi qy to x, and its lift *)
  USE_THEN "SP" (MP_TAC o SPECL
   [`rfs_top_at (hs:(A)rfs_history) ts`; `rfs_atlas_at (hs:(A)rfs_history) ts`;
    `rfs_metric_at (hs:(A)rfs_history) ts`; `eps:real`; `x:A`; `e:real^3->A`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `len = mfd_length (rfs_atlas_at (hs:(A)rfs_history) ts) (rfs_metric_at hs ts)
                               (gamma:real->A) (&0) (&1)` THEN
  SUBGOAL_THEN `&0 <= len` ASSUME_TAC THENL
   [EXPAND_TAC "len" THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
    EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) ts` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real`; `Q:real`; `len:real`; `eps:real`; `eps_n:real`; `C_in:real`;
                 `tp:real`; `theta1:real`] P3H_FINISH_ARITH2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:real`; `Q:real`; `len:real`; `eps:real`; `eps_in:real`]
                P3H_FINISH_ARITH1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "LF" (MP_TAC o SPECL
   [`g0:real^3->real^3^3`; `A0:real`; `rfs_top_at (hs:(A)rfs_history) ts`;
    `rfs_atlas_at (hs:(A)rfs_history) ts`; `rfs_metric_at (hs:(A)rfs_history) ts`;
    `Phi:real^3->A`; `m:real`; `h:real`; `(G:real->real^3->real^3^3) tp`; `tp:real`;
    `d1:real`; `ddx:real`; `gamma:real->A`; `qy:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `c:real->real^3`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Thm 12.32 and the C^2 bound at (q, t'), and D6 *)
  FIRST_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `q:real^3`; `tp:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
          (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!z U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3))
            ((G:real->real^3->real^3^3) tp) C_in eps_in z U
          ==> !y l. y IN U /\ l <= 2
                    ==> lrm_deriv_norm2 l
                          (metric_local (open_set_atlas (:real^3))
                             (chart_at (open_set_atlas (:real^3)) y)
                             (\w. mfd_scalar (open_set_atlas (:real^3)) (G tp) z %% G tp w))
                          (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) / h * len` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `tp:real`; `q:real^3`;
    `qy:real^3`; `c:real->real^3`; `sqrt(&2) / h * len`; `rfs_top_at (hs:(A)rfs_history) ts`;
    `rfs_atlas_at (hs:(A)rfs_history) ts`; `rfs_metric_at (hs:(A)rfs_history) ts`; `h:real`;
    `m:real`; `Phi:real^3->A`; `x:A`; `C:real`; `eps:real`; `C_in:real`; `eps_in:real`;
    `Kr:real`; `dq:real`; `delta:real`; `eps_n:real`; `dd0c:real`; `ddx:real`;
    `d1 + inv eps_n`; `A1:real`; `epsp:real`; `dq2:real`; `d:real`] P3H_D_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The numerical facts about the constants chosen in the                    *)
(* final assembly of part D (P3H_PART_D, unit pc_p3_c172f).                 *)
(* ========================================================================= *)

let P3H_NUM_DQ = prove
 (`!eps_in Kr dq.
     &0 < eps_in /\ eps_in <= &1 / &2 /\ &0 <= Kr /\
     dq = min (&1 / &300) (eps_in / (&500 * (&1 + sqrt Kr)))
     ==> &0 < dq /\ dq <= &1 / &300 /\ &72 * sqrt Kr * dq <= &1 / &2 /\
         &1 + &72 * dq < (&1 + eps_in) * (&1 - &72 * sqrt Kr * dq)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k = sqrt Kr` THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps_in / (&500 * (&1 + k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dq /\ dq <= &1 / &300 /\ dq * (&500 * (&1 + k)) <= eps_in`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= k ==> &0 < &500 * (&1 + k)`;
               ASSUME `&0 <= k`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * dq /\ eps_in * (k * dq) <= (&1 / &2) * (k * dq)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC);;

let P3H_NUM_THETA = prove
 (`!c M dq theta0 theta1.
     &0 < c /\ &0 <= M /\ &0 < dq /\
     theta0 = max (&0) (&1 - c / (&2 * M + &144 * dq + &1)) /\
     theta1 = (&1 + theta0) / &2
     ==> &0 <= theta0 /\ theta0 < theta1 /\ theta1 < &1 /\ &1 / &2 <= theta1 /\
         !s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq < c / (&1 - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = &2 * M + &144 * dq + &1` THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c / B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= theta0 /\ theta0 < &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  SUBGOAL_THEN `&2 * M + &144 * dq = B - &1` SUBST1_TAC THENL
   [EXPAND_TAC "B" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c / B <= &1` THENL
   [SUBGOAL_THEN `&1 - s <= c / B` ASSUME_TAC THENL
     [UNDISCH_TAC `theta0 <= s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(B - &1) * c / B` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(B - &1) * c / B = c - c / B` SUBST1_TAC THENL
       [UNDISCH_TAC `&1 <= B` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(B - &1) * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `B < c` MP_TAC THENL
       [UNDISCH_TAC `~(c / B <= &1)` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
          REAL_ARITH `&1 <= B ==> &0 < B`] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]);;

let P3H_NUM_EPSN = prove
 (`!eps C_in theta1 eps_n.
     &0 < eps /\ &1 < C_in /\ theta1 < &1 /\
     eps_n = min (&1 / &4) (sqrt(&1 - theta1) / (&3 * (inv eps + &5 + C_in)))
     ==> &0 < eps_n /\ eps_n <= &1 / &4 /\
         &3 * eps_n * (inv eps + &5 + C_in) <= sqrt(&1 - theta1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &3 * (inv eps + &5 + C_in)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &1 < C ==> &0 < &3 * (x + &5 + C)`) THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - theta1) / (&3 * (inv eps + &5 + C_in))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps_n <= sqrt(&1 - theta1) / (&3 * (inv eps + &5 + C_in))` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P3H_NUM_EPSIN = prove
 (`!eps K eps_in.
     &0 < eps /\ eps <= &1 / &8 /\ &1 <= K /\ eps_in = eps / max K (&40)
     ==> &0 < eps_in /\ eps_in <= eps /\ eps_in <= &1 / &2 /\ K * eps_in <= eps /\
         eps_in * (&7 * (inv eps + &5) + &1) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K' = max K (&40)` THEN
  SUBGOAL_THEN `&40 <= K' /\ K <= K'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps_in * K' = eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < K'` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps_in` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&40 * eps_in <= eps /\ K * eps_in <= eps` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps_in * K' = eps` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps_in * (&7 * (inv eps + &5) + &1) = &7 * eps_in * inv eps + &36 * eps_in`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps_in * inv eps <= &1 / &40` ASSUME_TAC THENL
   [SUBGOAL_THEN `eps_in * inv eps = inv K'` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `eps_in * K' = eps`)) THEN
      UNDISCH_TAC `&0 < K'` THEN UNDISCH_TAC `&0 < eps_in` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_NUM_DD3 = prove
 (`!A0 D dd3.
     &1 <= D /\ dd3 = min (&1 / &10) (min (inv(abs A0 + &5)) (D / (&72 * (&1 + D))))
     ==> &0 < dd3 /\ dd3 <= &1 / &10 /\ A0 + &4 < inv dd3 /\ &72 * (&1 + D) * dd3 <= D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(abs A0 + &5) /\ &0 < D / (&72 * (&1 + D))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd3 /\ dd3 <= &1 / &10 /\ dd3 <= inv(abs A0 + &5) /\
                dd3 <= D / (&72 * (&1 + D))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs A0 + &5` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `dd3 <= D / (&72 * (&1 + D))` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= D ==> &0 < &72 * (&1 + D)`] THEN
    REAL_ARITH_TAC]);;

