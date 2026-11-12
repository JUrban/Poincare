(* ========================================================================= *)
(* Unit pc_p2b_g3a (Part 2B): G3 part a, the reduced volume of linf          *)
(* (vocabulary of pc_p2b_w920g): the limit V of the reduced volume of the    *)
(* kappa solution (FL5), Gaussian bounds of l on the flow (Lemma 9.25 with   *)
(* Claim 9.15), uniform Gaussian tails by Bishop-Gromov                      *)
(* (P2BX_MFD_GAUSS_TAIL), integrals over images of compact sets of the limit *)
(* (LIM_QF_CLOSE, pullback isometries, P2BC_INTEGRAL_RESTRICT), balls about  *)
(* q_k inside images of compact sets (LIM_BALL), and p2bg_rvol linf V.       *)
(* ========================================================================= *)

needs "src/pc_p2b_g1.ml";;
needs "src/pc_p2b_g3m.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_rf_unique_ncint.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The views of a kappa solution, the limit V of its reduced volume, the     *)
(* Gaussian bound of l and the uniform tails.                                *)
(* ========================================================================= *)

let P2BX_KVIEW_SLICE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) s.
     rfs_vtop (p2b_kview (top,atlas) g) s = (if s <= &0 then top else discrete_topology {}) /\
     rfs_vatlas (p2b_kview (top,atlas) g) s = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) g) s = g s`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM]);;

let P2BX_KVIEW_HYP = prove
 (`!kappa (top:A topology) atlas (g:real->A->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> !n:num s. ~(topspace(rfs_vtop ((\k:num. p2b_kview (top,atlas) g) n) s) = {})
                   ==> smooth_manifold_atlas (rfs_vtop ((\k:num. p2b_kview (top,atlas) g) n) s)
                                             (rfs_vatlas ((\k:num. p2b_kview (top,atlas) g) n) s) /\
                       riemannian_metric (rfs_vatlas ((\k:num. p2b_kview (top,atlas) g) n) s)
                                         (rfs_vmetric ((\k:num. p2b_kview (top,atlas) g) n) s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BX_KVIEW_SLICE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY]);;

(* The reduced volume of the kappa solution: the integral at tau and its    *)
(* limit V at infinity (FL5: positive, nonincreasing).                       *)

let P2BX_KFRV_FACTS = prove
 (`!(u:A->bool) kappa top atlas (g:real->A->real^3^3) p.
     P2A_FLOW_RV_STATEMENT u (:3) /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top
     ==> (!tau. &0 < tau
                ==> mfd_integrable_on (top,atlas) (g(--tau))
                      (\q. exp(--(p2b_klx (top,atlas) g p tau q)) / sqrt tau pow 3)
                      (topspace top) /\
                    p2b_kfrv (top,atlas) g p tau =
                    mfd_integral (top,atlas) (g(--tau)) (topspace top)
                      (\q. exp(--(p2b_klx (top,atlas) g p tau q)) / sqrt tau pow 3)) /\
         ?V. &0 <= V /\ ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
             (!t. &0 < t ==> V <= p2b_kfrv (top,atlas) g p t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL5") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN
   `!a tau1 tau2.
      a < &0 /\ &0 < tau1 /\ tau1 <= tau2 /\ tau2 < --a
      ==> mfd_integrable_on (top,atlas) ((g:real->A->real^3^3) (&0 - tau2))
            (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p tau2 q)) /
                 sqrt tau2 pow 3) (topspace top) /\
          &0 < p2a_frv (top,atlas) a (&0) g p tau2 /\
          p2a_frv (top,atlas) a (&0) g p tau2 <= p2a_frv (top,atlas) a (&0) g p tau1`
  (LABEL_TAC "FV") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "FL5" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `a:real`; `&0`; `g:real->A->real^3^3`; `p:A`] o
                    REWRITE_RULE[P2A_FLOW_RV_STATEMENT]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `tau2:real`)
                               (MP_TAC o SPECL [`tau1:real`; `tau2:real`] o CONJUNCT1)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    USE_THEN "FV" (MP_TAC o SPECL [`--(&2 * tau)`; `tau:real`; `tau:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2b_kfrv; p2a_frv; p2b_klx; REAL_SUB_LZERO; DIMINDEX_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `RV = \t. p2b_kfrv (top,atlas) (g:real->A->real^3^3) p t` THEN
  SUBGOAL_THEN `!t. &0 < t ==> &0 < (RV:real->real) t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "RV" THEN REWRITE_TAC[p2b_kfrv] THEN
    USE_THEN "FV" (MP_TAC o SPECL [`--(&2 * t)`; `t:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t1 t2. &0 < t1 /\ t1 <= t2 ==> (RV:real->real) t2 <= RV t1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "RV" THEN
    SUBGOAL_THEN
     `p2b_kfrv (top,atlas) (g:real->A->real^3^3) p t1 =
      p2a_frv (top,atlas) (--(&2 * t2)) (&0) g p t1 /\
      p2b_kfrv (top,atlas) (g:real->A->real^3^3) p t2 =
      p2a_frv (top,atlas) (--(&2 * t2)) (&0) g p t2`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2BX_KFRV_VIEW THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "FV" (MP_TAC o SPECL [`--(&2 * t2)`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `RV:real->real` P2BX_DECREASING_LIMIT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  EXPAND_TAC "RV" THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `inf {p2b_kfrv (top,atlas) (g:real->A->real^3^3) p t | &0 < t}` THEN
  ASM_REWRITE_TAC[]);;

(* The Gaussian bound of the reduced volume integrand at tau_k t (MT Cor    *)
(* 9.26 from Lemma 9.25 at q_k and Claim 9.15).                             *)

let P2BX_FLOW_GAUSS = prove
 (`!(u:A->bool) top atlas (g:real->A->real^3^3) p tau q (top':B topology) atlas' g' xl W phi
    c1 k t x.
     P2B_COR_9_10_STATEMENT u /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\ &0 < c1 /\
     (!kappa top atlas (g:real->A->real^3^3) p t p1 q1.
        p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < t /\
        p1 IN topspace top /\ q1 IN topspace top
        ==> (c1 * mfd_dist (top,atlas) (g(--t)) p1 q1 pow 2) / t -
            p2b_klx (top,atlas) g p t q1 - &1
            <= p2b_klx (top,atlas) g p t p1) /\
     &0 < t /\ x IN topspace top
     ==> exp(--(p2b_klx (top,atlas) g p (tau k * t) x)) / sqrt(tau k * t) pow 3
         <= exp(&3 / &2 * (t + inv(t pow 2)) + &1) *
            exp(--(c1 * (mfd_dist (top,atlas) (g(--(tau k * t))) (q k) x / sqrt(tau k * t))
                         pow 2)) /
            sqrt(tau k * t) pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L925") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `&0 < (tau:num->real) k * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`;
                 `(tau:num->real) k`; `(q:num->A) k`; `t:real`] P2BX_CLAIM_9_15) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "L925" (MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                   `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                                   `p:A`; `(tau:num->real) k * t`; `x:A`; `(q:num->A) k`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->A->real^3^3) (--((tau:num->real) k * t))) x (q k) =
                mfd_dist (top,atlas) (g(--(tau k * t))) (q k) x` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->A->real^3^3) (--((tau:num->real) k * t))) (q k) x` THEN
  ABBREV_TAC `s = (tau:num->real) k * t` THEN
  SUBGOAL_THEN `(d / sqrt s) pow 2 = d pow 2 / s` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt s pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  UNDISCH_TAC `(c1 * mfd_dist (top,atlas) ((g:real->A->real^3^3) (--s)) x ((q:num->A) k) pow 2) / s -
               p2b_klx (top,atlas) g p s (q k) - &1 <= p2b_klx (top,atlas) g p s x` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2b_klx (top,atlas) (g:real->A->real^3^3) p s ((q:num->A) k) <=
               &3 / &2 * (t + inv(t pow 2))` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* Uniform Gaussian tails of the reduced volume integrands of the flow at   *)
(* the times tau_k t outside the balls about q_k of radius sqrt(tau_k t) R. *)

let P2BX_FLOW_TAIL = prove
 (`!(u:A->bool) top atlas (g:real->A->real^3^3) p tau q (top':B topology) atlas' g' xl W phi
    t e.
     P2B_COR_9_10_STATEMENT u /\ P2B_LEMMA_9_25_STATEMENT u /\ P2A_FLOW_RV_STATEMENT u (:3) /\
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT u /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\ &0 < t /\ &0 < e
     ==> ?R. &0 <= R /\
             !k. mfd_integrable_on (top,atlas) (g(--(tau k * t)))
                   (\x. exp(--(p2b_klx (top,atlas) g p (tau k * t) x)) / sqrt(tau k * t) pow 3)
                   (topspace top DIFF
                    mfd_ball (top,atlas) (g(--(tau k * t))) (q k) (sqrt(tau k * t) * R)) /\
                 mfd_integral (top,atlas) (g(--(tau k * t)))
                   (topspace top DIFF
                    mfd_ball (top,atlas) (g(--(tau k * t))) (q k) (sqrt(tau k * t) * R))
                   (\x. exp(--(p2b_klx (top,atlas) g p (tau k * t) x)) / sqrt(tau k * t) pow 3)
                 <= e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FL5") (CONJUNCTS_THEN2 (LABEL_TAC "BG") STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[P2B_LEMMA_9_25_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L925"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPEC `c1:real` (INST_TYPE [`:3`,`:N`] P2BX_MFD_GAUSS_TAIL)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TAIL"))) THEN
  ABBREV_TAC `C = exp(&3 / &2 * (t + inv(t pow 2)) + &1)` THEN
  ABBREV_TAC `A = &4 / &3 * pi` THEN
  SUBGOAL_THEN `&0 <= C /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "A"] THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * A * K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  EXISTS_TAC `sqrt(&2 * ((C * A * K) / e) / c1)` THEN
  SUBGOAL_THEN `&0 <= &2 * ((C * A * K) / e) / c1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN X_GEN_TAC `k:num` THEN
  ABBREV_TAC `s = (tau:num->real) k * t` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2 * s)) (&0) (g:real->A->real^3^3)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2AF_CBFLOW_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) (--s)) /\
                mfd_complete (top,atlas) (g(--s))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`]
                P2BX_KFRV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "TAIL" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) (--s)`;
    `\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p s x)) / sqrt s pow 3`;
    `(q:num->A) k`; `sqrt s`; `sqrt(&2 * ((C * A * K) / e) / c1)`; `C:real`; `A:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) (--s)`; `(q:num->A) k`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      USE_THEN "BG" (MP_TAC o SPECL
       [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) (--s)`;
        `(q:num->A) k`; `r:real`; `r:real`;
        `mfd_volume (top,atlas) ((g:real->A->real^3^3) (--s))
           (mfd_ball (top,atlas) (g(--s)) ((q:num->A) k) r)`;
        `mfd_volume (top,atlas) ((g:real->A->real^3^3) (--s))
           (mfd_ball (top,atlas) (g(--s)) ((q:num->A) k) r)`] o
       REWRITE_RULE[P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "A" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN SIMP_TAC[]];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN EXPAND_TAC "C" THEN
      EXPAND_TAC "s" THEN MATCH_MP_TAC P2BX_FLOW_GAUSS THEN
      MAP_EVERY EXISTS_TAC [`u:A->bool`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                            `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * A * K * exp(--(c1 / &2 * sqrt(&2 * ((C * A * K) / e) / c1) pow 2))` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  SUBGOAL_THEN `c1 / &2 * &2 * ((C * A * K) / e) / c1 = (C * A * K) / e` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < c1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `y = (C * A * K) / e` THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--y) <= inv(&1 + y)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C * A * K) * inv(&1 + y)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * A * K = e * y` SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= y ==> &0 < &1 + y`] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Integrability on compact sets of functions continuous in charts;          *)
(* continuity of linf in the charts of the limit.                            *)
(* ========================================================================= *)

let P2BX_MFD_INTEGRABLE_CHARTCONT = prove
 (`!top atlas (g:A->real^N^N) f K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ mfd_lebesgue_measurable (top,atlas) K /\
     (!c. c IN atlas ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c))
     ==> mfd_integrable_on (top,atlas) g f K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `K:A->bool`]
                RFU_COMPACT_IN_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
    (X_CHOOSE_THEN `q:num->real^N` STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[mfd_integrable_on] THEN
  EXISTS_TAC `sum(1..k) (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                   ((E:num->A->bool) n))
                                    (mfd_chart_integrand atlas (g:A->real^N^N) f (c n))))` THEN
  MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `p:num->real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[(p:num->real^N) n,q n]` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN
     `mfd_chart_integrand atlas (g:A->real^N^N) (f:A->real) ((c:num->(A->bool)#(A->real^N)) n) =
      (\y. drop(lift(mfd_density atlas (c n) g y)) % lift(f(chart_inv (c n) y)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; LIFT_DROP; GSYM LIFT_CMUL] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) (FST(c n))` THEN
    ASM_SIMP_TAC[GRGV_DENSITY_CONTINUOUS] THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `mfd_chart_partition (atlas:((A->bool)#(A->real^N))->bool) K c E` THEN
    REWRITE_TAC[mfd_chart_partition] THEN MESON_TAC[]]);;

(* linf(t,.) read in a chart of the limit is continuous (locally Lipschitz *)
(* on chart boxes, P2BX_CDATA_LIMIT of pc_p2b_p920).                         *)

let P2BX_LINF_SLICE_CONT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c t.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ &0 < t
     ==> (\x. lift(linf t (chart_inv c x))) continuous_on IMAGE (SND c) (FST c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `pastecart (x0:real^3) (lift t)`] P2BX_CBOX_BALL) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`c:(B->bool)#(B->real^3)`;
                              `ball(pastecart (x0:real^3) (lift t),r)`] o
    CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2bg_g1out] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_g1out")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m0:num`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `ball(pastecart (x0:real^3) (lift t),r)`; `\j. (sub:num->num)(m0 + j)`;
                 `linf:real->B->real`] P2BX_CDATA_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`ball(pastecart (x0:real^3) (lift t),r)`;
                 `p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`]
                WAN_LOCLIP_CONTINUOUS_ON) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z)) continuous
                at (pastecart (x0:real^3) (lift t))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z)`;
                   `ball(pastecart (x0:real^3) (lift t),r)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `pastecart (x0:real^3) (lift t)`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((linf:real->B->real) t (chart_inv (c:(B->bool)#(B->real^3)) x))) =
                (\z. lift(p2bw_cfun c linf z)) o (\x:real^3. pastecart x (lift t))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST]);;

(* ========================================================================= *)
(* Integrals over images under a diffeomorphism of open sets (pullback       *)
(* isometry on the restricted manifolds) and their comparison under          *)
(* two-sided quadratic form bounds (the integral versions of P2BC_VOLUME_PB, *)
(* MFD_HAS_VOLUME_COMPARE_QF and P2BC_VOLUME_PB_COMPARE).                    *)
(* ========================================================================= *)

let P2BX_INTEGRAL_PB = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) h S v.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U
     ==> (mfd_has_integral (top',atlas') g' h (IMAGE psi S) v <=>
          mfd_has_integral (subtopology top U,restrict_atlas atlas U)
            (mfd_pullback_metric (restrict_atlas atlas U) (restrict_atlas atlas' U') psi
               (restrict_metric atlas' U' g')) (h o psi) S v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas' U')
                  (restrict_metric atlas' U' (g':B->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) S SUBSET U'` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (psi:A->B) U` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `U':B->bool`; `h:B->real`; `IMAGE (psi:A->B) S`; `v:real`]
                P2BC_INTEGRAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_ISOMETRY THEN EXISTS_TAC `psi':B->A` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas atlas U)
      (mfd_pullback_metric (restrict_atlas atlas U) (restrict_atlas atlas' U') (psi:A->B)
         (restrict_metric atlas' U' (g':B->real^N^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `subtopology top' (U':B->bool)`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]);;

let P2BX_INTEGRAL_COMPARE_QF = prove
 (`!top atlas (G1:A->real^3^3) G2 ff S v1 v2 lam.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas G1 /\ riemannian_metric atlas G2 /\ &0 <= lam /\
     (!x. x IN S ==> &0 <= ff x) /\
     mfd_has_integral (top,atlas) G1 ff S v1 /\ mfd_has_integral (top,atlas) G2 ff S v2 /\
     (!y w. y IN S ==> w dot (G1 y ** w) <= lam * (w dot (G2 y ** w)))
     ==> v1 <= lam * sqrt lam * v2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G2:A->real^3^3`; `ff:A->real`; `S:A->bool`; `v2:real`]
                  MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_lebesgue_measurable];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_HAS_INTEGRAL_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G2:A->real^3^3`;
    `\x:A. ff x * sqrt(det((G1:A->real^3^3) x)) / sqrt(det((G2:A->real^3^3) x))`;
    `\x:A. (lam * sqrt lam) * ff x`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G2:A->real^3^3`; `G1:A->real^3^3`; `ff:A->real`; `S:A->bool`;
                   `v1:real`] MFD_HAS_INTEGRAL_CHANGE_METRIC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G2:A->real^3^3`;
                   `ff:A->real`; `S:A->bool`; `v2:real`; `lam * sqrt lam`] MFD_HAS_INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(det((G2:A->real^3^3) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(det((G1:A->real^3^3) x)) <= (lam * sqrt lam) * sqrt(det((G2:A->real^3^3) x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * sqrt lam = sqrt lam pow dimindex(:3)` SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_3; ARITH_RULE `3 = SUC 2`; real_pow] THEN
      ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC GRGA_SQRT_DET_QF_LE THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN
    ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ff:A->real) x * (lam * sqrt lam)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ];
    REAL_ARITH_TAC]);;

(* The sandwich: images under psi of the integral of a nonnegative h when  *)
(* the pullback metric scaled by c is (1 +/- d)-close to g on S.           *)

let P2BX_PB_INTEGRAL_SANDWICH = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' S h v v' c d.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\
     &0 < c /\ &0 <= d /\ d < &1 /\ (!x. &0 <= h x) /\
     (!y w. y IN S
            ==> abs(c * (w dot (mfd_pullback_metric atlas atlas' psi g' y ** w)) -
                    w dot (g y ** w)) <= d * (w dot (g y ** w))) /\
     mfd_has_integral (top,atlas) g (h o psi) S v /\
     mfd_has_integral (top',atlas') g' h (IMAGE psi S) v'
     ==> c * sqrt c * v' <= (&1 + d) * sqrt(&1 + d) * v /\
         (&1 - d) * sqrt(&1 - d) * v <= c * sqrt c * v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = mfd_pullback_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                     (restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U')
                     (psi:A->B) (restrict_metric atlas' U' (g':B->real^3^3))` THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas' U') (restrict_metric atlas' U' (g':B->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (h1:A->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `subtopology top' (U':B->bool)`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (restrict_metric atlas U (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_integral (subtopology top U,restrict_atlas atlas U)
                  (restrict_metric atlas U (g:A->real^3^3)) ((h:B->real) o (psi:A->B)) S v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `U:A->bool`; `(h:B->real) o (psi:A->B)`; `S:A->bool`; `v:real`]
                  P2BC_INTEGRAL_RESTRICT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_integral (subtopology top U,restrict_atlas atlas U) (h1:A->real^3^3)
                  ((h:B->real) o (psi:A->B)) S v'`
  ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^3^3`;
                   `h:B->real`; `S:A->bool`; `v':real`] P2BX_INTEGRAL_PB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> ?J. (h1:A->real^3^3) y =
                transp J ** mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** J /\
                restrict_metric atlas U (g:A->real^3^3) y = transp J ** g y ** J`
  (LABEL_TAC "J") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXPAND_TAC "h1" THEN
    MATCH_MP_TAC P2BC_RPB_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (U:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                   `h1:A->real^3^3`; `restrict_metric atlas U (g:A->real^3^3)`;
                   `(h:B->real) o (psi:A->B)`; `S:A->bool`; `v':real`; `v:real`;
                   `(&1 + d) / c`] P2BX_INTEGRAL_COMPARE_QF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
      USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:A) IN S`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `J:real^3^3` (CONJUNCTS_THEN SUBST1_TAC)) THEN
      REWRITE_TAC[P2BC_QF_CONG] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `(J:real^3^3) ** (w:real^3)`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`(J ** w) dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y **
                 J ** (w:real^3))`,`a:real`) THEN
      SPEC_TAC(`(J ** w) dot ((g:A->real^3^3) y ** J ** (w:real^3))`,`b:real`) THEN
      REPEAT GEN_TAC THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> ((&1 + d) / c) * b = ((&1 + d) * b) / c`;
                   REAL_LE_RDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * sqrt c * ((&1 + d) / c * sqrt((&1 + d) / c) * v)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[SQRT_DIV] THEN
      UNDISCH_TAC `&0 < sqrt c` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                 `restrict_metric atlas U (g:A->real^3^3)`; `h1:A->real^3^3`;
                 `(h:B->real) o (psi:A->B)`; `S:A->bool`; `v:real`; `v':real`;
                 `c / (&1 - d)`] P2BX_INTEGRAL_COMPARE_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:A) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `J:real^3^3` (CONJUNCTS_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[P2BC_QF_CONG] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `(J:real^3^3) ** (w:real^3)`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(J ** w) dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y **
               J ** (w:real^3))`,`a:real`) THEN
    SPEC_TAC(`(J ** w) dot ((g:A->real^3^3) y ** J ** (w:real^3))`,`b:real`) THEN
    REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < &1 - d ==> (c / (&1 - d)) * a = (c * a) / (&1 - d)`;
                 REAL_LE_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 - d /\ &0 < sqrt(&1 - d)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - d) * sqrt(&1 - d) * (c / (&1 - d) * sqrt(c / (&1 - d)) * v')` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[SQRT_DIV] THEN
    UNDISCH_TAC `&0 < sqrt(&1 - d)` THEN UNDISCH_TAC `&0 < &1 - d` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* The integral over psi(S) as an integral over S for the metric g, with a   *)
(* density between the bounds given by the closeness of the scaled pullback  *)
(* metric to g.                                                              *)
(* ========================================================================= *)

let P2BX_PB_DENSITY = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' S h v' c d.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\
     &0 < c /\ &0 <= d /\ d < &1 /\ (!x. &0 <= h x) /\
     (!y w. y IN S
            ==> abs(c * (w dot (mfd_pullback_metric atlas atlas' psi g' y ** w)) -
                    w dot (g y ** w)) <= d * (w dot (g y ** w))) /\
     mfd_has_integral (top',atlas') g' h (IMAGE psi S) v'
     ==> ?F1. mfd_has_integral (top,atlas) g F1 S v' /\
              !y. y IN S
                  ==> ((&1 - d) * sqrt(&1 - d)) / (c * sqrt c) * h(psi y) <= F1 y /\
                      F1 y <= ((&1 + d) * sqrt(&1 + d)) / (c * sqrt c) * h(psi y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = mfd_pullback_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                     (restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U')
                     (psi:A->B) (restrict_metric atlas' U' (g':B->real^3^3))` THEN
  ABBREV_TAC `rg = restrict_metric (atlas:((A->bool)#(A->real^3))->bool) U (g:A->real^3^3)` THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas' U') (restrict_metric atlas' U' (g':B->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (h1:A->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `subtopology top' (U':B->bool)`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (rg:A->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "rg" THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_integral (subtopology top U,restrict_atlas atlas U) (h1:A->real^3^3)
                  ((h:B->real) o (psi:A->B)) S v'`
  ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^3^3`;
                   `h:B->real`; `S:A->bool`; `v':real`] P2BX_INTEGRAL_PB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x. ((h:B->real) o (psi:A->B)) x * sqrt(det((h1:A->real^3^3) x)) /
                  sqrt(det((rg:A->real^3^3) x))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `U:A->bool`;
                   `\x. ((h:B->real) o (psi:A->B)) x * sqrt(det((h1:A->real^3^3) x)) /
                        sqrt(det((rg:A->real^3^3) x))`; `S:A->bool`; `v':real`]
                  P2BC_INTEGRAL_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                   `rg:A->real^3^3`; `h1:A->real^3^3`; `(h:B->real) o (psi:A->B)`;
                   `S:A->bool`; `v':real`] MFD_HAS_INTEGRAL_CHANGE_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(y:A) IN topspace(subtopology top U)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(det((h1:A->real^3^3) y)) /\ &0 < sqrt(det((rg:A->real^3^3) y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`;
                          `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?J. (h1:A->real^3^3) y =
        transp J ** mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** J /\
        (rg:A->real^3^3) y = transp J ** g y ** J`
  (X_CHOOSE_THEN `J:real^3^3` STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "rg"] THEN
    MATCH_MP_TAC P2BC_RPB_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. (&1 - d) * (w dot ((rg:A->real^3^3) y ** w)) <= c * (w dot ((h1:A->real^3^3) y ** w)) /\
        c * (w dot (h1 y ** w)) <= (&1 + d) * (w dot (rg y ** w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN ASM_REWRITE_TAC[P2BC_QF_CONG] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `(J:real^3^3) ** (w:real^3)`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ &0 < &1 - d /\ &0 < sqrt(&1 - d) /\ &0 < sqrt(&1 + d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(det((h1:A->real^3^3) y)) <= ((&1 + d) * sqrt(&1 + d)) / (c * sqrt c) *
                                    sqrt(det((rg:A->real^3^3) y)) /\
    sqrt(det(rg y)) <= (c * sqrt c) / ((&1 - d) * sqrt(&1 - d)) * sqrt(det(h1 y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `((&1 + d) * sqrt(&1 + d)) / (c * sqrt c) = sqrt((&1 + d) / c) pow dimindex(:3)`
      SUBST1_TAC THENL
       [REWRITE_TAC[DIMINDEX_3; ARITH_RULE `3 = SUC 2`; real_pow] THEN
        SUBGOAL_THEN `&0 <= (&1 + d) / c` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_POW_2] THEN REWRITE_TAC[SQRT_DIV] THEN
        UNDISCH_TAC `&0 < sqrt c` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC GRGA_SQRT_DET_QF_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
        REWRITE_TAC[positive_definite; symmetric_matrix] THEN
        ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
        MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
        REWRITE_TAC[positive_definite; symmetric_matrix] THEN
        ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `w:real^3` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `rg:A->real^3^3`)) (concl th) &&
          can (find_term ((=) `d:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> (&1 + d) / c * x = ((&1 + d) * x) / c`;
                     REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `(c * sqrt c) / ((&1 - d) * sqrt(&1 - d)) = sqrt(c / (&1 - d)) pow dimindex(:3)`
      SUBST1_TAC THENL
       [REWRITE_TAC[DIMINDEX_3; ARITH_RULE `3 = SUC 2`; real_pow] THEN
        SUBGOAL_THEN `&0 <= c / (&1 - d)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_POW_2] THEN REWRITE_TAC[SQRT_DIV] THEN
        UNDISCH_TAC `&0 < sqrt(&1 - d)` THEN UNDISCH_TAC `&0 < &1 - d` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC GRGA_SQRT_DET_QF_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
        REWRITE_TAC[positive_definite; symmetric_matrix] THEN
        ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
        MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
        REWRITE_TAC[positive_definite; symmetric_matrix] THEN
        ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `w:real^3` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `rg:A->real^3^3`)) (concl th) &&
          can (find_term ((=) `d:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < &1 - d ==> c / (&1 - d) * x = (c * x) / (&1 - d)`;
                     REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (h:B->real) ((psi:A->B) y)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * sqrt c /\ &0 < (&1 - d) * sqrt(&1 - d)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt(det((h1:A->real^3^3) y))` THEN
  ABBREV_TAC `s2 = sqrt(det((rg:A->real^3^3) y))` THEN
  ABBREV_TAC `a = ((&1 - d) * sqrt(&1 - d)) / (c * sqrt c)` THEN
  ABBREV_TAC `b = ((&1 + d) * sqrt(&1 + d)) / (c * sqrt c)` THEN
  ABBREV_TAC `hy = (h:B->real) ((psi:A->B) y)` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c * sqrt c) / ((&1 - d) * sqrt(&1 - d)) = inv a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_INV_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= s1 / s2 /\ s1 / s2 <= b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `s2 <= (c * sqrt c) / ((&1 - d) * sqrt(&1 - d)) * s1` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * (inv a * s1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The integrals of the reduced volume integrands over the images of a       *)
(* compact set of the limit converge to the integral of exp(-linf(t,.)) /    *)
(* t^(3/2) over it.                                                          *)
(* ========================================================================= *)

let P2BX_POW32_BOUNDS = prove
 (`!d. &0 <= d /\ d <= &1
       ==> (&1 + d) * sqrt(&1 + d) <= &1 + &3 * d /\
           &1 - &2 * d <= (&1 - d) * sqrt(&1 - d)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + d) <= &1 + d /\ &1 - d <= sqrt(&1 - d)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= d * (&1 + d) ==> &1 + d <= (&1 + d) * (&1 + d)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= d * (&1 - d) ==> (&1 - d) * (&1 - d) <= &1 - d`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + d) * (&1 + d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `d * d <= d ==> (&1 + d) * (&1 + d) <= &1 + &3 * d`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - d) * (&1 - d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= d * d ==> &1 - &2 * d <= (&1 - d) * (&1 - d)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let P2BX_EXP_NEG_LIP = prove
 (`!a b. &0 <= a /\ &0 <= b ==> abs(exp(--a) - exp(--b)) <= abs(a - b)`,
  SUBGOAL_THEN `!a b. &0 <= a /\ a <= b ==> abs(exp(--a) - exp(--b)) <= abs(a - b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `exp(--b) = exp(--a) * exp(--(b - a))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `--(b - a)` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `exp(--a) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < exp(--a)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(b - a)) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `exp(--a) - exp(--a) * exp(--(b - a)) = exp(--a) * (&1 - exp(--(b - a)))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * abs(&1 - exp(--(b - a)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPECL [`a:real`; `b:real`] REAL_LE_TOTAL) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let P2BX_MFD_INTEGRAL_DIFF_BOUND = prove
 (`!top atlas (g:A->real^N^N) f1 f2 S v1 v2 w M.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g f1 S v1 /\ mfd_has_integral (top,atlas) g f2 S v2 /\
     mfd_has_volume (top,atlas) g S w /\ (!x. x IN S ==> abs(f1 x - f2 x) <= M)
     ==> abs(v1 - v2) <= M * w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f1:A->real`; `f2:A->real`; `S:A->bool`; `v1:real`; `v2:real`]
                MFD_HAS_INTEGRAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= m /\ --m <= x ==> abs x <= m`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `\x:A. (f1:A->real) x - (f2:A->real) x`; `\x:A. (M:real)`; `S:A->bool`] THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CONST] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `\x:A. --(M:real)`; `\x:A. (f1:A->real) x - (f2:A->real) x`; `S:A->bool`] THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CONST] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The rescaling of the reduced volume integrand: with c = 1/T,             *)
(* A / c^(3/2) * (X / (T t)^(3/2)) = A * (X / t^(3/2)).                    *)

let P2BX_SCALE_ALG = prove
 (`!A X TT t. &0 < TT /\ &0 < t
             ==> A / (inv TT * sqrt(inv TT)) * (X / sqrt(TT * t) pow 3) = A * (X / sqrt t pow 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt TT /\ &0 < sqrt t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL; SQRT_INV] THEN
  SUBGOAL_THEN `inv TT = inv(sqrt TT pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < sqrt TT` THEN UNDISCH_TAC `&0 < sqrt t` THEN
  SPEC_TAC(`sqrt TT`,`a:real`) THEN SPEC_TAC(`sqrt t`,`b:real`) THEN
  CONV_TAC REAL_FIELD);;

(* Continuity of exp(-L) / C from continuity of L. *)

let P2BX_CONT_EXP_NEG_DIV = prove
 (`!(L:real^N->real) s C.
     (\x. lift(L x)) continuous_on s ==> (\x. lift(exp(--(L x)) / C)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  SUBGOAL_THEN `(\x:real^N. lift(exp(--((L:real^N->real) x)))) =
                (lift o exp o drop) o (\x. --(lift(L x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL; REAL_CONTINUOUS_AT_EXP]]);;

(* The pointwise comparison of the pulled back density with the limit       *)
(* integrand.                                                                 *)

let P2BX_PIECE_REAL = prove
 (`!lk li ff st d eta.
     &0 <= lk /\ &0 <= li /\ abs(lk - li) < eta /\ &0 < st /\ &0 <= d /\ d <= &1 /\
     (&1 - d) * sqrt(&1 - d) * (exp(--lk) / st) <= ff /\
     ff <= (&1 + d) * sqrt(&1 + d) * (exp(--lk) / st)
     ==> abs(ff - exp(--li) / st) <= (&3 * d + eta) / st`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:real` P2BX_POW32_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lk:real`; `li:real`] P2BX_EXP_NEG_LIP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < exp(--lk) /\ exp(--lk) <= &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = exp(--lk)` THEN ABBREV_TAC `b = exp(--li)` THEN
  SUBGOAL_THEN `&0 <= a / st /\ a / st <= inv st` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - &2 * d) * (a / st) <= ff /\ ff <= (&1 + &3 * d) * (a / st)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(&1 - d) * sqrt(&1 - d) * (a / st)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(&1 + d) * sqrt(&1 + d) * (a / st)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * (a / st) <= d * inv st` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d * (a / st)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a / st - b / st) <= eta * inv st` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(inv st) = inv st` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE; REAL_LE_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  UNDISCH_TAC `abs(a / st - b / st) <= eta * inv st` THEN
  UNDISCH_TAC `d * (a / st) <= d * inv st` THEN UNDISCH_TAC `&0 <= d * (a / st)` THEN
  UNDISCH_TAC `(&1 - &2 * d) * (a / st) <= ff` THEN
  UNDISCH_TAC `ff <= (&1 + &3 * d) * (a / st)` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The choice of the error budget. *)

let P2BX_EPS_ALG = prove
 (`!e st vk d eta.
     &0 < e /\ &0 < st /\ &0 <= vk /\ &0 <= d /\ d <= eta /\
     eta = e * st / (&4 * (vk + &1))
     ==> (&3 * d + eta) / st * vk <= e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * eta) / st * vk` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < vk + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * eta) / st * vk = (e * vk) / (vk + &1)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < st` THEN UNDISCH_TAC `&0 < vk + &1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The closeness of the rescaled pullback metrics at one backward time       *)
(* (LIM_QF_CLOSE for the views of the setup); linf is nonnegative; the limit *)
(* integrand is integrable on compact sets.                                  *)
(* ========================================================================= *)

let P2BX_LIMIT_RIEM = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi s.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\ s < &1
     ==> riemannian_metric atlas' (g' s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[ricci_flow_on]] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BX_QF_VIEW = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi t K d.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     &0 < t /\ compact_in top' K /\ &0 < d
     ==> ?k0. !k. k0 <= k
            ==> K SUBSET W k /\
                (?psi. mfd_diffeo top' atlas' (W k) top atlas (IMAGE (phi k) (W k)) (phi k) psi) /\
                IMAGE (phi k) (W k) SUBSET topspace top /\
                riemannian_metric atlas (g(--(tau k * t))) /\
                !y v. y IN K
                      ==> abs(inv(tau k) *
                              (v dot (mfd_pullback_metric atlas' atlas (phi k)
                                        (g(--(tau k * t))) y ** v)) -
                              v dot (g'(&1 - t) y ** v))
                          <= d * (v dot (g'(&1 - t) y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`] P2BX_KVIEW_HYP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_setup] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_setup")) (concl th))) THEN
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->A->real^3^3)`; `q:num->A`;
                 `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`;
                 `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&1 - t`; `&1 - t`; `K:B->bool`; `d:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &1 - t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `&1 - t`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  SUBGOAL_THEN `--((tau:num->real) k) + (&1 - t) / inv(tau k) = --(tau k * t)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--((tau:num->real) k * t) <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x <= &0`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BX_KVIEW_SLICE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  REWRITE_TAC[OPEN_IN_SUBSET]);;

let P2BX_LINF_NONNEG = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf t y.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     &0 < t /\ y IN topspace top'
     ==> &0 <= linf t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `t:real`; `{y:B}`; `&1`] P2BX_QF_VIEW) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "QF")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2bg_g1out; p2bg_conv] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_g1out")) (concl th))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{y:B}`; `t:real`; `t:real`; `--((linf:real->B->real) t y)`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `linf:real->B->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LE_REFL; IN_SING; REAL_NEG_GT0] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` (MP_TAC o SPEC `m1 + k0:num`)) THEN
  REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:B`; `t:real`]) THEN REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m1 + k0 <= (sub:num->num)(m1 + k0)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
  REMOVE_THEN "QF" (MP_TAC o SPEC `(sub:num->num)(m1 + k0)`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:num->B->A) ((sub:num->num)(m1 + k0)) y IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((phi:num->B->A) ((sub:num->num)(m1 + k0))) (W((sub:num->num)(m1 + k0))) SUBSET topspace top` THEN
    UNDISCH_TAC `(y:B) IN W((sub:num->num)(m1 + k0))` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`;
                                `g:real->A->real^3^3`; `p:A`] o
    GEN_REWRITE_RULE I [P2B_COR_9_10_STATEMENT] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "P2B_COR_9_10_STATEMENT"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`(tau:num->real)((sub:num->num)(m1 + k0)) * t`;
                             `(phi:num->B->A) ((sub:num->num)(m1 + k0)) y`] o CONJUNCT1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `abs(p2b_klx (top,atlas) (g:real->A->real^3^3) p
                  ((tau:num->real)((sub:num->num)(m1 + k0)) * t) ((phi:num->B->A) ((sub:num->num)(m1 + k0)) y) -
                   (linf:real->B->real) t y) < --(linf t y)` THEN
  REAL_ARITH_TAC);;

let P2BX_LINF_INTEGRABLE_COMPACT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf t K.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     &0 < t /\ compact_in top' K
     ==> mfd_integrable_on (top',atlas') (g'(&1 - t)) (\y. exp(--(linf t y)) / sqrt t pow 3) K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MATCH_MP_TAC P2BX_MFD_INTEGRABLE_CHARTCONT THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX_CONT_EXP_NEG_DIV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                   `sub:num->num`; `linf:real->B->real`; `c:(B->bool)#(B->real^3)`; `t:real`]
                  P2BX_LINF_SLICE_CONT) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* On a compact set K of the limit, the integral of the reduced volume       *)
(* integrand over phi(K) at tau t converges to the integral over K of        *)
(* exp(-linf(t,.)) / t^(3/2) at time 1 - t.                                  *)
(* ========================================================================= *)

let P2BX_PIECE_LIMIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf t K e.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\ P2A_FLOW_RV_STATEMENT u (:3) /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     &0 < t /\ compact_in top' K /\ &0 < e
     ==> ?m0. !m. m0 <= m
                  ==> K SUBSET W(sub m) /\
                      IMAGE (phi(sub m)) K SUBSET topspace top /\
                      mfd_lebesgue_measurable (top,atlas) (IMAGE (phi(sub m)) K) /\
                      mfd_integrable_on (top,atlas) (g(--(tau(sub m) * t)))
                        (\x. exp(--(p2b_klx (top,atlas) g p (tau(sub m) * t) x)) /
                             sqrt(tau(sub m) * t) pow 3)
                        (IMAGE (phi(sub m)) K) /\
                      abs(mfd_integral (top,atlas) (g(--(tau(sub m) * t))) (IMAGE (phi(sub m)) K)
                            (\x. exp(--(p2b_klx (top,atlas) g p (tau(sub m) * t) x)) /
                                 sqrt(tau(sub m) * t) pow 3) -
                          mfd_integral (top',atlas') (g'(&1 - t)) K
                            (\y. exp(--(linf t y)) / sqrt t pow 3)) <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top' ==> &0 <= (linf:real->B->real) t y` ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX_LINF_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the limit integrand on K *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `t:real`; `K:B->bool`] P2BX_LINF_INTEGRABLE_COMPACT) THEN
  ASM_REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
  ABBREV_TAC `v2 = mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) K
                     (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)` THEN
  DISCH_TAC THEN
  (* the volume of K and the error budget *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`; `K:B->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vk:real`) THEN
  SUBGOAL_THEN `&0 <= vk` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(g':real->B->real^3^3)(&1 - t)`; `K:B->bool`; `vk:real`]
                         MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt t pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `eta = e * sqrt t pow 3 / (&4 * (vk + &1))` THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = min (&1 / &2) eta` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 / &2 /\ d <= eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* closeness of the metrics and convergence of the lengths *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `t:real`; `K:B->bool`; `d:real`]
                P2BX_QF_VIEW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "QF")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2bg_g1out; p2bg_conv] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_g1out")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `t:real`; `t:real`; `eta:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `linf:real->B->real`)) (concl th) &&
      can (find_term ((=) `t1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(X_CHOOSE_THEN `m1:num` (LABEL_TAC "CV")) THEN
  EXISTS_TAC `m1 + k0:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `m <= (sub:num->num) m` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN K
        ==> abs(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real)((sub:num->num) m) * t)
                        ((phi:num->B->A) (sub m) y) - (linf:real->B->real) t y) < eta`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "CV" (MP_TAC o SPECL [`m:num`; `y:B`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "QF" (MP_TAC o SPEC `(sub:num->num) m`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B`) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < (tau:num->real)((sub:num->num) m) * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the reduced volume integrand of the flow *)
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`]
                P2BX_KFRV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(tau:num->real)((sub:num->num) m) * t` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h = \x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p
                                ((tau:num->real)((sub:num->num) m) * t) x)) /
                     sqrt(tau(sub m) * t) pow 3` THEN
  SUBGOAL_THEN `compact_in top (IMAGE ((phi:num->B->A)((sub:num->num) m)) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top' (W((sub:num->num) m):B->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A)((sub:num->num) m)) K SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^3))->bool) (IMAGE ((phi:num->B->A)((sub:num->num) m)) K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_integrable_on (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real)((sub:num->num) m) * t)))
                  h (IMAGE ((phi:num->B->A)(sub m)) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `v1 = mfd_integral (top,atlas)
                     ((g:real->A->real^3^3)(--((tau:num->real)((sub:num->num) m) * t)))
                     (IMAGE ((phi:num->B->A)(sub m)) K) h` THEN
  SUBGOAL_THEN `mfd_has_integral (top,atlas)
                  ((g:real->A->real^3^3)(--((tau:num->real)((sub:num->num) m) * t))) h
                  (IMAGE ((phi:num->B->A)(sub m)) K) v1` ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* positivity facts *)
  SUBGOAL_THEN `!x:A. &0 <= h x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv((tau:num->real)((sub:num->num) m)) /\ &0 <= d /\ d < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN topspace top
                      ==> &0 <= p2b_klx (top,atlas) (g:real->A->real^3^3) p
                                 ((tau:num->real)((sub:num->num) m) * t) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`;
                                `g:real->A->real^3^3`; `p:A`] o
      GEN_REWRITE_RULE I [P2B_COR_9_10_STATEMENT] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "P2B_COR_9_10_STATEMENT"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(tau:num->real)((sub:num->num) m) * t`; `x:A`] o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET topspace top'` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the pulled back density *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(--((tau:num->real)((sub:num->num) m) * t))`;
                 `(W:num->B->bool)((sub:num->num) m)`;
                 `IMAGE ((phi:num->B->A)((sub:num->num) m)) (W(sub m))`;
                 `(phi:num->B->A)((sub:num->num) m)`; `psi:A->B`; `K:B->bool`; `h:A->real`;
                 `v1:real`; `inv((tau:num->real)((sub:num->num) m))`; `d:real`]
                P2BX_PB_DENSITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F1:B->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`; `F1:B->real`;
                 `\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`; `K:B->bool`;
                 `v1:real`; `v2:real`; `vk:real`; `(&3 * d + eta) / sqrt t pow 3`]
                P2BX_MFD_INTEGRAL_DIFF_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `F1:B->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[P2BX_SCALE_ALG] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_PIECE_REAL THEN
    EXISTS_TAC `p2b_klx (top,atlas) (g:real->A->real^3^3) p
                  ((tau:num->real)((sub:num->num) m) * t) ((phi:num->B->A)(sub m) y)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE ((phi:num->B->A)((sub:num->num) m)) K SUBSET topspace top` THEN
      UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(K:B->bool) SUBSET topspace top'` THEN
      UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= e ==> a <= b ==> a <= e`) THEN
  MATCH_MP_TAC P2BX_EPS_ALG THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Splitting manifold integrals over a measurable subset; the reduced volume *)
(* of linf over compact sets and over the whole limit is at most V, and at   *)
(* least V by the uniform Gaussian tails of the flow and LIM_BALL.           *)
(* ========================================================================= *)

let P2BX_MFD_INTEGRAL_SPLIT = prove
 (`!top atlas (g:A->real^N^N) f S S'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_integrable_on (top,atlas) g f S' /\ mfd_lebesgue_measurable (top,atlas) S /\
     S SUBSET S'
     ==> mfd_integrable_on (top,atlas) g f S /\
         mfd_integrable_on (top,atlas) g f (S' DIFF S) /\
         mfd_integral (top,atlas) g S' f =
         mfd_integral (top,atlas) g S f + mfd_integral (top,atlas) g (S' DIFF S) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) (S':A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `f:A->real`;
                          `mfd_integral (top,atlas) (g:A->real^N^N) S' f`] THEN
    ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((S':A->bool) DIFF S)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_integrable_on (top,atlas) (g:A->real^N^N) f S /\
                mfd_integrable_on (top,atlas) g f ((S':A->bool) DIFF S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `S':A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `S:A->bool`; `(S':A->bool) DIFF S`;
                 `mfd_integral (top,atlas) (g:A->real^N^N) S f`;
                 `mfd_integral (top,atlas) (g:A->real^N^N) ((S':A->bool) DIFF S) f`]
                MFD_HAS_INTEGRAL_UNION) THEN
  ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) UNION (S' DIFF S) = S'` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `f:A->real`; `S':A->bool`] THEN
  ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL]);;

let P2BX_MFD_INTEGRAL_SUBSET_LE = prove
 (`!top atlas (g:A->real^N^N) f S S'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_integrable_on (top,atlas) g f S' /\ mfd_lebesgue_measurable (top,atlas) S /\
     S SUBSET S' /\ (!x. x IN S' ==> &0 <= f x)
     ==> mfd_integrable_on (top,atlas) g f S /\
         mfd_integral (top,atlas) g S f <= mfd_integral (top,atlas) g S' f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `S:A->bool`; `S':A->bool`] P2BX_MFD_INTEGRAL_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `(S':A->bool) DIFF S`;
                 `mfd_integral (top,atlas) (g:A->real^N^N) ((S':A->bool) DIFF S) f`; `&0`]
                MFD_HAS_INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL; REAL_MUL_LZERO] THEN DISCH_TAC THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `\x:A. &0 * (f:A->real) x`; `f:A->real`;
                        `(S':A->bool) DIFF S`] THEN
  ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL; REAL_MUL_LZERO] THEN
  REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[]);;

(* The subsequence of G1 dominates the identity. *)

let P2BX_G1OUT_SUBSEQ = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau
    (top':B topology) atlas' g' W phi sub linf.
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf ==> !n. n <= sub n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bg_g1out; p3_subseq] THEN STRIP_TAC THEN
  MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]);;

(* On a compact set the integral of the limit integrand is at most V.      *)

let P2BX_RVOL_COMPACT_LE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t K.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\ P2A_FLOW_RV_STATEMENT u (:3) /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
     &0 < t /\ compact_in top' K
     ==> mfd_integral (top',atlas') (g'(&1 - t)) K (\y. exp(--(linf t y)) / sqrt t pow 3) <= V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `vK = mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) K
                     (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = (vK - V) / &4` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `t:real`; `K:B->bool`; `e:real`] P2BX_PIECE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m0:num` (LABEL_TAC "PL")) THEN
  UNDISCH_TAC `((\t. p2b_kfrv (top,atlas) (g:real->A->real^3^3) p t) ---> V) at_posinfinity` THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` (LABEL_TAC "LB")) THEN
  SUBGOAL_THEN `?N. !k. N <= k ==> b / t < (tau:num->real) k` (X_CHOOSE_TAC `N:num`) THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o SPEC `b / t`); ALL_TAC] THEN
  SUBGOAL_THEN `m0 + N <= (sub:num->num)(m0 + N)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP P2BX_G1OUT_SUBSEQ); ALL_TAC] THEN
  REMOVE_THEN "PL" (MP_TAC o SPEC `m0 + N:num`) THEN REWRITE_TAC[LE_ADD] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (tau:num->real)((sub:num->num)(m0 + N)) * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`]
                P2BX_KFRV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(tau:num->real)((sub:num->num)(m0 + N)) * t` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(--((tau:num->real)((sub:num->num)(m0 + N)) * t))`;
                 `\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p
                                ((tau:num->real)((sub:num->num)(m0 + N)) * t) x)) /
                      sqrt(tau(sub(m0 + N)) * t) pow 3`;
                 `IMAGE ((phi:num->B->A)((sub:num->num)(m0 + N))) K`; `topspace top:A->bool`]
                P2BX_MFD_INTEGRAL_SUBSET_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  USE_THEN "LB" (MP_TAC o SPEC `(tau:num->real)((sub:num->num)(m0 + N)) * t`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_ge] THEN
    SUBGOAL_THEN `b / t < (tau:num->real)((sub:num->num)(m0 + N))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `vK <= p2b_kfrv (top,atlas) (g:real->A->real^3^3) p
            ((tau:num->real)((sub:num->num)(m0 + N)) * t) + e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_integral (top,atlas)
                  ((g:real->A->real^3^3)(--((tau:num->real)((sub:num->num)(m0 + N)) * t)))
                  (IMAGE ((phi:num->B->A)((sub:num->num)(m0 + N))) K)
                  (\x. exp(--(p2b_klx (top,atlas) g p (tau(sub(m0 + N)) * t) x)) /
                       sqrt(tau(sub(m0 + N)) * t) pow 3) + e` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_RADD]];
    ALL_TAC] THEN
  UNDISCH_TAC `vK <= p2b_kfrv (top,atlas) (g:real->A->real^3^3) p
                       ((tau:num->real)((sub:num->num)(m0 + N)) * t) + e` THEN
  UNDISCH_TAC `abs(p2b_kfrv (top,atlas) (g:real->A->real^3^3) p
                     ((tau:num->real)((sub:num->num)(m0 + N)) * t) - V) < e` THEN
  UNDISCH_TAC `(vK - V) / &4 = e` THEN UNDISCH_TAC `V < vK` THEN REAL_ARITH_TAC);;

(* The limit integrand is integrable on the whole limit, with integral at   *)
(* most V (monotone convergence along the closures of the exhaustion W).    *)

let P2BX_RVOL_INTEGRABLE_LE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\ P2A_FLOW_RV_STATEMENT u (:3) /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\ &0 < t
     ==> mfd_integrable_on (top',atlas') (g'(&1 - t)) (\y. exp(--(linf t y)) / sqrt t pow 3)
           (topspace top') /\
         mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
           (\y. exp(--(linf t y)) / sqrt t pow 3) <= V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`;
                 `\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`;
                 `\n. top' closure_of ((W:num->B->bool) n)`; `V:real`] P2BX_MFD_MONO_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      GEN_TAC THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(W:num->B->bool)(SUC n)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC P2BX_LINF_INTEGRABLE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC P2BX_RVOL_COMPACT_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  BETA_TAC THEN
  SUBGOAL_THEN `UNIONS {top' closure_of (W:num->B->bool) n | n IN (:num)} = topspace top'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV; CLOSURE_OF_SUBSET_TOPSPACE];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) && is_const(rator(lhs(concl th))) &&
      fst(dest_const(rator(lhs(concl th)))) = "UNIONS")) THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top' closure_of (W:num->B->bool) n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                    (top' closure_of (W:num->B->bool) n)
                    (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
  MATCH_MP_TAC P2BX_RVOL_COMPACT_LE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[]);;

(* The reduced volume of linf is at least V: the balls about q k of radius *)
(* sqrt(tau_k t) R carry all but e of the reduced volume of the flow and   *)
(* lie in the images of a compact set of the limit (LIM_BALL).             *)

let P2BX_RVOL_GE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2A_FLOW_RV_STATEMENT u (:3) /\ P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     (!s. &0 < s ==> V <= p2b_kfrv (top,atlas) g p s) /\
     mfd_integrable_on (top',atlas') (g'(&1 - t)) (\y. exp(--(linf t y)) / sqrt t pow 3)
       (topspace top') /\
     &0 < t
     ==> V <= mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                (\y. exp(--(linf t y)) / sqrt t pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_G1OUT_SUBSEQ) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `vM = mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) (topspace top')
                     (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = (V - vM) / &4` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `t:real`; `e:real`] P2BX_FLOW_TAIL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TL"))) THEN
  SUBGOAL_THEN `!k. --((tau:num->real) k) + (&1 - t) / inv(tau k) = --(tau k * t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. --((tau:num->real) k * t) <= &0` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x <= &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`] P2BX_KVIEW_HYP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_setup] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_setup")) (concl th))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] LIM_BALL) THEN REWRITE_TAC[LIM_BALL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->A->real^3^3)`; `q:num->A`;
    `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`;
    `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
    `&1 - t`; `sqrt t * (R + &1)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2BX_KVIEW_SLICE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2BX_KVIEW_SLICE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `k0:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "LB")))) THEN
  (* a member of the subsequence beyond k0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `t:real`; `K:B->bool`; `e:real`] P2BX_PIECE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m0:num` (MP_TAC o SPEC `m0 + k0:num`)) THEN
  REWRITE_TAC[LE_ADD] THEN
  SUBGOAL_THEN `k0 <= (sub:num->num)(m0 + k0)` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m0 + k0:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`(sub:num->num)(m0 + k0)`,`k:num`) THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (tau:num->real) k * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(--((tau:num->real) k * t)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the flow integrand *)
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`]
                P2BX_KFRV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(tau:num->real) k * t` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2b_kfrv (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) =
                mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (topspace top) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. &0 <= (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ball about q k *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `((g:real->A->real^3^3)(--((tau:num->real) k * t)))`; `(q:num->A) k`;
                 `sqrt((tau:num->real) k * t) * R`;
                 `(sqrt t * (R + &1)) * inv(sqrt(inv((tau:num->real) k)))`] P2BX_MFD_BALL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SQRT_MUL; SQRT_INV; REAL_INV_INV] THEN
    SUBGOAL_THEN `&0 <= sqrt((tau:num->real) k) * sqrt t` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R)) SUBSET (IMAGE ((phi:num->B->A) k) K)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN IMAGE ((phi:num->B->A) k) (K INTER W k)` MP_TAC THENL
     [USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^3))->bool) (mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* splitting at the ball and comparing with the image of K *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `((g:real->A->real^3^3)(--((tau:num->real) k * t)))`; `(\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)`; `(mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R))`;
                 `topspace top:A->bool`] P2BX_MFD_INTEGRAL_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `((g:real->A->real^3^3)(--((tau:num->real) k * t)))`; `(\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)`; `(mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R))`;
                 `(IMAGE ((phi:num->B->A) k) K)`] P2BX_MFD_INTEGRAL_SUBSET_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`; `(\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)`; `K:B->bool`; `topspace top':B->bool`]
                P2BX_MFD_INTEGRAL_SUBSET_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]];
    STRIP_TAC] THEN
  (* the tail and the arithmetic *)
  USE_THEN "TL" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `V <= p2b_kfrv (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t)`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `V <= p2b_kfrv (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t)` THEN
  UNDISCH_TAC `p2b_kfrv (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) =
               mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (topspace top) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)` THEN
  UNDISCH_TAC `mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (topspace top) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) =
               mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R)) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) +
               mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (topspace top DIFF (mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R))) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)` THEN
  UNDISCH_TAC `mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (topspace top DIFF (mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R))) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) <= e` THEN
  UNDISCH_TAC `mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (mfd_ball (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k) (sqrt(tau k * t) * R)) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) <= mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (IMAGE ((phi:num->B->A) k) K) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3)` THEN
  UNDISCH_TAC `abs(mfd_integral (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) (IMAGE ((phi:num->B->A) k) K) (\x. exp(--(p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) x)) / sqrt(tau k * t) pow 3) -
                   mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) K (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)) <= e` THEN
  UNDISCH_TAC `mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) K (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3) <=
               mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) (topspace top') (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3)` THEN
  UNDISCH_TAC `mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) (topspace top') (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3) = vM` THEN
  UNDISCH_TAC `(V - vM) / &4 = e` THEN UNDISCH_TAC `vM < V` THEN
  REAL_ARITH_TAC);;

(* The reduced volume of linf at every t > 0 is the limit V of the reduced  *)
(* volume of the kappa solution.                                             *)

let P2BX_G3_RVOL = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2A_FLOW_RV_STATEMENT u (:3) /\ P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf
     ==> ?V. ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
             p2bg_rvol (top',atlas') g' linf V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`]
                P2BX_KFRV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `V:real` THEN ASM_REWRITE_TAC[p2bg_rvol] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`] P2BX_RVOL_INTEGRABLE_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= v /\ v <= a ==> a = v`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX_RVOL_GE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[]);;

