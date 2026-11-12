(* ========================================================================= *)
(* Unit pc_cmr_nonharm (a unit of the replacement chain of                   *)
(* pc_cm_replacement): a map u of S^2 with cmr_e S G eps u = 0 that is not   *)
(* constant is a harmonic sphere (cm_sharmonic).  Used in the assembly of    *)
(* CM Thm 2.1 for the slices of energy at least E_star: they are not         *)
(* harmonic spheres (energy gap) and not constant, so they have cmr_e > 0.   *)
(*                                                                           *)
(* Chart energies of small balls are small (uniformly in the                 *)
(* centre); zero decrease on a ball makes the chart picture harmonic there   *)
(* (it is then a minimizer, so it agrees a.e. with the harmonic replacement *)
(* of CM_REPLACEMENT, hence everywhere by continuity); cmr_e = 0 gives zero *)
(* decrease on every half ball of small energy.                             *)
(* ========================================================================= *)

needs "src/pc_cmr_l339.ml";;
needs "src/pc_cmc_global.ml";;

prioritize_real();;
type_invention_error := true;;

(* Small balls of a chart picture have small Dirichlet energy, uniformly in *)
(* the centre (the weak partials are in L^2 of the whole plane).            *)

let CMR_CHART_DIR_SMALL = prove
 (`!(u:real^3->real^K) (Q:real^3^3) eps.
     wan_s2_w12 u /\ orthogonal_matrix Q /\ &0 < eps
     ==> ?d. &0 < d /\
             !c r. &0 < r /\ r < d
                   ==> wan_dir (ball(c,r)) (\x. u(cm_capmap Q x)) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?v1:real^2->real^K. v1 IN lspace (:real^2) (&2) /\
                        wan_wpd (:real^2) 1 (\x. (u:real^3->real^K)(cm_capmap Q x)) v1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?v2:real^2->real^K. v2 IN lspace (:real^2) (&2) /\
                        wan_wpd (:real^2) 2 (\x. (u:real^3->real^K)(cm_capmap Q x)) v2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ARITH_RULE `1 <= 2 /\ 2 <= 2`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v1:real^2->real^K`; `eps / &2`] CMR_SQ_INTEGRAL_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v2:real^2->real^K`; `eps / &2`] CMR_SQ_INTEGRAL_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`c:real^2`; `r:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(c:real^2,r)`; `\x. (u:real^3->real^K)(cm_capmap Q x)`;
                 `\i:num. if i = 1 then (v1:real^2->real^K) else v2`] CMR_DIR_EQ_P) THEN
  REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:num) = 1 \/ i = 2` MP_TAC THENL
     [UNDISCH_TAC `1 <= (i:num) /\ i <= 2` THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
       ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
       MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
       ASM_REWRITE_TAC[SUBSET_UNIV]]);
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SUM_2; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a < e / &2 /\ b < e / &2 ==> a + b < e`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* The same for the G-energy.                                               *)

let CMR_CHART_GDIR_SMALL = prove
 (`!S (G:real^K->real^K^K) Lam (u:real^3->real^K) (Q:real^3^3) eps.
     CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\ &0 < eps
     ==> ?d. &0 < d /\
             !c r. &0 < r /\ r < d
                   ==> wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `Q:real^3^3`; `eps / (abs Lam + &1)`]
                CMR_CHART_DIR_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real^2`; `r:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^2`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                   `r:real`] CMR_CHART_CMAP) THEN
    ASM_SIMP_TAC[cm_cmap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,r)`; `G:real^K->real^K^K`;
                 `\x. (u:real^3->real^K)(cm_capmap Q x)`; `&0`; `Lam:real`]
                HMD_GDIR_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; REAL_LE_REFL; REAL_MUL_LZERO] THEN
    UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN SIMP_TAC[CMR_GCOND];
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= wan_dir (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x))`
  ASSUME_TAC THENL [MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x)) * (abs Lam + &1)
    < eps`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wan_dir (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x))`;
                   `eps:real`; `abs Lam + &1`] REAL_LT_RDIV_EQ) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Lam * wan_dir (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x)) <=
    wan_dir (ball(c,r)) (\x. u(cm_capmap Q x)) * (abs Lam + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= D /\ Lam * D <= abs Lam * D ==> Lam * D <= D * (abs Lam + &1)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Zero decrease on a ball: the chart picture is harmonic on the ball.      *)

let CMR_DEC_ZERO_HARM = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\
     &0 < r /\ wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e /\
     cmr_dec S G Q c r u = &0
     ==> cm_harmonic S G (ball(c,r)) (\x. u(cm_capmap Q x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_dec S G Q (c:real^2) r (u:real^3->real^K) = &0` THEN
  REWRITE_TAC[cmr_dec] THEN DISCH_TAC THEN
  ABBREV_TAC `f = \x. (u:real^3->real^K)(cm_capmap Q x)` THEN
  SUBGOAL_THEN `cm_cmap S (ball(c:real^2,r)) (f:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `f:real^2->real^K`] CMR_MINW_WORKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `cm_minimizer S G (ball(c:real^2,r)) (f:real^2->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[cm_minimizer] THEN CONJ_TAC THENL
     [REWRITE_TAC[cm_wmap] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
      EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
      ASM_MESON_TAC[cm_cmap; CLOSURE_SUBSET; SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `w:real^2->real^K` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm_gen G (ball(c:real^2,r)) (cmr_minw S G c r (f:real^2->real^K))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `cm_gen G (ball(c:real^2,r)) (f:real^2->real^K) -
        cm_gen G (ball(c,r)) (cmr_minw S G c r f) = &0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_w120 (ball(c:real^2,r))
        (\x. (w:real^2->real^K) x - cmr_minw S G c r (f:real^2->real^K) x)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\x. (w:real^2->real^K) x - cmr_minw S G c r (f:real^2->real^K) x) =
        (\x. (\x. w x - f x) x - (\x. cmr_minw S G c r f x - f x) x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN GEN_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC WAN_W120_SUB THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cm_minimizer] o
      check (fun th -> can (find_term (fun t -> is_const t &&
                                           fst(dest_const t) = "cm_minimizer")) (concl th) &&
                       can (find_term (fun t -> is_const t &&
                                           fst(dest_const t) = "cmr_minw")) (concl th))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `cmw_repex S (G:real^K->real^K^K) e` THEN REWRITE_TAC[cmw_repex] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real^2`; `r:real`; `f:real^2->real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `negligible {x:real^2 | x IN ball(c,r) /\ ~((f:real^2->real^K) x = w0 x)}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[HMD_W120_REFL; OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN ball(c,r) ==> (f:real^2->real^K) x = w0 x` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_CONT_AE_EQ THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `closure(ball(c:real^2,r))` THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
    ASM_MESON_TAC[cm_cmap];
    ALL_TAC] THEN
  MATCH_MP_TAC HMD_HARMONIC_CONG THEN EXISTS_TAC `w0:real^2->real^K` THEN
  ASM_SIMP_TAC[]);;

(* cmr_e = 0: zero decrease on the half ball of every single cap of energy  *)
(* at most eps.                                                              *)

let CMR_E_ZERO_DEC = prove
 (`!S (G:real^K->real^K^K) e Lam eps (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ &0 <= eps /\ &2 * eps <= e /\
     orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,&2 * r)) G (\x. u(cm_capmap Q x)) <= &2 * eps /\
     cmr_e S G eps u = &0
     ==> cmr_dec S G Q c r u = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,r)) G (\x. (u:real^3->real^K)(cm_capmap Q x)) <= e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(c:real^2,&2 * r)) G (\x. (u:real^3->real^K)(cm_capmap Q x))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                     `&2 * r`] CMR_CHART_CMAP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[cm_cmap]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`] CMR_DEC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cm_sen G (u:real^3->real^K) -
    cm_sen G (cmr_repn S G 1 (\k:num. Q:real^3^3) (\k:num. c:real^2)
                       (\j. (\k:num. &2 * r) j / &2) u) IN cmr_eset S G eps u`
  MP_TAC THENL
   [REWRITE_TAC[cmr_eset; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`1:num`; `\k:num. Q:real^3^3`; `\k:num. c:real^2`;
                          `\k:num. &2 * r`] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Q:real^3^3`; `c:real^2`;
                   `&2 * r`; `u:real^3->real^K`] CMR_REPN_ONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`;
                   `ball(c:real^2,&2 * r)`] CMR_CAP_EN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= &2 * eps ==> a / &2 <= eps`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\j:num. (\k:num. &2 * r) j / &2) = (\k:num. r)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Q:real^3^3`; `c:real^2`;
                 `r:real`; `u:real^3->real^K`] CMR_REPN_ONE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `eps:real`;
                 `u:real^3->real^K`] CMR_ESET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `cm_sen G (u:real^3->real^K) -
                            (cm_sen G u - cmr_dec S G Q (c:real^2) r u)` o
             last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 <= cmr_dec S G Q (c:real^2) r (u:real^3->real^K)` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* With cmr_e = 0 every chart picture is harmonic on the whole plane (zero   *)
(* decrease on all balls of a fixed small radius, then the locality lemma    *)
(* CMC_HARMONIC_LOCAL); the charts of mat 1 and cmr_qb cover S^2, so a       *)
(* non-constant u is a harmonic sphere (CMR_SHARMONIC_FROM_CAPS).            *)
(* ========================================================================= *)

let CMR_NONHARM_CHART = prove
 (`!S (G:real^K->real^K^K) d e Lam eps (u:real^3->real^K) (Q:real^3^3).
     cm_target S G d /\ cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < eps /\
     &2 * eps <= e /\ cm_smap S u /\ cmr_e S G eps u = &0 /\ orthogonal_matrix Q
     ==> cm_harmonic S G (:real^2) (\x. u(cm_capmap Q x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`;
                 `Q:real^3^3`; `&2 * eps`] CMR_CHART_GDIR_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!c:real^2. cm_harmonic S G (ball(c,dd / &4)) (\x. (u:real^3->real^K)(cm_capmap Q x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^2` THEN
    SUBGOAL_THEN
     `wan_gdir (ball(c:real^2,&2 * (dd / &4))) G (\x. (u:real^3->real^K)(cm_capmap Q x)) <
      &2 * eps`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_gdir (ball(c:real^2,dd / &4)) G (\x. (u:real^3->real^K)(cm_capmap Q x)) <= e`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `wan_gdir (ball(c:real^2,&2 * (dd / &4))) G
                           (\x. (u:real^3->real^K)(cm_capmap Q x))` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                       `&2 * (dd / &4)`] CMR_CHART_CMAP) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[cm_cmap]]];
      ALL_TAC] THEN
    MATCH_MP_TAC CMR_DEC_ZERO_HARM THEN MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CMR_E_ZERO_DEC THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_HARMONIC_LOCAL THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^2` THEN EXISTS_TAC `ball(x:real^2,dd / &4)` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN SIMP_TAC[cm_harmonic]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN
    REWRITE_TAC[cm_smap] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN EXISTS_TAC `dd / &4` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The charts of mat 1 and cmr_qb cover S^2 (they miss only the poles      *)
(* basis 3 and --basis 3 respectively).                                      *)

let CMR_QB_CHARTS_COVER = prove
 (`!y:real^3. y IN sphere(vec 0,&1)
              ==> y IN IMAGE (cm_capmap (mat 1)) (:real^2) \/
                  y IN IMAGE (cm_capmap cmr_qb) (:real^2)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix cmr_qb /\ cmr_qb ** basis 3 = --(basis 3):real^3`
  STRIP_ASSUME_TAC THENL [MESON_TAC[CMR_QB_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
  MP_TAC(ISPEC `cmr_qb` CMR_CAPMAP_FACTS) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[last(CONJUNCTS th)]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[last(CONJUNCTS th)]) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  ASM_CASES_TAC `y:real^3 = basis 3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH `b:real^3 = --b <=> b = vec 0`] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]);;

(* The result: zero improvement and non-constant give a harmonic sphere.    *)

let CMR_NONHARM = prove
 (`!S (G:real^K->real^K^K) d e Lam eps (u:real^3->real^K).
     cm_target S G d /\ cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < eps /\
     &2 * eps <= e /\ cm_smap S u /\ cmr_e S G eps u = &0 /\
     ~(?c. !y. y IN sphere(vec 0,&1) ==> u y = c)
     ==> cm_sharmonic S G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CMR_SHARMONIC_FROM_CAPS THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `2:num`;
                        `\k:num. if k = 1 then mat 1 else cmr_qb:real^3^3`;
                        `\k:num. (:real^2)`] THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `orthogonal_matrix(if (k:num) = 1 then mat 1 else cmr_qb:real^3^3)`
    ASSUME_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN MESON_TAC[CMR_QB_FACTS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_NONHARM_CHART THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`; `Lam:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:real^3` CMR_QB_CHARTS_COVER) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `1:num` THEN ASM_REWRITE_TAC[ARITH];
    EXISTS_TAC `2:num` THEN ASM_REWRITE_TAC[ARITH]]);;

