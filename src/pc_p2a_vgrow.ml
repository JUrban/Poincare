(* ========================================================================= *)
(* Unit pc_p2a_vgrow: volume growth along a Ricci flow on a closed manifold  *)
(* (MT p. 410, from the evolution of the volume form (3.8)), the statement   *)
(* P2_VOLUME_GROWTH_STATEMENT of pc_p3_iface: if R >= -K on [t1,t2] then     *)
(* Vol(t2) <= exp(K (t2 - t1)) Vol(t1).                                      *)
(* Proof: in preferred coordinates d/ds sqrt(det(g s x)) = -R sqrt(det g)   *)
(* (GRGT_DENSITY_EVOLUTION_PREF), so exp(-K (s - t1)) sqrt(det(g s x)) does *)
(* not increase on [t1,t2] (mean value theorem; continuity up to the        *)
(* initial time from the smooth extension of ricci_flow_from); the volume   *)
(* comparison MFD_HAS_VOLUME_COMPARE then integrates the pointwise bound.   *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_grg_rfint.ml";;

prioritize_real();;
type_invention_error := true;;

(* The constant scalar family 1 is smooth up to the initial time. *)

let P2AQ_SFUN_ONE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b.
        pde_sfun_from atlas a b (\s x. &1)`,
  REWRITE_TAC[pde_sfun_from] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`&1`; `\z:real^(1,N)finite_sum. lift(&1)`] THEN
  REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST]);;

(* The time derivative of the exponential weight. *)

let P2AQ_EXP_DERIV = prove
 (`!K t1 s. ((\s. exp(--K * (s - t1))) has_real_derivative
             (--K * exp(--K * (s - t1)))) (atreal s)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING);;

(* The density sqrt(det(g s p)) in preferred coordinates is continuous in   *)
(* time on [t1,t2], including the initial time a.                           *)

let P2AQ_PREF_DENSITY_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) p t1 t2.
        ricci_flow_from (top,atlas) a b g /\ p IN topspace top /\
        a <= t1 /\ t2 < b
        ==> (\s. sqrt(det(g s p))) real_continuous_on real_interval[t1,t2]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `\s:real x:A. &1`; `c:(A->bool)#(A->real^N)`]
                GRGT_PSI_EXISTS) THEN
  ASM_REWRITE_TAC[P2AQ_SFUN_ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool`
   (X_CHOOSE_THEN `P:real^(1,N)finite_sum->real^1` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) p IN IMAGE (SND c) (FST c)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> pastecart (lift s) (SND(c:(A->bool)#(A->real^N)) p) IN W /\
            drop((P:real^(1,N)finite_sum->real^1)
                   (pastecart (lift s) (SND c p))) =
            sqrt(det((g:real->A->real^N^N) s p))`
  (LABEL_TAC "PV") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s:real`; `SND(c:(A->bool)#(A->real^N)) p`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[mfd_chart_integrand; mfd_density; LIFT_DROP; REAL_MUL_LID] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\s. drop((P:real^(1,N)finite_sum->real^1)
                         (pastecart (lift s) (SND(c:(A->bool)#(A->real^N)) p)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "PV" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MP_TAC(ISPECL [`P:real^(1,N)finite_sum->real^1`;
                 `W:real^(1,N)finite_sum->bool`; `s:real`;
                 `SND(c:(A->bool)#(A->real^N)) p`] GRGT_TIME_DERIVATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "PV" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(ACCEPT_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL)]);;

(* Pointwise density growth: with R >= -K at p on [t1,t2],                   *)
(* sqrt(det(g t2 p)) <= exp(K (t2 - t1)) sqrt(det(g t1 p)).                  *)

let P2AQ_DENSITY_GROWTH = prove
 (`!top atlas a b (g:real->A->real^N^N) K t1 t2 p.
        ricci_flow_from (top,atlas) a b g /\
        a <= t1 /\ t1 <= t2 /\ t2 < b /\ p IN topspace top /\
        (!t. t1 <= t /\ t <= t2 ==> --K <= mfd_scalar atlas (g t) p)
        ==> sqrt(det(g t2 p)) <= exp(K * (t2 - t1)) * sqrt(det(g t1 p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RK")))))) THEN
  ASM_CASES_TAC `t1:real = t2` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < t2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL
   [`\s. exp(--K * (s - t1)) * sqrt(det((g:real->A->real^N^N) s p))`;
    `\s. exp(--K * (s - t1)) *
         (--(mfd_scalar atlas ((g:real->A->real^N^N) s) p) * sqrt(det(g s p))) +
         (--K * exp(--K * (s - t1))) * sqrt(det(g s p))`;
    `t1:real`; `t2:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `--K * exp(--K * (s - t1))` THEN REWRITE_TAC[P2AQ_EXP_DERIV];
        MATCH_MP_TAC P2AQ_PREF_DENSITY_CONT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `a:real`; `b:real`] THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`; `p:A`]
                    GRGT_DENSITY_EVOLUTION_PREF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL
       [`\s. exp(--K * (s - t1))`; `--K * exp(--K * (s - t1))`;
        `\s. sqrt(det((g:real->A->real^N^N) s p))`;
        `--(mfd_scalar atlas ((g:real->A->real^N^N) s) p) * sqrt(det(g s p))`;
        `s:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[P2AQ_EXP_DERIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` MP_TAC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(det((g:real->A->real^N^N) s p))` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--K <= mfd_scalar atlas ((g:real->A->real^N^N) s) p` ASSUME_TAC THENL
   [USE_THEN "RK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= exp(--K * (s - t1)) * sqrt(det((g:real->A->real^N^N) s p)) *
          (mfd_scalar atlas (g s) p + K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (exp(--K * (s - t1)) * sqrt(det((g:real->A->real^N^N) s p)) *
           (mfd_scalar atlas (g s) p + K)) * (t2 - t1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--K * (t2 - t1)) * sqrt(det((g:real->A->real^N^N) t2 p)) <=
    sqrt(det(g t1 p))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID] THEN
    UNDISCH_TAC
     `&0 <= (exp(--K * (s - t1)) * sqrt(det((g:real->A->real^N^N) s p)) *
             (mfd_scalar atlas (g s) p + K)) * (t2 - t1)` THEN
    CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(K * (t2 - t1)) * exp(--K * (t2 - t1)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(K * (t2 - t1)) *
              (exp(--K * (t2 - t1)) * sqrt(det((g:real->A->real^N^N) t2 p)))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The headline (statement P2_VOLUME_GROWTH_STATEMENT of pc_p3_iface).       *)
(* ------------------------------------------------------------------------- *)

let P2AQ_VOLUME_GROWTH = prove
 (`!u:A->bool. P2_VOLUME_GROWTH_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_VOLUME_GROWTH_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `K:real`; `t1:real`; `t2:real`; `v1:real`; `v2:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  SUBGOAL_THEN
   `riemannian_metric atlas ((g:real->A->real^3^3) t1) /\
    riemannian_metric atlas (g t2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_COMPARE) THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `(g:real->A->real^3^3) t1`; `(g:real->A->real^3^3) t2`;
    `topspace top:A->bool`] THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2AQ_DENSITY_GROWTH THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

