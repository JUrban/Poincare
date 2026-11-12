(* ========================================================================= *)
(* Unit pc_p3_s1621 (Part 3 proofs; MT Ch 16): MT Prop 16.21(3) (p. 385).    *)
(* For the setting of Prop 16.4 and a bound Lb, one compact space-time set K *)
(* (p3_st_compact) contains every admissible curve from x of L-length <= Lb  *)
(* back to T(i-1). K = p3n_kset is a finite union of compact pieces: the     *)
(* parabolic ball near tt (Lemma 16.15(1)), for each surgery time t_k in     *)
(* [T(i-1),tt) the old points outside the cap regions d < A0 + 40 over       *)
(* [t_k - de,t_k + de] (after t_k by the cap avoidance of Lemma 16.15(2),    *)
(* before t_k by the parabolic ball of the point where the curve passes t_k, *)
(* P3N_END_COVER with the uniform radius of P3N_END_DATA), and the middle    *)
(* parts of the slabs. L+ <= L + 6 b sqrt b from R >= -6 (P3N_LPLUS_FROM_L). *)
(* The headline P3N_PROP_16_21_FIX derives Prop 16.21 from Lemma 16.15, both *)
(* in the form with the second scale rr <= r' (16.15 with the caps clause    *)
(* for every surgery time); route theorem P3N_PROP_16_21_ROUTE.              *)
(* ========================================================================= *)

needs "src/pc_p3_s16l15.ml";;
needs "src/pc_p3_c17curv.ml";;
needs "src/pc_p3_c17vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 16.21: the scalar curvature along a space-time curve               *)
(* is continuous off the event times and measurable; for an admissible      *)
(* curve the L_plus integrand is integrable, and L_plus <= L + 6 b sqrt b   *)
(* (R >= -6 by the pinching of the slices).                                 *)
(* ========================================================================= *)

(* the scalar curvature is jointly continuous on a slab *)

let P3N_SLAB_SCALAR_CONT = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ k <= hs_count hs
     ==> continuous_map
           (prod_topology (subtopology euclideanreal
                             {t | hs_time hs k <= t /\ t < hs_time hs (k + 1)})
                          (subtopology (hs_top hs k) (topspace(hs_top hs k))),
            euclideanreal)
           (\z. mfd_scalar (hs_atlas hs k) (hs_metric hs k (FST z)) (SND z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k)
                                 (hs_time hs (k + 1)) (hs_metric (hs:(A)rfs_history) k)` THEN
    REWRITE_TAC[ricci_flow_from] THEN SIMP_TAC[]]);;

(* continuity of R along the curve at a parameter that is not an event time *)

let P3N_ST_SCALAR_CONT_AT = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b tau0 e.
     rfs_history_ok hs /\ rfs_st_curve hs tt gamma (&0) b /\ &0 < tau0 /\ tau0 < b /\
     (!j. j <= hs_count hs + 1 ==> ~(tt - tau0 = hs_time hs j)) /\ &0 < e
     ==> ?d. &0 < d /\
             !tau. abs(tau - tau0) < d
                   ==> &0 < tau /\ tau < b /\
                       abs(mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                      (gamma tau) -
                           mfd_scalar (rfs_atlas_at hs (tt - tau0))
                                      (rfs_metric_at hs (tt - tau0)) (gamma tau0)) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve" with Failure _ -> false)) THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN topspace(rfs_top_at (hs:(A)rfs_history) (tt - tau0))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
          (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
               (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tt - tau0 /\ tt - tau0 < rfs_horizon (hs:(A)rfs_history)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_TOPSPACE_LIVE THEN EXISTS_TAC `(gamma:real->A) tau0` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - tau0`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < tt - tau0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= x /\ ~(x = a) ==> a < x`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "hs_count" with Failure _ -> false))
          (concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar (hs_atlas hs k) (hs_metric hs k (tt - tau0))
                              ((gamma:real->A) tau0)` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_SLAB_SCALAR_CONT) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP] THEN
  DISCH_THEN(MP_TAC o SPEC `{y:real | abs(y - R0) < e}` o CONJUNCT2) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_OPEN_IN; real_open; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXISTS_TAC `e - abs(y - R0)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`tt - tau0:real`; `(gamma:real->A) tau0`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    UNDISCH_TAC `(gamma:real->A) tau0 IN topspace(rfs_top_at (hs:(A)rfs_history) (tt - tau0))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
  (* the time factor *)
  UNDISCH_TAC `open_in (subtopology euclideanreal
                 {t | hs_time (hs:(A)rfs_history) k <= t /\ t < hs_time hs (k + 1)}) u` THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM REAL_OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `real_open (u':real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `tt - tau0:real`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `tt - tau0 IN (u:real->bool)` THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  (* the space factor *)
  UNDISCH_TAC `open_in (subtopology (hs_top (hs:(A)rfs_history) k) (topspace(hs_top hs k))) v` THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `v:A->bool`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (min d1 d2) (min (min tau0 (b - tau0))
                                   (min ((tt - tau0) - hs_time (hs:(A)rfs_history) k)
                                        (hs_time hs (k + 1) - (tt - tau0))))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - tau`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET" with Failure _ -> false)) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; FST; SND] THEN
  DISCH_THEN(MP_TAC o SPECL [`tt - tau:real`; `(gamma:real->A) tau`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.21: R along a space-time curve is measurable; the                *)
(* L_plus integrand of an admissible curve is integrable and               *)
(* L_plus <= L + 6 b sqrt b.                                                *)
(* ========================================================================= *)

let P3N_ST_SCALAR_MEAS = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b.
     rfs_history_ok hs /\ rfs_st_curve hs tt gamma (&0) b
     ==> (\tau. mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           (gamma tau))
         real_measurable_on real_interval[&0,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `{&0, b} UNION
              IMAGE (\j. tt - hs_time (hs:(A)rfs_history) j) {j | j <= hs_count hs + 1}` THEN
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_continuous_on; IN_DIFF; IN_REAL_INTERVAL; IN_UNION; IN_INSERT;
                NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `tau0:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `b:real`; `tau0:real`;
                   `e:real`] P3N_ST_SCALAR_CONT_AT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "hs_count" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_NEGLIGIBLE_FINITE THEN
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE]]);;

(* sqrt tau (max 0 R + S) = sqrt tau (R + S) + sqrt tau max 0 (--R) *)

let P3N_MAX_SPLIT = prove
 (`!s r q. s * (max (&0) r + q) = s * (r + q) + s * max (&0) (--r)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `max (&0) r = r + max (&0) (--r)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* R >= -6 along a space-time curve of a pinched history *)

let P3N_ST_SCALAR_LOW = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b tau.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ rfs_st_curve hs tt gamma (&0) b /\
     &0 <= tau /\ tau <= b
     ==> --(&6) <= mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                              (gamma tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve" with Failure _ -> false)) THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN topspace(rfs_top_at (hs:(A)rfs_history) (tt - tau))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
          (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
               (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tt - tau` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - tau`; `(gamma:real->A) tau`]
                  P2A_TOPSPACE_LIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_pinched; rfs_view] THEN
  DISCH_THEN(MP_TAC o SPECL [`tt - tau:real`; `(gamma:real->A) tau`]) THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `--(&6) <= a ==> a <= r ==> --(&6) <= r`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> --(&6) <= --(&6 * x)`) THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC);;

let P3N_LPLUS_FROM_L = prove
 (`!(hs:(A)rfs_history) tt x b (gamma:real->A).
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b gamma
     ==> (\tau. sqrt tau *
                (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                      (gamma tau)) +
                 mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           gamma (&0) b tau pow 2))
         real_integrable_on real_interval[&0,b] /\
         p3_Lplus hs tt gamma b <= rfs_L_length hs tt gamma b + &6 * b * sqrt b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\tau. mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                      (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau))
    real_measurable_on real_interval[&0,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_ST_SCALAR_MEAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve" with Failure _ -> false)) THEN
  (* R >= -6 on the curve *)
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> --(&6) <= mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                   (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)`
  (LABEL_TAC "rlow") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_ST_SCALAR_LOW THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the correction sqrt tau max 0 (--R) is integrable *)
  SUBGOAL_THEN
   `(\tau. sqrt tau * max (&0) (--(mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                             (rfs_metric_at hs (tt - tau))
                                             ((gamma:real->A) tau))))
    real_integrable_on real_interval[&0,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\tau:real. &6 * sqrt b` THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
        REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL; ETA_AX; REAL_CONTINUOUS_ON_SQRT];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_MAX THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        EXISTS_TAC `(:real)` THEN
        REWRITE_TAC[SUBSET_UNIV; REAL_MEASURABLE_ON_CONST; REAL_LEBESGUE_MEASURABLE_INTERVAL];
        MATCH_MP_TAC REAL_MEASURABLE_ON_NEG THEN FIRST_ASSUM ACCEPT_TAC];
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "rlow" (ASSUME_TAC o C MP (CONJ (ASSUME `&0 <= tau`) (ASSUME `tau <= b`)) o
                      SPEC `tau:real`) THEN
      SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt b * &6` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the L_plus integrand is the sum *)
  SUBGOAL_THEN
   `(\tau. sqrt tau *
           (max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                 (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) +
            mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                      gamma (&0) b tau pow 2)) =
    (\tau. rfs_L_integrand hs tt gamma b tau +
           sqrt tau * max (&0) (--(mfd_scalar (rfs_atlas_at hs (tt - tau))
                                              (rfs_metric_at hs (tt - tau)) (gamma tau))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfs_L_integrand] THEN X_GEN_TAC `tau:real` THEN
    REWRITE_TAC[P3N_MAX_SPLIT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\tau. rfs_L_integrand (hs:(A)rfs_history) tt gamma b tau +
           sqrt tau * max (&0) (--(mfd_scalar (rfs_atlas_at hs (tt - tau))
                                              (rfs_metric_at hs (tt - tau))
                                              ((gamma:real->A) tau))))
    real_integrable_on real_interval[&0,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p3_Lplus; rfs_L_length] THEN
  SUBGOAL_THEN
   `(\tau. sqrt tau *
           (max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                 (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) +
            mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                      gamma (&0) b tau pow 2)) =
    (\tau. rfs_L_integrand hs tt gamma b tau +
           sqrt tau * max (&0) (--(mfd_scalar (rfs_atlas_at hs (tt - tau))
                                              (rfs_metric_at hs (tt - tau)) (gamma tau))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfs_L_integrand] THEN X_GEN_TAC `tau:real` THEN
    REWRITE_TAC[P3N_MAX_SPLIT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_L_integrand (hs:(A)rfs_history) tt gamma b`;
                 `\tau. sqrt tau * max (&0) (--(mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                                         (rfs_metric_at hs (tt - tau))
                                                         ((gamma:real->A) tau)))`;
                 `real_interval[&0,b]`] REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `y <= c ==> x + y <= x + c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,b]) (\tau:real. &6 * sqrt b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    USE_THEN "rlow" (ASSUME_TAC o C MP (CONJ (ASSUME `&0 <= tau`) (ASSUME `tau <= b`)) o
                      SPEC `tau:real`) THEN
    SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b * &6` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* L >= -6 b sqrt b for an admissible curve of a pinched history (used for *)
(* the infimum rfs_Lx in Cor 16.24)                                        *)

let P3N_L_LOWER = prove
 (`!(hs:(A)rfs_history) tt x b (gamma:real->A).
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b gamma
     ==> --(&6 * b * sqrt b) <= rfs_L_length hs tt gamma b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_L_length] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,b]) (\tau:real. --(&6 * sqrt b))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `b:real`; `tau:real`]
                P3N_ST_SCALAR_LOW) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  REWRITE_TAC[rfs_L_integrand] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau * --(&6)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `s <= c ==> --(&6 * c) <= s * --(&6)`) THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(REAL_ARITH `--(&6) <= r /\ &0 <= q ==> --(&6) <= r + q`) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]]]);;

(* ========================================================================= *)
(* Prop 16.21: the persisting region of an event.  The old                 *)
(* points P = Y INTER X of the new stage Y = hs_top hs k (old stage         *)
(* X = hs_top hs (k - 1)) are open in X and in Y with the same subspace    *)
(* topology, and the new points lie in the minus cap cores.                *)
(* ========================================================================= *)

let P3N_EVENT_PERSIST = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs
     ==> open_in (hs_top hs (k - 1))
                 (topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))) /\
         open_in (hs_top hs k) (topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))) /\
         subtopology (hs_top hs (k - 1))
                     (topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))) =
         subtopology (hs_top hs k)
                     (topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))) /\
         topspace(hs_top hs k) DIFF topspace(hs_top hs (k - 1)) SUBSET
         UNIONS {IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) | i |
                 i IN ev_index(hs_event hs k)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN
  ABBREV_TAC `X = hs_top (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `Y = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `ev = hs_event (hs:(A)rfs_history) k` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_CUT_SAME_SUBSPACE) THEN STRIP_TAC THEN
  ABBREV_TAC `Zs = topspace(ev_ztop (ev:(A)rfs_event))` THEN
  ABBREV_TAC `Xs = topspace(X:A topology)` THEN
  ABBREV_TAC `Co = mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))` THEN
  ABBREV_TAC `Sg = mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
  ABBREV_TAC `D = ev_disc (ev:(A)rfs_event)` THEN
  SUBGOAL_THEN `topspace(Y:A topology) = Zs DIFF D` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(Y:A topology) INTER Xs = (Zs DIFF Co) DIFF D` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (Xs:A->bool) Co` THEN
    UNDISCH_TAC `(Zs:A->bool) DIFF Co = Xs DIFF Sg` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) (Zs DIFF D)` ASSUME_TAC THENL
   [EXPAND_TAC "Zs" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  (* open in Y *)
  SUBGOAL_THEN `open_in (Y:A topology) (topspace Y INTER Xs)` ASSUME_TAC THENL
   [SUBGOAL_THEN `topspace(Y:A topology) INTER Xs = (Zs DIFF D) INTER (Zs DIFF Co)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `topspace(Y:A topology) INTER Xs = (Zs DIFF Co) DIFF D` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `Y = subtopology (ev_ztop (ev:(A)rfs_event)) (Zs DIFF D)`) THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* open in X *)
  SUBGOAL_THEN `open_in (X:A topology) (topspace Y INTER Xs)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `Xs DIFF Sg:A->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBGOAL_THEN `topspace(Y:A topology) INTER Xs = (Xs DIFF Sg) INTER (Zs DIFF D)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `topspace(Y:A topology) INTER Xs = (Zs DIFF Co) DIFF D` THEN
      UNDISCH_TAC `(Zs:A->bool) DIFF Co = Xs DIFF Sg` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try let l,r = dest_eq(concl th) in
          fst(dest_const(fst(strip_comb l))) = "subtopology" &&
          can (find_term (fun t -> t = `ev_ztop (ev:(A)rfs_event)`)) l
      with Failure _ -> false)) THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = topspace(Y:A topology) INTER Xs` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the same subspace topology *)
    SUBGOAL_THEN `(P:A->bool) SUBSET Xs DIFF Sg /\ P SUBSET Zs DIFF D` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(P:A->bool) = (Zs DIFF Co) DIFF D` THEN
      UNDISCH_TAC `(Zs:A->bool) DIFF Co = Xs DIFF Sg` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `subtopology (ev_ztop (ev:(A)rfs_event)) P` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `subtopology (subtopology X (Xs DIFF Sg)) (P:A->bool)` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          try let l,r = dest_eq(concl th) in
              fst(dest_const(fst(strip_comb l))) = "subtopology" &&
              can (find_term (fun t -> t = `ev_ztop (ev:(A)rfs_event)`)) l
          with Failure _ -> false)) THEN
        REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[]];
      SUBST1_TAC(ASSUME `Y = subtopology (ev_ztop (ev:(A)rfs_event)) (Zs DIFF D)`) THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the new points *)
  REWRITE_TAC[ASSUME `hs_event (hs:(A)rfs_history) k = ev`;
              ASSUME `topspace(Y:A topology) = Zs DIFF D`] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN Co` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN Zs` THEN UNDISCH_TAC `~((y:A) IN Xs)` THEN
    UNDISCH_TAC `(Zs:A->bool) DIFF Co = Xs DIFF Sg` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:A) IN Co` THEN EXPAND_TAC "Co" THEN REWRITE_TAC[IN_MFD_CUT_CORES] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "ev_capp" with Failure _ -> false))
          (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "DISJOINT" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(y:A) IN D` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "ev_capp" with Failure _ -> false))
          (concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET" with Failure _ -> false))) THEN
    REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1))` THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Prop 16.21: the cap regions of an event.  p3n_capphi                    *)
(* selects the parametrisation of cap i of event k; p3n_capreg (open,      *)
(* d < c) and p3n_capcl (closed, d <= c) are the unions over the caps.      *)
(* For dl(t_k) <= 1/46 the regions with c <= A0 + 50 are open resp.        *)
(* closed in the new stage, and they contain the new points (c > A0 + 4).  *)
(* ========================================================================= *)

let p3n_capphi = new_definition
 `p3n_capphi (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real->real,h:real->real)
             (hs:(A)rfs_history) (k:num) (i:num) =
    @Phi:real^3->A. ?xi. p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi`;;

let p3n_capreg = new_definition
 `p3n_capreg (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real->real,h:real->real)
             (hs:(A)rfs_history) (k:num) (c:real) =
    UNIONS {IMAGE (p3n_capphi (md,g0,A0) (dl,h) hs k i) {x | p3_std_dist g0 x < c} | i |
            i IN ev_index(hs_event hs k)}`;;

let p3n_capcl = new_definition
 `p3n_capcl (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real->real,h:real->real)
            (hs:(A)rfs_history) (k:num) (c:real) =
    UNIONS {IMAGE (p3n_capphi (md,g0,A0) (dl,h) hs k i) {x | p3_std_dist g0 x <= c} | i |
            i IN ev_index(hs_event hs k)}`;;

let P3N_CAPPHI = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k i.
     p3_cap_ok (md,g0,A0) (dl,h) hs k i
     ==> ?xi. p3_cap_param (md,g0,A0) (dl,h) hs k i (p3n_capphi (md,g0,A0) (dl,h) hs k i) xi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_cap_ok; p3n_capphi] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]);;

(* the regions in the new stage *)

let P3N_CAPREG_FACTS = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ dl(hs_time hs k) <= &1 / &46
     ==> (!c. &0 < c /\ c <= A0 + &50
              ==> open_in (hs_top hs k) (p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k c)) /\
         (!c. &0 <= c /\ c < A0 + &50
              ==> closed_in (hs_top hs k) (p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) hs k c)) /\
         (!c c'. c < c'
                 ==> p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) hs k c SUBSET
                     p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k c') /\
         (!c. A0 + &4 < c
              ==> topspace(hs_top hs k) DIFF topspace(hs_top hs (k - 1)) SUBSET
                  p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (dl:real->real)(hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN
    DISCH_THEN(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN SIMP_TAC[rfs_history_ok];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &50 <= A0 + &4 + inv((dl:real->real)(hs_time (hs:(A)rfs_history) k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&46 <= x ==> A0 + &50 <= A0 + &4 + x`) THEN
    MATCH_MP_TAC REAL_LE_RINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* every cap has its parametrisation *)
  SUBGOAL_THEN
   `!i. i IN ev_index(hs_event (hs:(A)rfs_history) k)
        ==> ?xi. p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i
                   (p3n_capphi (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i) xi`
  (LABEL_TAC "par") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC P3N_CAPPHI THEN
    UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the image facts for one cap *)
  SUBGOAL_THEN
   `!i c1 c2. i IN ev_index(hs_event (hs:(A)rfs_history) k) /\ &0 <= c1 /\ c1 < A0 + &50 /\
              &0 < c2 /\ c2 <= A0 + &50
              ==> closed_in (hs_top hs k)
                    (IMAGE (p3n_capphi (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i)
                           {x | p3_std_dist g0 x <= c1}) /\
                  open_in (hs_top hs k)
                    (IMAGE (p3n_capphi (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i)
                           {x | p3_std_dist g0 x < c2})`
  (LABEL_TAC "img") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "par" (MP_TAC o C MP (ASSUME `i IN ev_index(hs_event (hs:(A)rfs_history) k)`) o
                  SPEC `i:num`) THEN REWRITE_TAC[p3_cap_param] THEN
    DISCH_THEN(X_CHOOSE_THEN `xi:real^3->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P3N_PARAM_IMAGE_TOP THEN
    EXISTS_TAC `hs_atlas (hs:(A)rfs_history) k` THEN
    EXISTS_TAC `{x:real^3 | --(inv((dl:real->real)(hs_time (hs:(A)rfs_history) k))) <
                            A0 + &4 - p3_std_dist g0 x}` THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_VIEW_AT_EVENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c1:real`] P3N_STD_SUBLEVEL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c2:real`] P3N_STD_SUBLEVEL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ev_index(hs_event (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[rfs_event_ok; mfd_cut_cap] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* open *)
    X_GEN_TAC `c:real` THEN STRIP_TAC THEN REWRITE_TAC[p3n_capreg] THEN
    MATCH_MP_TAC(ISPEC `hs_top (hs:(A)rfs_history) k` OPEN_IN_UNIONS) THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`i:num`; `&0`; `c:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    (* closed *)
    X_GEN_TAC `c:real` THEN STRIP_TAC THEN REWRITE_TAC[p3n_capcl] THEN
    MATCH_MP_TAC(ISPEC `hs_top (hs:(A)rfs_history) k` CLOSED_IN_UNIONS) THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`i:num`; `c:real`; `A0 + &50`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    (* monotone *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p3n_capcl; p3n_capreg] THEN
    MATCH_MP_TAC(SET_RULE `(!x:num. P x ==> (f:num->A->bool) x SUBSET g x)
                           ==> UNIONS {f x | x | P x} SUBSET UNIONS {g x | x | P x}`) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    (* the new points *)
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_EVENT_PERSIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(SET_RULE `(t:A->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
    REWRITE_TAC[p3n_capreg] THEN
    MATCH_MP_TAC(SET_RULE `(!x:num. P x ==> (f:num->A->bool) x SUBSET g x)
                           ==> UNIONS {f x | x | P x} SUBSET UNIONS {g x | x | P x}`) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o C MP (ASSUME `i IN ev_index(hs_event (hs:(A)rfs_history) k)`) o
                  SPEC `i:num`) THEN REWRITE_TAC[p3_cap_param] THEN
    DISCH_THEN(X_CHOOSE_THEN `xi:real^3->real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "ev_capm" with Failure _ -> false))
          (concl th))) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.21: |Rm| near an event time on compact subsets of               *)
(* Omega.  The tensor norm of the limit metric is that of its restriction  *)
(* to Omega (a Riemannian metric there, P3H_LIMIT_RESTRICT_RIEMANNIAN),     *)
(* hence bounded on compact subsets of Omega; the C^2 convergence of       *)
(* rfs_limit_metric then bounds |Rm| of the slab metrics near the event     *)
(* time (P3H_LIMIT_RM_BOUND for a compact K in Omega).                     *)
(* ========================================================================= *)

let P3N_RMD2_LIMIT_RESTRICT = prove
 (`!top atlas Om ts (g:real->A->real^3^3) gl l x.
     smooth_manifold_atlas top atlas /\ open_in top Om /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ x IN Om
     ==> rfa_rmd2 l atlas gl x =
         rfa_rmd2 l (restrict_atlas atlas Om) (restrict_metric atlas Om gl) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `subtopology top (Om:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om`;
                 `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) Om gl`;
                 `(FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) INTER Om,
                   SND(chart_at atlas x))`; `x:A`] RFA_RMD2_CHART) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ts:real`; `g:real->A->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[restrict_atlas; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                            `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`] THEN
      ASM_REWRITE_TAC[PAIR];
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x) INTER Om)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`] THEN
    ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `Om:A->bool`; `gl:A->real^3^3`; `z:A`] METRIC_LOCAL_RESTRICT) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER]]);;

(* a bound for the tensor norm of the limit metric on a compact subset of Omega *)

let P3N_RMD2_LIMIT_BOUND = prove
 (`!top atlas Om ts (g:real->A->real^3^3) gl K l.
     smooth_manifold_atlas top atlas /\ open_in top Om /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ compact_in top K /\ K SUBSET Om
     ==> ?B. !y. y IN K ==> rfa_rmd2 l atlas gl y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `subtopology top (Om:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om`;
                 `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) Om gl`; `K:A->bool`]
                P3H_RMD2_COMPACT_BOUND_FIXED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ts:real`; `g:real->A->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN DISCH_TAC THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                 `ts:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`; `l:num`; `y:A`]
                P3N_RMD2_LIMIT_RESTRICT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* |Rm| of the slab metrics near the event time on a compact subset of Omega *)

let P3N_LIMIT_RM_BOUND_K = prove
 (`!top atlas a Om ts (g:real->A->real^3^3) gl K.
     smooth_manifold_atlas top atlas /\ a < ts /\
     (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
     open_in top Om /\ rfs_limit_metric (top,atlas) Om ts g gl /\
     compact_in top K /\ K SUBSET Om
     ==> ?d B. &0 < d /\ d <= ts - a /\
               !t x. ts - d < t /\ t < ts /\ x IN K ==> mfd_rm_norm atlas (g t) x <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                 `ts:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`; `K:A->bool`; `0`]
                P3N_RMD2_LIMIT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN
  X_CHOOSE_TAC `Kb:real` (SPEC `K0:real` LRG_RM_NEAR_BOUND) THEN
  UNDISCH_TAC `rfs_limit_metric (top,atlas) (Om:A->bool) ts (g:real->A->real^3^3) gl` THEN
  REWRITE_TAC[rfs_limit_metric] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mf") (MP_TAC o SPECL [`K:A->bool`; `2`; `&1 / &4`])) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min d0 (ts - a)`; `sqrt(max Kb (&0))`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ x IN Om` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                             ((g:real->A->real^3^3) t) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3H_RM_NORM_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmd2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x) INTER Om)` THEN
  EXISTS_TAC `metric_local (atlas:((A->bool)#(A->real^3))->bool)
                           (chart_at atlas (x:A)) (gl:A->real^3^3)` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "mf" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`] THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
      SET_TAC[]];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[rfa_rmd2];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.21: a Lebesgue number for the distance balls of a               *)
(* Riemannian metric: a compact set K disjoint from a closed set F has a    *)
(* radius rho with all balls B(p,rho), p in K, disjoint from F.             *)
(* ========================================================================= *)

let P3N_MFD_LEBESGUE = prove
 (`!top atlas (g:A->real^3^3) K Fc.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ closed_in top Fc /\ DISJOINT K Fc
     ==> ?rho. &0 < rho /\
               !p y. p IN K /\ y IN mfd_ball (top,atlas) g p rho ==> ~(y IN Fc)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  (* a radius at each point *)
  SUBGOAL_THEN
   `?r. !p. p IN K
            ==> &0 < r p /\
                mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g p (r p) SUBSET
                topspace top DIFF Fc`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC MFD_BALL_NEIGHBOURHOOD_BASE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the finite subcover by the half balls *)
  FIRST_ASSUM(MP_TAC o SPEC
    `IMAGE (\p:A. mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g p (r p / &2)) K` o
    CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `p:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `p:A` THEN DISCH_TAC THEN EXISTS_TAC `p:A` THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\p:A. mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g p (r p / &2)`;
                 `K:A->bool`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `P0:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inf (IMAGE (\p:A. r p / &2) P0)` THEN
  MP_TAC(ISPEC `IMAGE (\p:A. r p / &2) P0` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q0:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q:A. q IN P0 /\
                      p IN mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g q (r q / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:A) IN mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g q (r q)` MP_TAC THENL
   [UNDISCH_TAC `(p:A) IN mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g q (r q / &2)` THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas:((A->bool)#(A->real^3))->bool) g p
                    (inf (IMAGE (\p:A. (r:A->real) p / &2) P0))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas:((A->bool)#(A->real^3))->bool) g q p +
                  mfd_dist (top,atlas) g p y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "inf" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top DIFF Fc` MP_TAC THENL
   [ASM SET_TAC[]; SET_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.21: the sets of an event k and the uniform                      *)
(* parabolic data just before it.  S = Y minus the cap regions d < A0 + 50  *)
(* and C = Y minus the cap regions d < A0 + 40 consist of old points; C is  *)
(* compact in both stages; there is r0 > 0 such that for every p in S the  *)
(* parabolic ball P(p,t_k,r0,-r0^2) exists, has |Rm| <= r0^-2 and its      *)
(* ball at t_k lies in C.                                                  *)
(* ========================================================================= *)

let P3N_CAPREG_SUB_CL = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k c.
     p3n_capreg (md,g0,A0) (dl,h) hs k c SUBSET p3n_capcl (md,g0,A0) (dl,h) hs k c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_capreg; p3n_capcl] THEN
  MATCH_MP_TAC(SET_RULE `(!x:num. P x ==> (f:num->A->bool) x SUBSET g x)
                         ==> UNIONS {f x | x | P x} SUBSET UNIONS {g x | x | P x}`) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let P3N_END_SETS = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ dl(hs_time hs k) <= &1 / &46
     ==> topspace(hs_top hs k) DIFF
         p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40) SUBSET
         topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1)) /\
         compact_in (hs_top hs k)
           (topspace(hs_top hs k) DIFF
            p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)) /\
         compact_in (hs_top hs (k - 1))
           (topspace(hs_top hs k) DIFF
            p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)) /\
         compact_in (hs_top hs k)
           (topspace(hs_top hs k) DIFF
            p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)) /\
         closed_in (hs_top hs k) (p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)) /\
         DISJOINT (topspace(hs_top hs k) DIFF
                   p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50))
                  (p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)) /\
         topspace(hs_top hs k) DIFF
         p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50) SUBSET
         topspace(hs_top hs k) DIFF
         p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_CAPREG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "op") (CONJUNCTS_THEN2 (LABEL_TAC "cl")
    (CONJUNCTS_THEN2 (LABEL_TAC "mono") (LABEL_TAC "new")))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_EVENT_PERSIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `compact_space(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `X = hs_top (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `R40 = p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &40)` THEN
  ABBREV_TAC `R50 = p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &50)` THEN
  ABBREV_TAC `F40 = p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &40)` THEN
  SUBGOAL_THEN `open_in Y (R40:A->bool) /\ open_in Y (R50:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "R40" THEN USE_THEN "op" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "R50" THEN USE_THEN "op" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in Y (F40:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F40" THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(F40:A->bool) SUBSET R50 /\ (R40:A->bool) SUBSET F40` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["F40"; "R50"] THEN USE_THEN "mono" MATCH_MP_TAC THEN
      REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["R40"; "F40"] THEN REWRITE_TAC[P3N_CAPREG_SUB_CL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace Y DIFF topspace X SUBSET (R40:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R40" THEN USE_THEN "new" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `topspace Y DIFF (R40:A->bool) SUBSET topspace Y INTER topspace X`
  ASSUME_TAC THENL
   [UNDISCH_TAC `topspace Y DIFF topspace X SUBSET (R40:A->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in Y (topspace Y DIFF (R40:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* compact in X *)
    SUBGOAL_THEN `compact_in (subtopology X (topspace Y INTER topspace X))
                             (topspace Y DIFF (R40:A->bool))` MP_TAC THENL
     [SUBST1_TAC(ASSUME `subtopology X (topspace Y INTER topspace X) =
                          subtopology Y (topspace Y INTER topspace (X:A topology))`) THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[]];
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
    UNDISCH_TAC `(F40:A->bool) SUBSET R50` THEN SET_TAC[];
    UNDISCH_TAC `(R40:A->bool) SUBSET F40` THEN UNDISCH_TAC `(F40:A->bool) SUBSET R50` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.21: the uniform parabolic data just before an                   *)
(* event k: a radius r0 such that for every p in Y minus the cap regions   *)
(* d < A0 + 50 the parabolic ball P(p,t_k,r0,-r0^2) exists, carries        *)
(* |Rm| <= r0^-2 and its ball at t_k avoids the cap regions d < A0 + 40.   *)
(* ========================================================================= *)

let P3N_END_DATA = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ dl(hs_time hs k) <= &1 / &46
     ==> ?r0. &0 < r0 /\ r0 pow 2 < hs_time hs k - hs_time hs (k - 1) /\
              !p. p IN topspace(hs_top hs k) DIFF
                       p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)
                  ==> rfs_parabolic_exists (rfs_view hs) (hs_time hs k) p r0 (r0 pow 2) /\
                      (!s y. hs_time hs k - r0 pow 2 < s /\ s <= hs_time hs k /\
                             y IN rfs_vball (rfs_view hs) (hs_time hs k) p r0
                             ==> p3_vrm (rfs_view hs) s y <= inv(r0 pow 2)) /\
                      rfs_vball (rfs_view hs) (hs_time hs k) p r0 SUBSET
                      topspace(hs_top hs k) DIFF
                      p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_END_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_EVENT_PERSIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  (* the slabs k - 1 and k and the event *)
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ (k - 1) + 1 = k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "ricci_flow_from" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(k - 1) + 1 = k`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "ricci_flow_from" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_event_ok" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_event_ok] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
                       MAP_EVERY ASSUME_TAC [el 0 cs; el 1 cs; el 14 cs]) THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k /\
                hs_time hs k < hs_time hs (k + 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(C MP (ASSUME `k - 1 <= hs_count (hs:(A)rfs_history)`)
               (SPEC `k - 1` (CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfs_history_ok]
                 (ASSUME `rfs_history_ok (hs:(A)rfs_history)`)))))) THEN
      REWRITE_TAC[ASSUME `(k - 1) + 1 = k`];
      ACCEPT_TAC(C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`)
                   (SPEC `k:num` (CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfs_history_ok]
                     (ASSUME `rfs_history_ok (hs:(A)rfs_history)`))))))];
    ALL_TAC] THEN
  ABBREV_TAC `Y = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `X = hs_top (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `tk = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `S50 = topspace Y DIFF
                    p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &50)` THEN
  ABBREV_TAC `C40 = topspace Y DIFF
                    p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &40)` THEN
  ABBREV_TAC `F40 = p3n_capcl (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &40)` THEN
  (* |Rm| before the event on C40 *)
  MP_TAC(ISPECL [`X:A topology`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_time (hs:(A)rfs_history) (k - 1)`; `ev_omega(hs_event (hs:(A)rfs_history) k)`;
                 `tk:real`; `hs_metric (hs:(A)rfs_history) (k - 1)`;
                 `ev_limit(hs_event (hs:(A)rfs_history) k)`; `C40:A->bool`]
                P3N_LIMIT_RM_BOUND_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`X:A topology`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                     `hs_time (hs:(A)rfs_history) (k - 1)`; `tk:real`;
                     `hs_metric (hs:(A)rfs_history) (k - 1)`; `t:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ASM_SIMP_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  (* |Rm| at the event time on Y *)
  MP_TAC(ISPECL [`Y:A topology`; `hs_atlas (hs:(A)rfs_history) k`; `tk:real`;
                 `hs_time (hs:(A)rfs_history) (k + 1)`; `tk:real`;
                 `hs_metric (hs:(A)rfs_history) k`] P3H_RF_RM_BOUND_COMPACT_TIME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN
  (* the Lebesgue number at the event time *)
  SUBGOAL_THEN `smooth_manifold_atlas Y (hs_atlas (hs:(A)rfs_history) k) /\
                riemannian_metric (hs_atlas hs k) (hs_metric hs k tk)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Y:A topology`; `hs_atlas (hs:(A)rfs_history) k`; `tk:real`;
                   `hs_time (hs:(A)rfs_history) (k + 1)`; `hs_metric (hs:(A)rfs_history) k`;
                   `tk:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Y:A topology`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k tk`; `S50:A->bool`; `F40:A->bool`]
                P3N_MFD_LEBESGUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  (* the radius *)
  ABBREV_TAC `M = max (abs B1) (abs B2) + &1` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (min rho (inv M)) (min (&1) (min d1 ((tk - hs_time (hs:(A)rfs_history) (k - 1)) / &2)))` THEN
  ABBREV_TAC `r0 = min (min rho (inv M)) (min (&1) (min d1 ((tk - hs_time (hs:(A)rfs_history) (k - 1)) / &2)))` THEN
  SUBGOAL_THEN `&0 < inv M` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r0 /\ r0 <= rho /\ r0 <= inv M /\ r0 <= &1 /\ r0 <= d1 /\
                r0 <= (tk - hs_time (hs:(A)rfs_history) (k - 1)) / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "r0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r0 pow 2 <= r0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r0 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `M <= inv(r0 pow 2)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`r0 pow 2`; `inv M`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_INV_INV]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  (* the ball at the event time *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tk:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_vball (rfs_view (hs:(A)rfs_history)) tk p r0 =
                mfd_ball (Y,hs_atlas hs k) (hs_metric hs k tk) p r0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[rfs_vball; rfs_view]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0 SUBSET C40`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace Y /\ ~(y IN F40)` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(y:A) IN mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
        EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:A) IN mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      MAP_EVERY EXPAND_TAC ["C40"; "F40"] THEN
      MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                     `p3_hscale hf rp dl`; `hs:(A)rfs_history`; `k:num`; `A0 + &40`]
                    P3N_CAPREG_SUB_CL) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in Y (mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0)`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in X (mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `topspace Y INTER topspace (X:A topology)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0 =
                  (topspace Y INTER topspace X) INTER
                  mfd_ball (Y,hs_atlas hs k) (hs_metric hs k tk) p r0` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the parabolic ball exists *)
    REWRITE_TAC[rfs_parabolic_exists] THEN
    SUBGOAL_THEN `rfs_vball (rfs_view (hs:(A)rfs_history)) tk p r0 =
                  mfd_ball (Y,hs_atlas hs k) (hs_metric hs k tk) p r0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[rfs_vball; rfs_view]; ALL_TAC] THEN
    REWRITE_TAC[rfs_persists; rfs_view] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s:real = tk` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the curvature bound *)
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_vrm; rfs_view; rfs_vatlas; rfs_vmetric] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s:real = tk` THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "M" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b2 ==> x <= max (abs b1) (abs b2) + &1`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (Y,hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k tk) p r0` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "M" THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b1 ==> x <= max (abs b1) (abs b2) + &1`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* Prop 16.21: a curve with L_plus < L0 that passes the time               *)
(* tk = tt - tauk at a point p with a parabolic ball P(p,tk,r0,-r0^2) and  *)
(* |Rm| <= r0^-2 stays in B(p,tk,r0/2) for backward time                   *)
(* min (r0^4/(1024 L0^2)) (r0^2/8) after tauk: P3N_PAR_BALL for the        *)
(* shifted curve with the shifted L_plus integrand as majorant.            *)
(* ========================================================================= *)

let P3N_MUL_MONO2 = prove
 (`!u v s m. &0 <= u /\ u <= v /\ &0 <= s /\ &0 <= m ==> u * s <= v * (m + s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v * s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let P3N_END_COVER = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) tau0 tk r0 L0 tauk.
     rfs_history_ok hs /\ rfs_st_curve hs tt gamma (&0) tau0 /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\ &0 < L0 /\
     &0 < tauk /\ tauk < tau0 /\ tt - tauk = tk /\ &0 < r0 /\
     rfs_parabolic_exists (rfs_view hs) tk (gamma tauk) r0 (r0 pow 2) /\
     (!s y. tk - r0 pow 2 < s /\ s <= tk /\ y IN rfs_vball (rfs_view hs) tk (gamma tauk) r0
            ==> p3_vrm (rfs_view hs) s y <= inv(r0 pow 2))
     ==> !tau. tauk <= tau /\ tau <= tau0 /\
               tau - tauk <= min (r0 pow 4 / (&1024 * L0 pow 2)) (r0 pow 2 / &8)
               ==> gamma tau IN rfs_vball (rfs_view hs) tk (gamma tauk) (r0 / &2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ABBREV_TAC `tp = min (r0 pow 4 / (&1024 * L0 pow 2)) (r0 pow 2 / &8)` THEN
  SUBGOAL_THEN `&0 < tp /\ tp <= r0 pow 4 / (&1024 * L0 pow 2) /\ tp <= r0 pow 2 / &8`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tp" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_ARITH `&0 < &1024 /\ &0 < &8`];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p3_Lplus]) THEN
  ABBREV_TAC `f = \tau. sqrt tau *
                (max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                      (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) +
                 mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           gamma (&0) tau0 tau pow 2)` THEN
  SUBGOAL_THEN `!t. &0 <= t ==> &0 <= (f:real->real) t` (LABEL_TAC "fpos") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2; REAL_LE_MAX; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `b = min tp (tau0 - tauk)` THEN
  SUBGOAL_THEN `&0 < b /\ b <= tp /\ b <= tau0 - tauk` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the shifted majorant *)
  SUBGOAL_THEN `(f:real->real) real_integrable_on real_interval[tauk,tauk + b]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3N_INTEGRAL_SHIFT_EQ) THEN
  REWRITE_TAC[REAL_ARITH `(tauk + b) - tauk = b`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `real_integral (real_interval[tauk,tauk + b]) (f:real->real) < L0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,tau0]) (f:real->real)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "fpos" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the shifted curve *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`; `tauk:real`;
                 `tau0:real`] P3N_ST_CURVE_SHIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tk:real`; `(gamma:real->A) tauk`; `r0:real`;
                 `tau0 - tauk`; `b:real`; `\s. (gamma:real->A)(tauk + s)`;
                 `\x. (f:real->real)(tauk + x)`; `&4 * L0 / r0`] P3N_PAR_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [(* the point is in the slice *)
      UNDISCH_TAC `rfs_st_curve (hs:(A)rfs_history) tt (gamma:real->A) (&0) tau0` THEN
      REWRITE_TAC[rfs_st_curve] THEN
      DISCH_THEN(MP_TAC o SPEC `tauk:real` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      (* the start point *)
      REWRITE_TAC[REAL_ADD_RID];
      (* nonnegative *)
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "fpos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      (* the speed term *)
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[P3N_SPEED_SHIFT; REAL_ADD_RID; REAL_ARITH `tauk + (tau0 - tauk) = tau0`] THEN
      SUBGOAL_THEN `tk - t = tt - (tauk + t)` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`rfs_atlas_at (hs:(A)rfs_history) (tt - (tauk + t))`;
                     `rfs_metric_at (hs:(A)rfs_history) (tt - (tauk + t))`; `gamma:real->A`;
                     `tauk:real`; `tau0:real`; `&0`; `tau0:real`; `tauk + t`]
                    P2A_SPEED_INTERIOR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "f" THEN BETA_TAC THEN
      MATCH_MP_TAC P3N_MUL_MONO2 THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_LE_MAX; REAL_LE_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      (* lam > 0 *)
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      (* the majorant integral *)
      MATCH_MP_TAC P3N_1615_ARITH1 THEN EXISTS_TAC `r0:real` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC)];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau - tauk`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ARITH `tauk + (tau - tauk) = tau`]);;

(* ========================================================================= *)
(* Prop 16.21: closure properties of p3_st_compact: the                    *)
(* empty family, one piece, monotonicity, binary and finite unions.        *)
(* ========================================================================= *)

let P3N_STC_EMPTY = prove
 (`!hs:(A)rfs_history. p3_st_compact hs (\t. {})`,
  GEN_TAC THEN REWRITE_TAC[p3_st_compact; NOT_IN_EMPTY] THEN
  MAP_EVERY EXISTS_TAC [`0`; `\j:num. {}:A->bool`; `\j:num. {}:A->bool`;
                        `\j:num. &0`; `\j:num. &0`; `&1`] THEN
  REWRITE_TAC[LT; REAL_LT_01]);;

let P3N_STC_MONO = prove
 (`!(hs:(A)rfs_history) K K'.
     p3_st_compact hs K /\ (!t. K' t SUBSET K t) ==> p3_st_compact hs K'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_st_compact] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `W:num->A->bool`; `C:num->A->bool`; `a:num->real`;
                        `b:num->real`; `eta:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P3N_STC_PIECE = prove
 (`!(hs:(A)rfs_history) W C a b eta.
     a <= b /\ C SUBSET W /\ &0 < eta /\ rfs_persists (rfs_view hs) W (a - eta) b /\
     (!s. a <= s /\ s <= b ==> compact_in (rfs_top_at hs s) C)
     ==> p3_st_compact hs (\t. {y | a <= t /\ t <= b /\ y IN C})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_st_compact; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`1`; `\j:num. W:A->bool`; `\j:num. C:A->bool`;
                        `\j:num. a:real`; `\j:num. b:real`; `eta:real`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `j < 1 <=> j = 0`] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]);;

(* persistence over a shorter interval *)

let P3N_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b a' b'.
     rfs_persists V W a b /\ a <= a' /\ b' <= b ==> rfs_persists V W a' b'`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_STC_UNION = prove
 (`!(hs:(A)rfs_history) K1 K2.
     p3_st_compact hs K1 /\ p3_st_compact hs K2
     ==> p3_st_compact hs (\t. K1 t UNION K2 t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_st_compact] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `W1:num->A->bool` (X_CHOOSE_THEN `C1:num->A->bool`
      (X_CHOOSE_THEN `a1:num->real` (X_CHOOSE_THEN `b1:num->real`
        (X_CHOOSE_THEN `eta1:real` STRIP_ASSUME_TAC))))))
    (X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `W2:num->A->bool` (X_CHOOSE_THEN `C2:num->A->bool`
      (X_CHOOSE_THEN `a2:num->real` (X_CHOOSE_THEN `b2:num->real`
        (X_CHOOSE_THEN `eta2:real` STRIP_ASSUME_TAC))))))) THEN
  MAP_EVERY EXISTS_TAC
   [`n1 + n2:num`;
    `\j:num. if j < n1 then (W1:num->A->bool) j else W2 (j - n1)`;
    `\j:num. if j < n1 then (C1:num->A->bool) j else C2 (j - n1)`;
    `\j:num. if j < n1 then (a1:num->real) j else a2 (j - n1)`;
    `\j:num. if j < n1 then (b1:num->real) j else b2 (j - n1)`;
    `min eta1 eta2`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < n1:num` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `C1:num->A->bool`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "rfs_persists" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3N_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(a1:num->real) j - eta1`; `(b1:num->real) j`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `j - n1:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `C2:num->A->bool`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "rfs_persists" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3N_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(a2:num->real) (j - n1) - eta2`; `(b2:num->real) (j - n1)`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K1:real->A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K2:real->A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n1 + j:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(n1 + j < n1:num)`; ARITH_RULE `(n1 + j) - n1 = j:num`] THEN
    ASM_ARITH_TAC]);;

(* a finite union indexed by k <= n *)

let P3N_STC_UNIONS = prove
 (`!(hs:(A)rfs_history) (K:num->real->A->bool) n.
     (!k. k <= n ==> p3_st_compact hs (K k))
     ==> p3_st_compact hs (\t. UNIONS {K k t | k | k <= n})`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC P3N_STC_MONO THEN EXISTS_TAC `(K:num->real->A->bool) 0` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; LE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p3_st_compact (hs:(A)rfs_history)
                  (\t. UNIONS {(K:num->real->A->bool) k t | k | k <= n} UNION K (SUC n) t)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`hs:(A)rfs_history`;
      `\t. UNIONS {(K:num->real->A->bool) k t | k | k <= n}`; `(K:num->real->A->bool) (SUC n)`]
      P3N_STC_UNION)) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P3N_STC_MONO THEN
  EXISTS_TAC `\t. UNIONS {(K:num->real->A->bool) k t | k | k <= n} UNION K (SUC n) t` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNION; LE] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* Prop 16.21: a positive lower bound of finitely many                     *)
(* positive numbers, and the three kinds of compact pieces: the event      *)
(* piece (C40 of event k over [t_k - dl,t_k + dl]), the middle piece (a     *)
(* whole slab slice) and the parabolic piece (cball(x,tt,r/2) near tt).    *)
(* ========================================================================= *)

let P3N_FINITE_MIN = prove
 (`!n (f:num->real). (!k. k <= n ==> &0 < f k) ==> ?d. &0 < d /\ !k. k <= n ==> d <= f k`,
  INDUCT_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `(f:num->real) 0` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[LE] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:num->real`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((f:num->real) (SUC n))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    X_GEN_TAC `k:num` THEN REWRITE_TAC[LE] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `d <= x ==> min d y <= x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* the event piece *)

let P3N_EVPIECE = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k de eta.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ dl(hs_time hs k) <= &1 / &46 /\
     &0 < de /\ &0 < eta /\ de + eta < hs_time hs k - hs_time hs (k - 1) /\
     de < hs_time hs (k + 1) - hs_time hs k
     ==> p3_st_compact hs
           (\t. {y | hs_time hs k - de <= t /\ t <= hs_time hs k + de /\
                     y IN topspace(hs_top hs k) DIFF
                          p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_END_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_EVENT_PERSIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ (k - 1) + 1 = k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3N_STC_PIECE THEN
  EXISTS_TAC `topspace(hs_top (hs:(A)rfs_history) k) INTER topspace(hs_top hs (k - 1))` THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    (* persistence across the event *)
    REWRITE_TAC[rfs_persists; rfs_view] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < hs_time (hs:(A)rfs_history) k` THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
      DISCH_THEN(MP_TAC o SPEC `k - 1` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    (* compact in the slices *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < hs_time (hs:(A)rfs_history) k` THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[]]]);;

(* the middle piece of a slab *)

let P3N_MIDPIECE = prove
 (`!(hs:(A)rfs_history) k a b eta.
     rfs_history_ok hs /\ k <= hs_count hs /\ &0 < eta /\
     hs_time hs k <= a - eta /\ a <= b /\ b < hs_time hs (k + 1)
     ==> p3_st_compact hs (\t. {y | a <= t /\ t <= b /\ y IN topspace(hs_top hs k)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_STC_PIECE THEN
  EXISTS_TAC `topspace(hs_top (hs:(A)rfs_history) k)` THEN EXISTS_TAC `eta:real` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_persists; rfs_view] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[GSYM compact_space]]);;

(* the parabolic piece near tt *)

let P3N_PXPIECE = prove
 (`!(hs:(A)rfs_history) tt x r taup eta.
     rfs_history_ok hs /\ &0 < r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     &0 <= taup /\ &0 < eta /\ taup + eta < r pow 2
     ==> p3_st_compact hs
           (\t. {y | tt - taup <= t /\ t <= tt /\
                     y IN mfd_cball (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                                    x (r / &2)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (rfs_view (hs:(A)rfs_history)) (rfs_vball (rfs_view hs) tt x r)
                           (tt - r pow 2) tt` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r (r pow 2)` THEN
    REWRITE_TAC[rfs_parabolic_exists];
    ALL_TAC] THEN
  MATCH_MP_TAC P3N_STC_PIECE THEN
  EXISTS_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r` THEN EXISTS_TAC `eta:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[rfs_vball; rfs_view; SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3N_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`tt - r pow 2`; `tt:real`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r (r pow 2)` THEN
    REWRITE_TAC[rfs_parabolic_exists];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_SIMP_TAC[P2AB_COMPACT] THEN
    MATCH_MP_TAC P3N_PAR_KC_CLOSED THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Prop 16.21: coverage near an event k with T0 <= t_k < tt.                *)
(* After t_k the curve avoids the cap regions d < A0 + 50 (Lemma 16.15(2), *)
(* hypothesis (E) for the caps of the event), hence lies in S50 of the new *)
(* stage; before t_k it stays in the parabolic ball of the point where it  *)
(* passes t_k (P3N_END_COVER with the uniform radius of P3N_END_DATA),     *)
(* hence in C40.                                                           *)
(* ========================================================================= *)

let P3N_START_COVER = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) tt (gamma:real->A) tau0 T0 k de tau.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ T0 <= hs_time hs k /\ hs_time hs k < tt /\
     dl(hs_time hs k) <= &1 / &46 /\
     (!k j Phi xi tp.
        1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
        T0 <= hs_time hs k /\ hs_time hs k < tt /\
        p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k j Phi xi /\
        hs_time hs k <= tp /\
        tp <= hs_time hs k + p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
        (!s. hs_time hs k <= s /\ s <= tp
             ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET topspace(rfs_top_at hs s))
        ==> !tau. &0 <= tau /\ tau <= tau0 /\ hs_time hs k <= tt - tau /\ tt - tau <= tp
                  ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50})) /\
     rfs_st_curve hs tt gamma (&0) tau0 /\
     &0 <= de /\ de <= p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
     de < hs_time hs (k + 1) - hs_time hs k /\
     &0 <= tau /\ tau <= tau0 /\ hs_time hs k <= tt - tau /\ tt - tau <= hs_time hs k + de
     ==> gamma tau IN topspace(hs_top hs k) DIFF
                      p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_CAPREG_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `A0 + &50` o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [(* the point is in the new stage *)
    UNDISCH_TAC `rfs_st_curve (hs:(A)rfs_history) tt (gamma:real->A) (&0) tau0` THEN
    REWRITE_TAC[rfs_st_curve] THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - tau`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* no cap contains it *)
  REWRITE_TAC[p3n_capreg; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `U:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `p3_hscale hf rp dl`; `hs:(A)rfs_history`; `k:num`; `j:num`] P3N_CAPPHI) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `xi:real^3->real^3`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`k:num`; `j:num`; `p3n_capphi (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k j`;
     `xi:real^3->real^3`; `hs_time (hs:(A)rfs_history) k + de`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p3_cap_param" with Failure _ -> false))
          (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &50)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[p3n_capreg] THEN MATCH_MP_TAC(SET_RULE `(x:A->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[]);;

let P3N_END_COVER2 = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) tt (gamma:real->A) tau0 T0 k L0 r0 de tau.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     1 <= k /\ k <= hs_count hs /\ T0 <= hs_time hs k /\ hs_time hs k < tt /\
     dl(hs_time hs k) <= &1 / &46 /\
     (!k j Phi xi tp.
        1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
        T0 <= hs_time hs k /\ hs_time hs k < tt /\
        p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k j Phi xi /\
        hs_time hs k <= tp /\
        tp <= hs_time hs k + p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
        (!s. hs_time hs k <= s /\ s <= tp
             ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET topspace(rfs_top_at hs s))
        ==> !tau. &0 <= tau /\ tau <= tau0 /\ hs_time hs k <= tt - tau /\ tt - tau <= tp
                  ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50})) /\
     rfs_st_curve hs tt gamma (&0) tau0 /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\ &0 < L0 /\
     &0 < r0 /\
     (!p. p IN topspace(hs_top hs k) DIFF
               p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)
          ==> rfs_parabolic_exists (rfs_view hs) (hs_time hs k) p r0 (r0 pow 2) /\
              (!s y. hs_time hs k - r0 pow 2 < s /\ s <= hs_time hs k /\
                     y IN rfs_vball (rfs_view hs) (hs_time hs k) p r0
                     ==> p3_vrm (rfs_view hs) s y <= inv(r0 pow 2)) /\
              rfs_vball (rfs_view hs) (hs_time hs k) p r0 SUBSET
              topspace(hs_top hs k) DIFF
              p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)) /\
     &0 <= de /\ de <= min (r0 pow 4 / (&1024 * L0 pow 2)) (r0 pow 2 / &8) /\
     tt - hs_time hs k < tau /\ tau <= tau0 /\ tau <= (tt - hs_time hs k) + de
     ==> gamma tau IN topspace(hs_top hs k) DIFF
                      p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1)` ASSUME_TAC THENL
   [ACCEPT_TAC(C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`)
                (SPEC `k:num` (CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfs_history_ok]
                  (ASSUME `rfs_history_ok (hs:(A)rfs_history)`))))));
    ALL_TAC] THEN
  ABBREV_TAC `tauk = tt - hs_time (hs:(A)rfs_history) k` THEN
  (* the curve passes t_k in S50 *)
  SUBGOAL_THEN `(gamma:real->A) tauk IN topspace(hs_top hs k) DIFF
                p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &50)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_START_COVER THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `tt:real`; `tau0:real`; `T0:real`; `&0`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x / &2`) THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A) tauk` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_parabolic_exists" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`;
                 `hs_time (hs:(A)rfs_history) k`; `r0:real`; `L0:real`; `tauk:real`]
                P3N_END_COVER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    (try fst(dest_const(fst(strip_comb(concl th))))= "SUBSET" with Failure _ -> false) &&
    can (find_term (fun t -> t = `A0 + &40`)) (concl th))) THEN
  UNDISCH_TAC `(gamma:real->A) tau IN
               rfs_vball (rfs_view (hs:(A)rfs_history)) (hs_time hs k) (gamma tauk) (r0 / &2)` THEN
  REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.21: the compact space-time set p3n_kset: the                    *)
(* parabolic piece near tt, the event pieces of the events in [T0,tt) and  *)
(* the middle pieces of all slabs, for a width de; it is p3_st_compact     *)
(* when de is small against the slab lengths and r^2 - taup.               *)
(* ========================================================================= *)

let p3n_kset = new_definition
 `p3n_kset (md:real->real,g0:real^3->real^3^3,A0:real)
           (rp:real->real,dl:real->real,hf:real->real->real)
           (hs:(A)rfs_history) (tt:real) (x:A) (r:real) (T0:real) (taup:real) (de:real)
           (t:real) =
    {y | tt - taup <= t /\ t <= tt /\
         y IN mfd_cball (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt) x (r / &2)}
    UNION
    UNIONS {(if 1 <= k /\ T0 <= hs_time hs k /\ hs_time hs k < tt
             then {y | hs_time hs k - de <= t /\ t <= hs_time hs k + de /\
                       y IN topspace(hs_top hs k) DIFF
                            p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40)}
             else {}) | k | k <= hs_count hs}
    UNION
    UNIONS {{y | hs_time hs k + de <= t /\ t <= hs_time hs (k + 1) - de /\
                 y IN topspace(hs_top hs k)} | k | k <= hs_count hs}`;;

let P3N_KSET_COMPACT = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) tt x r T0 taup de.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     tt < rfs_horizon hs /\ &0 < r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     &0 <= taup /\ &0 < de /\ taup + de < r pow 2 /\
     (!k. k <= hs_count hs ==> &3 * de <= hs_time hs (k + 1) - hs_time hs k) /\
     (!t. T0 <= t /\ t < rfs_horizon hs ==> dl t <= &1 / &46)
     ==> p3_st_compact hs (p3n_kset (md,g0,A0) (rp,dl,hf) hs tt x r T0 taup de)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3n_kset (md,g0,A0) (rp,dl,hf) (hs:(A)rfs_history) tt x r T0 taup de =
    \t. (\t. {y | tt - taup <= t /\ t <= tt /\
                  y IN mfd_cball (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                                 x (r / &2)}) t UNION
        (\t. UNIONS {(\k t. if 1 <= k /\ T0 <= hs_time hs k /\ hs_time hs k < tt
                            then {y | hs_time hs k - de <= t /\ t <= hs_time hs k + de /\
                                      y IN topspace(hs_top hs k) DIFF
                                           p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k
                                                      (A0 + &40)}
                            else {}) k t | k | k <= hs_count hs} UNION
                     UNIONS {(\k t. {y | hs_time hs k + de <= t /\
                                         t <= hs_time hs (k + 1) - de /\
                                         y IN topspace(hs_top hs k)}) k t |
                             k | k <= hs_count hs}) t`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3n_kset]; ALL_TAC] THEN
  MATCH_MP_TAC P3N_STC_UNION THEN CONJ_TAC THENL
   [(* the parabolic piece *)
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3N_PXPIECE THEN EXISTS_TAC `de / &2` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P3N_STC_UNION THEN CONJ_TAC THENL
   [(* the event pieces *)
    MATCH_MP_TAC P3N_STC_UNIONS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    ASM_CASES_TAC `1 <= k /\ T0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < tt` THEN
    ASM_REWRITE_TAC[P3N_STC_EMPTY; ETA_AX] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P3N_EVPIECE THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `de / &2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `de:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `de:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the middle pieces *)
  MATCH_MP_TAC P3N_STC_UNIONS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC P3N_MIDPIECE THEN EXISTS_TAC `de / &2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `de:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.21: every point of a curve with the facts of                    *)
(* Lemma 16.15 lies in p3n_kset at its time: near tt in the parabolic      *)
(* piece (16.15(1)); just after an event k in [T0,tt) in the event piece   *)
(* (16.15(2)); just before an event in [T0,tt - taup] in the event piece    *)
(* (P3N_END_COVER2); otherwise in the middle piece of its slab.            *)
(* ========================================================================= *)

let P3N_IN_UNIONS_GSPEC = prove
 (`!(f:num->A->bool) P x. x IN UNIONS {f k | k | P k} <=> ?k. P k /\ x IN f k`,
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let P3N_KSET_COVER = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) tt x r T0 L0 taup de (r0:num->real)
    (gamma:real->A) tau0 tau.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_std_initial g0 A0 /\
     &0 < T0 /\ T0 < tt /\ tt < rfs_horizon hs /\ &0 < taup /\ &0 < L0 /\
     &0 < de /\ de <= taup /\ &2 * de <= T0 /\
     (!t. T0 <= t /\ t < rfs_horizon hs ==> dl t <= &1 / &46) /\
     (!k. k <= hs_count hs ==> &3 * de <= hs_time hs (k + 1) - hs_time hs k) /\
     (!k. k <= hs_count hs /\ hs_time hs k < T0 ==> de <= T0 - hs_time hs k) /\
     (!k. k <= hs_count hs /\ tt - taup < hs_time hs k
          ==> de <= hs_time hs k - (tt - taup)) /\
     (!k. 1 <= k /\ k <= hs_count hs /\ T0 <= hs_time hs k /\ hs_time hs k < tt
          ==> de <= p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\ &0 < r0 k /\
              de <= min (r0 k pow 4 / (&1024 * L0 pow 2)) (r0 k pow 2 / &8) /\
              (!p. p IN topspace(hs_top hs k) DIFF
                        p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)
                   ==> rfs_parabolic_exists (rfs_view hs) (hs_time hs k) p (r0 k) (r0 k pow 2) /\
                       (!s y. hs_time hs k - r0 k pow 2 < s /\ s <= hs_time hs k /\
                              y IN rfs_vball (rfs_view hs) (hs_time hs k) p (r0 k)
                              ==> p3_vrm (rfs_view hs) s y <= inv(r0 k pow 2)) /\
                       rfs_vball (rfs_view hs) (hs_time hs k) p (r0 k) SUBSET
                       topspace(hs_top hs k) DIFF
                       p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40))) /\
     &0 < tau0 /\ tau0 <= tt - T0 /\ rfs_st_curve hs tt gamma (&0) tau0 /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\
     (!tau. &0 <= tau /\ tau <= min taup tau0
            ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)) /\
     (!k j Phi xi tp.
        1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
        T0 <= hs_time hs k /\ hs_time hs k < tt /\
        p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k j Phi xi /\
        hs_time hs k <= tp /\
        tp <= hs_time hs k + p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
        (!s. hs_time hs k <= s /\ s <= tp
             ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET topspace(rfs_top_at hs s))
        ==> !tau. &0 <= tau /\ tau <= tau0 /\ hs_time hs k <= tt - tau /\ tt - tau <= tp
                  ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50})) /\
     &0 < tau /\ tau <= tau0
     ==> gamma tau IN p3n_kset (md,g0,A0) (rp,dl,hf) hs tt x r T0 taup de (tt - tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p3n_kset; IN_UNION; P3N_IN_UNIONS_GSPEC] THEN
  ASM_CASES_TAC `tt - taup <= tt - tau` THENL
   [(* the parabolic piece *)
    DISJ1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `r / &2`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the slab of the time *)
  SUBGOAL_THEN `&0 <= tt - tau /\ tt - tau < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - tau`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN topspace(hs_top hs k)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_st_curve (hs:(A)rfs_history) tt (gamma:real->A) (&0) tau0` THEN
    REWRITE_TAC[rfs_st_curve] THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN SIMP_TAC[rfs_history_ok]; ALL_TAC] THEN
  ASM_CASES_TAC `tt - tau < hs_time (hs:(A)rfs_history) k + de` THENL
   [(* just after the event k *)
    SUBGOAL_THEN `1 <= k /\ T0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < tt`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_CASES_TAC `k = 0` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
        UNDISCH_TAC `tt - tau < hs_time (hs:(A)rfs_history) k + de` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `T0 - hs_time (hs:(A)rfs_history) k`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_parabolic_exists" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A) tau IN topspace(hs_top hs k) DIFF
                  p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k (A0 + &50)`
    MP_TAC THENL
     [MATCH_MP_TAC P3N_START_COVER THEN
      MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `tt:real`; `tau0:real`; `T0:real`; `de:real`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `&3 * de`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                   `hs:(A)rfs_history`; `k:num`] P3N_END_SETS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `hs_time (hs:(A)rfs_history) (k + 1) - de < tt - tau` THENL
   [(* just before the event k + 1 *)
    SUBGOAL_THEN `k + 1 <= hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `k = hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `hs_time (hs:(A)rfs_history) (k + 1) - de < tt - tau` THEN
      UNDISCH_TAC `tt < rfs_horizon (hs:(A)rfs_history)` THEN
      ASM_REWRITE_TAC[rfs_horizon] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k + 1) <= tt - taup` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `tt - taup`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= k + 1 /\ T0 <= hs_time (hs:(A)rfs_history) (k + 1) /\
                  hs_time hs (k + 1) < tt` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `k + 1` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_parabolic_exists" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P3N_END_COVER2 THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `tt:real`; `tau0:real`; `T0:real`; `L0:real`;
                          `(r0:num->real) (k + 1)`; `de:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the middle piece of the slab k *)
  DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.21: for a fixed history with the facts of Lemma                 *)
(* 16.15 for a class Q of curves from x, a compact space-time set K        *)
(* containing all of them: the radii r0 k of P3N_END_DATA, the width de    *)
(* below all the finitely many constraints (P3N_FINITE_MIN), K = p3n_kset. *)
(* ========================================================================= *)

let P3N_1621_K = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) x tt r T0 L0 taup
    (Q:real->(real->A)->bool).
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_hfun C hf /\ p3_std_initial g0 A0 /\
     &0 < T0 /\ T0 < tt /\ tt < rfs_horizon hs /\
     &0 < r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     &0 < taup /\ taup < r pow 2 /\ &0 < L0 /\
     (!t. T0 <= t /\ t < rfs_horizon hs ==> dl t <= &1 / &46) /\
     (!tau0 gamma.
        Q tau0 gamma
        ==> &0 < tau0 /\ tau0 <= tt - T0 /\ rfs_st_curve hs tt gamma (&0) tau0 /\
            (\tau. sqrt tau *
                   (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau))
                                         (rfs_metric_at hs (tt - tau)) (gamma tau)) +
                    mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                              gamma (&0) tau0 tau pow 2))
            real_integrable_on real_interval[&0,tau0] /\
            p3_Lplus hs tt gamma tau0 < L0 /\
            (!tau. &0 <= tau /\ tau <= min taup tau0
                   ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)) /\
            (!k j Phi xi tp.
               1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
               T0 <= hs_time hs k /\ hs_time hs k < tt /\
               p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k j Phi xi /\
               hs_time hs k <= tp /\
               tp <= hs_time hs k + p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
               (!s. hs_time hs k <= s /\ s <= tp
                    ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET
                        topspace(rfs_top_at hs s))
               ==> !tau. &0 <= tau /\ tau <= tau0 /\ hs_time hs k <= tt - tau /\
                         tt - tau <= tp
                         ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50})))
     ==> ?K. p3_st_compact hs K /\
             !tau0 gamma. Q tau0 gamma
                          ==> !tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K (tt - tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the radii of the relevant events *)
  SUBGOAL_THEN
   `!k. ?r:real.
      1 <= k /\ k <= hs_count hs /\ T0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < tt
      ==> &0 < r /\
          (!p. p IN topspace(hs_top hs k) DIFF
                    p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &50)
               ==> rfs_parabolic_exists (rfs_view hs) (hs_time hs k) p r (r pow 2) /\
                   (!s y. hs_time hs k - r pow 2 < s /\ s <= hs_time hs k /\
                          y IN rfs_vball (rfs_view hs) (hs_time hs k) p r
                          ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
                   rfs_vball (rfs_view hs) (hs_time hs k) p r SUBSET
                   topspace(hs_top hs k) DIFF
                   p3n_capreg (md,g0,A0) (dl,p3_hscale hf rp dl) hs k (A0 + &40))`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `1 <= k /\ k <= hs_count (hs:(A)rfs_history) /\ T0 <= hs_time hs k /\
                   hs_time hs k < tt` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                   `hs:(A)rfs_history`; `k:num`] P3N_END_DATA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `r0:num->real`)] THEN
  (* the scales are positive *)
  SUBGOAL_THEN `!k. k <= hs_count (hs:(A)rfs_history)
                    ==> &0 < p3_hscale hf rp dl (hs_time hs k) /\
                        hs_time hs k < hs_time hs (k + 1)`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                     `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                     `hs:(A)rfs_history`; `k:num`] P3N_STRUCT_BASIC) THEN
      ASM_SIMP_TAC[];
      ACCEPT_TAC(C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`)
                   (SPEC `k:num` (CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfs_history_ok]
                     (ASSUME `rfs_history_ok (hs:(A)rfs_history)`))))))];
    ALL_TAC] THEN
  (* the width *)
  MP_TAC(ISPECL [`hs_count (hs:(A)rfs_history)`;
                 `\k. min (min ((hs_time (hs:(A)rfs_history) (k + 1) - hs_time hs k) / &3)
                               (if hs_time hs k < T0 then T0 - hs_time hs k else &1))
                          (min (if tt - taup < hs_time hs k then hs_time hs k - (tt - taup)
                                else &1)
                               (if 1 <= k /\ T0 <= hs_time hs k /\ hs_time hs k < tt
                                then min (p3_hscale hf rp dl (hs_time hs k) pow 2 / &2)
                                         (min ((r0:num->real) k pow 4 / (&1024 * L0 pow 2))
                                              (r0 k pow 2 / &8))
                                else &1))`] P3N_FINITE_MIN) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "pos" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN CONJ_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC) THEN TRY(COND_CASES_TAC THEN ASM_REAL_ARITH_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_01] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_parabolic_exists" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_ARITH `&0 < &1024 /\ &0 < &8 /\ &0 < &2`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d0"))) THEN
  ABBREV_TAC `de = min d0 (min taup (min (T0 / &2) ((r pow 2 - taup) / &2)))` THEN
  SUBGOAL_THEN `&0 < de /\ de <= d0 /\ de <= taup /\ &2 * de <= T0 /\ taup + de < r pow 2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "de" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k <= hs_count (hs:(A)rfs_history)
        ==> &3 * de <= hs_time hs (k + 1) - hs_time hs k /\
            (hs_time hs k < T0 ==> de <= T0 - hs_time hs k) /\
            (tt - taup < hs_time hs k ==> de <= hs_time hs k - (tt - taup)) /\
            (1 <= k /\ T0 <= hs_time hs k /\ hs_time hs k < tt
             ==> de <= p3_hscale hf rp dl (hs_time hs k) pow 2 / &2 /\
                 de <= min ((r0:num->real) k pow 4 / (&1024 * L0 pow 2)) (r0 k pow 2 / &8))`
  (LABEL_TAC "dek") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "d0" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    BETA_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `p3n_kset (md,g0,A0) (rp,dl,hf) (hs:(A)rfs_history) tt x r T0 taup de` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3N_KSET_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "dek" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau0:real`; `gamma:real->A`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `gamma:real->A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `Q:real->(real->A)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC P3N_KSET_COVER THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `L0:real`; `r0:num->real`; `tau0:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "dek" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "dek" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "dek" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    USE_THEN "dek" (MP_TAC o C MP (ASSUME `k <= hs_count (hs:(A)rfs_history)`) o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_parabolic_exists" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Prop 16.21: the headline.  MT Prop 16.21(3) (p. 385) with the second      *)
(* scale rr (0 < rr <= r', rr <= r) from Lemma 16.15 in the same form.       *)
(* Constants: eps1621 = eps1615; L0 = Lb + 6 T sqrt T + 1 with T = T(i+1)    *)
(* (so that L+ < L0 for every admissible curve with L <= Lb, by              *)
(* P3N_LPLUS_FROM_L); dlt0 and taup from 16.15 at (r',rr,L0); dlt = min dlt0 *)
(* (1/100); the parabolic width min taup (rr^2/2) < r^2; then P3N_1621_K     *)
(* with T0 = T(i-1).                                                         *)
(* ========================================================================= *)

let P3N_P16_SETTING_MONO = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt dlt' rs' ks' dd (hs:(A)rfs_history).
     p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\ dlt <= dlt'
     ==> p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt' (rs',ks',dd) hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC);;

let P3N_PROP_16_21_FIX = prove
 (`!u:A->bool. P3_LEMMA_16_15_STATEMENT u
     ==> P3_PROP_16_21_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_21_STATEMENT; P3_LEMMA_16_15_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1615:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1615"))) THEN
  EXISTS_TAC `eps1615:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "p1615" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                    `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "q1615")] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`;
                       `rr:real`; `Lb:real`] THEN
  STRIP_TAC THEN
  (* the bound L0 for L+ *)
  SUBGOAL_THEN `&0 < p3_T (SUC i) /\ &0 < p3_T (i - 1) /\ p3_T (i - 1) < p3_T i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3_T] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2 /\ &0 < &32`];
      SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2 /\ &0 < &32`];
      SIMP_TAC[REAL_LT_DIV2_EQ; REAL_ARITH `&0 < &32`] THEN
      MATCH_MP_TAC REAL_POW_MONO_LT THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3_T (SUC i) * sqrt(p3_T (SUC i))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L0 = Lb + &6 * p3_T (SUC i) * sqrt(p3_T (SUC i)) + &1` THEN
  SUBGOAL_THEN `&0 < L0` ASSUME_TAC THENL [EXPAND_TAC "L0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Lemma 16.15 at (r',L0) *)
  USE_THEN "q1615" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                                    `r':real`; `rr:real`; `L0:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt0:real` (X_CHOOSE_THEN `taup:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1615"))))) THEN
  EXISTS_TAC `min dlt0 (&1 / &100)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `x:A`; `tt:real`; `r:real`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* the setting *)
  SUBGOAL_THEN `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt0 (rs',ks',dd)
                               (hs:(A)rfs_history)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_P16_SETTING_MONO THEN EXISTS_TAC `min dlt0 (&1 / &100)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history) /\
                rfs_horizon hs <= p3_T (SUC i)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt0 (rs',ks',dd)
                                (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rr pow 2 /\ rr pow 2 <= r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the bound on the surgery parameter after T(i-1) *)
  SUBGOAL_THEN `!t. p3_T (i - 1) <= t /\ t < rfs_horizon (hs:(A)rfs_history)
                    ==> p3_stepf dd t <= &1 / &46` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                   `ds:num->real`; `r':real`; `min dlt0 (&1 / &100)`; `rs':num->real`;
                   `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `t:real`]
                  P3N_1615_PARAMS) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the curves *)
  SUBGOAL_THEN
   `!tau0 (gamma:real->A).
      &0 < tau0 /\ tau0 <= tt - p3_T (i - 1) /\ rfs_L_adm hs tt x tau0 gamma /\
      rfs_L_length hs tt gamma tau0 <= Lb
      ==> rfs_st_curve hs tt gamma (&0) tau0 /\
          (\tau. sqrt tau *
                 (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau))
                                       (rfs_metric_at hs (tt - tau)) (gamma tau)) +
                  mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                            gamma (&0) tau0 tau pow 2))
          real_integrable_on real_interval[&0,tau0] /\
          p3_Lplus hs tt gamma tau0 < L0 /\
          (!tau. &0 <= tau /\ tau <= min taup tau0
                 ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)) /\
          (!k j Phi xi tp.
             1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
             p3_T (i - 1) <= hs_time hs k /\ hs_time hs k < tt /\
             p3_cap_param (md,g0,A0) (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd))
                          hs k j Phi xi /\
             hs_time hs k <= tp /\
             tp <= hs_time hs k +
                   p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 / &2 /\
             (!s. hs_time hs k <= s /\ s <= tp
                  ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET
                      topspace(rfs_top_at hs s))
             ==> !tau. &0 <= tau /\ tau <= tau0 /\
                       hs_time hs k <= tt - tau /\ tt - tau <= tp
                       ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50}))`
  (LABEL_TAC "curves") THENL
   [MAP_EVERY X_GEN_TAC [`tau0:real`; `gamma:real->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tau0:real`; `gamma:real->A`]
                  P3N_LPLUS_FROM_L) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `rfs_st_curve (hs:(A)rfs_history) tt gamma (&0) tau0 /\ (gamma:real->A) (&0) = x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_L_adm (hs:(A)rfs_history) tt x tau0 gamma` THEN
      REWRITE_TAC[rfs_L_adm] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `tau0 * sqrt tau0 <= p3_T (SUC i) * sqrt(p3_T (SUC i))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `p3_Lplus (hs:(A)rfs_history) tt gamma tau0 < L0` ASSUME_TAC THENL
     [EXPAND_TAC "L0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "c1615" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                                      `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`;
                                      `tau0:real`; `gamma:real->A`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the compact set *)
  MP_TAC(BETA_RULE(ISPECL
   [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`; `g0:real^3->real^3^3`;
    `A0:real`; `p3_stepf rs'`; `p3_stepf dd`; `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`;
    `p3_T (i - 1)`; `L0:real`; `min taup (rr pow 2 / &2)`;
    `\tau0 (gamma:real->A). &0 < tau0 /\ tau0 <= tt - p3_T (i - 1) /\
                           rfs_L_adm (hs:(A)rfs_history) tt x tau0 gamma /\
                           rfs_L_length hs tt gamma tau0 <= Lb`] P3N_1621_K)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`tau0:real`; `gamma:real->A`] THEN STRIP_TAC THEN
    USE_THEN "curves" (MP_TAC o SPECL [`tau0:real`; `gamma:real->A`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `r / &2`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* The route theorem for Prop 16.21 (the statement of Lemma 16.15 in the     *)
(* route equals the hypothesis of P3N_PROP_16_21_FIX).                       *)
(* ========================================================================= *)

let P3N_PROP_16_21_ROUTE = prove
 (`!u:A->bool. P3_PROP_16_21_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_21_ROUTE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_PROP_16_21_FIX) THEN
  REWRITE_TAC[GSYM P3_LEMMA_16_15_STATEMENT] THEN MESON_TAC[]);;

