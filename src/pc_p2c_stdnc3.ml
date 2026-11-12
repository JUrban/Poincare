(* ========================================================================= *)
(* Unit pc_p2c_stdnc3 (Part 2C): large times and the main theorem            *)
(* STNC_STD_NONCOLL |- P2C_STD_NONCOLL_STATEMENT.  For t0 < t < te, G on     *)
(* [0,t] is a complete flow of bounded curvature (p2a_cbflow); FL4 (MT Thm   *)
(* 7.10) gives q with l(q, t - t0) <= 3/2; FL2 (MT Lemma 7.2) a minimizer to *)
(* (q, t - t0); a chart curve psi_q(u z) over the forward times [t0/2, t0]   *)
(* glued to it bounds l by l0 on the chart image B of q at backward time t - *)
(* t0/2, B has volume >= V0 at time t0/2, and FL6 (MT Thm 8.1 for complete   *)
(* flows) gives the volume bound at (x,t).  FL2, FL4 and FL6 are statement   *)
(* constants of pc_p2a_fldefs.                                               *)
(* ========================================================================= *)

needs "src/pc_p2c_stdnc2.ml";;
needs "src/pc_p2a_flw3.ml";;
needs "src/pc_p2c_fview.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A partial standard flow restricted to [0,t], t < te, is a                *)
(* complete flow of bounded curvature on a connected manifold.              *)
(* ------------------------------------------------------------------------- *)

let STNC_RESTRICT_CBFLOW = prove
 (`!g0 te (G:real->real^3->real^3^3) t.
     p3_partial_std g0 te G /\ &0 < t /\ t < te
     ==> p2a_cbflow (euclidean,open_set_atlas (:real^3)) (&0) t G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_partial_std] THEN STRIP_TAC THEN
  REWRITE_TAC[P2AF_CBFLOW_3; P2C_EUCLID_FACTS] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `te:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`&0`; `te:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[ricci_flow_from];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `K:real` THEN ASM_SIMP_TAC[]]);;

let STNC_VIEW_FACTS = prove
 (`!te (G:real->real^3->real^3^3) t x r.
     &0 <= t /\ t < te
     ==> rfs_vtop (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G) t =
         euclidean /\
         rfs_vatlas (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
           t = open_set_atlas (:real^3) /\
         rfs_vmetric (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
           t = G t /\
         rfs_vball (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
           t x r = mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vball; IN_ELIM_THM]);;

let STNC_NONCOLL_OUTSIDE = prove
 (`!te (G:real->real^3->real^3^3) kappa r0 x t.
     ~(&0 <= t /\ t < te)
     ==> p3_noncoll_at (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                      {s | &0 <= s /\ s < te} G) kappa r0 x t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p3_noncoll_at; rfs_parabolic_exists; rfs_flow_view; rfs_persists] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas"))
        (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < r ==> t - r < t /\ t <= t`) THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[smooth_manifold_atlas; open_set_atlas; IN_SING; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o SPECL [`(:real^3)`; `\x:real^3. x`] o CONJUNCT1 o CONJUNCT1) THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; SUBSET_EMPTY; UNIV_NOT_EMPTY]);;


(* ------------------------------------------------------------------------- *)
(* The chart curve sol(s) = psi_q(((s - s1)/(s2 - s1)) z) of                *)
(* the competitor, |z| < 1/4: its velocity Dpsi(u z)(z/(s2 - s1)) and its   *)
(* C^1 regularity on (s1 - (s2 - s1), s2 + (s2 - s1)).                      *)
(* ------------------------------------------------------------------------- *)

let STNC_SOL_ARG = prove
 (`!(z:real^3) s1 s2 s.
     z IN ball(vec 0,&1 / &4) /\ s1 < s2 /\ s1 - (s2 - s1) < s /\ s < s2 + (s2 - s1)
     ==> ((s - s1) / (s2 - s1)) % z IN ball(vec 0,&1 / &2)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1 / &4)` THEN
  REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((s - s1) / (s2 - s1)) < &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * norm(z:real^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC]);;

let STNC_SOL_VD = prove
 (`!g0 A0 (q:real^3) z s1 s2 s.
     p3_std_initial g0 A0 /\ z IN ball(vec 0,&1 / &4) /\ s1 < s2 /\
     s1 - (s2 - s1) < s /\ s < s2 + (s2 - s1)
     ==> ((\v. stnc_psi g0 A0 q (((drop v - s1) / (s2 - s1)) % z)) has_vector_derivative
          frechet_derivative (stnc_psi g0 A0 q) (at (((s - s1) / (s2 - s1)) % z))
            (inv(s2 - s1) % z))
         (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((s - s1) / (s2 - s1)) % (z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC STNC_SOL_ARG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(stnc_psi g0 A0 (q:real^3)) differentiable (at (((s - s1) / (s2 - s1)) % z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s2 - s1 = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\v. stnc_psi g0 A0 q (((drop v - s1) / (s2 - s1)) % z)) =
    stnc_psi g0 A0 q o
    (\v:real^1. drop v % (inv(s2 - s1) % z) + (--(s1 / (s2 - s1))) % (z:real^3)) /\
    (\h:real^1. drop h % frechet_derivative (stnc_psi g0 A0 q)
                           (at (((s - s1) / (s2 - s1)) % z)) (inv(s2 - s1) % z)) =
    frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at (((s - s1) / (s2 - s1)) % z)) o
    (\h. drop h % (inv(s2 - s1) % z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^1` THENL
     [AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `~(s2 - s1 = &0)` THEN CONV_TAC REAL_FIELD;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^1. drop x % inv(s2 - s1) % (z:real^3)) =
                  (\x. drop x % inv(s2 - s1) % z + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
    BETA_TAC THEN
    SUBGOAL_THEN
     `drop(lift s) % (inv(s2 - s1) % z) + --(s1 / (s2 - s1)) % z =
      ((s - s1) / (s2 - s1)) % (z:real^3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_DROP; VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `~(s2 - s1 = &0)` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]]);;

let STNC_SOL_C1 = prove
 (`!g0 A0 (q:real^3) z s1 s2 s.
     p3_std_initial g0 A0 /\ z IN ball(vec 0,&1 / &4) /\ s1 < s2 /\ s1 <= s /\ s <= s2
     ==> (\v. stnc_psi g0 A0 q (((drop v - s1) / (s2 - s1)) % z)) differentiable
           (at (lift s)) /\
         (\v. vector_derivative (\v. stnc_psi g0 A0 q (((drop v - s1) / (s2 - s1)) % z))
                (at v)) continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2AW_VDERIV_CONT_OPEN THEN
  EXISTS_TAC `\v:real^1. frechet_derivative (stnc_psi g0 A0 (q:real^3))
                           (at (((drop v - s1) / (s2 - s1)) % z)) (inv(s2 - s1) % z)` THEN
  EXISTS_TAC `interval(lift(s1 - (s2 - s1)),lift(s2 + (s2 - s1)))` THEN
  REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `v:real` THEN
    STRIP_TAC THEN MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`;
                                  `s1:real`; `s2:real`; `v:real`] STNC_SOL_VD) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:real^1. frechet_derivative (stnc_psi g0 A0 (q:real^3))
                  (at (((drop v - s1) / (s2 - s1)) % z)) (inv(s2 - s1) % z)) =
    (\y. frechet_derivative (stnc_psi g0 A0 q) (at y) (inv(s2 - s1) % z)) o
    (\v:real^1. ((drop v - s1) / (s2 - s1)) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(\v:real^1. (drop v - s1) % inv(s2 - s1) % (z:real^3)) =
                  (\v. drop v % inv(s2 - s1) % z - s1 % inv(s2 - s1) % z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RDISTRIB]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[CONTINUOUS_CONST; o_DEF; LIFT_DROP] THEN
    REWRITE_TAC[ETA_AX; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
  EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
  SIMP_TAC[INTERIOR_OPEN; OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH];
    MATCH_MP_TAC STNC_SOL_ARG THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The competitor.  A minimizer gamma' to (sol(s1), s1^2)                   *)
(* glued with the identity-chart curve sol on [s1,s2] (P2A_CHART_CURVE_SEG, *)
(* P2A_SEG_GLUE) bounds the reduced distance at (sol(s2), s2^2)             *)
(* (P2AW_FLOW_LX_LE), the pattern of P2AW_FLOW_CMP_L.                        *)
(* ------------------------------------------------------------------------- *)

let STNC_COMPETITOR = prove
 (`!te (G:real->real^3->real^3^3) g0 t (x:real^3) m s1 s2 (gamma':real->real^3)
    (sol:real^1->real^3).
     p3_partial_std g0 te G /\ &0 < t /\ t < te /\
     (!s y. &0 <= s /\ s <= t ==> m <= mfd_scalar (open_set_atlas (:real^3)) (G s) y) /\
     p2a_min (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
             t x (s1 pow 2) gamma' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 < t /\ gamma'(s1 pow 2) = sol(lift s1) /\
     (!s. s1 <= s /\ s <= s2
          ==> sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> p2a_Lx (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
                t x (s2 pow 2) (sol(lift s2)) <=
         p2a_L_length (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
                      t gamma' (s1 pow 2) +
         p2a_cL (p2a_rlocal (p2a_flow_view (euclidean,open_set_atlas (:real^3))
                                           (real_interval[&0,t]) G)
                            (:real^3) t ((:real^3),(\y:real^3. y)))
                t sol s1 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_cbflow (euclidean,open_set_atlas (:real^3)) (&0) t (G:real->real^3->real^3^3)`
  ASSUME_TAC THENL [MATCH_MP_TAC STNC_RESTRICT_CBFLOW THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (euclidean,open_set_atlas (:real^3))
                              (real_interval[&0,t]) (G:real->real^3->real^3^3)) (:real^3) (&0) t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; GSYM OPEN_IN; OPEN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t])
                    (G:real->real^3->real^3^3)` THEN
  SUBGOAL_THEN `((:real^3),(\y:real^3. y)) IN p2a_vatlas (V:(real->(real^3)topology)#
                  (real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3)) t`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt t /\ sqrt t pow 2 = t /\ s2 < sqrt t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
                    (real->real^3->real^3^3)`;
                 `t:real`; `(:real^3)`; `&0`; `t:real`; `(:real^3)`; `\y:real^3. y`;
                 `sol:real^1->real^3`; `s1:real`; `s2:real`; `s1 / &2`;
                 `(s2 + sqrt t) / &2`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_ID; INTER_UNIV; IN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 < sqrt t pow 2` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[INTER_UNIV] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `!y:real^3. chart_inv ((:real^3),(\y:real^3. y)) y = y` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GRGE_OPEN_SET_CHART_INV THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `!y:real^3. chart_inv ((:real^3),(\y:real^3. y)) y = y`]) THEN
  SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
                    (real->real^3->real^3^3)`;
                 `t:real`; `x:real^3`; `\tau. (sol:real^1->real^3)(lift(sqrt tau))`;
                 `gamma':real->real^3`;
                 `\tau. if tau <= s1 pow 2 then (gamma':real->real^3) tau
                        else (sol:real^1->real^3)(lift(sqrt tau))`;
                 `s2 pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[p2a_min];
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `t:real`;
                 `G:real->real^3->real^3^3`; `m:real`; `x:real^3`; `s2 pow 2`;
                 `\tau. if tau <= s1 pow 2 then (gamma':real->real^3) tau
                        else (sol:real^1->real^3)(lift(sqrt tau))`]
                P2AW_FLOW_LX_LE) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
                  ALL_TAC] THEN
  SUBGOAL_THEN `~(s2 pow 2 <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> l <= x ==> l <= y`) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The L-Lagrangian along the competitor chart curve: in the                *)
(* identity chart the region metric is G itself and the chart scalar is the  *)
(* scalar curvature (P2AW_FLOW_RLOCAL_ID); |llag| <= Kb gives cL <= Kb      *)
(* (s2 - s1) (P2A_CL_ABS_BOUND, integrable by P2A_LLAG_CURVE_CONTINUOUS).   *)
(* ------------------------------------------------------------------------- *)

let STNC_CL_LE = prove
 (`!(Gt:real->real^3->real^3^3) tt (sol:real^1->real^3) s1 s2 Kb.
     s1 <= s2 /\
     (\s. p2a_llag Gt tt s (sol(lift s)) (vector_derivative sol (at (lift s))))
       real_integrable_on real_interval[s1,s2] /\
     (!s. s1 <= s /\ s <= s2
          ==> abs(p2a_llag Gt tt s (sol(lift s)) (vector_derivative sol (at (lift s)))) <= Kb)
     ==> p2a_cL Gt tt sol s1 s2 <= Kb * (s2 - s1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gt:real->real^3->real^3^3`; `tt:real`; `sol:real^1->real^3`;
                 `\v:real^1. vector_derivative (sol:real^1->real^3) (at v)`; `s1:real`;
                 `s2:real`; `Kb:real`; `{}:real->bool`] P2A_CL_ABS_BOUND) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN REAL_ARITH_TAC);;

let STNC_RLOCAL_ID = prove
 (`!te (G:real->real^3->real^3^3) g0 t s y.
     p3_partial_std g0 te G /\ &0 < t /\ t < te /\ &0 < s /\ s <= t
     ==> p2a_rlocal (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
                    (:real^3) t ((:real^3),(\y:real^3. y)) s y = G s y /\
         lscalar (p2a_rlocal (p2a_flow_view (euclidean,open_set_atlas (:real^3))
                                             (real_interval[&0,t]) G)
                             (:real^3) t ((:real^3),(\y:real^3. y)) s) y =
         mfd_scalar (open_set_atlas (:real^3)) (G s) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `t:real`;
                 `G:real->real^3->real^3^3`; `(:real^3)`; `\y:real^3. y`; `s:real`; `y:real^3`]
                P2AW_FLOW_RLOCAL_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC STNC_RESTRICT_CBFLOW THEN ASM_MESON_TAC[];
      REWRITE_TAC[open_set_atlas; IN_SING]];
    ALL_TAC] THEN
  SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; OPEN_UNIV; IN_UNIV]);;

let STNC_LLAG_BOUND = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0 L lam Lam K0 t (q:real^3) z s1 s2 s.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t /\ t < te /\
     (!s y v. &0 <= s /\ s <= t0 ==> v dot (G s y ** v) <= L * (v dot (g0 y ** v))) /\
     &0 <= L /\ &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     (!s y. &0 <= s /\ s <= t0 ==> mfd_rm_norm (open_set_atlas (:real^3)) (G s) y <= K0) /\
     z IN ball(vec 0,&1 / &4) /\ &0 < s1 /\ s1 < s2 /\ s1 <= s /\ s <= s2 /\
     &0 <= t - s2 pow 2 /\ t - s1 pow 2 <= t0 /\ s2 pow 2 < t
     ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (euclidean,open_set_atlas (:real^3))
                                                 (real_interval[&0,t]) G)
                                  (:real^3) t ((:real^3),(\y:real^3. y)))
                      t s (stnc_psi g0 A0 q (((s - s1) / (s2 - s1)) % z))
                      (vector_derivative (\v. stnc_psi g0 A0 q (((drop v - s1) / (s2 - s1)) % z))
                                         (at (lift s))))
         <= L * Lam / (&16 * (s2 - s1) pow 2) + &12 * t * K0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "eq")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "qf") (CONJUNCTS_THEN2 (LABEL_TAC "rm")
    STRIP_ASSUME_TAC)))))))))) THEN
  ABBREV_TAC `u = (s - s1) / (s2 - s1)` THEN
  SUBGOAL_THEN `u % (z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC STNC_SOL_ARG THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`; `s1:real`;
                 `s2:real`; `s:real`] STNC_SOL_VD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
  ABBREV_TAC `A = frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at (u % z))
                    (inv(s2 - s1) % z)` THEN
  ABBREV_TAC `y = stnc_psi g0 A0 (q:real^3) (u % z)` THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 <= s2 pow 2 /\ s1 pow 2 <= s pow 2 /\ &0 <= s pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`te:real`; `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`; `t:real`;
                 `t - s pow 2`; `y:real^3`] STNC_RLOCAL_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC(REAL_ARITH
      `&0 <= x ==> t - x <= t`) THEN REWRITE_TAC[REAL_LE_POW_2]] THEN
    MATCH_MP_TAC(REAL_ARITH `x < t ==> &0 < t - x`) THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[p2a_llag] THEN
  SUBGOAL_THEN `&0 <= t - s pow 2 /\ t - s pow 2 <= t0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) (t - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= A dot ((G:real->real^3->real^3^3) (t - s pow 2) y ** A) /\
    A dot (G (t - s pow 2) y ** A) <= L * Lam / (&16 * (s2 - s1) pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PV411_QPOS THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`] THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * (A dot ((g0:real^3->real^3^3) y ** A))` THEN CONJ_TAC THENL
     [USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "qf" (MP_TAC o SPECL [`q:real^3`; `u % z:real^3`; `inv(s2 - s1) % z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A"; "y"] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * Lam * ((inv(s2 - s1) % z) dot (inv(s2 - s1) % (z:real^3)))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `(z:real^3) dot z <= &1 / &16` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1 / &4)` THEN
      REWRITE_TAC[IN_BALL_0; GSYM NORM_POW_2] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= (&1 / &4) pow 2 ==> x <= &1 / &16`) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= L * Lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L * Lam * inv(s2 - s1) * inv(s2 - s1) * (z dot z) =
                  (L * Lam) * (z dot (z:real^3)) / (s2 - s1) pow 2 /\
                  L * Lam / (&16 * (s2 - s1) pow 2) = (L * Lam) * (&1 / &16) / (s2 - s1) pow 2`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < s2 - s1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3)
                  (t - s pow 2)) y) <= &6 * K0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_rm_norm (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3)
                  (t - s pow 2)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AZ_MFD_SCALAR_ABS THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV];
      MATCH_MP_TAC(REAL_ARITH `x <= k ==> &6 * x <= &6 * k`) THEN
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s pow 2 /\ s pow 2 <= t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&2 * s pow 2 * mfd_scalar (open_set_atlas (:real^3))
                  ((G:real->real^3->real^3^3) (t - s pow 2)) y) <= &12 * t * K0`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC(REAL_ARITH `x * y <= t * (&6 * k) ==> &2 * x * y <= &12 * t * k`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The reduced distance is bounded on the chart image B of the              *)
(* FL4 point q.  With s1 = sqrt(t - t0), s2 = sqrt(t - t0/2):               *)
(*   Lx(s2^2, psi z) <= L(gamma') + cL(sol) <= 3 sqrt te + C               *)
(* and l = Lx / (2 s2) with s2 >= sqrt(t0/2).                                *)
(* ------------------------------------------------------------------------- *)

let STNC_S12_FACTS = prove
 (`!te t0 t. &0 < t0 /\ t0 < t /\ t < te
     ==> &0 < sqrt(t - t0) /\ sqrt(t - t0) < sqrt(t - t0 / &2) /\
         sqrt(t - t0) pow 2 = t - t0 /\ sqrt(t - t0 / &2) pow 2 = t - t0 / &2 /\
         sqrt(t - t0 / &2) pow 2 < t /\ sqrt(t - t0 / &2) <= sqrt te /\
         sqrt(t0 / &2) <= sqrt(t - t0 / &2) /\ &0 < sqrt(t0 / &2) /\ &0 < sqrt te /\
         t0 / (&4 * sqrt te) <= sqrt(t - t0 / &2) - sqrt(t - t0) /\
         sqrt(t - t0 / &2) - sqrt(t - t0) <= sqrt te`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(t - t0) /\ sqrt(t - t0) < sqrt(t - t0 / &2) /\
                sqrt(t - t0) pow 2 = t - t0 /\ sqrt(t - t0 / &2) pow 2 = t - t0 / &2 /\
                sqrt(t - t0 / &2) <= sqrt te /\ sqrt(t - t0) <= sqrt te /\
                sqrt(t0 / &2) <= sqrt(t - t0 / &2) /\ &0 < sqrt(t0 / &2) /\ &0 < sqrt te`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ABBREV_TAC `a = sqrt(t - t0)` THEN ABBREV_TAC `b = sqrt(t - t0 / &2)` THEN
  ABBREV_TAC `c = sqrt te` THEN
  SUBGOAL_THEN `b - a = (t0 / &2) / (b + a)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < b + a` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `b pow 2 = t - t0 / &2` THEN UNDISCH_TAC `a pow 2 = t - t0` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b + a /\ b + a <= &2 * c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &4 * c`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t0 * inv(&4 * c)) * (&2 * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]);;

let STNC_CL_ARITH = prove
 (`!P K0 t te t0 d c.
     &0 <= P /\ &0 <= K0 /\ &0 < t0 /\ &0 < c /\ &0 <= t /\ t <= te /\
     t0 / (&4 * c) <= d /\ d <= c
     ==> (P / (&16 * d pow 2) + &12 * t * K0) * d <= P * c / t0 + &12 * te * K0 * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `t0 / (&4 * c)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &4`];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 <= &4 * c * d` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 / (&4 * c) <= d` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &4`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P / (&16 * d pow 2) + &12 * t * K0) * d = P / (&16 * d) + (&12 * t * K0) * d`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &16 * d`] THEN
    SUBGOAL_THEN `(P * c / t0) * (&16 * d) = P * ((&16 * c * d) / t0)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < t0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[]]);;

let STNC_LX_BALL = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0 L lam Lam K0 (x:real^3) t (q:real^3)
    (gamma':real->real^3) z.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t0 /\ t0 < t /\ t < te /\
     &1 <= L /\
     (!s y v. &0 <= s /\ s <= t0 ==> v dot (G s y ** v) <= L * (v dot (g0 y ** v))) /\
     &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     &0 <= K0 /\
     (!s y. &0 <= s /\ s <= t0 ==> mfd_rm_norm (open_set_atlas (:real^3)) (G s) y <= K0) /\
     p2a_min (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
             t x (t - t0) gamma' /\
     gamma' (t - t0) = q /\
     p2a_lx (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
            t x (t - t0) q <= &3 / &2 /\
     z IN ball(vec 0,&1 / &4)
     ==> p2a_lx (p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t]) G)
                t x (t - t0 / &2) (stnc_psi g0 A0 q z) <=
         (&3 * sqrt te + L * Lam * sqrt te / t0 + &12 * te * K0 * sqrt te) /
         (&2 * sqrt(t0 / &2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qf") (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm") STRIP_ASSUME_TAC)))))))))))) THEN
  MP_TAC(ISPECL [`te:real`; `t0:real`; `t:real`] STNC_S12_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s1 = sqrt(t - t0)` THEN ABBREV_TAC `s2 = sqrt(t - t0 / &2)` THEN STRIP_TAC THEN
  ABBREV_TAC `V = p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t])
                    (G:real->real^3->real^3^3)` THEN
  SUBGOAL_THEN
   `p2a_min (V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
               (real->real^3->real^3^3)) t x (s1 pow 2) gamma' /\
    (gamma':real->real^3) (s1 pow 2) = q /\ p2a_lx V t x (s1 pow 2) q <= &3 / &2`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t - t0 / &2 = s2 pow 2` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s2 /\ &0 < s2 - s1 /\ &0 < t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sol = \v. stnc_psi g0 A0 (q:real^3) (((drop v - s1) / (s2 - s1)) % z)` THEN
  SUBGOAL_THEN `(s2 - s1) * inv(s2 - s1) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift s1) = q /\ sol(lift s2) = stnc_psi g0 A0 q z`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sol" THEN REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN ASM_SIMP_TAC[STNC_PSI_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cbflow (euclidean,open_set_atlas (:real^3)) (&0) t (G:real->real^3->real^3^3)`
  ASSUME_TAC THENL [MATCH_MP_TAC STNC_RESTRICT_CBFLOW THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  SUBGOAL_THEN `!s y. &0 <= s /\ s <= t
                      ==> m <= mfd_scalar (open_set_atlas (:real^3))
                                ((G:real->real^3->real^3^3) s) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma':real->real^3) (s1 pow 2) = sol(lift s1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (sol:real^1->real^3) differentiable (at (lift s)) /\
            (\v. vector_derivative sol (at v)) continuous (at (lift s))`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN MATCH_MP_TAC STNC_SOL_C1 THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`te:real`; `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`; `t:real`;
                 `x:real^3`; `m:real`; `s1:real`; `s2:real`; `gamma':real->real^3`;
                 `sol:real^1->real^3`] STNC_COMPETITOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME
    `p2a_flow_view (euclidean,open_set_atlas (:real^3)) (real_interval[&0,t])
                   (G:real->real^3->real^3^3) = V`]) THEN
  SUBGOAL_THEN
   `p2a_L_length (V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3)) t (gamma':real->real^3) (s1 pow 2) <= &3 * sqrt te`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_L_length (V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3)) t (gamma':real->real^3) (s1 pow 2) =
                  p2a_Lx V t x (s1 pow 2) q` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      SUBGOAL_THEN `q = (gamma':real->real^3) (s1 pow 2)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P2A_MIN_LX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `p2a_lx (V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3)) t x (s1 pow 2) (q:real^3) <= &3 / &2` THEN
    REWRITE_TAC[p2a_lx] THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1` SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->(real^3)topology)#
                    (real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3))
                    (:real^3) t ((:real^3),(\y:real^3. y))` THEN
  SUBGOAL_THEN
   `p2a_cL Gt t (sol:real^1->real^3) s1 s2 <=
    (L * Lam / (&16 * (s2 - s1) pow 2) + &12 * t * K0) * (s2 - s1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC STNC_CL_LE THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`(:real^3)`; `s1 / &2`; `(s2 + sqrt t) / &2`] THEN
      SUBGOAL_THEN `&0 < sqrt t /\ sqrt t pow 2 = t /\ s2 < sqrt t` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "Gt" THEN
        MP_TAC(ISPECL [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
                          (real->real^3->real^3^3)`;
                       `(:real^3)`; `&0`; `t:real`; `(:real^3)`; `\y:real^3. y`; `t:real`;
                       `s1 / &2`; `(s2 + sqrt t) / &2`] P2A_REGION_LSMOOTH) THEN
        REWRITE_TAC[INTER_UNIV; IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
        REPEAT CONJ_TAC THENL
         [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
          ASM_REWRITE_TAC[REAL_LE_REFL; GSYM OPEN_IN; OPEN_UNIV];
          EXPAND_TAC "V" THEN ASM_REWRITE_TAC[open_set_atlas; IN_SING];
          ASM_REAL_ARITH_TAC;
          X_GEN_TAC `s:real` THEN STRIP_TAC THEN
          SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 < sqrt t pow 2` MP_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
            ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
        STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
        STRIP_TAC THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN EXPAND_TAC "Gt" THEN
    REWRITE_TAC[LIFT_DROP] THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC STNC_LLAG_BOUND THEN
    MAP_EVERY EXISTS_TAC [`te:real`; `t0:real`; `lam:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(L * Lam / (&16 * (s2 - s1) pow 2) + &12 * t * K0) * (s2 - s1) <=
    L * Lam * sqrt te / t0 + &12 * te * K0 * sqrt te`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `L * Lam / (&16 * (s2 - s1) pow 2) = (L * Lam) / (&16 * (s2 - s1) pow 2) /\
                  L * Lam * sqrt te / t0 = (L * Lam) * sqrt te / t0` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC STNC_CL_ARITH THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lx] THEN
  SUBGOAL_THEN `sqrt(s2 pow 2) = s2` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `N = &3 * sqrt te + L * Lam * sqrt te / t0 + &12 * te * K0 * sqrt te` THEN
  SUBGOAL_THEN `p2a_Lx (V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#(real->real^3->real^3^3)) t x (s2 pow 2) (stnc_psi g0 A0 (q:real^3) z) <= N`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN UNDISCH_TAC `(sol:real^1->real^3)(lift s2) = stnc_psi g0 A0 q z` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    SUBGOAL_THEN `&0 <= &3 * sqrt te /\ &0 <= L * Lam * sqrt te / t0 /\
                  &0 <= &12 * te * K0 * sqrt te` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `N / (&2 * s2)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < s ==> &0 < &2 * s`]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Large times, t0 < t < te: FL4, FL2, the competitor bound on              *)
(* the chart image B = psi_q(ball(0,1/4)) and FL6 (MT Thm 8.1).             *)
(* ------------------------------------------------------------------------- *)

let STNC_B_VOLUME = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0 L lam Lam (q:real^3) s.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t0 /\ t0 < te /\
     &1 <= L /\
     (!s y v. &0 <= s /\ s <= t0 ==> v dot (g0 y ** v) <= L * (v dot (G s y ** v))) /\
     &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     &0 <= s /\ s <= t0
     ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) (G s)
               (IMAGE (stnc_psi g0 A0 q) (ball(vec 0,&1 / &4))) v /\
             (lam * sqrt lam * (&4 / &3 * pi * (&1 / &4) pow 3)) / (L * sqrt L) <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (LABEL_TAC "eq") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "qf") STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `lam:real`; `Lam:real`; `q:real^3`;
                 `&1 / &4`] STNC_PSI_VOLUME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3) /\
                riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
      REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
      ASM_CASES_TAC `s = &0` THENL
       [ASM_MESON_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `B = IMAGE (stnc_psi g0 A0 (q:real^3)) (ball(vec 0,&1 / &4))` THEN
  SUBGOAL_THEN `compact(IMAGE (stnc_psi g0 A0 (q:real^3)) (cball(vec 0,&1 / &4))) /\
                (B:real^3->bool) SUBSET IMAGE (stnc_psi g0 A0 q) (cball(vec 0,&1 / &4))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[STNC_PSI_SMOOTH];
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC];
      EXPAND_TAC "B" THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) s`;
                 `IMAGE (stnc_psi g0 A0 (q:real^3)) (cball(vec 0,&1 / &4))`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; COMPACT_IN_EUCLIDEAN] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) s`; `B:real^3->bool`;
                 `IMAGE (stnc_psi g0 A0 (q:real^3)) (cball(vec 0,&1 / &4))`; `w:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `\x:real^3. &1`; `v0:real`] THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume; P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  ABBREV_TAC `vB = mfd_volume (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s)
                     (B:real^3->bool)` THEN
  STRIP_TAC THEN EXISTS_TAC `vB:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `(G:real->real^3->real^3^3) s`; `B:real^3->bool`;
                 `v0:real`; `vB:real`; `L:real`] MFD_HAS_VOLUME_COMPARE_QF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2C_EUCLID_FACTS; REAL_ARITH `&1 <= L ==> &0 <= L`] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `u:real^3`] THEN DISCH_TAC THEN
    USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < L * sqrt L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let STNC_LARGE_TIME = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t0 /\ t0 < te
     ==> ?kappa2. &0 < kappa2 /\
           !x t r. t0 < t /\ t < te /\ &0 < r /\ r pow 2 <= t0 / &2 /\
                   (!s y. t - r pow 2 < s /\ s <= t /\
                          y IN mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r
                          ==> mfd_rm_norm (open_set_atlas (:real^3)) (G s) y <= inv(r pow 2))
                   ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) (G t)
                             (mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r) v /\
                           kappa2 * r pow 3 <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                 `t0:real`] STNC_METRIC_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "eq"))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qf")))) o
    MATCH_MP STNC_PSI_QF) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t0:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [p3_partial_std]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  ABBREV_TAC `K0 = max K (&0)` THEN
  SUBGOAL_THEN `&0 <= K0 /\
                !s y. &0 <= s /\ s <= t0
                      ==> mfd_rm_norm (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) y
                          <= K0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `l0 = (&3 * sqrt te + L * Lam * sqrt te / t0 + &12 * te * K0 * sqrt te) /
                   (&2 * sqrt(t0 / &2))` THEN
  ABBREV_TAC `V0 = (lam * sqrt lam * (&4 / &3 * pi * (&1 / &4) pow 3)) / (L * sqrt L)` THEN
  SUBGOAL_THEN `&0 < V0` ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:3)`] P2AU_FLOW_THM_8_1_3) THEN
  REWRITE_TAC[P2A_FLOW_THM_8_1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`te:real`; `l0:real`; `V0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fl6"))) THEN
  EXISTS_TAC `kappa2:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`; `r:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_cbflow (euclidean,open_set_atlas (:real^3)) (&0) t (G:real->real^3->real^3^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC STNC_RESTRICT_CBFLOW THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `te:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* FL4: the minimum point q of l at t - t0 *)
  MP_TAC(ISPECL [`(:real^3)`; `(:3)`] P2AU_FLOW_THM_7_10_3) THEN
  REWRITE_TAC[P2A_FLOW_THM_7_10_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                             `&0`; `t:real`; `G:real->real^3->real^3^3`; `x:real^3`;
                             `t - t0`]) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; DIMINDEX_3; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  (* FL2: a minimizer to (q, t - t0) *)
  MP_TAC(ISPECL [`(:real^3)`; `(:3)`] P2AK_FLOW_MIN_EXISTS_3) THEN
  REWRITE_TAC[P2A_FLOW_MIN_EXISTS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                             `&0`; `t:real`; `G:real->real^3->real^3^3`; `x:real^3`;
                             `q:real^3`; `t - t0`]) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->real^3` STRIP_ASSUME_TAC) THEN
  (* FL6 with B = psi_q(ball(0,1/4)) at backward time t - t0/2 *)
  USE_THEN "fl6" (MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                  `&0`; `t:real`; `G:real->real^3->real^3^3`; `x:real^3`;
                                  `r:real`; `t - t0 / &2`;
                                  `IMAGE (stnc_psi g0 A0 (q:real^3)) (ball(vec 0,&1 / &4))`]) THEN
  REWRITE_TAC[DIMINDEX_3; REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM OPEN_IN] THEN MATCH_MP_TAC STNC_PSI_OPEN THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `t - (t - t0 / &2) = t0 / &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "V0" THEN MATCH_MP_TAC STNC_B_VOLUME THEN
    MAP_EVERY EXISTS_TAC [`te:real`; `t0:real`; `Lam:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT STRIP_TAC THEN USE_THEN "eq" (MP_TAC o SPECL [`s:real`; `y:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "l0" THEN MATCH_MP_TAC STNC_LX_BALL THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `gamma':real->real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT STRIP_TAC THEN USE_THEN "eq" (MP_TAC o SPECL [`s:real`; `y:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* The headline.  t0 = te/2; small times by STNC_SMALL_TIME_VOL,              *)
(* large times by STNC_LARGE_TIME (r <= sqrt(t0/2) forces r^2 <= t0/2),     *)
(* times outside [0,te) are vacuous (STNC_NONCOLL_OUTSIDE).                  *)
(* ------------------------------------------------------------------------- *)

let STNC_STD_NONCOLL = prove
 (`P2C_STD_NONCOLL_STATEMENT`,
  REWRITE_TAC[P2C_STD_NONCOLL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `te:real`;
                       `G:real->real^3->real^3^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < te` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t0 = te / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < te` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                 `t0:real`] STNC_SMALL_TIME_VOL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` (X_CHOOSE_THEN `kappa1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))))) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                 `t0:real`] STNC_LARGE_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "large"))) THEN
  SUBGOAL_THEN `&0 < sqrt(t0 / &2) /\ sqrt(t0 / &2) pow 2 = t0 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min kappa1 kappa2`; `min rho1 (sqrt(t0 / &2))`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN
  ASM_CASES_TAC `&0 <= t /\ t < te` THENL
   [ALL_TAC; MATCH_MP_TAC STNC_NONCOLL_OUTSIDE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[p3_noncoll_at] THEN X_GEN_TAC `r:real` THEN
  ASM_SIMP_TAC[STNC_VIEW_FACTS] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t <= t0` THENL
   [USE_THEN "small" (MP_TAC o SPECL [`t:real`; `x:real^3`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `kappa1 * r pow 3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "large" (MP_TAC o SPECL [`x:real^3`; `t:real`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `r pow 2 <= sqrt(t0 / &2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `kappa2 * r pow 3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

