(* ========================================================================= *)
(* Unit pc_p2a_p164: lemmas on the reduced length Lx for MT Prop 16.4        *)
(* (pc_p3_s164):                                                             *)
(* (a) joint space-time upper semicontinuity of Lx at a reached interior     *)
(*     point (P2AO_LX_USC_ST_VIEW, history form P2AO_LX_USC_ST);             *)
(* (b) backward vertical extension of an admissible curve along the flow     *)
(*     line of its end point (P2AO_VERT_EXT_VIEW, history form               *)
(*     P2AO_VERT_EXT);                                                       *)
(* (c) P2AO_LADM_RESTRICT and (d) P2AO_CONST_BASE (see the last section).    *)
(* ========================================================================= *)

needs "src/pc_p2a_brg.ml";;
needs "src/pc_p2a_smx.ml";;
needs "src/pc_p2a_rgx.ml";;
needs "src/pc_p2a_usc.ml";;
needs "src/pc_p2a_l72c.ml";;
needs "src/pc_p2a_c712.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* (b) in view form.  The constant curve at a point q of a backward region   *)
(* is an L-segment whose L-integrand is sqrt(tau) R(q, tt - tau) (the scalar *)
(* curvature of the region family in a chart, continuous in time); glued to  *)
(* an admissible curve ending at q (P2AXR_SEG_GLUE_X) and smoothed           *)
(* (P2AXS_SMOOTHING_X) it gives the extension.                               *)
(* ========================================================================= *)

(* P2AU_VELOCITY_CONST of pc_p2a_flow (not in this closure), proof copied. *)

let P2AO_VELOCITY_CONST = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (x:A) a b t.
     a < b /\ t IN real_interval[a,b] ==> mfd_velocity atlas (\s. x) a b t = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_velocity] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; HAS_VECTOR_DERIVATIVE_CONST]);;

let P2AO_CONST_INTEGRAND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (q:A) b2 sig.
     &0 < b2 /\ &0 <= sig /\ sig <= b2
     ==> p2a_L_integrand V tt (\tau. q) b2 sig =
         sqrt sig * mfd_scalar (p2a_vatlas V (tt - sig)) (p2a_vmetric V (tt - sig)) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_integrand; mfd_speed] THEN
  SUBGOAL_THEN
   `mfd_velocity (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - sig)) (\tau. q:A) (&0) b2 sig =
    vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2AO_VELOCITY_CONST THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LZERO; SQRT_0] THEN REAL_ARITH_TAC);;

(* The constant curve on [b1,b2] at a point of a backward region ending at  *)
(* tt - b1 (two-sided at the left end) is an L-segment.                     *)

let P2AO_CONST_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (q:A) W a b1 b2.
     p2a_svs V /\ &0 < b1 /\ b1 < b2 /\ q IN W /\ a < tt - b2 /\
     p2a_region V W a (tt - b1) /\ p2a_smooth V q (tt - b1)
     ==> p2a_lseg V tt b1 b2 (\tau. q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!sig. b1 <= sig /\ sig <= b2
          ==> (q:A) IN topspace(p2a_vtop (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - sig))`
  ASSUME_TAC THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt - b1`; `tt - sig`]
                  P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - sig))`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt - b1`; `tt - b1`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `?U (phi:A->real^N). (U,phi) IN p2a_vatlas (V:(real->A topology)#
                          (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - b1) /\
                        q IN U`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - b1)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - b1)`; `q:A`] CHART_AT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - b1)) (q:A))`;
      `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - b1)) (q:A))`] THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  (* the region family in the chart, on a time window around tt - b1 *)
  ABBREV_TAC `h = sqrt(((b2 - b1) + (tt - b1 - a)) / &2)` THEN
  SUBGOAL_THEN `&0 < h /\ h pow 2 = ((b2 - b1) + (tt - b1 - a)) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN `&0 < ((b2 - b1) + (tt - b1 - a)) / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. --h < s /\ s < h ==> s pow 2 < h pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (--h) h
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) W (tt - b1) (U INTER W,phi) ((tt - b1) - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_LSCALAR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN DISCH_TAC THEN
  ABBREV_TAC `ls = \s. lscalar (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W (tt - b1)
                   (U INTER W,phi:A->real^N) ((tt - b1) - s pow 2)) (phi(q:A))` THEN
  SUBGOAL_THEN `&0 < sqrt(b2 - b1) /\ sqrt(b2 - b1) < h` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. lift((ls:real->real) (drop s))) continuous_on
                interval[lift(&0),lift(sqrt(b2 - b1))]` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. lift((ls:real->real) (drop s))) =
                  (\z. lift(lscalar ((\s. p2a_rlocal (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W (tt - b1)
                     (U INTER W,phi:A->real^N) ((tt - b1) - s pow 2)) (drop(fstcart z)))
                     (sndcart z))) o (\s. pastecart s ((phi:A->real^N) q))`
    SUBST1_TAC THENL
     [EXPAND_TAC "ls" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                        SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(--h),lift h) PCROSS IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the L-integrand of the constant curve *)
  SUBGOAL_THEN
   `!sig. b1 <= sig /\ sig <= b2
          ==> p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) tt (\tau. q:A) b2 sig =
              sqrt sig * (ls:real->real) (sqrt(sig - b1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `q:A`; `b2:real`; `sig:real`]
                  P2AO_CONST_INTEGRAND) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN EXPAND_TAC "ls" THEN
    SUBGOAL_THEN `(tt - b1) - sqrt(sig - b1) pow 2 = tt - sig` SUBST1_TAC THENL
     [SUBGOAL_THEN `sqrt(sig - b1) pow 2 = sig - b1` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC P2AK_SCALAR_CHART THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\sig. sqrt sig * (ls:real->real) (sqrt(sig - b1))) real_continuous_on
    real_interval[b1,b2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
    SUBGOAL_THEN `(\sig. (ls:real->real) (sqrt(sig - b1))) = ls o (\sig. sqrt(sig - b1))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\sig. sqrt(sig - b1)) = sqrt o (\sig. sig - b1)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[&0,sqrt(b2 - b1)]` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `sig:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lseg] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
    EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC P2A_CD1_FROM_AT THEN
    EXISTS_TAC `\s:real^1. vec 0:real^N` THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; CONTINUOUS_CONST];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC P2A_CD1_FROM_AT THEN EXISTS_TAC `\s:real^1. vec 0:real^N` THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; CONTINUOUS_CONST];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau:real = b1` THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[p2a_smooth] THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt - b1`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC `\sig. sqrt sig * (ls:real->real) (sqrt(sig - b1))` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; IN_REAL_INTERVAL]]);;

(* (b), view form. *)

let P2AO_VERT_EXT_VIEW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) D Rmax e W a.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_admx V tt x b gamma /\
     &0 < D /\ &0 <= Rmax /\ &0 < e /\
     gamma b IN W /\ a < tt - b - D /\ p2a_region V W a (tt - b) /\
     (!s. tt - b - D <= s /\ s <= tt - b
          ==> mfd_scalar (p2a_vatlas V s) (p2a_vmetric V s) (gamma b) <= Rmax)
     ==> ?gamma'. p2a_adm1 V tt x (b + D) gamma' /\ gamma'(b + D) = gamma b /\
                  p2a_L_length V tt gamma' (b + D) <=
                  p2a_L_length V tt gamma b + sqrt(b + D) * Rmax * D + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b /\ p2a_smooth (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                  ((gamma:real->A) b) (tt - b)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `(gamma:real->A) b`; `W:A->bool`;
                 `a:real`; `b:real`; `b + D`] P2AO_CONST_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `gg = \tau. if tau <= b then (gamma:real->A) tau else gamma b` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `\tau:real. (gamma:real->A) b`;
                 `gamma:real->A`; `gg:real->A`; `b + D`; `b:real`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "gg" THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    X_GEN_TAC `tau:real` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[b,b + D])
      (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt (\tau. (gamma:real->A) b) (b + D)) <=
    sqrt(b + D) * Rmax * D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[b,b + D]) (\sig. sqrt(b + D) * Rmax)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `p2a_lseg (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) tt b (b + D) (\tau. (gamma:real->A) b)` THEN
        REWRITE_TAC[p2a_lseg] THEN SIMP_TAC[];
        X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)`; `tt:real`; `(gamma:real->A) b`; `b + D`;
                       `sig:real`] P2AO_CONST_INTEGRAND) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt sig * Rmax` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&0 < D ==> b <= b + D`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b + D`; `gg:real->A`; `e:real`]
                P2AXS_SMOOTHING_X) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g1:real->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "gg" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b + D <= b)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* (b) in history form, through the history bridge P2AB_HIST_VIEW_X          *)
(* (pc_p2a_brg): persisting sets are regions, admissible curves are p2a_admx *)
(* curves, p2a_adm1 curves are admissible, lengths agree                     *)
(* (P2A_L_LENGTH_VIEW).  The base point is backward smooth by its parabolic  *)
(* neighbourhood.                                                            *)
(* ========================================================================= *)

(* P2A_VBALL_ALT and P2A_C712_VBALL_CENTRE of pc_p2a_c712 (not in this       *)
(* closure), proofs copied.                                                  *)

let P2AO_VBALL_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r.
     rfs_vball V t x r =
     mfd_ball (p2a_vtop V t,p2a_vatlas V t) (p2a_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; p2a_vtop; p2a_vatlas; p2a_vmetric]);;

let P2AO_VBALL_CENTRE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r.
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ &0 < r ==> x IN rfs_vball V tt x r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2AO_VBALL_ALT; GSYM P2A_VIEW_PROJ_3; p2a_svs] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `tt:real`) THEN
  SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) = {})`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]);;

(* A base point with a parabolic neighbourhood is backward smooth. *)

let P2AO_HIST_BSMOOTH = prove
 (`!(hs:(A)rfs_history) tt x r dt.
     rfs_history_ok hs /\ &0 < tt /\ x IN topspace(rfs_top_at hs tt) /\
     &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt
     ==> p2a_bsmooth (rfs_view hs) x tt`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:A)` P2AB_HIST_VIEW_X) THEN REWRITE_TAC[P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_TOPSPACE_LIVE) THEN
  REWRITE_TAC[p2a_bsmooth] THEN
  MAP_EVERY EXISTS_TAC [`rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r`; `tt - min dt tt`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2AO_VBALL_CENTRE THEN ASM_REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS];
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_region")) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2A_PERSISTS_MONO THEN EXISTS_TAC `tt - dt` THEN
      UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r dt` THEN
      REWRITE_TAC[rfs_parabolic_exists] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

(* (b), history form. *)

let P2AO_VERT_EXT = prove
 (`!(hs:(A)rfs_history) tt x b (gamma:real->A) D Rmax e.
     rfs_history_ok hs /\ rfs_L_adm hs tt x b gamma /\ &0 < D /\ b + D < tt /\
     &0 <= Rmax /\ &0 < e /\ x IN topspace(rfs_top_at hs tt) /\
     (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt) /\
     (?W eta. &0 < eta /\ gamma b IN W /\
              rfs_persists (rfs_view hs) W (tt - b - D - eta) (tt - b)) /\
     (!s. tt - b - D <= s /\ s <= tt - b
          ==> mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at hs s) (gamma b) <= Rmax)
     ==> ?gamma'. rfs_L_adm hs tt x (b + D) gamma' /\ gamma'(b + D) = gamma b /\
                  rfs_L_length hs tt gamma' (b + D) <=
                  rfs_L_length hs tt gamma b + sqrt(b + D) * Rmax * D + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_L_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (rfs_view (hs:(A)rfs_history)) x tt` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AO_HIST_BSMOOTH THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:A)` P2AB_HIST_VIEW_X) THEN REWRITE_TAC[P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_TOPSPACE_LIVE) THEN
  ABBREV_TAC `a = (tt - b - D) - min eta ((tt - b - D) / &2)` THEN
  SUBGOAL_THEN `&0 <= a /\ a < tt - b - D /\ tt - b - D - eta <= a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (rfs_view (hs:(A)rfs_history)) W a (tt - b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_region")) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2A_PERSISTS_MONO THEN EXISTS_TAC `tt - b - D - eta` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                 `gamma:real->A`; `D:real`; `Rmax:real`; `e:real`; `W:A->bool`; `a:real`]
                P2AO_VERT_EXT_VIEW) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2A_ATLAS_LC_HIST] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g1:real->A` THEN ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm1")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_L_adm")) (concl th) &&
    not(can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th)))) THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Tools for (a).  The joined curve of pc_p2a_usc (the curve cut at s1^2 and *)
(* continued by an affine chart piece to p) with a free end parameter sb,    *)
(* not only sqrt b: P2AO_JCURVE_GEN is P2A_JCURVE (pc_p2a_usc) with sqrt b   *)
(* replaced by sb in the joined curve (same proof).  A real lemma on square  *)
(* roots of nearby numbers.                                                  *)
(* ========================================================================= *)

let P2AO_JCURVE_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s1 sb sa sb' p.
     p2a_svs V /\ p2a_adm V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < sqrt b /\ s1 < sb /\ sa < s1 /\ sb < sb' /\
     (!s. sa < s /\ s < sb' ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     gamma(s1 pow 2) IN U INTER W /\
     (!s. s1 <= s /\ s <= sb
          ==> phi(gamma(s1 pow 2)) + (inv(sb - s1) * (s - s1)) % (p - phi(gamma(s1 pow 2)))
              IN IMAGE phi (U INTER W))
     ==> p2a_adm V tt x (sb pow 2) (p2a_jcurve gamma U W phi s1 sb p) /\
         p2a_jcurve gamma U W phi s1 sb p (sb pow 2) = chart_inv (U INTER W,phi) p /\
         p2a_L_length V tt (p2a_jcurve gamma U W phi s1 sb p) (sb pow 2) =
         p2a_L_length V tt gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt
                (\v. phi(gamma(s1 pow 2)) +
                     (inv(sb - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
                s1 sb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 = b /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < b` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sb /\ s1 pow 2 < sb pow 2 /\ sqrt(sb pow 2) = sb` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sb` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(sb - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `sb:real`; `sa:real`; `sb':real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(sb - s1) % ((p:real^N) - phi((gamma:real->A)(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(sb - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(sb - s1) % ((p:real^N) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N)
                          ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                           (inv(sb - s1) * (sqrt tau - s1)) % (p - phi(gamma(s1 pow 2))))`;
                 `gamma:real->A`; `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 sb p`;
                 `sb pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[p2a_jcurve];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_jcurve] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2a_jcurve] THEN
    SUBGOAL_THEN `~(sb pow 2 <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `inv(sb - s1) * (sb - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* Square roots of nearby positive numbers. *)

let P2AO_SQRT_CLOSE = prove
 (`!b b' d. &0 < b /\ &0 < b' /\ abs(b' - b) < sqrt b * d ==> abs(sqrt b' - sqrt b) < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt b /\ &0 < sqrt b'` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt b' - sqrt b) * (sqrt b' + sqrt b) = b' - b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(x - y) * (x + y) = x pow 2 - y pow 2`] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt b' - sqrt b) * sqrt b <= abs(b' - b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt b' - sqrt b) * sqrt b < d * sqrt b` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RMUL_EQ]);;


(* ========================================================================= *)
(* (a) in view form.  The core P2AO_LX_USC_ST_ADM follows P2A_LX_USC_GEN     *)
(* (pc_p2a_usc; its first part is reused verbatim, with the constant 64 for  *)
(* 16 in the choice of eps): the curve is cut at s1^2 and continued in the   *)
(* region chart at its end point by the affine piece to a nearby point q,    *)
(* now ending at a nearby time tt - s2^2 (P2AO_JCURVE_GEN); the              *)
(* neighbourhood is open in the slice of the region end b'' and so persists  *)
(* (P2A_REGION_OPEN_BACK).  P2AO_LX_USC_ST_VIEW smooths a p2a_admx curve     *)
(* first (P2AXS_SMOOTHING_X).                                                *)
(* ========================================================================= *)

let P2AO_LX_USC_ST_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\ &0 < e
     ==> ?O et. &0 < et /\ et < b /\ gamma b IN O /\
                p2a_persists V O (tt - b - et) (tt - b + et) /\
                !s q. abs(s - (tt - b)) < et /\ q IN O
                      ==> ?gamma'. p2a_adm1 V tt x (tt - s) gamma' /\ gamma'(tt - s) = q /\
                                   p2a_L_length V tt gamma' (tt - s) <=
                                   p2a_L_length V tt gamma b + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* the region chart at the end point *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `sqrt b`] P2A_MIN_REGION_AT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  (* the punctured window at the end point *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `sqrt b`]
                P2A_MIN_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))))) THEN
  SUBGOAL_THEN `?h1. &0 < h1 /\ h1 < h /\ h1 < sqrt b` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min h (sqrt b) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  (LABEL_TAC "WIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  (LABEL_TAC "WINLE") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (sqrt b - h1) (sqrt b + h1)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a closed ball in the chart image *)
  SUBGOAL_THEN `?rho0. &0 < rho0 /\
                       cball((phi:A->real^N)((gamma:real->A) b),rho0) SUBSET
                       IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p2a_lsmooth] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* metric and curvature bounds near the end point *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QB"))))) THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB")) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. sqrt b - h1 / &2 <= s /\ s <= sqrt b + h1 / &2 /\
          y IN cball((phi:A->real^N)((gamma:real->A) b),rho0)
          ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b''
                 (U INTER W,phi)) tt s y (vec 0)) <= Kp`
  (LABEL_TAC "KP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN USE_THEN "KB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eps. &0 < eps /\ eps * (&64 * (Cg + &1)) = e`
  (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / (&64 * (Cg + &1))` THEN
    SUBGOAL_THEN `&0 < &64 * (Cg + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < &64 * (Cg + &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cg * eps <= e / &64` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (e / &8) (c * eps / &4)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e / &8 /\ eta <= c * eps / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < c * eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the L-length near the end point is small *)
  SUBGOAL_THEN `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt gamma b
                real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b`;
                 `&0`; `b:real`; `b:real`; `b:real`; `eta:real`]
                REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE; REAL_INTEGRAL_REFL;
               REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KAP"))) THEN
  MP_TAC(SPECL [`sqrt b`; `kap:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HK"))) THEN
  (* continuity of the chart curve at the end point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sqrt b - h1 / &2`; `sqrt b`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2A_ADM_SCONT (ASSUME
      `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "H2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      USE_THEN "WINLE" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift(sqrt b)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho0 / &4`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY"))) THEN
  (* the cut point s1 = sqrt b - d1 *)
  MP_TAC(SPECL [`c * eps / &4`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KA"))) THEN
  MP_TAC(SPECL [`e / &8`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KBB"))) THEN
  SUBGOAL_THEN
   `?d1. &0 < d1 /\ d1 <= h1 / &2 /\ d1 < hk /\ d1 < dy /\
         Kp * d1 <= c * eps / &4 /\ Kp * d1 <= e / &8`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min (h1 / &2) (min hk dy / &2)) (min ka kb)` THEN
    SUBGOAL_THEN `&0 < min (min (h1 / &2) (min hk dy / &2)) (min ka kb)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THENL
     [USE_THEN "KA" MATCH_MP_TAC; USE_THEN "KBB" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt b - d1` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < sqrt b /\ sqrt b - h1 < s1 /\ sqrt b - h1 / &2 <= s1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* facts on [s1, sqrt b] *)
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= sqrt b
        ==> (phi:A->real^N)((gamma:real->A)(r pow 2)) IN cball(phi(gamma b),rho0) /\
            norm(phi(gamma(r pow 2)) - phi(gamma b)) < rho0 / &4`
  (LABEL_TAC "INB") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "DY" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DIST_LIFT] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[dist; IN_CBALL] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(r pow 2))`; `(phi:A->real^N)((gamma:real->A) b)`]
                  NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. s1 pow 2 <= u /\ u <= b
        ==> abs(real_integral (real_interval[s1 pow 2,u])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) tt gamma b)) < eta`
  (LABEL_TAC "SMALL") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN USE_THEN "KAP" MATCH_MP_TAC THEN
    SUBGOAL_THEN `abs(s1 pow 2 - b) < kap` ASSUME_TAC THENL
     [USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s1 pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the displacement of the curve near the end *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `sqrt b - h1`; `sqrt b + h1`; `s1:real`; `c:real`; `Kp:real`; `eps:real`]
                P2A_END_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `(phi:A->real^N)((gamma:real->A)(r pow 2))`;
                                     `A:real^N`]) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "INB" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KP" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "INB" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "SMALL" (MP_TAC o SPEC `s pow 2`) THEN ANTS_TAC THENL
       [CONJ_TAC THEN TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `sqrt b pow 2 = b`))) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "s1" THEN ASM_REWRITE_TAC[REAL_ARITH `s - (s - d) = d:real`]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `zeta = sqrt(eps * d1)` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * d1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * d1` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))) <= &2 * zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))) pow 2 <=
                 &4 * eps * (sqrt b - s1)` THEN
    EXPAND_TAC "s1" THEN REWRITE_TAC[REAL_ARITH `s - (s - d) = d:real`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the end time is interior to the region *)
  SUBGOAL_THEN `a' < tt - b /\ tt - b < b''` STRIP_ASSUME_TAC THENL
   [USE_THEN "WIN" (MP_TAC o SPEC `sqrt b`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the open set of end points, open in the slice b'' *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `b'':real`; `(gamma:real->A) b`; `min (rho0 / &4) zeta`]
                P2A_CHART_PREIMAGE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OP")))) THEN
  SUBGOAL_THEN
   `!t. a' < t /\ t <= b''
        ==> smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#
              (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) (p2a_vatlas V t) /\
            open_in (p2a_vtop V t) (O:A->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `t:real`]
                  P2A_REGION_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "OP" MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  (* the time window *)
  ABBREV_TAC `et = min (min (b / &2) (sqrt b * d1 / &2))
                       (min ((tt - b - a') / &2) ((b'' - (tt - b)) / &2))` THEN
  SUBGOAL_THEN `&0 < et /\ et < b /\ et <= sqrt b * d1 / &2 /\
                a' <= tt - b - et /\ tt - b + et <= b''` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "et" THEN
    SUBGOAL_THEN `&0 < sqrt b * d1` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`O:A->bool`; `et:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2A_PERSISTS_ALT] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `O:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_manifold_atlas"))
          (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `q:A`] THEN STRIP_TAC THEN
  USE_THEN "OP" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  ABBREV_TAC `bq = tt - s` THEN
  SUBGOAL_THEN `&0 < bq /\ abs(bq - b) < sqrt b * (d1 / &2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt bq - sqrt b) < d1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AO_SQRT_CLOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s2 = sqrt bq` THEN
  SUBGOAL_THEN `&0 < s2 /\ s2 pow 2 = bq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN MP_TAC(ASSUME `&0 < bq`) THEN
    SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 < s2 /\ d1 / &2 < s2 - s1 /\ s2 - s1 < &3 * d1 / &2 /\
                s2 < sqrt b + h1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the joined curve *)
  ABBREV_TAC `P1 = (phi:A->real^N)((gamma:real->A)(s1 pow 2))` THEN
  ABBREV_TAC `Pb = (phi:A->real^N)((gamma:real->A) b)` THEN
  ABBREV_TAC `pq = (phi:A->real^N) q` THEN
  SUBGOAL_THEN `norm((P1:real^N) - Pb) < rho0 / &4` ASSUME_TAC THENL
   [USE_THEN "INB" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s2
        ==> (P1:real^N) + (inv(s2 - s1) * (r - s1)) % (pq - P1) IN cball(Pb,rho0)`
  (LABEL_TAC "ZIN") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ABBREV_TAC `t = inv(s2 - s1) * (r - s1)` THEN
    SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Pb:real^N) - (P1 + t % (pq - P1)) = (&1 - t) % (Pb - P1) + t % (Pb - pq)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&1 - t) * norm((Pb:real^N) - P1) + abs t * norm(Pb - pq)` THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM NORM_MUL; NORM_TRIANGLE]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((Pb:real^N) - P1) <= rho0 /\ norm((Pb:real^N) - pq) <= rho0`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(&1 - t) * rho0 + abs t * rho0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_ARITH `&0 <= t /\ t <= &1 ==> abs(&1 - t) = &1 - t /\ abs t = t`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `sqrt b - h1`; `sqrt b + h1`; `pq:real^N`]
                P2AO_JCURVE_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "H2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(is_forall(concl th)))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 s2 pq bq = q`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pq" THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the length of the affine piece *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `P1:real^N`; `(pq:real^N) - P1`; `inv(s2 - s1)`;
                 `s1:real`; `s2:real`; `cball(Pb:real^N,rho0)`; `Cg:real`; `Kp:real`]
                P2A_ZPIECE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`r:real`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "KP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* the final estimate for the joined curve *)
  SUBGOAL_THEN
   `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt
       (p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 s2 (pq:real^N)) bq <=
    p2a_L_length V tt gamma b + &3 * e / &4`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`;
                   `s1 pow 2`] P2A_LENGTH_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "SMALL" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `norm((pq:real^N) - P1) pow 2 <= &9 * eps * d1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * zeta) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC(NORM_ARITH
         `!z:real^N. norm(y - z) < e /\ norm(z - w) <= &2 * e ==> norm(y - w) <= &3 * e`) THEN
        EXISTS_TAC `Pb:real^N` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(s2 - s1) * (inv(&2) * Cg * norm(inv(s2 - s1) % ((pq:real^N) - P1)) pow 2 + Kp) <=
      &9 * (Cg * eps) + &3 / &2 * (Kp * d1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
      ABBREV_TAC `nn = norm((pq:real^N) - P1)` THEN
      ABBREV_TAC `dd = s2 - s1` THEN
      SUBGOAL_THEN `dd * (inv(&2) * Cg * (inv dd * nn) pow 2 + Kp) =
                    inv(&2) * Cg * (nn pow 2 / dd) + Kp * dd` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < dd` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&9 * eps * d1 <= &18 * eps * dd` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= eps * (&2 * dd - d1) ==> &9 * eps * d1 <= &18 * eps * dd`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `nn pow 2 / dd <= &18 * eps` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `Cg * (nn pow 2 / dd) <= Cg * (&18 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `Kp * dd <= Kp * (&3 * d1 / &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* smoothing *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `bq:real`;
                 `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 s2 pq`; `e / &4`]
                P2A_SMOOTHING_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma':real->A` THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]);;

(* (a), view form. *)

let P2AO_LX_USC_ST_VIEW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_admx V tt x b gamma /\
     &0 < e /\ p2a_smooth V (gamma b) (tt - b)
     ==> ?W eta. &0 < eta /\ eta < b /\ gamma b IN W /\
                 p2a_persists V W (tt - b - eta) (tt - b + eta) /\
                 !s q. abs(s - (tt - b)) < eta /\ q IN W
                       ==> ?gamma'. p2a_adm1 V tt x (tt - s) gamma' /\ gamma'(tt - s) = q /\
                                    p2a_L_length V tt gamma' (tt - s) <=
                                    p2a_L_length V tt gamma b + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `e / &2`] P2AXS_SMOOTHING_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `g1:real->A`;
                 `e / &2`] P2AO_LX_USC_ST_ADM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[p2a_adm1]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` (X_CHOOSE_THEN `et:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`O:A->bool`; `et:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    UNDISCH_TAC `(g1:real->A) b IN O` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `q:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `q:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm1")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* (a) in history form.  A near-minimizing admissible curve to (q, tt - b)   *)
(* (the infimum is honest: P2AB_SCALAR_LOWER, P2AB_LADM_LOWER), the view     *)
(* form at its end point, the bridge back (P2AB_ADM1_LADM, the length        *)
(* equality P2A_L_LENGTH_VIEW) and Lx <= L for admissible curves.            *)
(* ========================================================================= *)

let P2AO_PERSISTS_EQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b. rfs_persists V W a b <=> p2a_persists V W a b`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; p2a_persists]);;

(* Lx is at most the L-length of any admissible curve to the point. *)

let P2AO_LX_LE_HIST = prove
 (`!(hs:(A)rfs_history) tt x b (g:real->A).
     rfs_history_ok hs /\ rfs_L_adm hs tt x b g
     ==> rfs_Lx hs tt x b (g b) <= rfs_L_length hs tt g b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:A)`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[RFA_P2A_REQ_RLOWER] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  REWRITE_TAC[rfs_Lx] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`--(abs m * sqrt b * b)`; `rfs_L_length hs tt (g:real->A) b`] THEN
  REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `g:real->A` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `l:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_LADM_LOWER THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]);;

(* (a), history form. *)

let P2AO_LX_USC_ST = prove
 (`!(hs:(A)rfs_history) tt x b q e.
     rfs_history_ok hs /\ &0 < e /\ b < tt /\ x IN topspace(rfs_top_at hs tt) /\
     (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt) /\
     (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q) /\
     (?W eta. &0 < eta /\ q IN W /\
              rfs_persists (rfs_view hs) W (tt - b - eta) (tt - b + eta))
     ==> ?W eta. &0 < eta /\ eta < b /\ q IN W /\
                 rfs_persists (rfs_view hs) W (tt - b - eta) (tt - b + eta) /\
                 !s q'. abs(s - (tt - b)) < eta /\ q' IN W
                        ==> (?gamma'. rfs_L_adm hs tt x (tt - s) gamma' /\ gamma'(tt - s) = q') /\
                            rfs_Lx hs tt x (tt - s) q' <= rfs_Lx hs tt x b q + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_L_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (rfs_view (hs:(A)rfs_history)) x tt` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AO_HIST_BSMOOTH THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[RFA_P2A_REQ_RLOWER] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  (* a near-minimizing admissible curve *)
  SUBGOAL_THEN
   `?g1. rfs_L_adm hs tt x b g1 /\ (g1:real->A) b = q /\
         rfs_L_length hs tt g1 b < rfs_Lx hs tt x b q + e / &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{rfs_L_length hs tt g b | g | rfs_L_adm hs tt x b (g:real->A) /\ g b = q}`;
                   `rfs_Lx (hs:(A)rfs_history) tt x b q + e / &2`] INF_APPROACH) THEN
    REWRITE_TAC[GSYM rfs_Lx] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        EXISTS_TAC `--(abs m * sqrt b * b)` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
        X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN MATCH_MP_TAC P2AB_LADM_LOWER THEN
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[EXISTS_IN_GSPEC] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b g1` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_smooth (rfs_view (hs:(A)rfs_history)) ((g1:real->A) b) (tt - b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b g1` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                 `g1:real->A`; `e / &2`] P2AO_LX_USC_ST_VIEW) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2AB_SVS; P2A_ATLAS_LC_HIST] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W1:A->bool` (X_CHOOSE_THEN `et:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`W1:A->bool`; `min et ((tt - b) / &2)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(g1:real->A) b IN W1` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `p2a_persists (rfs_view (hs:(A)rfs_history)) W1 (tt - b - et) (tt - b + et)` THEN
    REWRITE_TAC[P2AO_PERSISTS_EQ; P2A_PERSISTS_ALT] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC(TAUT `(c ==> a) ==> (a ==> b) ==> (c ==> b)`) THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `q':A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `q':A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm1")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `rfs_L_adm hs tt x (tt - s) (g2:real->A)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [EXISTS_TAC `g2:real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - s`; `g2:real->A`]
                  P2AO_LX_LE_HIST) THEN
    ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
    UNDISCH_TAC `rfs_L_length hs tt (g1:real->A) b < rfs_Lx hs tt x b q + e / &2` THEN
    REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Two more lemmas in history form for Prop 16.4.                            *)
(*                                                                           *)
(* (c) P2AO_LADM_RESTRICT: Lx at an earlier point of an admissible curve is  *)
(*     at most its L-length plus 6 sqrt b (b - b') (R >= -6 by pinching on   *)
(*     the cut-off piece).                                                   *)
(* (d) P2AO_CONST_BASE: the constant curve at the base point (history form   *)
(*     of P2A_CONST_SMALL_TIME, pc_p2a_c712).                                *)
(* ========================================================================= *)

(* R >= -6 in a pinched history (as at the end of P3N_ST_SCALAR_LOW of     *)
(* pc_p3_s1621, which is not in this closure).                               *)

let P2AO_PINCHED_LOW = prove
 (`!(hs:(A)rfs_history) t y.
     rfs_pinched (rfs_view hs) /\ &0 <= t /\ y IN topspace(rfs_top_at hs t)
     ==> --(&6) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) y`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_pinched; rfs_view] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:A`]) THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `--(&6) <= a ==> a <= r ==> --(&6) <= r`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> --(&6) <= --(&6 * x)`) THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC);;

(* (c). *)

let P2AO_LADM_RESTRICT = prove
 (`!(hs:(A)rfs_history) tt x b b' (gamma:real->A).
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b gamma /\
     &0 < b' /\ b' < b /\ b < tt /\ x IN topspace(rfs_top_at hs tt) /\
     (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt)
     ==> (?gamma'. rfs_L_adm hs tt x b' gamma' /\ gamma' b' = gamma b') /\
         rfs_Lx hs tt x b' (gamma b') <= rfs_L_length hs tt gamma b + &6 * sqrt b * (b - b')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b' gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `b:real`; `b':real`] P2AXR_LENGTH_SPLIT_X) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  (* the cut-off piece is not too negative *)
  SUBGOAL_THEN
   `--(&6 * sqrt b * (b - b')) <=
    real_integral (real_interval[b',b])
      (p2a_L_integrand (rfs_view (hs:(A)rfs_history)) tt gamma b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[b',b]) (\tau. --(&6 * sqrt b))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN CONJ_TAC THENL
       [UNDISCH_TAC `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b gamma` THEN
        REWRITE_TAC[p2a_admx] THEN SIMP_TAC[];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      REWRITE_TAC[p2a_L_integrand; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
      SUBGOAL_THEN `(gamma:real->A) tau IN topspace(rfs_top_at hs (tt - tau))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b gamma` THEN
        REWRITE_TAC[p2a_admx; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - tau`; `(gamma:real->A) tau`]
                    P2AO_PINCHED_LOW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ABBREV_TAC `R0 = mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                         ((gamma:real->A) tau)` THEN
      ABBREV_TAC `sp = mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                         (gamma:real->A) (&0) b tau` THEN
      SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt tau * --(&6) <= sqrt tau * (R0 + sp pow 2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `sp:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the restricted curve, smoothed, is admissible; the Lx bound *)
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?g'. rfs_L_adm hs tt x b' g' /\ (g':real->A) b' = gamma b' /\
                 rfs_L_length hs tt g' b' <= p2a_L_length (rfs_view hs) tt gamma b' + e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b':real`;
                   `gamma:real->A`; `e:real`] P2AXS_SMOOTHING_X) THEN
    ASM_SIMP_TAC[P2AB_SVS; P2A_ATLAS_LC_HIST] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
    MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_Lx hs tt x b' ((gamma:real->A) b') <= p2a_L_length (rfs_view hs) tt gamma b'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b':real`; `g':real->A`]
                  P2AO_LX_LE_HIST) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN ASM_REAL_ARITH_TAC);;

(* (d). *)

let P2AO_CONST_BASE = prove
 (`!(hs:(A)rfs_history) tt x r dt.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs tt) /\ &0 < r /\ &0 < dt /\
     rfs_parabolic_exists (rfs_view hs) tt x r dt
     ==> ?t0 K. &0 < t0 /\
                !b. &0 < b /\ b < t0
                    ==> rfs_L_adm hs tt x b (\s. x) /\
                        rfs_L_length hs tt (\s. x) b <= K * b * sqrt b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2a_svs (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2AB_SVS]; ALL_TAC] THEN
  (* tt > 0: before time 0 the slices are empty *)
  SUBGOAL_THEN `&0 < tt` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_TOPSPACE_LIVE) THEN
    ASM_CASES_TAC `tt = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `(x:A) IN rfs_vball (rfs_view hs) (&0) x r` MP_TAC THENL
     [MATCH_MP_TAC P2AO_VBALL_CENTRE THEN ASM_REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS];
      ALL_TAC] THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) (&0) x r dt` THEN
    REWRITE_TAC[rfs_parabolic_exists; P2AO_PERSISTS_EQ; P2A_PERSISTS_ALT] THEN
    DISCH_THEN(MP_TAC o SPEC `--(dt / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `--(dt / &2)`] P2AB_DEAD) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `dt:real`]
                P2AO_HIST_BSMOOTH) THEN
  ASM_REWRITE_TAC[p2a_bsmooth] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `W:A->bool`; `a:real`]
                P2A_CONST_SMALL_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t0:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kr:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
  MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[p2a_adm1] THEN
  REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC P2A_CD1_FROM_AT THEN
  EXISTS_TAC `\s:real^1. vec 0:real^3` THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; CONTINUOUS_CONST]);;

