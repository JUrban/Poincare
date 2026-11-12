(* ========================================================================= *)
(* Unit pc_rfa_pinch3: R-PINCH3, the statement                               *)
(* P2B_REQ_PINCH_ROUND3_STATEMENT of pc_p2b_pinch3req, proved as             *)
(* RFA_P2B_REQ_PINCH_ROUND3.  A compact connected 3-d Ricci flow, ancient up *)
(* to b, with positive sectional curvature and (1+e)-pinching before any     *)
(* time for every e > 0 has constant positive curvature at every t < b.      *)
(* Route: the pointwise pinching function G_c = lambda - c R/2               *)
(* (lambda = mfd_sec_min) stays nonnegative under the flow (the minimum      *)
(* principle RFA_MINP_BARRIER with the Rayleigh barrier                      *)
(* RFA_SECMIN_BARRIER_HI); c = 1/(3(1+e)) at an early time and e -> 0 give   *)
(* lambda >= R/6, so every sectional curvature is R/6; then Einstein, and    *)
(* Schur by the contracted Bianchi identity, give one constant.              *)
(* ========================================================================= *)

needs "src/pc_rfa_pinch.ml";;
needs "src/pc_rfa_pinchrm.ml";;
needs "src/pc_rfa_h3d.ml";;
needs "src/pc_p2b_pinch3req.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The reaction inequality.  For principal curvatures                        *)
(* p1 <= p2, p3 with p1 >= 0, S = p1 + p2 + p3 = R/2 and                     *)
(* abs(Ric)^2 = (p2+p3)^2 + (p1+p3)^2 + (p1+p2)^2, the reaction term of      *)
(* G = p1 - c S is at least 2 S G >= 2 B G where G < 0 and S <= B: by the    *)
(* identity (p1^2 + p2 p3) S - p1 Q = p2^2 (p3 - p1) + p3^2 (p2 - p1) >= 0,  *)
(* Q = abs(Ric)^2 / 2 <= S^2 (the ODE fact d/dt(p1/S) >= 0).                 *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_REACTION = prove
 (`!p1 p2 p3 c B.
     &0 <= p1 /\ p1 <= p2 /\ p1 <= p3 /\ &0 <= c /\ p1 + p2 + p3 <= B /\
     p1 - c * (p1 + p2 + p3) < &0
     ==> &2 * B * (p1 - c * (p1 + p2 + p3)) <=
         &2 * (p1 pow 2 + p2 * p3) -
         c * ((p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = p1 + p2 + p3` THEN
  ABBREV_TAC `G = p1 - c * S` THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < S` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c * S <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= c * --S ==> c * S <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Q = p1 pow 2 + p2 pow 2 + p3 pow 2 + p2 * p3 + p1 * p2 + p1 * p3` THEN
  SUBGOAL_THEN `(p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2 = &2 * Q`
  SUBST1_TAC THENL [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p1 pow 2 + p2 * p3) * S = p1 * Q + (p2 pow 2 * (p3 - p1) + p3 pow 2 * (p2 - p1))`
  ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["S"; "Q"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2 pow 2 * (p3 - p1) + p3 pow 2 * (p2 - p1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Q <= S pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `S pow 2 - Q = p1 * p2 + p1 * p3 + p2 * p3` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["S"; "Q"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= p1 * p2 /\ &0 <= p1 * p3 /\ &0 <= p2 * p3` MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `S * (&2 * S * G) <= S * (&2 * (p1 pow 2 + p2 * p3) - c * (&2 * Q))`
  MP_TAC THENL
   [SUBGOAL_THEN
     `S * (&2 * (p1 pow 2 + p2 * p3) - c * (&2 * Q)) =
      &2 * Q * G + &2 * (p2 pow 2 * (p3 - p1) + p3 pow 2 * (p2 - p1))`
    SUBST1_TAC THENL
     [EXPAND_TAC "G" THEN
      UNDISCH_TAC `(p1 pow 2 + p2 * p3) * S =
                   p1 * Q + (p2 pow 2 * (p3 - p1) + p3 pow 2 * (p2 - p1))` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `S * (&2 * S * G) <= &2 * Q * G /\ &0 <= P
      ==> S * (&2 * S * G) <= &2 * Q * G + &2 * P`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= --G * (S pow 2 - Q) ==> S * (&2 * S * G) <= &2 * Q * G`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * B * G <= &2 * S * G ==> &2 * S * G <= r ==> &2 * B * G <= r`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --G * (B - S) ==> &2 * B * G <= &2 * S * G`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The barrier for the pinching function at a bad point.  At                 *)
(* (t0,x0) with G_c = lambda - c R/2 < 0, lambda >= 0 and 3 abs(Rm) <= B,    *)
(* q - c R/2, with q the Rayleigh barrier of RFA_SECMIN_BARRIER_HI and R the *)
(* scalar curvature of the chart at x0, is an upper barrier for G_c at x0    *)
(* with Lap + 2 B G_c <= D (RFA_PN3_REACTION).  The set-up follows           *)
(* RFA_HI_BARRIER of pc_rfa_pinch; the function here is linear.              *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_BARRIER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t0 x0 c B.
     ricci_flow_on (top,atlas) a b g /\ a < t0 /\ t0 < b /\ x0 IN topspace top /\
     &0 <= c /\ &0 <= mfd_sec_min atlas (g t0) x0 /\
     mfd_sec_min atlas (g t0) x0 - c * mfd_scalar atlas (g t0) x0 / &2 < &0 /\
     &3 * sqrt(rfa_rmd2 0 atlas (g t0) x0) <= B
     ==> ?d W (phi:real->real^3->real) D.
           &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
           W SUBSET IMAGE (SND(chart_at atlas x0))
                          (FST(chart_at atlas x0) INTER topspace top) /\
           (!y. y IN W
                ==> mfd_sec_min atlas (g t0) (chart_inv (chart_at atlas x0) y) -
                    c * mfd_scalar atlas (g t0) (chart_inv (chart_at atlas x0) y) / &2 <=
                    phi t0 y) /\
           phi t0 (SND(chart_at atlas x0) x0) =
           mfd_sec_min atlas (g t0) x0 - c * mfd_scalar atlas (g t0) x0 / &2 /\
           (!t. t0 - d < t /\ t <= t0
                ==> mfd_sec_min atlas (g t) x0 - c * mfd_scalar atlas (g t) x0 / &2 <=
                    phi t (SND(chart_at atlas x0) x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           llap (metric_local atlas (chart_at atlas x0) (g t0)) (phi t0)
                (SND(chart_at atlas x0) x0) +
           &2 * B * (mfd_sec_min atlas (g t0) x0 - c * mfd_scalar atlas (g t0) x0 / &2)
           <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`;
                 `t0:real`; `x0:A`] RFA_SECMIN_BARRIER_HI) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `W1:real^3->bool`
    (X_CHOOSE_THEN `q:real->real^3->real` (X_CHOOSE_THEN `Dq:real`
     (X_CHOOSE_THEN `p2:real` (X_CHOOSE_THEN `p3:real` STRIP_ASSUME_TAC)))))) THEN
  (* the chart *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`;
                 `topspace(top:A topology)`] RFA_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN W1
        ==> mfd_scalar atlas ((g:real->A->real^3^3) t0)
                       (chart_inv (chart_at atlas x0) y) =
            lscalar (metric_local atlas (chart_at atlas x0) (g t0)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^3) IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)))
                          (FST(chart_at atlas x0))`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_scalar] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`;
                   `chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)) y`]
           RFA_MFD_SCALAR_CHART) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ch = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)` THEN
  ABBREV_TAC `y0 = SND (ch:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `V = IMAGE (SND (ch:(A->bool)#(A->real^3))) (FST ch)` THEN
  SUBGOAL_THEN
   `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
        lscalar (metric_local atlas (ch:(A->bool)#(A->real^3)) (g t)) y0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `lam0 = mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0` THEN
  SUBGOAL_THEN
   `metric_field V (metric_local atlas (ch:(A->bool)#(A->real^3))
                                 ((g:real->A->real^3^3) t0)) /\
    (y0:real^3) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ASSUME `lricci_flow V a b
        (\t. metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`) THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPEC `t0:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W1:real^3->bool) SUBSET V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN UNDISCH_TAC
     `(W1:real^3->bool) SUBSET IMAGE (SND(ch:(A->bool)#(A->real^3)))
                                    (FST ch INTER topspace top)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* smoothness in space *)
  SUBGOAL_THEN
   `smooth_map_on W1 (\y. lift(lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                         ((g:real->A->real^3^3) t0)) y)) /\
    smooth_map_on W1 (\y. lift(lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                         ((g:real->A->real^3^3) t0)) y / &2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LRG_LSCALAR_SMOOTH; MATCH_MP_TAC RFA_HALF_SCALAR_SMOOTH] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on W1 (\y. lift(c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                             ((g:real->A->real^3^3) t0)) y / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  ABBREV_TAC
   `LR = llap (metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
              (lscalar (metric_local atlas ch (g t0))) y0` THEN
  ABBREV_TAC
   `NR = ltnorm2 2 (metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
                   (lric2 (metric_local atlas ch (g t0))) y0` THEN
  (* time derivatives *)
  SUBGOAL_THEN
   `((\t. lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) t)) y0)
     has_real_derivative (LR + &2 * NR)) (atreal t0 within {s | t0 - d1 <= s /\ s <= t0})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(BETA_RULE(ISPECL [`V:real^3->bool`; `a:real`; `b:real`;
       `\t. metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
       `t0:real`; `y0:real^3`] LSCALAR_EVOLUTION)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (q:real->real^3->real) t y0 -
          c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                    ((g:real->A->real^3^3) t)) y0 / &2)
     has_real_derivative (Dq - (c * inv(&2)) * (LR + &2 * NR)))
    (atreal t0 within {s | t0 - d1 <= s /\ s <= t0})`
  (LABEL_TAC "T3") THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t. c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                         ((g:real->A->real^3^3) t)) y0 / &2) =
      (\t. (c * inv(&2)) * lscalar (metric_local atlas ch (g t)) y0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the Laplacian of the barrier at y0 *)
  SUBGOAL_THEN
   `llap (metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
         (\y. (q:real->real^3->real) t0 y -
              c * lscalar (metric_local atlas ch (g t0)) y / &2) y0 =
    llap (metric_local atlas ch (g t0)) (q t0) y0 - (c * inv(&2)) * LR`
  (LABEL_TAC "T4") THENL
   [MP_TAC(ISPECL [`W1:real^3->bool`;
                   `metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `(q:real->real^3->real) t0`;
                   `\y. c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                       ((g:real->A->real^3^3) t0)) y / &2`;
                   `y0:real^3`] RFA_LLAP_SUB) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(\y. c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                         ((g:real->A->real^3^3) t0)) y / &2) =
      (\y. (c * inv(&2)) * lscalar (metric_local atlas ch (g t0)) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`W1:real^3->bool`;
                   `metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                               ((g:real->A->real^3^3) t0))`;
                   `c * inv(&2)`; `y0:real^3`] RFA_LLAP_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* assembling the barrier *)
  EXISTS_TAC `min d1 (t0 - a)` THEN EXISTS_TAC `W1:real^3->bool` THEN
  EXISTS_TAC
   `\t y. (q:real->real^3->real) t y -
          c * lscalar (metric_local atlas (ch:(A->bool)#(A->real^3))
                                    ((g:real->A->real^3^3) t)) y / &2` THEN
  EXISTS_TAC `Dq - (c * inv(&2)) * (LR + &2 * NR)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `mfd_scalar atlas ((g:real->A->real^3^3) t0) (chart_inv (ch:(A->bool)#(A->real^3)) y) =
      lscalar (metric_local atlas ch (g t0)) y`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `u <= v ==> u - r <= v - r:real`) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[ASSUME
      `mfd_scalar atlas ((g:real->A->real^3^3) t0) x0 = &2 * (lam0 + p2 + p3)`] THEN
    MP_TAC(SPEC `t0:real` (ASSUME
      `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
           lscalar (metric_local atlas (ch:(A->bool)#(A->real^3)) (g t)) y0`)) THEN
    REWRITE_TAC[ASSUME
      `mfd_scalar atlas ((g:real->A->real^3^3) t0) x0 = &2 * (lam0 + p2 + p3)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(q:real->real^3->real) t0 y0`)) THEN
    REFL_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `u <= v ==> u - r <= v - r:real`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `(q:real->real^3->real) t y0`)) (concl th) &&
      can (find_term (fun t -> t = `d1:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{s | t0 - d1 <= s /\ s <= t0}` THEN CONJ_TAC THENL
     [USE_THEN "T3" ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "T4" (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `NR:real`)) THEN
  REWRITE_TAC[ASSUME
    `mfd_scalar atlas ((g:real->A->real^3^3) t0) x0 = &2 * (lam0 + p2 + p3)`] THEN
  MP_TAC(SPECL [`lam0:real`; `p2:real`; `p3:real`; `c:real`; `B:real`]
               RFA_PN3_REACTION) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `lam0 + p2 + p3 <= B` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lam0 - c * (lam0 + p2 + p3) < &0` ASSUME_TAC THENL
     [UNDISCH_TAC `lam0 - c * mfd_scalar atlas ((g:real->A->real^3^3) t0) x0 / &2 < &0` THEN
      SUBGOAL_THEN
       `mfd_scalar atlas ((g:real->A->real^3^3) t0) x0 = &2 * (lam0 + p2 + p3)`
      SUBST1_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `llap (metric_local atlas (ch:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
         ((q:real->real^3->real) t0) y0 + &2 * (lam0 pow 2 + p2 * p3) = Dq` THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Preservation of the pointwise pinching lambda >= c R/2 along              *)
(* a Ricci flow on a closed 3-manifold with lambda >= 0, by the minimum      *)
(* principle RFA_MINP_BARRIER with H = 0, psi(t,u) = 2 B min u 0 and the     *)
(* barrier RFA_PN3_BARRIER, B = 3 sup abs(Rm) on [a,(t+b)/2].  The           *)
(* structure follows RFA_HI_PINCH_PRESERVED and RFA_SECMIN_LOWER_PRESERVED.  *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c.
     ricci_flow_from (top,atlas) a b g
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. mfd_sec_min atlas (g (FST z)) (SND z) -
                c * mfd_scalar atlas (g (FST z)) (SND z) / &2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                     (subtopology (top:A topology) (topspace top)),
       euclideanreal)
      (\z. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                      ((g:real->A->real^3^3) (FST z)) (SND z)) /\
    continuous_map
      (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                     (subtopology (top:A topology) (topspace top)),
       euclideanreal)
      (\z. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                       ((g:real->A->real^3^3) (FST z)) (SND z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN;
      MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ricci_flow_from];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN ASM_REWRITE_TAC[]);;

let RFA_PN3_PINCH_PRESERVED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c.
     compact_space top /\ ricci_flow_from (top,atlas) a b g /\ &0 <= c /\
     (!t x. a <= t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     (!x. x IN topspace top
          ==> c * mfd_scalar atlas (g a) x / &2 <= mfd_sec_min atlas (g a) x)
     ==> !t x. a <= t /\ t < b /\ x IN topspace top
               ==> c * mfd_scalar atlas (g t) x / &2 <= mfd_sec_min atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x -
                    c * mfd_scalar atlas (g t) x / &2`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= l - r ==> r <= l:real`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `x1:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `e = (t1 + b) / &2` THEN
  SUBGOAL_THEN `t1 < e /\ e < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`; `e:real`]
         RFA_RMD2_SQRT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `C3 = &3 * C` THEN
  SUBGOAL_THEN `&0 <= C3` ASSUME_TAC THENL
   [EXPAND_TAC "C3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace(top:A topology)`; `a:real`; `e:real`; `g:real->A->real^3^3`;
                 `\t x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                    ((g:real->A->real^3^3) t) (x:A) -
                        c * mfd_scalar atlas (g t) x / &2`;
                 `\t:real u:real. &2 * C3 * min u (&0)`; `\t:real. &0`]
         RFA_MINP_BARRIER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [(* atlas *)
    FIRST_ASSUM ACCEPT_TAC;
    (* compact *)
    ASM_REWRITE_TAC[GSYM compact_space];
    (* open *)
    REWRITE_TAC[OPEN_IN_TOPSPACE];
    (* a < e *)
    ASM_REAL_ARITH_TAC;
    (* metrics *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* continuity *)
    MATCH_MP_TAC RFA_CMAP_RESTRICT_TU THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SUBSET_REFL] THEN
    MATCH_MP_TAC RFA_PN3_CONTINUOUS THEN ASM_REWRITE_TAC[];
    (* Lipschitz *)
    REPEAT STRIP_TAC THEN EXISTS_TAC `&2 * C3` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= C ==> abs C = C`; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    (* H' = psi(t,H) *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `min (&0) (&0) = &0`; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    (* initial *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `r <= l ==> &0 <= l - r:real`) THEN ASM_SIMP_TAC[];
    (* the barrier *)
    MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `t0 < b /\
      &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t0) x0 /\
      &3 * sqrt(rfa_rmd2 0 atlas (g t0) x0) <= C3`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        UNDISCH_TAC
         `!t x. a <= t /\ t < b /\ x IN topspace top
                ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                      ((g:real->A->real^3^3) t) x` THEN
        DISCH_THEN(MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        EXPAND_TAC "C3" THEN
        MATCH_MP_TAC(REAL_ARITH `x <= C ==> &3 * x <= &3 * C`) THEN
        UNDISCH_TAC
         `!t x. a <= t /\ t <= e /\ x IN topspace top
                ==> sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                                    ((g:real->A->real^3^3) t) x) <= C` THEN
        DISCH_THEN(MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t0:real`; `x0:A`; `c:real`; `C3:real`]
           RFA_PN3_BARRIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^3->bool`
      (X_CHOOSE_THEN `phi:real->real^3->real` (X_CHOOSE_THEN `D:real`
        STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^3->bool`; `phi:real->real^3->real`;
                          `D:real`] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> min x (&0) = x`]]);;


(* ------------------------------------------------------------------------- *)
(* From pinching at a point to the pointwise pinching function.              *)
(* If every sectional curvature at x is at most (1+e) times every other one, *)
(* then each is at most (1+e) lambda, and R/2 is the sum of the three        *)
(* sectional curvatures of a frame (RFA_FRAME3), so R/2 <= 3 (1+e) lambda.   *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_LOCAL_PINCH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) e x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     &0 < e /\
     (!u v u' v'. ~collinear {vec 0,u,v} /\ ~collinear {vec 0,u',v'}
                  ==> mfd_sectional atlas g x u v <=
                      (&1 + e) * mfd_sectional atlas g x u' v')
     ==> inv(&3 * (&1 + e)) * mfd_scalar atlas g x / &2 <= mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + e /\ &0 < &3 * (&1 + e)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
    SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> mfd_sectional atlas (g:A->real^3^3) x u v <= (&1 + e) * mfd_sec_min atlas g x`
  (LABEL_TAC "secb") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_sectional atlas (g:A->real^3^3) x u v / (&1 + e) <= mfd_sec_min atlas g x`
    MP_TAC THENL
     [REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        EXISTS_TAC `mfd_sectional atlas (g:A->real^3^3) x (basis 1) (basis 2)` THEN
        MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN
        DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3`
          STRIP_ASSUME_TAC)) THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
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
    `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`; `basis 1:real^3`;
    `basis 2:real^3`] RFA_FRAME3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")))))))) THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) x / &2 <= (&3 * (&1 + e)) * mfd_sec_min atlas g x`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_scalar] THEN USE_THEN "sum" SUBST1_TAC THEN
    SUBGOAL_THEN
     `mfd_sectional atlas (g:A->real^3^3) x u1 v1 <= (&1 + e) * mfd_sec_min atlas g x /\
      mfd_sectional atlas g x u1 w1 <= (&1 + e) * mfd_sec_min atlas g x /\
      mfd_sectional atlas g x v1 w1 <= (&1 + e) * mfd_sec_min atlas g x`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "secb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&3 * (&1 + e)) * ((&3 * (&1 + e)) * mfd_sec_min atlas (g:A->real^3^3) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &3 * (&1 + e)` THEN
    CONV_TAC REAL_FIELD]);;


(* ------------------------------------------------------------------------- *)
(* Isotropy, Einstein and Schur.  lambda >= R/6 at a point                   *)
(* gives sec = R/6 for every plane (RFA_PN3_ISO_POINT); isotropy at x holds  *)
(* in every chart at x (RFA_PN3_ISO_CHART, LSECTIONAL_CHART_TRANS); an       *)
(* isotropic point is Einstein (RFA_PN3_EINSTEIN_ISO, Ricci eigenframe);     *)
(* Einstein on a chart gives dR = 0 there (RFA_PN3_SCHUR_CHART, by the       *)
(* contracted Bianchi identity LRG_CONTRACTED_BIANCHI and the frame trace    *)
(* RFA_TRACE_FRAME); so R is locally constant, hence constant on a connected *)
(* manifold (RFA_PN3_CONST_CURV).  Copies, with the RFA_PN3_ names, from     *)
(* pc_rfa_shrink (whose load closure is twice as large):                     *)
(* RFA_PN3_LNABLA_FMUL = RFA_SH_LNABLA_FMUL, RFA_PN3_LOCCONST_CONNECTED =    *)
(* RFA_SH_LOCCONST_CONNECTED, RFA_PN3_SCAL_LOCCONST = RFA_SH_SCAL_LOCCONST.  *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_LNABLA_FMUL = prove
 (`!k U (G:real^N->real^N^N) (h:real^N->real) (tf:real^N->(num->real^N)->real) y u.
     open U /\ y IN U /\ smooth_map_on U (\z. lift(h z)) /\
     (!u. smooth_map_on U (\z. lift(tf z u)))
     ==> lnabla k G (\z u. h z * tf z u) y u =
         rfa_d1 h y (u(k + 1)) * tf y u + h y * lnabla k G tf y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla] THEN
  MP_TAC(ISPECL [`h:real^N->real`; `\z. (tf:real^N->(num->real^N)->real) z u`; `y:real^N`;
                 `(u:num->real^N)(k + 1)`] RFA_D1_MUL_AT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rfa_d1] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC);;

let RFA_PN3_LOCCONST_CONNECTED = prove
 (`!top (h:A->real).
     connected_space top /\
     (!x. x IN topspace top
          ==> ?W. open_in top W /\ x IN W /\ !x'. x' IN W ==> h x' = h x)
     ==> !x y. x IN topspace top /\ y IN topspace top ==> h y = h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x0:A` THEN X_GEN_TAC `y0:A` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN]) THEN
  DISCH_THEN(MP_TAC o SPEC `{x:A | x IN topspace top /\ (h:A->real) x = h x0}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_MESON_TAC[]];
      REWRITE_TAC[closed_in] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_MESON_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

let RFA_PN3_SCAL_LOCCONST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
            ==> frechet_derivative (\x. lift(lscalar (metric_local atlas c g) x)) (at y) =
                (\v. vec 0))
     ==> !x. x IN topspace top
             ==> ?W. open_in top W /\ x IN W /\
                     !x'. x' IN W ==> mfd_scalar atlas g x' = mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas (x:A) = (U:A->bool,phi:A->real^N)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^N^N) x =
                lscalar (metric_local atlas (U,phi) g) ((phi:A->real^N) x)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[mfd_scalar; SND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) U) (metric_local atlas (U,phi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o
      GEN_REWRITE_RULE I [riemannian_metric]) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN IMAGE phi U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "open" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN ball((phi:A->real^N) x,r)
        ==> lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) z =
            lscalar (metric_local atlas (U,phi) g) (phi x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift(lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) z)`;
                   `ball((phi:A->real^N) x,r)`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(z:real^N) IN IMAGE (phi:A->real^N) U` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real^1`) THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(phi:A->real^N) x` (ASSUME
      `!x'. x' IN ball((phi:A->real^N) x,r)
            ==> lift(lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) x') = C`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN REWRITE_TAC[GSYM LIFT_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x':A | x' IN U /\ (phi:A->real^N) x' IN ball(phi x,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`; `euclidean:(real^N)topology`;
                   `ball((phi:A->real^N) x,r)`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x':A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x':A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x':A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x':A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x':A))`;
                 `g:A->real^N^N`; `x':A`] LSCALAR_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_PN3_ISO_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     mfd_scalar atlas g x / &6 <= mfd_sec_min atlas g x
     ==> !u v. ~collinear {vec 0,u,v}
               ==> mfd_sectional atlas g x u v = mfd_scalar atlas g x / &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_UPPER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_GE_SECMIN) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_PN3_ISO_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x k c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     c IN atlas /\ x IN FST c /\
     (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g x u v = k)
     ==> !u v. ~collinear {vec 0,u,v}
               ==> lsectional (metric_local atlas c g) (SND c x) u v = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_sectional]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?U phi. (c:(A->bool)#(A->real^3)) = (U,phi)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `?V psi. chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A) = (V,psi)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) =
      `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:(A->bool)#(A->real^3)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `linear(chart_jac (U:A->bool,phi:A->real^3) (V:A->bool,psi:A->real^3) (x:A)) /\
    (!a b. chart_jac (U:A->bool,phi:A->real^3) (V,psi) (x:A) a =
           chart_jac (U,phi) (V,psi) x b ==> a = b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                     `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`; `x:A`]
             CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`; `g:A->real^3^3`; `x:A`;
                 `u:real^3`; `v:real^3`] LSECTIONAL_CHART_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th))) THEN
  MP_TAC(ISPECL [`chart_jac (U:A->bool,phi:A->real^3) (V:A->bool,psi:A->real^3) (x:A)`;
                 `{vec 0:real^3,u,v}`]
                COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  SUBGOAL_THEN
   `chart_jac (U:A->bool,phi:A->real^3) (V:A->bool,psi:A->real^3) (x:A) (vec 0) = vec 0`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `chart_jac (U:A->bool,phi:A->real^3) (V:A->bool,psi:A->real^3) (x:A)`
                 LINEAR_0) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

let RFA_PN3_EINSTEIN_ISO = prove
 (`!U (G:real^3->real^3^3) y k.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = k)
     ==> !v w. lricci G y v w = lscalar G y / &3 * (v dot (G y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "offd")))) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp (S:real^3^3) ** basis i) dot
              ((G:real^3->real^3^3) y ** (transp S ** basis j)) = if i = j then &1 else &0`
  (LABEL_TAC "on") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `i:num`; `j:num`]
                  RFA_GFRAME_ORTHO) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j n. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ 1 <= n /\ n <= 3 /\
            ~(i = j) /\ ~(i = n) /\ ~(j = n)
            ==> lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis i)
                       (transp S ** basis i) = lscalar G y / &2 - k`
  (LABEL_TAC "diag") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `transp (S:real^3^3) ** basis j`; `transp (S:real^3^3) ** basis n`;
                   `transp (S:real^3^3) ** basis i`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL [USE_THEN "on" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN
     `lsectional (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis j)
                 (transp S ** basis n) = k`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RFA_ON_NONCOLL THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
      USE_THEN "on" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
    USE_THEN "on" (fun th -> ASM_SIMP_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis i)
                   (transp S ** basis i) = lscalar G y / &2 - k`
  (LABEL_TAC "diag1") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "diag" MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`2`; `3`]; MAP_EVERY EXISTS_TAC [`1`; `3`];
      MAP_EVERY EXISTS_TAC [`1`; `2`]] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y = &6 * k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
    USE_THEN "diag1" (fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                                MP_TAC(SPEC `3` th)) THEN
    REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `lricci (G:real^3->real^3^3) y`;
                 `\v w. lscalar (G:real^3->real^3^3) y / &3 *
                        (v dot ((G:real^3->real^3^3) y ** w))`;
                 `v:real^3`; `w:real^3`] RFA_BILIN_FRAME_EQ) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[LINEAR_LIFT_DOT];
    GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(transp (S:real^3^3) ** basis a) dot ((G:real^3->real^3^3) y ** (transp S ** basis b)) =
    if a = b then &1 else &0`
  SUBST1_TAC THENL [USE_THEN "on" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `a:num = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
    USE_THEN "diag1" (MP_TAC o SPEC `b:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN USE_THEN "offd" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;
let RFA_PN3_SCHUR_CHART = prove
 (`!U (G:real^3->real^3^3).
     metric_field U G /\
     (!z. z IN U ==> !v w. lricci G z v w = lscalar G z / &3 * (v dot (G z ** w)))
     ==> !y. y IN U ==> frechet_derivative (\x. lift(lscalar G x)) (at y) = (\v. vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(lscalar (G:real^3->real^3^3) z))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(lscalar (G:real^3->real^3^3) z / &3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(lscalar (G:real^3->real^3^3) z / &3)) = (\z. inv(&3) % lift(lscalar G z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(lscalar (G:real^3->real^3^3) z)) differentiable (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. rfa_d1 (\z. lscalar (G:real^3->real^3^3) z / &3) y v =
                    inv(&3) * rfa_d1 (lscalar G) y v`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z. lscalar (G:real^3->real^3^3) z / &3) = (\z. inv(&3) * lscalar G z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_D1_CMUL_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`; `lric2 (G:real^3->real^3^3)`;
                 `\z u. lscalar (G:real^3->real^3^3) z / &3 * lmetric2 G z u`]
                RFA_EQON_LNABLA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfa_eqon; lric2; lmetric2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfa_eqon] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "eqd") THEN
  SUBGOAL_THEN
   `!u. lnabla 2 G (lric2 (G:real^3->real^3^3)) y u =
        inv(&3) * rfa_d1 (lscalar G) y (u 3) * lmetric2 G y u`
  (LABEL_TAC "dric") THENL
   [GEN_TAC THEN USE_THEN "eqd" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`;
                   `\z. lscalar (G:real^3->real^3^3) z / &3`; `lmetric2 (G:real^3->real^3^3)`;
                   `y:real^3`; `u:num->real^3`] RFA_PN3_LNABLA_FMUL) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[LRG_LMETRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:num->real^3`]
                  LNABLA_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "eqd" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\x. lift(lscalar (G:real^3->real^3^3) x)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real^3` THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
  (* the contracted Bianchi identity at y in the direction e, before S is chosen *)
  MP_TAC(SPEC `e:real^3` (MATCH_MP LRG_CONTRACTED_BIANCHI
    (CONJ (ASSUME `metric_field U (G:real^3->real^3^3)`) (ASSUME `(y:real^3) IN U`)))) THEN
  USE_THEN "dric" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  (* the trace in the G-orthonormal frame transp S ** basis s *)
  MP_TAC(BETA_RULE(ISPECL
    [`(G:real^3->real^3^3) y`; `S:real^3^3`;
     `\p q. inv(&3) * rfa_d1 (lscalar (G:real^3->real^3^3)) y q * (p dot (G y ** e))`]
    RFA_TRACE_FRAME)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
     [REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      UNDISCH_TAC
       `linear(frechet_derivative (\x. lift(lscalar (G:real^3->real^3^3) x)) (at y))` THEN
      REWRITE_TAC[linear; rfa_d1] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[DROP_ADD; DROP_CMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  (* dR(e) in the frame *)
  SUBGOAL_THEN
   `rfa_d1 (lscalar (G:real^3->real^3^3)) y e =
    sum(1..dimindex(:3)) (\s. rfa_d1 (lscalar G) y (transp (S:real^3^3) ** basis s) *
                              ((transp S ** basis s) dot (G y ** e)))`
  (LABEL_TAC "exp") THENL
   [MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `e:real^3`] RFA_FRAME_VEXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[rfa_d1; DIMINDEX_3; VSUM_3; SUM_3] THEN
    UNDISCH_TAC
     `linear(frechet_derivative (\x. lift(lscalar (G:real^3->real^3^3) x)) (at y))` THEN
    SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_d1; ETA_AX] THEN USE_THEN "exp" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN REAL_ARITH_TAC);;

let RFA_PN3_CONST_CURV = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x / &6 <= mfd_sec_min atlas g x)
     ==> !x y u v. x IN topspace top /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                   ==> mfd_sectional atlas g x u v = mfd_scalar atlas g y / &6`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
            ==> mfd_sectional atlas (g:A->real^3^3) x u v = mfd_scalar atlas g x / &6`
  (LABEL_TAC "iso") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`] RFA_PN3_ISO_POINT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c z. c IN atlas /\ z IN IMAGE (SND c) (FST c)
          ==> !v w. lricci (metric_local atlas c (g:A->real^3^3)) z v w =
                    lscalar (metric_local atlas c g) z / &3 *
                    (v dot (metric_local atlas c g z ** w))`
  (LABEL_TAC "ein") THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `z:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `mfd_scalar atlas (g:A->real^3^3) x / &6`;
                   `c:(A->bool)#(A->real^3)`] RFA_PN3_ISO_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "iso" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MATCH_MP_TAC RFA_PN3_EINSTEIN_ISO THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                          `mfd_scalar atlas (g:A->real^3^3) x / &6`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c z. c IN atlas /\ z IN IMAGE (SND c) (FST c)
          ==> frechet_derivative (\x. lift(lscalar (metric_local atlas c (g:A->real^3^3)) x))
                                 (at z) = (\v. vec 0)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `z:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`]
                  RFA_PN3_SCHUR_CHART) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                       (g:A->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN
        USE_THEN "ein" (MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `z':real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]
                RFA_PN3_SCAL_LOCCONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)`]
                RFA_PN3_LOCCONST_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "const")] THEN
  REPEAT STRIP_TAC THEN
  USE_THEN "iso" (MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "const" (MP_TAC o SPECL [`y:A`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REFL_TAC);;


(* ------------------------------------------------------------------------- *)
(* The headline R-PINCH3.  For t0 < b and e > 0 the pinching                 *)
(* hypothesis with T = t0 gives t1 < t0 with (1+e)-pinching at t1, hence     *)
(* lambda >= R/(6(1+e)) at t1 (RFA_PN3_LOCAL_PINCH), carried to t0 by        *)
(* RFA_PN3_PINCH_PRESERVED on [t1,b); e -> 0 (RFA_PN3_LIMIT) gives           *)
(* lambda >= R/6 at t0, so every sectional curvature at t0 is one constant   *)
(* (RFA_PN3_CONST_CURV), positive since sec > 0.  RFA_PN3_RF_ON_FROM is a    *)
(* copy of P2BX_RF_ON_FROM of pc_p2b_g1c.                                    *)
(* ------------------------------------------------------------------------- *)

let RFA_PN3_RF_ON_FROM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) b (g:real->A->real^N^N) a.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ a < b
     ==> ricci_flow_from (top,atlas) a b g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a - &1`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ricci_flow_on]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`&1`; `\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                (metric_local atlas c ((g:real->A->real^N^N)(drop(fstcart z))) (sndcart z))`] THEN
  REWRITE_TAC[REAL_LT_01; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let RFA_PN3_SECMIN_NONNEG = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g x u v)
     ==> &0 <= mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
    SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_sectional atlas (g:A->real^3^3) x (basis 1) (basis 2)` THEN
    MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFA_PN3_LIMIT = prove
 (`!L R. &0 <= L /\ (!e. &0 < e ==> inv(&3 * (&1 + e)) * R / &2 <= L) ==> R / &6 <= L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!e. &0 < e ==> R <= &6 * L + &6 * (e * L)` (LABEL_TAC "lin") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &3 * (&1 + e)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&3 * (&1 + e)) * R / &2 = (R / &2) / (&3 * (&1 + e))`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `R / &6 <= L` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = (R - &6 * L) / (&12 * (L + &1))` THEN
  SUBGOAL_THEN `&0 < e /\ &12 * (L + &1) * e = R - &6 * L` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < R - &6 * L /\ &0 < &12 * (L + &1)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "e" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < &12 * (L + &1)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  USE_THEN "lin" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * L` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&12 * (L + &1) * e = R - &6 * L` THEN
  UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `~(R / &6 <= L)` THEN REAL_ARITH_TAC);;

let RFA_P2B_REQ_PINCH_ROUND3 = prove
 (`!w:B->bool. P2B_REQ_PINCH_ROUND3_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_PINCH_ROUND3_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "flow")
      (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "pinch")))))) THEN
  X_GEN_TAC `t0:real` THEN DISCH_TAC THEN
  (* the slices *)
  SUBGOAL_THEN
   `!t. t < b ==> smooth_manifold_atlas top atlas /\
                  riemannian_metric atlas ((g:real->B->real^3^3) t)`
  (LABEL_TAC "slice") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "flow" (MP_TAC o SPEC `t - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[ricci_flow_on]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* lambda >= 0 *)
  SUBGOAL_THEN
   `!t x. t < b /\ x IN topspace top
          ==> &0 <= mfd_sec_min atlas ((g:real->B->real^3^3) t) x`
  (LABEL_TAC "lam0") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_PN3_SECMIN_NONNEG THEN REPEAT STRIP_TAC THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* lambda >= R/6 at t0 *)
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfd_scalar atlas ((g:real->B->real^3^3) t0) x / &6 <=
            mfd_sec_min atlas (g t0) x`
  (LABEL_TAC "r6") THENL
   [X_GEN_TAC `x0:B` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_PN3_LIMIT THEN
    CONJ_TAC THENL [USE_THEN "lam0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pinch" (fun th -> MP_TAC(MATCH_MP (SPECL [`e:real`; `t0:real`] th)
                                                (ASSUME `&0 < e`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gp")))) THEN
    USE_THEN "slice" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `t1:real`;
                   `b:real`; `g:real->B->real^3^3`; `inv(&3 * (&1 + e))`]
                  RFA_PN3_PINCH_PRESERVED) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC RFA_PN3_RF_ON_FROM THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "lam0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:B` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_PN3_LOCAL_PINCH THEN
        EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        USE_THEN "gp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`t0:real`; `x0:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* one constant at t0 *)
  USE_THEN "slice" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t0`] RFA_PN3_CONST_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "cc")] THEN
  ASM_CASES_TAC `topspace top = {}:B->bool` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y0:B` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) t0) y0 / &6` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~collinear {vec 0:real^3,basis 1,basis 2}` ASSUME_TAC THENL
     [REWRITE_TAC[COLLINEAR_LEMMA] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
      SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "cc" (MP_TAC o SPECL [`y0:B`; `y0:B`; `basis 1:real^3`; `basis 2:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "cc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

